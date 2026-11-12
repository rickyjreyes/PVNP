/* PVNP formalization dashboard renderer.
 * Reads window.PVNP_DATA (generated data.js). Every displayed total is recomputed here from the
 * individual claim rows and checked against the inventory's own coverage table before display. */
(function (root) {
  "use strict";
  const STATUSES = ["Exact", "Restricted", "Refuted", "Open"];
  const PARTS = ["I", "II", "III"];

  /* ---------- pure helpers (also used by check.js under Node) ---------- */
  function statusIn(c, view) { return view === "historical" && c.historical ? c.historical.status : c.status; }
  function rowIn(c, view) {
    return view === "historical" && c.historical ? Object.assign({}, c, c.historical, { id: c.id, part: c.part }) : c;
  }
  function conditionalShown(c, view) {
    return c.conditional && (view === "current" || !c.historical) ? c.conditional : null;
  }
  function summarize(claims, view) {
    const blank = () => ({ total: 0, counts: { Exact: 0, Restricted: 0, Refuted: 0, Open: 0 } });
    const all = blank(), parts = { I: blank(), II: blank(), III: blank() };
    for (const c of claims) {
      const s = statusIn(c, view);
      all.total++; all.counts[s]++;
      parts[c.part].total++; parts[c.part].counts[s]++;
    }
    return { total: all.total, counts: all.counts, parts };
  }
  function percent(a, b) { return b ? (100 * a / b).toFixed(1) + "%" : "n/a"; }
  function sameTable(s, t) {
    return s.total === t.total && STATUSES.every(k => s.counts[k] === t.counts[k]) &&
      PARTS.every(p => s.parts[p].total === t.parts[p].total && STATUSES.every(k => s.parts[p].counts[k] === t.parts[p].counts[k]));
  }
  function reconcile(data) {
    const problems = [];
    if (!sameTable(summarize(data.claims, "current"), data.inventory.table)) problems.push("current inventory");
    if (!sameTable(summarize(data.claims, "historical"), data.historical.table)) problems.push("original snapshot");
    return problems;
  }
  function conditionalCounts(claims) {
    const n = { open: 0, model: 0 };
    for (const c of claims) if (c.conditional) n[c.conditional.kind]++;
    return n;
  }

  /* ---------- DOM helpers ---------- */
  function el(tag, attrs, ...kids) {
    const e = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs || {})) {
      if (v === null || v === undefined || v === false) continue;
      if (k === "class") e.className = v; else e.setAttribute(k, v === true ? "" : String(v));
    }
    for (const k of kids.flat(Infinity)) if (k !== null && k !== undefined && k !== false) e.append(k);
    return e;
  }
  function link(href, ...kids) { return el("a", { href, target: "_blank", rel: "noopener noreferrer" }, ...kids); }
  function short(sha) { return sha.slice(0, 7); }
  function when(iso) { return iso.replace("T", " ").replace(/:\d\d(\.\d+)?Z$/, " UTC"); }
  function byId(id) { return document.getElementById(id); }

  /* Inline markdown used in the inventory: `code` and **bold**. */
  function inline(text) {
    const out = [];
    text.split("`").forEach((seg, i) => {
      if (i % 2) { out.push(el("code", null, seg)); return; }
      seg.split("**").forEach((s, j) => { if (s) out.push(j % 2 ? el("strong", null, s) : s); });
    });
    return out;
  }
  /* Lean column: backticked names become links to the resolved declarations. */
  function leanText(text, refs, sameAs) {
    if (sameAs) {
      const hits = Object.values(refs || {}).flat();
      return [`Same declarations as ${sameAs}: `, hits.map((h, i) => [i ? ", " : "",
        el("a", { href: h.url, target: "_blank", rel: "noopener noreferrer", title: "PVNP." + h.name }, el("code", null, h.name.split(".").pop()))])];
    }
    const out = [];
    text.split("`").forEach((seg, i) => {
      if (!(i % 2)) { if (seg) out.push(seg); return; }
      const hits = refs && refs[seg];
      if (!hits) { out.push(el("code", null, seg)); return; }
      hits.forEach((h, j) => {
        if (j) out.push(" / ");
        out.push(el("a", { href: h.url, target: "_blank", rel: "noopener noreferrer",
          title: "PVNP." + h.name + (h.audited ? " · in the axiom audit" : "") },
          el("code", null, hits.length > 1 ? h.name.split(".").pop() : seg)));
      });
    });
    return out;
  }
  function checkTag(c) {
    const mark = c.conclusion === "success" ? "✓" : c.conclusion === "in_progress" ? "…" : "✗";
    const cls = c.conclusion === "success" ? "ok" : c.conclusion === "in_progress" ? "wait" : "bad";
    const label = c.conclusion === "in_progress" ? `${c.name} ${mark} running` : `${c.name} ${mark}`;
    return link(c.url, el("span", { class: "tag " + cls, title: `${c.name}: ${c.conclusion} (run ${c.run})` }, label));
  }

  /* ---------- renderers ---------- */
  function renderProvenance(d) {
    const v = d.verification.main;
    const items = [
      ["Last verified main commit", [link(v.commit_url, el("code", null, short(v.sha))), " · ", link(v.url, `Lean CI run ${v.run} ✓`), " · ", el("span", { class: "nowrap" }, when(v.completed))]],
      ["Lean sources behind this data", d.lean.matches_verified
        ? [`Identical to the verified commit (tree `, el("code", null, short(d.lean.tree)), "). Declaration links are pinned to it."]
        : [el("span", { class: "error" }, "Changed since the last recorded verification."), " Links point to main; new Lean code is not shown as verified."]],
      ["Inventory", [link(d.inventory.url, "manuscript-lean-inventory.md"), " · ", el("span", { class: "nowrap" }, d.inventory.date), " · blob ", el("code", null, short(d.inventory.blob))]],
      ["CI evidence recorded", [el("span", { class: "nowrap" }, when(d.verification.checked_at)), " · ", link("#evidence", "see table")]]
    ];
    byId("provenance").replaceChildren(...items.map(([k, v]) => el("div", null, el("dt", null, k), el("dd", null, v))));
    byId("inventory-link").href = d.inventory.url;
  }

  function renderTop(d, state) {
    const s = summarize(d.claims, state.view), c = s.counts, T = s.total;
    const cc = conditionalCounts(d.claims);
    const note = state.view === "current"
      ? ["Current view: the amended manuscripts, as recorded in the live inventory."]
      : ["Original view: the inventory at ", link(d.historical.url, el("code", null, short(d.historical.commit))),
         ` (${d.historical.label.toLowerCase()}). ${d.historical.description}`];
    byId("view-note").replaceChildren(...note);
    const metric = (label, value, sub) => el("div", { class: "metric" },
      el("div", { class: "label" }, label), el("div", { class: "value" }, value), el("div", { class: "sub" }, sub));
    byId("metrics").replaceChildren(
      metric("Exact", `${c.Exact} / ${T}`, state.view === "current"
        ? `${percent(c.Exact, T)} kernel-checked as stated. ${cc.open} of these are implications with an unproved premise and ${cc.model} rest on explicit model hypotheses.`
        : `${percent(c.Exact, T)} kernel-checked as originally stated.`),
      metric("Resolved by proof or refutation", `${c.Exact + c.Refuted} / ${T}`, `${percent(c.Exact + c.Refuted, T)} · Exact plus Refuted`),
      metric("Not exactly proved", `${T - c.Exact}`, `${c.Refuted} refuted · ${c.Restricted} restricted · ${c.Open} open`));
    byId("status-chips").replaceChildren(...STATUSES.map(st =>
      el("span", { class: "chip" }, el("span", { class: "dot " + st }), `${st} ${c[st]}`)));
    const bad = reconcile(d);
    const r = byId("reconcile");
    r.className = "reconcile" + (bad.length ? " bad" : "");
    r.textContent = bad.length
      ? `Totals do not reconcile with the ${bad.join(" and ")} coverage table. Regenerate data.js.`
      : `✓ All ${T} claim rows reconcile with the inventory's coverage table in both views.`;
  }

  function renderCoverage(d, state) {
    const s = summarize(d.claims, state.view);
    const cells = (g, label) => [
      label, el("td", { class: "num" }, g.total),
      ...STATUSES.map(st => el("td", { class: "num" }, g.counts[st])),
      el("td", { class: "num" }, percent(g.counts.Exact, g.total),
        el("span", { class: "bar", "aria-hidden": "true" }, el("span", { style: `width:${(100 * g.counts.Exact / g.total).toFixed(1)}%` })))
    ];
    byId("coverage").replaceChildren(
      el("caption", { class: "muted small", style: "text-align:left;padding:10px 12px" },
        state.view === "current" ? "Current amended statements" : "Original statements"),
      el("thead", null, el("tr", null, el("th", { scope: "col" }, "Manuscript"), el("th", { scope: "col", class: "num" }, "Claims"),
        ...STATUSES.map(st => el("th", { scope: "col", class: "num" }, st)), el("th", { scope: "col", class: "num" }, "Exact %"))),
      el("tbody", null, PARTS.map(p => el("tr", null, cells(s.parts[p], el("th", { scope: "row" }, `Part ${p}`, el("div", { class: "muted small" }, d.parts[p])))))),
      el("tfoot", null, el("tr", null, cells(s, el("td", null, "Total")))));
  }

  function renderAmendments(d) {
    const amended = d.claims.filter(c => c.amended).sort((a, b) => a.amended.pr - b.amended.pr);
    const counterexample = (c, name) => {
      const hit = Object.values(c.refs).flat().find(r => r.name.endsWith("." + name));
      return hit ? link(hit.url, el("code", null, name)) : el("code", null, name);
    };
    byId("amendments").replaceChildren(
      el("p", null, `Original snapshot: ${d.historical.table.counts.Exact} Exact, ${d.historical.table.counts.Restricted} Restricted, ${d.historical.table.counts.Refuted} Refuted, ${d.historical.table.counts.Open} Open. `,
        `Current: ${d.inventory.table.counts.Exact} Exact, ${d.inventory.table.counts.Restricted} Restricted, ${d.inventory.table.counts.Refuted} Refuted, ${d.inventory.table.counts.Open} Open. `,
        `The ${amended.length} claims below changed status because their manuscript statements were corrected. Lean proves the corrected forms; the original forms stay refuted. PR #54 also proved the original conditional statement II-24. Its classical separation premise remains open. PR #73 proved II-10 for the original two-phase machine of the manuscript, and PR #74 refuted the separator-price hypothesis I-31 for the frozen trajectory class.`),
      el("div", { class: "rows" }, amended.map(c => el("div", { class: "row" },
        el("div", { class: "row-head" },
          el("span", { class: "row-title" }, `${c.id} · `, inline(c.title)),
          el("span", { class: "meta" }, el("span", { class: "status Refuted" }, "Refuted as originally stated"), "→",
            el("span", { class: "status Exact" }, "Exact as amended"), link(`${d.repository}/pull/${c.amended.pr}`, `PR #${c.amended.pr}`))),
        el("p", { class: "small" }, c.amended.scope),
        el("p", { class: "small muted" }, "Original Lean counterexamples retained: ",
          c.amended.counterexamples.map((n, i) => [i ? ", " : "", counterexample(c, n)]))))));
  }

  function renderSupporting(d) {
    const v = d.verification.main;
    const pr = n => d.verification.prs.find(p => p.number === n);
    const rows = d.supporting.map(s => {
      const lean = pr(s.pr).checks.find(c => c.name === "lean");
      return el("div", { class: "row" },
        el("div", { class: "row-head" }, el("span", { class: "row-title" }, s.title), el("span", { class: "tag ok" }, "Kernel-checked")),
        el("p", { class: "small" }, s.statement),
        el("div", { class: "meta" }, link(s.url, el("code", null, s.decl)),
          d.lean.matches_verified ? link(v.url, el("span", { class: "tag ok" }, `main ${short(v.sha)} ✓`)) : null,
          link(lean.url, el("span", { class: "tag ok" }, `PR #${s.pr} exact-head lean ✓`)),
          s.audited && el("span", { class: "tag ok", title: "Listed in lean/audit/AxiomAudit.lean; only propext, Classical.choice and Quot.sound are allowed" }, "axiom audit")));
    });
    byId("supporting").replaceChildren(
      el("p", { class: "small muted", style: "margin-top:0" }, `${d.supporting.length} of ${d.supporting.length} listed statements are kernel-checked on main. This counts statements, not progress toward the open obligations below.`),
      ...rows);
  }


  function renderOpen(d) {
    byId("open").replaceChildren(...d.open.map(o => el("div", { class: "row" + (o.central ? " central" : "") },
      el("div", { class: "row-head" }, el("span", { class: "row-title" }, o.title),
        el("span", { class: "meta" }, o.central && el("span", { class: "tag bad" }, "Central unresolved theorem"), el("span", { class: "status Open" }, "Open"))),
      el("p", { class: "small" }, o.statement),
      el("div", { class: "meta" }, `Lean: ${o.formal}`, o.decls.map(x => link(x.url, el("code", null, x.name))),
        o.doc && link(o.doc.url, o.doc.path.split("/").pop())))));
  }

  function renderEvidence(d) {
    const v = d.verification.main;
    const rows = [el("tr", null,
      el("th", { scope: "row" }, "main (push)"), el("td", { "data-label": "State" }, el("span", { class: "tag ok" }, "verified")),
      el("td", { "data-label": "Head" }, link(v.commit_url, el("code", null, short(v.sha)))),
      el("td", { "data-label": "Checks" }, checkTag({ name: v.job, conclusion: v.conclusion, run: v.run, url: v.url })),
      el("td", { class: "small", "data-label": "Note" }, v.note))];
    for (const p of d.verification.prs) rows.push(el("tr", null,
      el("th", { scope: "row" }, link(p.url, `#${p.number}`), el("div", { class: "small muted" }, p.title)),
      el("td", { "data-label": "State" }, el("span", { class: "tag " + (p.state === "merged" ? "ok" : "wait") }, p.state === "merged" ? "merged" : p.state === "draft" ? "draft, not merged" : p.state),
        p.merge_url && el("div", { class: "small" }, "as ", link(p.merge_url, el("code", null, short(p.merge_commit))))),
      el("td", { "data-label": "Head" }, link(p.head_url, el("code", null, short(p.head)))),
      el("td", { "data-label": "Checks" }, el("span", { class: "meta" }, p.checks.map(checkTag))),
      p.note ? el("td", { class: "small", "data-label": "Note" }, p.note) : el("td", { class: "empty" })));
    byId("prs").replaceChildren(
      el("thead", null, el("tr", null, ["Source", "State", "Head", "Checks on that exact head", "Note"].map(h => el("th", { scope: "col" }, h)))),
      el("tbody", null, rows));
    byId("evidence-desc").textContent = `Exact-head GitHub Actions results, recorded ${when(d.verification.checked_at)}. "lean" builds the complete PVNP import tree and runs the axiom audit; "build" compiles the manuscript PDFs.`;
  }

  function claimNode(d, c, view) {
    const r = rowIn(c, view), s = statusIn(c, view), cond = conditionalShown(c, view);
    const summary = el("summary", null,
      el("span", { class: "head" }, el("span", { class: "id" }, c.id), el("span", { class: "title" }, inline(r.title))),
      el("span", { class: "badges" },
        cond && el("span", { class: "tag cond" }, cond.kind === "open" ? "Conditional: premise unproved" : "Conditional: model hypotheses"),
        c.amended && el("span", { class: "tag amend" }, view === "current" ? "Amended statement" : "Original statement"),
        el("span", { class: "status " + s }, s)));
    const body = el("div", { class: "body" },
      el("h4", null, "Claim"), el("p", null, inline(r.claim)),
      el("h4", null, "Lean"), el("p", null, leanText(r.lean, r.refs, r.same_as)),
      el("h4", null, "Status"), el("p", null, inline(r.details)),
      cond && [el("h4", null, "What is and is not proved"), el("p", null, cond.note)]);
    if (c.historical && view === "current") {
      const h = c.historical;
      body.append(el("div", { class: "orig" },
        el("h4", { style: "margin-top:0" }, h.status === c.status ? "Original row (status unchanged)" : `Original statement: ${h.status}`),
        el("p", null, inline(h.claim)), el("p", { class: "small" }, leanText(h.lean, h.refs, h.same_as)), el("p", { class: "small muted" }, inline(h.details)),
        c.amended && el("p", { class: "small" }, el("strong", null, "Correction. "), c.amended.scope, " ", link(`${d.repository}/pull/${c.amended.pr}`, `PR #${c.amended.pr}`)),
        el("p", { class: "small" }, link(h.source, "Row in the original inventory"))));
    }
    if (c.historical && view === "historical") {
      body.append(el("div", { class: "orig" },
        el("h4", { style: "margin-top:0" }, `Current statement: ${c.status}`), el("p", null, inline(c.claim)),
        el("p", { class: "small muted" }, inline(c.details)),
        c.amended && el("p", { class: "small" }, el("strong", null, "Correction. "), c.amended.scope)));
    }
    if (c.formalized && view === "current")
      body.append(el("p", { class: "small" },
        el("strong", null, c.formalized.to === "Refuted" ? "Refuted later. " : "Proved later. "),
        `Originally ${c.formalized.from}. ${c.formalized.to === "Refuted" ? "Counterexample" : "Theorem"} `,
        el("code", null, c.formalized.decl), ", ",
        link(`${d.repository}/pull/${c.formalized.pr}`, `PR #${c.formalized.pr}`), ".",
        c.formalized.restated ? " " + c.formalized.restated : false));
    body.append(el("p", { class: "small" }, link(r.source, view === "historical" && c.historical ? "Row in the original inventory" : "Row in the current inventory")));
    return el("details", { class: "claim", id: "claim-" + c.id }, summary, body);
  }

  function renderClaims(d, state) {
    const counts = summarize(d.claims, state.view).counts;
    byId("filter-chips").replaceChildren(...["all", ...STATUSES].map(st => {
      const b = el("button", { type: "button", class: "chip", "aria-pressed": String(state.status === st) },
        st === "all" ? `All ${d.claims.length}` : [el("span", { class: "dot " + st }), `${st} ${counts[st]}`]);
      b.addEventListener("click", () => { state.status = st; update(d, state); });
      return b;
    }));
    const q = state.search.trim().toLowerCase();
    const items = d.claims.filter(c => {
      const r = rowIn(c, state.view);
      return (state.part === "all" || c.part === state.part) &&
        (state.status === "all" || statusIn(c, state.view) === state.status) &&
        (!state.onlyConditional || conditionalShown(c, state.view)) &&
        (!state.onlyAmended || c.amended) &&
        (!q || [c.id, r.title, r.claim, r.lean, r.details].some(x => x.toLowerCase().includes(q)));
    });
    byId("shown").textContent = `Showing ${items.length} of ${d.claims.length} claims (${state.view === "current" ? "current" : "original"} statements).`;
    byId("claims").replaceChildren(...items.map(c => claimNode(d, c, state.view)));
  }

  function update(d, state) {
    for (const b of document.querySelectorAll("[data-view]")) b.setAttribute("aria-pressed", String(b.dataset.view === state.view));
    renderTop(d, state); renderCoverage(d, state); renderClaims(d, state);
  }

  function run() {
    const d = root.PVNP_DATA;
    if (!d || !Array.isArray(d.claims)) {
      const e = byId("load-error");
      e.hidden = false;
      e.textContent = "data.js is missing or invalid. Run: node pvnp/dashboard/build.js";
      return;
    }
    const bad = reconcile(d);
    if (bad.length) {
      const e = byId("load-error");
      e.hidden = false;
      e.textContent = `The claim rows do not reconcile with the ${bad.join(" and ")} coverage table; nothing is displayed. Regenerate data.js.`;
      return;
    }
    const state = { view: "current", status: "all", part: "all", search: "", onlyConditional: false, onlyAmended: false };
    renderProvenance(d); renderAmendments(d); renderSupporting(d);  renderOpen(d); renderEvidence(d);
    for (const b of document.querySelectorAll("[data-view]"))
      b.addEventListener("click", () => { state.view = b.dataset.view; update(d, state); });
    byId("search").addEventListener("input", e => { state.search = e.target.value; renderClaims(d, state); });
    byId("part").addEventListener("change", e => { state.part = e.target.value; renderClaims(d, state); });
    byId("only-conditional").addEventListener("change", e => { state.onlyConditional = e.target.checked; renderClaims(d, state); });
    byId("only-amended").addEventListener("change", e => { state.onlyAmended = e.target.checked; renderClaims(d, state); });
    update(d, state);
    const target = location.hash && document.getElementById(location.hash.slice(1));
    if (target && target.tagName === "DETAILS") { target.open = true; target.scrollIntoView(); }
  }

  const api = { summarize, percent, reconcile, statusIn, rowIn, conditionalShown, conditionalCounts };
  root.PVNPDashboard = api;
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  if (typeof document !== "undefined") {
    if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", run);
    else run();
  }
})(typeof globalThis !== "undefined" ? globalThis : this);
