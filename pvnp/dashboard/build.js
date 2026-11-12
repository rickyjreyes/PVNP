#!/usr/bin/env node
/* Generates pvnp/dashboard/data.js from versioned sources. Do not edit data.js by hand.
 *
 * Sources:
 *   pvnp/proofs/manuscript-lean-inventory.md  current claim statuses (authoritative)
 *   the same file at results.json historical.commit (original-statement snapshot, via git)
 *   pvnp/dashboard/results.json               curated provenance, supporting results, CI evidence
 *   lean/PVNP/**.lean, lean/audit/AxiomAudit.lean  declaration links and audit membership
 *
 * Usage:
 *   node pvnp/dashboard/build.js           regenerate data.js
 *   node pvnp/dashboard/build.js --check   exit 1 if data.js differs from a fresh build
 * Requires a git checkout with full history (CI uses fetch-depth: 0).
 */
"use strict";
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { execFileSync } = require("node:child_process");
const { parseInventory, tally, STATUSES, PARTS } = require("./inventory.js");

const ROOT = path.resolve(__dirname, "..", "..");
const DATA_FILE = path.join(__dirname, "data.js");
const PART_NAMES = {
  I: "Curvature-Bounded Wave Computation",
  II: "Discrete WCC and Turing Equivalence",
  III: "Physical Complexity Reassessment"
};

function git(args, opts = {}) {
  return execFileSync("git", args, { cwd: ROOT, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"], ...opts });
}
function gitHas(rev) {
  try { git(["cat-file", "-e", rev + "^{commit}"]); return true; } catch (_) { return false; }
}
function blobHash(buf) {
  return crypto.createHash("sha1").update(`blob ${buf.length}\0`).update(buf).digest("hex");
}
function fail(msg) { throw new Error(msg); }

/* ---- Lean declaration index (namespace-aware, comment-stripped) ---- */
const DECL = /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([^\s:({\[⦃]+)/;

function stripComments(text) {
  let out = "", depth = 0;
  for (let i = 0; i < text.length; i++) {
    const two = text.slice(i, i + 2);
    if (two === "/-") { depth++; i++; continue; }
    if (depth > 0) {
      if (two === "-/") { depth--; i++; }
      else if (text[i] === "\n") out += "\n";
      continue;
    }
    if (two === "--") { while (i < text.length && text[i] !== "\n") i++; out += "\n"; continue; }
    out += text[i];
  }
  return out;
}

function indexLeanSource(rel, text, index) {
  const lines = stripComments(text).split("\n");
  const stack = [];
  lines.forEach((line, i) => {
    let m;
    if ((m = line.match(/^\s*namespace\s+(\S+)/))) { stack.push({ kind: "ns", name: m[1] }); return; }
    if ((m = line.match(/^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$/))) { stack.push({ kind: "sec", name: m[1] || "" }); return; }
    if (/^\s*mutual\s*$/.test(line)) { stack.push({ kind: "mutual", name: "" }); return; }
    if ((m = line.match(/^\s*end(?:\s+(\S+))?\s*$/))) {
      const name = m[1] || "";
      const j = stack.map(e => e.name).lastIndexOf(name);
      if (j < 0) fail(`${rel}:${i + 1}: unmatched 'end ${name}'`);
      stack.length = j;
      return;
    }
    if ((m = line.match(DECL))) {
      let name = m[2];
      const ns = stack.filter(e => e.kind === "ns").map(e => e.name).join(".");
      const full = name.startsWith("_root_.") ? name.slice(7) : (ns ? ns + "." + name : name);
      const entry = { full, file: rel, line: i + 1 };
      if (!index.byFull.has(full)) index.byFull.set(full, []);
      index.byFull.get(full).push(entry);
      const last = full.split(".").pop();
      if (!index.byLast.has(last)) index.byLast.set(last, []);
      index.byLast.get(last).push(entry);
    }
  });
}

function buildLeanIndex() {
  const index = { byFull: new Map(), byLast: new Map(), files: new Set() };
  const walk = dir => {
    for (const e of fs.readdirSync(path.join(ROOT, dir), { withFileTypes: true })) {
      const rel = dir + "/" + e.name;
      if (e.isDirectory()) walk(rel);
      else if (e.name.endsWith(".lean")) {
        index.files.add(rel);
        indexLeanSource(rel, fs.readFileSync(path.join(ROOT, rel), "utf8"), index);
      }
    }
  };
  walk("lean/PVNP");
  return index;
}

function unique(list) { return list && list.length === 1 ? list[0] : null; }

function lookup(index, token, ctx) {
  const tries = [];
  if (ctx) tries.push(`PVNP.${ctx}.${token}`);
  tries.push(`PVNP.${token}`, token);
  for (const t of tries) { const hit = unique(index.byFull.get(t)); if (hit) return hit; }
  const cands = (index.byLast.get(token.split(".").pop()) || []).filter(e => e.full.endsWith("." + token));
  if (cands.length === 1) return cands[0];
  if (cands.length > 1 && ctx) {
    const scoped = cands.filter(e => e.full.includes(`.${ctx}.`));
    if (scoped.length === 1) return scoped[0];
  }
  return null;
}

function namespaceOf(full) {
  const parts = full.split(".");
  parts.pop();
  if (parts[0] === "PVNP") parts.shift();
  return parts.join(".");
}

/* Expand "A.b_WCC/WCCD" into "A.b_WCC", "A.b_WCCD". */
function alternatives(token) {
  if (!token.includes("/")) return [token];
  const [first, ...rest] = token.split("/");
  const stem = first.slice(0, first.lastIndexOf("_") + 1);
  return [first, ...rest.map(r => stem + r)];
}

/* ---- main generation ---- */
/* overrides (tests only): { registry: object, inventory: string } replace the files on disk. */
function generate(overrides = {}) {
  const reg = overrides.registry || JSON.parse(fs.readFileSync(path.join(__dirname, "results.json"), "utf8"));
  const repo = reg.repository;
  const invBuf = overrides.inventory !== undefined ? Buffer.from(overrides.inventory, "utf8")
    : fs.readFileSync(path.join(ROOT, reg.inventory_path));
  const current = parseInventory(invBuf.toString("utf8"), "current inventory");

  if (!gitHas(reg.historical.commit))
    fail(`historical commit ${reg.historical.commit} is not available; fetch full history (git fetch --unshallow)`);
  const histText = git(["show", `${reg.historical.commit}:${reg.inventory_path}`]);
  const historical = parseInventory(histText, "historical inventory");
  for (const s of STATUSES)
    if (historical.counts[s] !== reg.historical.expected[s])
      fail(`historical snapshot ${s} = ${historical.counts[s]}, registry expects ${reg.historical.expected[s]}`);
  if (historical.total !== current.total) fail("historical and current inventories list different numbers of claims");

  /* Lean tree provenance: permalinks are pinned to the verified commit only if lean/ is identical to it. */
  const leanTree = git(["rev-parse", "HEAD:lean"]).trim();
  const leanDirty = git(["status", "--porcelain", "--untracked-files=no", "--", "lean"]).trim() !== "";
  const verified = reg.verification.main;
  const leanMatches = !leanDirty && leanTree === verified.lean_tree;
  const ref = leanMatches ? verified.sha : "main";
  const blob = (file, line, at = ref) => `${repo}/blob/${at}/${file}${line ? "#L" + line : ""}`;

  const index = buildLeanIndex();
  const audited = new Set();
  for (const line of fs.readFileSync(path.join(ROOT, "lean/audit/AxiomAudit.lean"), "utf8").split("\n")) {
    const m = line.match(/^#print axioms\s+(\S+)/);
    if (m) audited.add(m[1]);
  }
  const link = e => ({ name: e.full.replace(/^PVNP\./, ""), url: blob(e.file, e.line), audited: audited.has(e.full) });

  const unresolved = new Set();
  function refsFor(leanText) {
    const refs = {};
    let ctx = "";
    for (const token of (leanText.match(/`[^`]+`/g) || []).map(t => t.slice(1, -1))) {
      if (refs[token]) continue;
      if (/^[\w.]+\.\*$/.test(token)) {
        const file = `lean/PVNP/${token.slice(0, -2).replace(/\./g, "/")}.lean`;
        if (index.files.has(file)) { refs[token] = [{ name: file.replace(/^lean\//, ""), url: blob(file), audited: false }]; continue; }
      }
      const hits = [];
      for (const alt of alternatives(token)) {
        const e = lookup(index, alt, ctx);
        if (e) { hits.push(link(e)); ctx = namespaceOf(e.full); }
      }
      if (hits.length) refs[token] = hits; else unresolved.add(token);
    }
    return refs;
  }

  function invLine(text, id) {
    const n = text.split(/\r?\n/).findIndex(l => new RegExp(`^\\|\\s*${id}\\s*\\|`).test(l));
    return n + 1;
  }
  const invText = invBuf.toString("utf8");

  /* Amendments: the status changes between the snapshots must be exactly the registered amendments. */
  const histById = new Map(historical.claims.map(c => [c.id, c]));
  const changed = current.claims.filter(c => histById.get(c.id).status !== c.status).map(c => c.id).sort();
  const registered = [...reg.amendments, ...reg.formalizations].map(a => a.id).sort();
  if (JSON.stringify(changed) !== JSON.stringify(registered))
    fail(`status changes since the historical snapshot (${changed.join(", ")}) differ from registered amendments (${registered.join(", ")})`);
  const proofById = new Map(reg.formalizations.map(f => [f.id, f]));
  const amendById = new Map(reg.amendments.map(a => [a.id, a]));

  /* Conditional annotations. */
  const cond = reg.conditional;
  const condKind = new Map();
  for (const kind of ["open", "model"])
    for (const [id, note] of Object.entries(cond[kind])) {
      if (condKind.has(id)) fail(`${id} is listed as conditional twice`);
      condKind.set(id, { kind, note });
    }
  const curById = new Map(current.claims.map(c => [c.id, c]));
  for (const id of [...condKind.keys(), ...Object.keys(cond.exempt)]) {
    if (!curById.has(id)) fail(`conditional registry names unknown claim ${id}`);
    if (curById.get(id).status !== "Exact") fail(`conditional registry names ${id}, which is not Exact`);
  }
  for (const id of Object.keys(cond.exempt)) if (condKind.has(id)) fail(`${id} is both conditional and exempt`);
  const CUE = /conditional|premise|unproved|hypothes|hypothetical|assum|⇒|\bimplies\b/i;
  const unflagged = current.claims.filter(c => c.status === "Exact" && CUE.test([c.title, c.claim, c.lean, c.details].join(" "))
    && !condKind.has(c.id) && !(c.id in cond.exempt)).map(c => c.id);
  if (unflagged.length) fail(`Exact claims with conditional wording are neither annotated nor exempted: ${unflagged.join(", ")}`);

  /* A Lean column reading "same" refers to the declarations of the row above it. */
  function withSame(rows) {
    const out = new Map();
    rows.forEach((c, i) => {
      const same = c.lean.trim().toLowerCase() === "same" && i > 0 && rows[i - 1].part === c.part;
      out.set(c.id, same ? { refs: out.get(rows[i - 1].id).refs, same_as: rows[i - 1].id } : { refs: refsFor(c.lean) });
    });
    return out;
  }
  const curRefs = withSame(current.claims), histRefs = withSame(historical.claims);

  const claims = current.claims.map(c => {
    const h = histById.get(c.id);
    const out = {
      id: c.id, part: c.part, title: c.title, claim: c.claim, lean: c.lean, status: c.status, details: c.details,
      ...curRefs.get(c.id), source: `${repo}/blob/main/${reg.inventory_path}?plain=1#L${invLine(invText, c.id)}`
    };
    if (condKind.has(c.id)) out.conditional = condKind.get(c.id);
    if (proofById.has(c.id)) {
      const proof = proofById.get(c.id);
      const theorem = exact(proof.decl, c.id);
      /* The row text must be the original one, unless the registry records why it was restated. */
      const restated = typeof proof.restated === "string" && proof.restated.length > 40;
      if (h.status !== proof.from || c.status !== "Exact" || (h.claim !== c.claim && !restated) ||
          !audited.has(theorem.full) || !Object.values(out.refs).flat().some(r => r.name === proof.decl))
        fail(`${c.id}: formalization must preserve the statement and link its audited theorem`);
      out.formalized = { pr: proof.pr, decl: proof.decl, from: proof.from };
      if (restated) out.formalized.restated = proof.restated;
    }
    if (amendById.has(c.id)) {
      const a = amendById.get(c.id);
      for (const cx of a.counterexamples) {
        if (!c.lean.includes(cx)) fail(`${c.id}: retained counterexample ${cx} is not named in the current inventory row`);
        if (!Object.values(out.refs).flat().some(r => r.name.endsWith("." + cx)))
          fail(`${c.id}: retained counterexample ${cx} does not resolve to a Lean declaration`);
      }
      out.amended = { pr: a.pr, scope: a.scope, counterexamples: a.counterexamples, from: h.status };
    }
    if (h.status !== c.status || h.claim !== c.claim || h.lean !== c.lean || h.details !== c.details)
      out.historical = {
        title: h.title, claim: h.claim, lean: h.lean, status: h.status, details: h.details, ...histRefs.get(c.id),
        source: `${repo}/blob/${reg.historical.commit}/${reg.inventory_path}?plain=1#L${invLine(histText, c.id)}`
      };
    return out;
  });

  function exact(name, what) {
    const e = unique(index.byFull.get("PVNP." + name));
    if (!e) fail(`${what}: Lean declaration PVNP.${name} not found`);
    return e;
  }
  const supporting = reg.supporting.map(s => {
    const e = exact(s.decl, s.title);
    if (!audited.has(e.full)) fail(`${s.title}: PVNP.${s.decl} is not in lean/audit/AxiomAudit.lean`);
    return { ...s, file: e.file, line: e.line, url: blob(e.file, e.line), audited: true };
  });

  const pending = reg.pending.map(p => {
    const pr = reg.verification.prs.find(x => x.number === p.pr);
    if (!pr) fail(`pending result PR #${p.pr} has no verification record`);
    if (fs.existsSync(path.join(ROOT, p.file)))
      fail(`${p.file} exists in this tree: PR #${p.pr} appears merged. Move it to "supporting" with its main verification.`);
    if (pr.state === "merged") fail(`PR #${p.pr} is recorded as merged but its result is still listed as pending`);
    if (!gitHas(pr.head)) fail(`PR #${p.pr} head ${pr.head} is not available locally; run git fetch origin`);
    const src = git(["show", `${pr.head}:${p.file}`]).split("\n");
    const audit = git(["show", `${pr.head}:lean/audit/AxiomAudit.lean`]);
    const parts = p.parts.map(part => ({
      ...part,
      decls: part.decls.map(d => {
        const short = d.name.split(".").pop();
        if (!new RegExp(`^(theorem|lemma)\\s+${short}\\b`).test(src[d.line - 1] || ""))
          fail(`PR #${p.pr}: ${d.name} is not declared at ${p.file}:${d.line} in ${pr.head}`);
        return { name: d.name, url: blob(p.file, d.line, pr.head), audited: audit.includes(`#print axioms PVNP.${d.name}\n`) };
      })
    }));
    return { ...p, parts, head: pr.head, url: blob(p.file, null, pr.head), doc_url: blob(p.doc, null, pr.head) };
  });

  const open = reg.open.map(o => {
    const out = { ...o, decls: o.decls.map(d => { const e = exact(d, o.title); return { name: d, url: blob(e.file, e.line) }; }) };
    if (o.doc) {
      const lines = fs.readFileSync(path.join(ROOT, o.doc.path), "utf8").split("\n");
      const n = lines.findIndex(l => l.startsWith(o.doc.find));
      if (n < 0) fail(`${o.title}: heading "${o.doc.find}" not found in ${o.doc.path}`);
      out.doc = { path: o.doc.path, url: `${repo}/blob/main/${o.doc.path}?plain=1#L${n + 1}` };
    }
    return out;
  });
  if (open.filter(o => o.central).length !== 1) fail("exactly one open obligation must be marked central");

  const run = id => `${repo}/actions/runs/${id}`;
  const verification = {
    main: { ...verified, url: run(verified.run), commit_url: `${repo}/commit/${verified.sha}` },
    checked_at: reg.verification.checked_at,
    prs: reg.verification.prs.map(p => ({
      ...p, url: `${repo}/pull/${p.number}`, head_url: `${repo}/commit/${p.head}`,
      merge_url: p.merge_commit ? `${repo}/commit/${p.merge_commit}` : null,
      checks: p.checks.map(c => ({ ...c, url: run(c.run) }))
    }))
  };

  return {
    schema: 1,
    repository: repo,
    inventory: {
      path: reg.inventory_path, date: reg.inventory_date, blob: blobHash(invBuf),
      url: `${repo}/blob/main/${reg.inventory_path}`,
      table: { parts: current.parts, counts: current.counts, total: current.total }
    },
    historical: {
      commit: reg.historical.commit, label: reg.historical.label, description: reg.historical.description,
      url: `${repo}/blob/${reg.historical.commit}/${reg.inventory_path}`,
      table: { parts: historical.parts, counts: historical.counts, total: historical.total }
    },
    lean: { tree: leanDirty ? "uncommitted changes" : leanTree, matches_verified: leanMatches, links_ref: ref },
    parts: Object.fromEntries(PARTS.map(p => [p, PART_NAMES[p]])),
    claims, supporting, pending, open, verification,
    unresolved_lean_names: [...unresolved].sort()
  };
}

function serialize(data) {
  return "/* Generated by pvnp/dashboard/build.js from versioned sources. Do not edit by hand.\n" +
    "   Regenerate with: node pvnp/dashboard/build.js */\n" +
    "window.PVNP_DATA = " + JSON.stringify(data, null, 1) + ";\n";
}

if (require.main === module) {
  try {
    const text = serialize(generate());
    if (process.argv.includes("--check")) {
      const old = fs.existsSync(DATA_FILE) ? fs.readFileSync(DATA_FILE, "utf8") : "";
      if (old !== text) {
        console.error("pvnp/dashboard/data.js is stale. Run: node pvnp/dashboard/build.js");
        process.exit(1);
      }
      console.log("data.js is up to date with the inventory, registry and Lean sources.");
    } else {
      fs.writeFileSync(DATA_FILE, text);
      console.log(`Wrote ${path.relative(ROOT, DATA_FILE)} (${text.length} bytes).`);
    }
  } catch (e) {
    console.error("Dashboard build failed: " + e.message);
    process.exit(1);
  }
}

module.exports = { generate, serialize, stripComments, lookup, alternatives };
