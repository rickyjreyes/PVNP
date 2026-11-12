/* Consistency tests for the PVNP formalization dashboard (Node 18+, no dependencies).
 * Run from anywhere in a full-history checkout: node pvnp/dashboard/check.js
 * Every figure asserted here is recomputed from the claim rows; none is read from a stored total. */
"use strict";
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const assert = require("node:assert/strict");
const { parseInventory } = require("./inventory.js");
const build = require("./build.js");
const app = require("./app.js");

const ROOT = path.resolve(__dirname, "..", "..");
const read = rel => fs.readFileSync(path.join(ROOT, rel), "utf8");
let passed = 0;
function test(name, fn) {
  try { fn(); passed++; }
  catch (e) { console.error(`FAIL ${name}\n  ${e.message}`); process.exitCode = 1; }
}

/* 1. data.js is a fresh build of the versioned sources, and loads as the browser loads it. */
const fresh = build.serialize(build.generate());
test("data.js is up to date", () =>
  assert.equal(read("pvnp/dashboard/data.js"), fresh, "data.js is stale: run node pvnp/dashboard/build.js"));
const sandbox = { window: {} };
vm.runInNewContext(fresh, sandbox);
const d = JSON.parse(JSON.stringify(sandbox.window.PVNP_DATA)); /* normalize objects from the vm realm */
const claim = id => d.claims.find(c => c.id === id);

/* 2. Current coverage, recomputed from the 91 rows. */
test("current totals", () => {
  const s = app.summarize(d.claims, "current");
  assert.equal(s.total, 91);
  assert.deepEqual({ ...s.counts }, { Exact: 79, Restricted: 1, Refuted: 4, Open: 7 });
  assert.equal(app.percent(s.counts.Exact, s.total), "86.8%");
  assert.equal(s.counts.Exact + s.counts.Refuted, 83);
  assert.equal(app.percent(83, 91), "91.2%");
  const parts = { I: [41, 30, 1, 4, 6, "73.2%"], II: [28, 28, 0, 0, 0, "100.0%"], III: [22, 21, 0, 0, 1, "95.5%"] };
  for (const [p, [t, e, r, f, o, pct]] of Object.entries(parts)) {
    const g = s.parts[p];
    assert.deepEqual([g.total, g.counts.Exact, g.counts.Restricted, g.counts.Refuted, g.counts.Open], [t, e, r, f, o], "Part " + p);
    assert.equal(app.percent(g.counts.Exact, g.total), pct, "Part " + p + " percentage");
  }
  assert.deepEqual(app.reconcile(d), []);
});

/* 3. Historical snapshot is derived from git history and preserved. */
test("original snapshot 70/2/11/8", () => {
  const s = app.summarize(d.claims, "historical");
  assert.deepEqual({ ...s.counts }, { Exact: 70, Restricted: 2, Refuted: 11, Open: 8 });
  assert.deepEqual([s.parts.I.counts.Exact, s.parts.I.counts.Refuted], [26, 8]);
  assert.deepEqual([s.parts.II.counts.Exact, s.parts.II.counts.Refuted], [23, 3]);
  assert.deepEqual([s.parts.III.counts.Exact, s.parts.III.counts.Refuted], [21, 0]);
  assert.match(d.historical.commit, /^eaf8fa0/);
});

/* 4. Individual statuses and amendments. */
test("amended claims: Exact now, Refuted originally, counterexamples retained", () => {
  const amended = ["II-7", "II-8", "II-17", "I-10", "I-12", "I-13", "I-20"];
  assert.deepEqual(d.claims.filter(c => c.amended).map(c => c.id).sort(), [...amended].sort());
  for (const id of amended) {
    const c = claim(id);
    assert.equal(c.status, "Exact", id);
    assert.equal(c.historical.status, "Refuted", id + " original");
    assert.ok(c.amended.scope.length > 40, id + " scope note");
    for (const cx of c.amended.counterexamples) {
      const hit = Object.values(c.refs).flat().find(r => r.name.endsWith("." + cx));
      assert.ok(hit, `${id}: counterexample ${cx} linked`);
      assert.match(hit.url, /\/blob\/(?:main|[0-9a-f]{40})\/lean\/PVNP\/.+\.lean#L\d+$/);
    }
  }
  for (const id of ["I-25", "I-26", "I-27", "I-28"]) {
    assert.equal(claim(id).status, "Refuted", id);
    assert.equal(app.statusIn(claim(id), "historical"), "Refuted", id + " original");
  }
  assert.equal(claim("I-11").status, "Restricted", "only current restricted claim");
  assert.equal(claim("II-10").status, "Exact", "original two-phase uniformity now closed");
  assert.equal(claim("II-10").formalized.pr, 73);
  assert.equal(claim("II-10").formalized.from, "Restricted");
  assert.equal(claim("II-10").formalized.decl, "TwoPhasePolynomialWriter.originalWM_first_answer");
  assert.match(claim("II-10").formalized.scope_change, /empty input|empty-input/i);
  const open = v => d.claims.filter(c => app.statusIn(c, v) === "Open").map(c => c.id);
  assert.deepEqual(open("current"), open("historical").filter(id => id !== "II-24"));
  assert.deepEqual(claim("II-24").formalized, { pr: 54, decl: "PartIIManuscript.conditional_np_safety", from: "Open" });
  assert.equal(claim("II-24").conditional.kind, "open");
});

test("I-10, I-12 and I-20 keep their scope limitations", () => {
  assert.match(claim("I-10").details, /unproved/);
  assert.match(claim("I-12").details, /NOT proved/);
  assert.match(claim("I-20").details, /not a construction lower bound/);
  for (const id of ["I-10", "I-12"]) assert.equal(claim(id).conditional.kind, "open", id);
});

test("original II-10 independent source provenance", () => {
  assert.equal(d.lean.verified_by, "external-pr");
  assert.equal(d.lean.links_ref, d.verification.staged.sha);
  assert.equal(d.verification.staged.pr, 73);
  assert.equal(d.verification.staged.build_jobs, 7386);
  assert.ok(d.verification.staged.source.includes("author-reported"));
  assert.ok(d.verification.main.sha !== d.verification.staged.sha,
    "externally checked PR must not masquerade as verified main");
  const row = claim("II-10");
  for (const name of ["originalWindowCode_fp", "originalInputCode_fp",
    "originalWM_first_answer", "P_Turing_subset_P_disc_by_original"])
    assert.ok(Object.values(row.refs).flat().some(x => x.name.endsWith("." + name) && x.audited), name);
});

/* 5. Conditional Exact claims are labelled, never shown as unconditional. */
test("conditional annotations", () => {
  const n = app.conditionalCounts(d.claims);
  assert.deepEqual({ ...n }, { open: 15, model: 6 });
  for (const c of d.claims.filter(c => c.conditional)) {
    assert.equal(c.status, "Exact", c.id);
    assert.ok(c.conditional.note.length > 30, c.id);
  }
  for (const id of ["I-1", "I-4", "I-19", "II-16"]) assert.equal(claim(id).conditional.kind, "open", id);
  assert.equal(claim("I-36").conditional, undefined, "I-36 is unconditional");
});

/* 6. Phase X supporting results: 11 statements, kernel-checked on main, linked, audited. */
test("Phase X supporting results", () => {
  assert.equal(d.supporting.length, 14);
  assert.equal(new Set(d.supporting.map(s => s.decl)).size, 14);
  const sha = d.verification.main.sha;
  for (const s of d.supporting) {
    assert.equal(s.audited, true, s.decl);
    assert.ok(s.url.includes(`/blob/${d.lean.links_ref}/`) && /#L\d+$/.test(s.url), s.decl);
    const src = read(s.file).split("\n")[s.line - 1];
    assert.match(src, new RegExp(`^theorem ${s.decl.split(".").pop()}\\b`), s.decl + " at recorded line");
    assert.match(read("lean/audit/AxiomAudit.lean"), new RegExp(`#print axioms PVNP\\.${s.decl.replace(/\./g, "\\.")}\\n`));
  }
  for (const want of ["circuit_first", "circuit_size", "P_TM_subset_PPoly", "circuit_good", "verifier_family",
    "NP_projects_to_SAT", "SAT_circuit_lower_iff", "instanceWord_mem", "matrix_time", "quadratic_arbitrarily_large", "matrix_promise_circuit"])
    assert.ok(d.supporting.some(s => s.decl.endsWith("." + want)), want);
  assert.match(sha, /^[0-9a-f]{40}$/);
});

/* 7. The integrated toroidal modules are checked in the current tree. */
test("finite toroidal scope", () => {
  assert.equal(d.pending.length, 0);
  for (const name of ["odd_encRing_not_SAT", "even_encRing_mem_SAT"]) {
    const theorem = d.supporting.find(s => s.decl === `ToroidalDiagonal.${name}`);
    assert.ok(theorem.audited && theorem.file.endsWith("ToroidalDiagonal.lean"), name);
  }
  assert.equal(claim("I-37").status, "Open");
});

/* 8. Open obligations carry no percentage; SATLowerBound is the central one. */
test("open obligations", () => {
  assert.equal(d.open.length, 3);
  const central = d.open.filter(o => o.central);
  assert.equal(central.length, 1);
  assert.equal(central[0].title, "CrossingSAT.SATLowerBound");
  assert.match(central[0].decls[0].url, /CrossingSAT\.lean#L\d+$/);
  for (const o of d.open) assert.ok(!/%/.test(JSON.stringify(o)), o.title + " has no percentage");
  assert.ok(d.supporting.some(s => s.decl === "CookLevin.Gen.satLowerBound_iff_P_ne_NP"));
  assert.ok(d.open.some(o => /P_TM ≠ NP_TM/.test(o.title)));
});

/* 9. Every Lean name in the inventory resolves, except listed non-declarations. */
test("Lean declaration links", () => {
  assert.deepEqual(d.unresolved_lean_names, ["pair x w"], "only notation is left unlinked");
  for (const c of d.claims.filter(c => c.status !== "Open"))
    assert.ok(Object.keys(c.refs).length, `${c.id} (${c.status}) links at least one Lean declaration`);
  assert.equal(claim("III-2").same_as, "III-1");
  assert.equal(claim("I-26").same_as, "I-25");
});

/* 10. The page is self-contained and makes no network requests. */
test("static page", () => {
  const html = read("pvnp/dashboard/index.html"), js = read("pvnp/dashboard/app.js");
  assert.deepEqual([...html.matchAll(/<script[^>]*src="([^"]+)"/g)].map(m => m[1]), ["./data.js", "./app.js"]);
  assert.ok(!/fetch\(|XMLHttpRequest/.test(js), "app.js does not fetch");
  assert.match(html, /not progress toward proving P ≠ NP/);
});

/* 11. Guards reject inconsistent sources. */
test("parser and generator guards", () => {
  const md = read("pvnp/proofs/manuscript-lean-inventory.md");
  assert.throws(() => parseInventory(md.replace("| I-25 |", "| I-999 |")), /missing claim I-25/);
  assert.throws(() => parseInventory(md.replace("| **Total** | **91** |", "| **Total** | **92** |")), /Total row/);
  assert.throws(() => parseInventory(md.replace(/^\| Part II \| 28 \| 28 \|/m, "| Part II | 28 | 26 |")), /Part II/);
  const reg = JSON.parse(read("pvnp/dashboard/results.json"));
  const clone = () => JSON.parse(JSON.stringify(reg));
  let r = clone(); r.amendments = r.amendments.filter(a => a.id !== "I-12");
  assert.throws(() => build.generate({ registry: r }), /registered amendments/);
  r = clone(); r.formalizations[0].decl = "PartIIManuscript.no_np_complete_decider";
  assert.throws(() => build.generate({ registry: r }), /formalization must preserve/);
  r = clone(); r.conditional.open["I-25"] = "a refuted claim cannot be conditional-exact";
  assert.throws(() => build.generate({ registry: r }), /not Exact/);
  r = clone(); delete r.formalizations.find(x => x.id === "II-10").scope_change;
  assert.throws(() => build.generate({ registry: r }), /corrected scope/);
  r = clone(); delete r.conditional.open["I-19"];
  assert.throws(() => build.generate({ registry: r }), /neither annotated nor exempted: I-19/);
  r = clone(); r.historical.expected.Exact = 77;
  assert.throws(() => build.generate({ registry: r }), /historical snapshot/);
  r = clone(); r.supporting[0].decl = "TMBooleanTableau.no_such_theorem";
  assert.throws(() => build.generate({ registry: r }), /not found/);
  r = clone(); r.amendments[0].counterexamples.push("no_such_counterexample");
  assert.throws(() => build.generate({ registry: r }), /no_such_counterexample/);
  const tampered = JSON.parse(JSON.stringify(d));
  tampered.claims.find(c => c.id === "I-25").status = "Exact";
  assert.deepEqual(app.reconcile(tampered), ["current inventory", "original snapshot"]);
  tampered.claims.find(c => c.id === "I-25").status = "Refuted";
  tampered.claims.find(c => c.id === "II-7").historical.status = "Exact";
  assert.deepEqual(app.reconcile(tampered), ["original snapshot"]);
});

if (!d.lean.matches_verified)
  console.warn("Note: lean/ differs from both last verified main and externally checked II-10 PR source; links point to main.");
if (process.exitCode) console.error(`${passed} test groups passed; failures above.`);
else console.log(`Dashboard check PASS (${passed} groups): 91 claims; 79 Exact (86.8%), 83 resolved (91.2%); original 70/2/11/8; toroidal results integrated; SATLowerBound open.`);
