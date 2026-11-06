/* Pure Node.js consistency test for the source-driven dashboard (no dependencies). */
"use strict";
const fs=require("node:fs");
const path=require("node:path");
const assert=require("node:assert/strict");
const {parseInventory,PROOFS,OPEN}=require("./app.js");

const source=path.join(__dirname,"..","proofs","manuscript-lean-inventory.md");
const markdown=fs.readFileSync(source,"utf8");
const d=parseInventory(markdown);
assert.equal(d.total,91);
assert.equal(d.exact,77);
assert.equal(d.resolved,81);
assert.deepEqual(d.counts,{Exact:77,Restricted:2,Refuted:4,Open:8});
const expected={
  I:{total:41,exact:30,restricted:1,refuted:4,open:6},
  II:{total:28,exact:26,restricted:1,refuted:0,open:1},
  III:{total:22,exact:21,restricted:0,refuted:0,open:1}
};
for(const [part,e] of Object.entries(expected)){
  assert.equal(d.parts[part].total,e.total);
  for(const status of ["Exact","Restricted","Refuted","Open"])
    assert.equal(d.parts[part].counts[status],e[status.toLowerCase()]);
}
const claim=id=>d.claims.find(c=>c.id===id);
for(const id of ["II-7","II-8","II-17","I-10","I-12","I-13","I-20"])
  assert.equal(claim(id).status,"Exact",id+" amended");
for(const id of ["I-25","I-26","I-27","I-28"])
  assert.equal(claim(id).status,"Refuted",id+" original");
assert.equal(PROOFS.length,11,"Phase X exact supporting proofs");
assert.equal(OPEN.length,4,"Major open obligations");
assert.equal(new Set(PROOFS.map(p=>p[1])).size,PROOFS.length,"Distinct supporting proofs");
assert.ok(OPEN.some(p=>p[0].includes("SATLowerBound")),"Explicit unresolved decisive target");
assert.throws(()=>parseInventory(markdown.replace("| I-25 |","| I-999 |")),"Missing claim detection");
assert.throws(()=>parseInventory(markdown.replace("| **Total** | **91** |","| **Total** | **92** |")),"Summary mismatch detection");
console.log("Dashboard check PASS: 91 reconciled claim rows, 77 exact, 81 resolved; four categories and all 11 Phase X proof links.");
