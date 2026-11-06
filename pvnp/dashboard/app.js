/* PVNP formalization dashboard. Claim counts are parsed from the live manuscript inventory. */
(function (root) {
  "use strict";
  const BASE = "https://github.com/rickyjreyes/PVNP/blob/main/";
  const RAW = "https://raw.githubusercontent.com/rickyjreyes/PVNP/main/pvnp/proofs/manuscript-lean-inventory.md";
  const PROOFS = [
    ["First-answer TM tableau", "TMBooleanTableau.circuit_first", "lean/PVNP/TMBooleanTableau.lean"],
    ["Explicit polynomial circuit-size bound", "TMBooleanTableau.circuit_size", "lean/PVNP/TMBooleanTableau.lean"],
    ["P_TM ⊆ P/poly", "TMBooleanTableau.P_TM_subset_PPoly", "lean/PVNP/TMBooleanTableau.lean"],
    ["Shared-gate CNF certificate", "CircuitCNF.circuit_good", "lean/PVNP/CircuitCNF.lean"],
    ["NP verifier circuit family", "VerifierCircuits.verifier_family", "lean/PVNP/VerifierCircuits.lean"],
    ["Non-uniform NP to dense SAT projections", "SATProjection.NP_projects_to_SAT", "lean/PVNP/SATProjection.lean"],
    ["SAT circuit lower-bound equivalence", "SATProjection.SAT_circuit_lower_iff", "lean/PVNP/SATProjection.lean"],
    ["Matrix SAT encoding equivalence", "CrossingSATMatrix.instanceWord_mem", "lean/PVNP/CrossingSATMatrix.lean"],
    ["Matrix crossing-sequence inequality", "CrossingSATMatrix.matrix_time", "lean/PVNP/CrossingSATMatrix.lean"],
    ["Quadratic hard-input family", "CrossingSATMatrix.quadratic_arbitrarily_large", "lean/PVNP/CrossingSATMatrix.lean"],
    ["Restricted matrix-family circuit", "CrossingSATMatrix.matrix_promise_circuit", "lean/PVNP/CrossingSATMatrix.lean"]
  ];
  const OPEN = [
    ["Uniform Cook–Levin TM reduction (CL-1)", "pvnp/proofs/remaining-obstructions.md"],
    ["Superpolynomial SAT circuit lower bound", "lean/PVNP/SATProjection.lean"],
    ["CrossingSAT.SATLowerBound", "lean/PVNP/CrossingSAT.lean"],
    ["Classical P_TM ≠ NP_TM", "lean/PVNP/SATTarget.lean"]
  ];
  const PARTS = {I:"Curvature-Bounded Computation", II:"Discrete WCC", III:"Physical Complexity"};

  function columns(line) {
    return line.trim().replace(/^\|\s*/, "").replace(/\s*\|$/, "").split(" | ").map(s => s.trim());
  }

  function parseInventory(markdown) {
    const claims=[], summaries={};
    let totalRow=null;
    const seen=new Set();
    for (const line of markdown.split(/\r?\n/)) {
      if (/^\|\s*(?:I|II|III)-\d+\s*\|/.test(line)) {
        const parts=columns(line);
        if(parts.length !== 5) throw new Error("Malformed claim row: "+line.slice(0,100));
        const id=parts[0], part=id.split("-")[0];
        if(seen.has(id)) throw new Error("Duplicate claim ID: "+id);
        seen.add(id);
        const match=parts[4].match(/^(Exact|Restricted|Refuted|Open)\b/);
        if(!match) throw new Error("Unrecognized status for "+id);
        claims.push({id,part,title:parts[1],claim:parts[2],lean:parts[3],status:match[1],details:parts[4]});
      }
      if (/^\| Part (?:I|II|III) \|/.test(line)) {
        const parts=columns(line),part=parts[0].replace("Part ","");
        if(parts.length !== 6 || !parts.slice(1).every(s => /^\d+$/.test(s)))
          throw new Error("Invalid summary row for Part "+part);
        summaries[part]=parts.slice(1).map(Number);
      }
      if (/^\| \*\*Total\*\* \|/.test(line)) {
        const parts=columns(line).map(s=>s.replace(/\*/g,""));
        if(parts.length !== 6 || !parts.slice(1).every(s=>/^\d+$/.test(s)))
          throw new Error("Invalid total summary row");
        totalRow=parts.slice(1).map(Number);
      }
    }
    if(Object.keys(summaries).length !== 3 || !totalRow) throw new Error("Missing authoritative coverage table");
    const statuses=["Exact","Restricted","Refuted","Open"];
    const counts={Exact:0,Restricted:0,Refuted:0,Open:0};
    const parts={};
    for(const part of Object.keys(PARTS)) {
      const group=claims.filter(c=>c.part===part);
      const tally=Object.fromEntries(statuses.map(s=>[s,group.filter(c=>c.status===s).length]));
      const listed=summaries[part];
      if(listed[0] !== group.length || statuses.some((s,i)=>tally[s]!==listed[i+1]))
        throw new Error("Coverage mismatch for Part "+part);
      for(let i=1;i<=listed[0];i++) if(!seen.has(part+"-"+i))
        throw new Error("Missing claim "+part+"-"+i);
      parts[part]={total:group.length,counts:tally};
    }
    for(const c of claims)counts[c.status]++;
    if(totalRow[0]!==claims.length || statuses.some((s,i)=>counts[s]!==totalRow[i+1]))
      throw new Error("Total coverage disagrees with claim rows");
    return {claims,parts,counts,total:claims.length,exact:counts.Exact,resolved:counts.Exact+counts.Refuted};
  }

  function node(tag, cls, content) {
    const el=document.createElement(tag);
    if(cls)el.className=cls;
    if(content!==undefined)el.textContent=String(content);
    return el;
  }
  function href(label, path, cls) {
    const a=node("a",cls,label);
    a.href=path.startsWith("https://")?path:BASE+path;
    a.target="_blank";a.rel="noopener noreferrer";
    return a;
  }
  function metric(label,value,sub) {
    const e=node("div","metric");
    e.append(node("div","metric-label",label),node("div","metric-value",value),node("div","metric-sub",sub));
    return e;
  }
  function fraction(a,b) {return b?(100*a/b).toFixed(1)+"%":"0.0%";}
  function renderTop(d) {
    const e=document.getElementById("metrics");e.replaceChildren();
    e.append(metric("Manuscript claims formally proved",d.exact+" / "+d.total,fraction(d.exact,d.total)+" exact"),
      metric("Resolved by proof or counterexample",d.resolved+" / "+d.total,fraction(d.resolved,d.total)+" determined"),
      metric("Not exactly proved",d.total-d.exact,
        d.counts.Refuted+" refuted · "+d.counts.Restricted+" restricted · "+d.counts.Open+" open"));
    const statuses=document.getElementById("status-strip");statuses.replaceChildren();
    for(const s of ["Exact","Refuted","Restricted","Open"])statuses.append(metric(s,d.counts[s],"of "+d.total+" total claims"));
    document.getElementById("coverage").textContent=fraction(d.exact,d.total);
  }
  function renderParts(d) {
    const e=document.getElementById("parts");e.replaceChildren();
    for(const part of ["I","II","III"]){
      const g=d.parts[part],p=node("div","paper");
      const header=node("div","paper-head");
      header.append(node("strong","", "Part "+part+" · "+PARTS[part]),
        node("span","muted",g.counts.Exact+"/"+g.total+" · "+fraction(g.counts.Exact,g.total)));
      const track=node("div","progress");
      const fill=node("div","fill");fill.style.width=fraction(g.counts.Exact,g.total);
      track.append(fill);p.append(header,track);e.append(p);
    }
  }
  function renderProofs(){
    const e=document.getElementById("proofs");e.replaceChildren();
    for(const [title,theorem,path] of PROOFS) {
      const row=node("div","proof-row");
      row.append(href(title,path,"proof-title"),node("code","proof-symbol",theorem),node("span","proof-done","Verified"));
      e.append(row);
    }
    const open=document.getElementById("open-theorems");open.replaceChildren();
    for(const [title,path] of OPEN) {
      const row=node("div","proof-row");
      row.append(href(title,path,"proof-title"),node("span","proof-open","Open"));
      open.append(row);
    }
  }
  function renderClaims(d) {
    const area=document.getElementById("claims");
    const search=document.getElementById("claim-search");
    const part=document.getElementById("part-filter");
    const status=document.getElementById("status-filter");
    function refresh(){
      const q=search.value.toLowerCase().trim();
      const items=d.claims.filter(c=>(part.value==="all"||c.part===part.value) &&
          (status.value==="all"||c.status===status.value) &&
          (!q||[c.id,c.title,c.claim,c.lean,c.details].some(s=>s.toLowerCase().includes(q))));
      area.replaceChildren();
      document.getElementById("shown").textContent=items.length+" of "+d.total+" claims";
      for(const c of items) {
        const el=node("details","claim");
        const summary=node("summary","");
        const label=node("span","claim-heading");
        label.append(node("b","claim-id",c.id),node("span","",c.title));
        summary.append(label,node("span","status "+c.status.toLowerCase(),c.status));
        const body=node("div","claim-body");
        body.append(node("p","",c.claim),node("p","", "Lean: "+c.lean),node("p","muted",c.details));
        el.append(summary,body);area.append(el);
      }
    }
    [search,part,status].forEach(el=>el.addEventListener(el===search?"input":"change",refresh));
    refresh();
  }
  async function showGitHubDetails(){
    try {
      const r=await fetch("https://api.github.com/repos/rickyjreyes/PVNP/commits/main",
        {headers:{"Accept":"application/vnd.github+json"}});
      if(r.ok) {
        const d=await r.json();
        document.getElementById("commit-sha").textContent=(d.sha||"").slice(0,12);
        document.getElementById("commit-link").href=d.html_url||BASE;
      }
    } catch(_){}
    try {
      const r=await fetch("https://api.github.com/repos/rickyjreyes/PVNP/pulls/49",
        {headers:{"Accept":"application/vnd.github+json"}});
      if(r.ok) {
        const p=await r.json(),label=p.merged?"Merged":p.state==="open"?(p.draft?"Draft, unmerged":"Open, unmerged"):"Closed, not merged";
        document.getElementById("torus-state").textContent=label;
      }
    } catch(_){}
  }
  async function run(){
    const target=document.getElementById("load-state");
    let data=null,source="";
    for(const url of ["../proofs/manuscript-lean-inventory.md",RAW]){
      try {
        const r=await fetch(url,{cache:"no-store"});
        if(!r.ok) continue;
        const s=await r.text();
        data=parseInventory(s);source=url;break;
      }catch(_){}
    }
    if(!data){
      target.textContent="Could not load or validate the authoritative manuscript inventory. Do not use cached numbers.";
      target.className="error";
      return;
    }
    target.textContent="Live inventory validated: "+data.total+" individual claims.";
    target.className="loaded";
    document.getElementById("source-link").href=source;
    renderTop(data);renderParts(data);renderProofs();renderClaims(data);
    void showGitHubDetails();
  }
  root.PVNPFormalizationDashboard={parseInventory,PROOFS,OPEN};
  if(typeof module!=="undefined" && module.exports)module.exports={parseInventory,PROOFS,OPEN};
  if(typeof document!=="undefined")document.addEventListener("DOMContentLoaded",run);
})(typeof globalThis!=="undefined"?globalThis:this);
