/* Parser for pvnp/proofs/manuscript-lean-inventory.md (Node only; no dependencies).
 *
 * The inventory is the single source of truth for manuscript claim statuses. This
 * parser reads the individual claim rows and the coverage table, and refuses to return
 * anything unless every listed total equals the count recomputed from the claim rows.
 */
"use strict";

const STATUSES = ["Exact", "Restricted", "Refuted", "Open"];
const PARTS = ["I", "II", "III"];

function cells(line) {
  return line.trim().replace(/^\|\s*/, "").replace(/\s*\|$/, "").split(" | ").map(s => s.trim());
}

/* Markdown escapes a literal bar inside a table cell as "\|". */
function unescapeCell(s) {
  return s.replace(/\\\|/g, "|");
}

function emptyTally() {
  return Object.fromEntries(STATUSES.map(s => [s, 0]));
}

function tally(claims, statusOf = c => c.status) {
  const counts = emptyTally();
  for (const c of claims) counts[statusOf(c)]++;
  return counts;
}

function parseInventory(markdown, label = "inventory") {
  const claims = [], seen = new Set(), table = {};
  let total = null;
  for (const line of markdown.split(/\r?\n/)) {
    if (/^\|\s*(?:I|II|III)-\d+\s*\|/.test(line)) {
      const c = cells(line);
      if (c.length !== 5) throw new Error(`${label}: malformed claim row (${c.length} columns): ${line.slice(0, 90)}`);
      const id = c[0], part = id.split("-")[0];
      if (seen.has(id)) throw new Error(`${label}: duplicate claim ID ${id}`);
      seen.add(id);
      const m = c[4].match(/^(Exact|Restricted|Refuted|Open)\b/);
      if (!m) throw new Error(`${label}: unrecognized status for ${id}: ${c[4].slice(0, 40)}`);
      claims.push({
        id, part, number: Number(id.split("-")[1]),
        title: unescapeCell(c[1]), claim: unescapeCell(c[2]), lean: unescapeCell(c[3]),
        status: m[1], details: unescapeCell(c[4])
      });
    } else if (/^\|\s*Part (?:I|II|III)\s*\|/.test(line)) {
      const c = cells(line), part = c[0].replace("Part ", "");
      if (c.length !== 6 || !c.slice(1).every(s => /^\d+$/.test(s)))
        throw new Error(`${label}: invalid coverage row for Part ${part}`);
      if (table[part]) throw new Error(`${label}: duplicate coverage row for Part ${part}`);
      table[part] = c.slice(1).map(Number);
    } else if (/^\|\s*\*\*Total\*\*\s*\|/.test(line)) {
      const c = cells(line).map(s => s.replace(/\*/g, ""));
      if (c.length !== 6 || !c.slice(1).every(s => /^\d+$/.test(s)))
        throw new Error(`${label}: invalid Total coverage row`);
      total = c.slice(1).map(Number);
    }
  }
  if (PARTS.some(p => !table[p]) || !total) throw new Error(`${label}: missing coverage table`);

  const parts = {};
  for (const part of PARTS) {
    const group = claims.filter(c => c.part === part);
    for (let i = 1; i <= table[part][0]; i++)
      if (!seen.has(`${part}-${i}`)) throw new Error(`${label}: missing claim ${part}-${i}`);
    const counts = tally(group);
    if (table[part][0] !== group.length || STATUSES.some((s, i) => counts[s] !== table[part][i + 1]))
      throw new Error(`${label}: coverage table disagrees with the claim rows for Part ${part}`);
    parts[part] = { total: group.length, counts };
  }
  const counts = tally(claims);
  if (total[0] !== claims.length || STATUSES.some((s, i) => counts[s] !== total[i + 1]))
    throw new Error(`${label}: Total row disagrees with the claim rows`);
  claims.sort((a, b) => PARTS.indexOf(a.part) - PARTS.indexOf(b.part) || a.number - b.number);
  return { claims, parts, counts, total: claims.length };
}

module.exports = { parseInventory, tally, STATUSES, PARTS };
