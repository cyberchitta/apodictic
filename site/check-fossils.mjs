#!/usr/bin/env node
// Fail on retired vocabulary anywhere a reader can see it.
//
// The failure this exists to catch: prose that describes the current design by
// contrast with a deleted one. It survives every build, and it survives a grep
// scoped to renamed identifiers, because the sentence contains no identifier at
// all. Four instances reached production before this check existed — the last
// of them in the <head>, where nobody reads.
//
// Scope is the BUILT site (head included) plus the public source files, because
// two of the four lived outside the Verso document.
//
// Adding a rule: a `pattern` must be specific enough that no legitimate
// sentence matches. Bare `axiom` does not qualify — `#print axioms`, "axiom
// archaeology" and "no `axiom`" are all correct usage.

import { readFileSync, readdirSync, statSync, existsSync } from "node:fs";
import { join, relative } from "node:path";

const ROOT = new URL("..", import.meta.url).pathname;

const RULES = [
  // --- identifiers deleted by the axiom -> structure switch (2026-09-06) ---
  { pattern: /Axioms\.lean/, why: "Axioms.lean was deleted" },
  { pattern: /\bactual_disposition\b|\bends_distinguishable\b|\bswap_dominance\b/,
    why: "axiom deleted in the structure switch" },
  { pattern: /\bApodictic\.World\b/, why: "the World structure was deleted" },
  // --- renamed by the reading-names pass (2026-09-06) ---
  { pattern: /AllocationDisposition/, why: "renamed to AllocationPlan" },
  { pattern: /\bcard_eq\b/, why: "renamed to oneUnitOneEnd" },
  { pattern: /\bserves_subset\b/, why: "renamed to servesOnlyWhatItCan" },
  { pattern: /Stock\.homog\b/, why: "renamed to Stock.unitsAlike" },
  // --- replaced by the horse frame (2026-09-06) ---
  { pattern: /\btoy_[a-zA-Z]+\b|\bswapPrefers\b/, why: "toy frame is now the horse frame" },
  { pattern: /\btoy frame\b/i, why: "the model is Rothbard's horses now" },
  // --- retired claims ---
  { pattern: /one collision/i, why: "the merged-collision finding was retired" },
  { pattern: /the axioms (each|the) theorem/i,
    why: "the library declares no axiom; the receipt is the signature" },
  { pattern: /axioms each theorem actually rests on/i,
    why: "the library declares no axiom" },
  { pattern: /#print axioms[^.]{0,70}(the whole point|is the receipt)/i,
    why: "the receipt is the signature; #print axioms only shows Lean's background" },
  // --- part slugs dropped by the restructure (2026-09-06) ---
  { pattern: /href="\/The-Result\/(Axioms|Commitments|Hypotheses|Theorems|Vocabulary|Findings|Not-in-the-base|Consistency)\//,
    why: "part renamed by the restructure; this link 404s" },
];

function walk(dir, out = []) {
  for (const name of readdirSync(dir)) {
    const p = join(dir, name);
    if (statSync(p).isDirectory()) walk(p, out);
    else if (p.endsWith(".html")) out.push(p);
  }
  return out;
}

const targets = [];
const built = join(ROOT, "site", "_site");
if (existsSync(built)) targets.push(...walk(built));
else console.error("note: site/_site not found — run `bun run build` first\n");
for (const f of ["README.md", "site/_data/site.json"]) {
  const p = join(ROOT, f);
  if (existsSync(p)) targets.push(p);
}

const hits = [];
for (const file of targets) {
  const lines = readFileSync(file, "utf8").split("\n");
  lines.forEach((line, i) => {
    for (const { pattern, why } of RULES) {
      const m = line.match(pattern);
      if (m) hits.push({ file: relative(ROOT, file), line: i + 1, found: m[0], why });
    }
  });
}

if (hits.length === 0) {
  console.log(`fossil check: clean (${targets.length} files)`);
  process.exit(0);
}
console.error(`fossil check: ${hits.length} hit(s)\n`);
for (const h of hits) console.error(`  ${h.file}:${h.line}  "${h.found}" — ${h.why}`);
process.exit(1);
