---
name: gap-register
description: Read a verbal DERIVATION in Mises or Rothbard for its suppressed premises before any Lean exists — a no-repair Lamport-style rendering of the passage, a register of gaps and ambiguous readings with stable IDs, a conclusion-first check for circular and too-strong support, and a note of every step that leans on classical logic. Then, once the theorem builds, reconcile its signature against the register. Load at the scoping pre-read of a theorem target whose source ARGUES for its conclusion, and again after that target's Lean is green. Not for an asserted premise (there is no proof to read), and not a validity checker — Lean is.
---

# The gap register

The Lean signature is the project's witness to a suppressed premise,
and it is shaped by the encoding. This skill produces a second
witness that no encoding has touched: the gaps in the PROSE, read
before the vocabulary is chosen. The two are then compared.

Everything it produces is **Claude's reading** — the claimed tier.
It goes in a dated note, labelled so. It never enters a docstring or
the Verso document as a verdict, and a tidy ID does not make an
entry true. Friction with this skill: `_notes/field-notes.md`.

## When

- The source ARGUES: Mises's regress, his ladder, Rothbard's exchange
  argument. If the source only ASSERTS ("a fundamental and constant
  truth…"), write that one line in the scoping note and stop: an
  assertion has no route to audit, and a one-step Lean proof from it
  is faithful, not suspicious.
- Before the encoding decisions, as a section of the scoping note.
  After the Lean is green, Part C.

## Part A — the blind register (a fresh agent)

Run Part A in a fresh agent (`Agent`, general-purpose — NOT a fork),
because the reader must not know the vocabulary or any candidate
encoding. Give it: this file's path with "follow Part A only"; the
conclusion sentence and the argument's sentences VERBATIM (wording
already verified under `CLAUDE.md`'s Sources rule); any other
passage the owner has placed in scope. Forbid it the repo, the
notes and the web. It writes the full register to a file and
returns the register as a flat list.

### A1. Boundaries

Do not repair. Do not add a hypothesis, lemma, witness, case or
definition the passage does not supply. Do not choose between
materially different readings. Do not reorder claims to make a
dependency legal. Do not swap the author's route for a better-known
one, and do not import what the author "says elsewhere" unless that
passage was supplied. Words like "clearly", "implies", "thereby
reveals" name a step; they do not support it. A false, circular or
overstated step is preserved and marked.

### A2. Freeze the source

- The conclusion, verbatim, and its literal logical shape. Keep a
  negative-existential negative; do not normalise ¬∃¬ to ∀.
- The argument, split into `SRC-1`, `SRC-2`, … in source order. Split
  a sentence only where it carries two steps.
- Accepted primitives: **elementary logic only**, classical or
  constructive left open. Nothing about action, preference, time or
  goods is background unless a supplied sentence states it.
- **Transcription assumptions**: every place the prose had to be
  bent to be rendered at all — a counterfactual read as an
  implication, the weakest parse of a compressed clause, "he" read
  as an arbitrary agent. Each is a decision the text never made.

### A3. Render

A Lamport hierarchy in source order, each step tagged with its
`SRC-n`, each missing support marked AT the step:

```text
⟨1⟩3. ASSUME: he does not prefer the nearer.   [SRC-3]
      PROVE:  he never consumes.
  ⟨2⟩1. He does not consume today.             [SRC-5]
          Proof: OPEN — GAP-1.
  ⟨2⟩4. Q.E.D.
⟨1⟩4. Q.E.D.
          Proof: OPEN — GAP-4; the consequent of ⟨1⟩3 is never denied.
```

The constructs do the finding, so keep their rules:

- `ASSUME/PROVE` exports only the implication. A reductio therefore
  needs a SUPPLIED denial of the consequent; if none, a gap.
- `CASE`: only the cases the source gives; exhaustiveness is its own
  obligation.
- `PICK`: the existence proof comes before the witness is usable.
- `Q.E.D.`: cites only what is visible. If the source never says
  which of its claims closes the conclusion, that is an `AMB`, and
  each candidate route is carried through A5 separately.

### A4. The register

One entry per underlying defect, reused wherever it propagates:

- `GAP-n` — the source needs it and supplies nothing.
- `AMB-n` — materially different readings, none selected. Ambiguity
  in the CONCLUSION sentence counts, and usually dominates.
- `EXT-n` — the source points outside the supplied text.
- `ADM-n` — the source says it is assuming or postponing.

Each entry: the exact proposition (or the competing readings); the
step where it bites; what depends on it; what supplied text would
close it; and `load-bearing: yes/no` — whether any route to the
conclusion passes through it. An idle assertion is still recorded.

### A5. From the conclusion backward

For each candidate route: the conclusion, then what that route needs
ALL of, recursively, down to a supplied sentence, a logical step, or
a register entry. Write it as `C0 <- R (AND: …)`. Look for, and name
by node:

- **circular** — the support path returns to the claim or to its
  contrapositive. Two halves of a passage that share one unsupported
  premise are not two arguments.
- **too strong** — the conclusion claims more than the route could
  deliver even with every leaf granted. State **what the argument
  reaches**: the weaker sentence it would establish. This line is
  the pass's main product.
- **route switch** — a silent change of definition, quantifier scope
  or case, with no bridge.

No verdict headline. With logic-only primitives every verbal
argument is "not established", which says nothing.

### A6. Where the logic matters

List each step that holds only classically: ¬¬P to P; contraposition
from (¬P → ¬C) to (C → P); ∃ recovered from ¬∀¬; an unannounced
split, including trichotomy on the ranking (prefers / indifferent /
prefers the other). Say whether each is load-bearing.

## Part B — placing it (main session)

Put the returned register in the target's scoping note under
`## Gap register (Claude's reading, blind)`, IDs unchanged. Then,
per load-bearing entry, list the CANDIDATE kinds with a line of
reason each, and rule on none:

- a universal claim about action (`Praxeology.lean`);
- a situational condition (a named hypothesis of the theorem);
- logical background (then: is the split praxeological content?);
- vocabulary — true by how a term is defined, which needs the owner
  to see that the definition is doing it.

Each `AMB` and each transcription assumption becomes an item in the
note's "decisions the owner must make".

## Part C — reconciliation (after the Lean is green)

Read the theorem's signature from the file, not from memory. In the
target's dated note:

| Signature hypothesis / structure field | Register ID(s) | Outcome |
| --- | --- | --- |

- **Matched** — evidence for `Status: suppressed-premise`.
- **Hypothesis with no entry** — the encoding forced it, or the blind
  reading missed it. Re-read the passage to say which. The first is
  a finding (`CLAUDE.md`: a decision the verbal tradition never made)
  and points at `our-reconstruction`.
- **Load-bearing entry with no hypothesis** — find what absorbed it:
  a structure field, a definition, the shape of a type. If a claim
  went into the vocabulary where no signature shows it, that goes to
  the owner.
- **`AMB`** — cite the ruling that resolved it.
- A6 against `#print axioms`: a classical step the proof did without
  means the theorem is weaker than the prose conclusion (a `¬¬`);
  say so in the docstring's terms.

The outcomes are evidence for the owner's ruling on each `Status:`,
not the ruling.

## Reference

`references/worked-regress.md` — the register for Mises's regress
(*Human Action* XVIII §2), condensed from the blind trial this skill
was cut from, with its reconciliation against `regress`.

Derived from `convert-lamport` and `reverse-lamport` in
WWresearch/lamport-proof v0.2.0 (MIT; `UPSTREAM-LICENSE`). Dropped:
the forward audit (Lean does it), the mapping ledger, the verdicts.
