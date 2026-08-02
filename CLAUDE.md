# CLAUDE.md — apodictic project brief

## What this project is

Machine-checked formalization of Austrian praxeology (Mises, Rothbard)
in Lean 4. We take Mises's claim that praxeological theorems carry
"apodictic certainty" like mathematical theorems, and audit it with a
proof assistant.

The core method is **axiom archaeology**: the verbal deductions in
*Human Action* and *Man, Economy, and State* contain suppressed
premises. Lean refuses enthymemes, so every hidden assumption must
surface as a named, documented axiom. The research output is the
minimal axiom list under each theorem (`#print axioms <thm>`), plus
the documented archaeology of where each axiom came from.

## Division of labor — read this first

The human is the principal investigator and interrogator. Claude
drafts encodings, axioms, and proofs. The human must understand and
approve every axiom and every design decision. Therefore:

- NEVER silently choose an encoding that makes a proof easier. If two
  encodings differ in philosophical commitment, STOP and present the
  choice with trade-offs.
- An easy proof is a warning sign, not a success. If a theorem goes
  through suspiciously fast, check whether an axiom is stronger than
  its praxeological pedigree justifies, and raise it.
- Every new axiom requires: (a) an entry in doc/axioms.md BEFORE it
  enters Axioms.lean, (b) a Source field (citation to Mises/Rothbard,
  or "tacit"), (c) a Status field: explicit-in-tradition /
  suppressed-premise / our-reconstruction.
- When Lean forces a decision the verbal tradition never made
  (totality? transitivity? divisibility into units?), that is a
  FINDING. Log it in doc/findings.md, don't just resolve it and
  move on.
- Prefer ugly proofs that compile over elegant proofs. Probative
  value is identical; refactoring is a later luxury.

## Philosophical constraints (non-negotiable)

The formalization must honor what praxeology actually claims, or the
result is a strawman Austrians can rightly dismiss:

- Ordinal preference only. No cardinal utility, no real-valued
  utility functions, not even as a convenience.
- Preference is over ends; action demonstrates preference. Keep the
  latent ranking and the choice function distinct; any bridge between
  them is an AXIOM to be flagged (this is the Nozick/Rothbard
  demonstrated-preference dispute, formalized).
- Time is explicit in the action framework from the start.
- No given ends–means data hanging free: means–ends links go through
  the agent's beliefs.
- Known trap ahead: marginal utility needs homogeneous units, but
  Rothbard denies indifference is demonstrable in action. Do NOT
  paper over this — it is likely the first publishable finding.

## Structure

- Apodictic/Axioms.lean — the COMPLETE trusted base. Nothing
  axiom-like anywhere else. Auditable at a glance.
- Apodictic/Action.lean — agents, ends, means, the action framework.
- Apodictic/MarginalUtility.lean — first theorem target: Rothbard's
  allocation version of marginal utility.
- doc/axioms.md — Layer 1: every axiom in English + notation +
  pedigree. This document is half the contribution; keep it in sync
  with the Lean at every commit.
- doc/findings.md — running log of forced decisions and buried bodies.

## Conventions

- Lean 4 + mathlib. Build with `lake build`; it must pass before
  any commit.
- Use mathlib order-theory vocabulary (Preorder/PartialOrder/
  LinearOrder) but do NOT reach for a stronger typeclass than the
  praxeological argument licenses just to close a goal.
- Axiom names are honest: no hiding axioms as instance assumptions
  or hypotheses smuggled into theorem statements.
- Tactic style: plain tactics (intro/apply/exact/cases/constructor/
  simp). No heavy automation (no `decide`/`polyrith`-style closes)
  on philosophically load-bearing steps — the proof should be
  readable enough to audit which axioms did the work.
- Each commit message notes any change to the trusted base.

## Current state / next steps

- [ ] Scaffold: lake project + mathlib, file skeleton, README.
- [ ] doc/axioms.md entry 1: the action axiom. OPEN QUESTION,
      human to decide: split belief / preference / opportunity-cost
      into three separable axioms, or state as one jointly
      constitutive package? Present trade-offs before encoding.
- [ ] Action framework compiles (Action.lean).
- [ ] Milestone 1: machine-checked marginal utility with honest
      treatment of the units/indifference problem.
- [ ] Write-up of findings to date before attempting exchange.

## Sources of record

Mises, *Human Action* (esp. chs. 1–7); Rothbard, *Man, Economy, and
State* (esp. ch. 1); Nozick, "On Austrian Methodology" (1977) as the
adversarial reader. When citing, verify wording against the Mises
Institute editions — do not quote from memory.
