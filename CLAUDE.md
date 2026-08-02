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
- Every `axiom` declaration carries a /-- docstring -/ with two
  required fields: `Source:` (citation to Mises/Rothbard, or "tacit")
  and `Status:` (explicit-in-tradition / suppressed-premise /
  our-reconstruction). Pedigree lives in the docstring, not in a
  separate hand-authored catalog — the axiom-by-axiom catalog is the
  source itself plus the Verso document.
- When Lean forces a decision the verbal tradition never made
  (totality? transitivity? divisibility into units?), that is a
  FINDING. Log it in `_notes/` in the session it happens; it is
  promoted to the findings chapter of the Verso document at editorial
  cadence.
- Three-tier record. `_notes/` is the contemporaneous lab notebook:
  every design decision, rejected alternative, dead end, and open
  question gets a dated entry in `_notes/` IN THE SESSION IT HAPPENS
  — low ceremony, no quality bar, never refactored for elegance.
  Nothing may exist only in a chat transcript. Docstrings carry
  per-declaration pedigree (above). The Verso document is the curated
  argument, written FROM the notes at editorial cadence — it may lag
  `_notes/`, never contradict them. Rejected encodings enter the
  document as type-checked Lean code with the argument for their
  rejection.
- End-of-session habit: a `_notes/` entry summarizing decisions made
  and questions opened.
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

Two lake packages in this repo:

- **Apodictic/** — the library: axioms, action framework, theorems.
  Depends on mathlib ONLY. This package must ALWAYS build standalone
  with `lake build`. It is the trusted artifact; nothing may ever
  block it.
  - Apodictic/Axioms.lean — the COMPLETE trusted base. Nothing
    axiom-like anywhere else. Auditable at a glance.
  - Apodictic/Action.lean — agents, ends, means, the action framework.
  - Apodictic/MarginalUtility.lean — first theorem target: Rothbard's
    allocation version of marginal utility.
- **ApodicticDoc/** — a Verso document package, depending on the
  Apodictic library. The connected essay lives here: axiom
  archaeology narrative, findings chapter, design decisions, and
  REJECTED encodings included as type-checked Lean code with the
  argument for their rejection. This document is half the
  contribution; keep it in sync with the Lean at every commit.

Invariant: if Verso lags a Lean toolchain bump, the document waits;
never downgrade the library's toolchain to accommodate the document.
Proofs over prose, always.

Plus the lab notebook, outside both packages:

- **`_notes/`** — the contemporaneous record (the machine-standard
  `_notes` mechanism; see the `working-notes` skill). This project's
  conventions: Claude edits it as part of the work; dated files per
  session (`_notes/YYYY-MM-DD-<topic>.md`), plus one pinned
  exception, `_notes/OPEN.md` — a living list of unresolved questions
  kept as current state rather than archaeology.

## Conventions

- Lean 4 + mathlib. `lake build` in the library package must pass
  before any commit; the doc package builds when Verso supports the
  library's toolchain.
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

- [x] Scaffold: two lake packages (library + Verso doc), file
      skeleton, README.
- [x] Action-axiom shape decided: shape C — action structure as a
      definition, assertions as separable axioms. Provisional;
      revisit after Milestone 1. Resolution, rejected alternatives,
      and micro-decisions in `_notes/2026-08-02-action-axiom-shape.md`.
- [x] Action framework compiles (Action.lean), first approximation.
      First axiom in the trusted base: `demonstrated_preference`
      (human-reviewed 2026-08-02).
- [x] Trusted-base architecture: distinguished frame. The ∀-frame
      form of `demonstrated_preference` was INCONSISTENT (`False`
      derived 2026-08-02; witness in notes). Axioms now speak only
      of the opaque `World`; `humans_act` enters as the non-vacuity
      axiom — resolving the existence-axiom question (yes, needed:
      as existence, not inference). Notes:
      `_notes/2026-08-02-trusted-base-inconsistency.md`.
- [x] Marginal utility, first pass (allocation version):
      `marginal_utility` proved via new vocabulary (Allocation.lean:
      `Stock`, serviceability-homogeneity; `AllocationDisposition`,
      counterfactual choice) and one new axiom
      (`allocation_demonstrated_preference`). Praxeological ledger:
      `World` + that axiom alone — `demonstrated_preference` does no
      work, and nothing is forced on `Prefers`. Axioms of 2026-08-02
      pending human review (see OPEN.md). Notes:
      `_notes/2026-08-02-marginal-utility-design.md`.
- [ ] Verso chapter "The Action Axiom" written from the notes.
- [ ] Milestone 1 completion — the honest units treatment:
      sub-stock-indexed disposition with homogeneity as an explicit
      axiom (currently enforced silently by the ℕ index type), and/or
      decomposition of `allocation_demonstrated_preference` into its
      three compressed commitments.
- [ ] Write-up of findings to date before attempting exchange.

## Sources of record

Mises, *Human Action* (esp. chs. 1–7); Rothbard, *Man, Economy, and
State* (esp. ch. 1); Nozick, "On Austrian Methodology" (1977) as the
adversarial reader. When citing, verify wording against the Mises
Institute editions — do not quote from memory.
