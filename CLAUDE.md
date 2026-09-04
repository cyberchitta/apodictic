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

The aim behind the audit (stated 2026-09-04): Austrian conclusions
fail to match reality in known cases, so some assumption is off,
and we want to POINT AT WHICH ONE in any given situation. Two
consequences for encoding. Cut assumptions as finely as reality can
pull them apart — a compressed axiom that fails explains nothing.
And sort by kind of claim: claimed-universal facts about action are
`axiom`s (on the receipt; if false, praxeology is wrong), while
situational applicability conditions are named, documented
hypotheses in the theorem statement (the theorem does not apply
where they fail). The Austrian defence "the conditions didn't
hold" then becomes checkable rather than unfalsifiable. Notes:
`_notes/2026-09-04-diagnostic-aim.md`.

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
- End-of-session habit: `/sakshi:session-close`, which writes the
  handoff to `_notes/debriefs/<YYYY-MM-DD>-close.md` with verified and
  claimed findings kept apart. That report IS the session summary;
  do not also write a dated summary note. Dated `_notes/` files are
  for decisions and findings AS THEY HAPPEN, per topic. Start a
  session that has gone cold with `/sakshi:session-open`.
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
  - Apodictic/Urgency.lean — the urgency principle as a theorem
    (derived 2026-09-04 from `swap_dominance`; independence of uses
    is a hypothesis).
  - Apodictic/MarginalUtility.lean — first theorem target: Rothbard's
    allocation version of marginal utility.
  - Apodictic/Consistency.lean — the consistency ledger, in Lean: a
    toy frame satisfying every axiom's statement plus asymmetry and
    the theorems' hypotheses. Evidence, not theory; nothing depends
    on it; its proofs may be classical.
- **ApodicticDoc/** — a Verso document package, depending on the
  Apodictic library. The connected essay lives here: axiom
  archaeology narrative, findings chapter, design decisions, and
  REJECTED encodings included as type-checked Lean code with the
  argument for their rejection. This document is half the
  contribution; it is written from `_notes/` at editorial cadence
  (human decision 2026-09-05) and may lag the Lean, never
  contradict it.

Invariant: if Verso lags a Lean toolchain bump, the document waits;
never downgrade the library's toolchain to accommodate the document.
Proofs over prose, always.

Plus the lab notebook, outside both packages:

- **`_notes/`** — the contemporaneous record (the machine-standard
  `_notes` mechanism; see the `working-notes` skill). This project's
  conventions: Claude edits it as part of the work; dated files per
  topic (`_notes/YYYY-MM-DD-<topic>.md`); `_notes/OPEN.md` — a living
  list of unresolved questions kept as current state rather than
  archaeology; `_notes/debriefs/` — session-close reports, the only
  handoff surface; `_notes/sources/` — the Mises Institute editions
  (gitignored binaries + text extraction); `_notes/field-notes.md` —
  the declared destination for friction with this repo's own
  conventions (format in the file header; friction with a
  portfolio-wide ritual goes to that project's file instead).

## Conventions

- Lean 4 + mathlib. `lake build` in the library package must pass
  before any commit; the doc package builds when Verso supports the
  library's toolchain.
- Use mathlib order-theory vocabulary (Preorder/PartialOrder/
  LinearOrder) but do NOT reach for a stronger typeclass than the
  praxeological argument licenses just to close a goal.
- Axiom names are honest: no hiding axioms as instance assumptions
  or hypotheses smuggled into theorem statements. (Situational
  applicability conditions stated openly as named hypotheses are
  not smuggling — see the aim above; the rule targets universal
  claims kept off the receipt.)
- Axioms enter at point of first use. Nothing lives in Axioms.lean
  unless some theorem's `#print axioms` cites it; doctrinally
  central axioms no theorem yet needs are parked with their
  pedigree in `_notes/2026-09-04-parked-axioms.md`. (Human
  decision 2026-09-04: no reviewing axioms that do no work.)
- Constructive by default (human decision 2026-09-04). No
  `Classical.choice` on a theorem's receipt. When a proof stalls
  for want of a case split, ask whether the split is praxeological
  content (then it is a named axiom, e.g. `ends_distinguishable`)
  or logical background; never let mathlib's classical lemmas
  answer that question silently. Check with `#print axioms`.
- Consistency lives in Lean, not in notes (human decision
  2026-09-04): every axiom entering `Axioms.lean` gets its statement
  mirrored as a frame predicate in `Consistency.lean` and satisfied
  by the toy frame, together with the properties we intend to add
  (asymmetry) and the theorems' hypotheses (non-vacuity).
- Universal claims about "the agent's X" must not quantify over
  the TYPE of X-shaped structures: given one, rivals are definable
  and the axiom refutes itself (∀-frame crash 2026-08-02;
  `swap_dominance` 2026-09-04). Name the actual one with an opaque
  predicate and restrict the axiom to it.
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
      First axiom drafted: `demonstrated_preference` (human-reviewed
      2026-08-02; PARKED 2026-09-04 — never cited by a theorem).
- [x] Trusted-base architecture: distinguished frame. The ∀-frame
      form of `demonstrated_preference` was INCONSISTENT (`False`
      derived 2026-08-02; witness in notes). Axioms now speak only
      of the opaque `World`. Chosen as the simplest formalism that
      keeps the axiom receipt working (human-confirmed 2026-09-04);
      the switch to a class-of-frames encoding is mechanical if
      ever needed. The action axiom DECOMPOSES (definition / bridge
      / existence) and only the bridge does deductive work — that,
      not "existence axiom needed", is the finding; `humans_act`
      is parked, uncited. Notes:
      `_notes/2026-08-02-trusted-base-inconsistency.md`,
      `_notes/2026-09-04-first-crash-status.md`.
- [x] Marginal utility (allocation version), second pass 2026-09-04:
      `marginal_utility` stated over `marginalEnds` (Rothbard's
      definition, MES p. 27) from ONE axiom, `urgency_principle`
      (MES pp. 24–27, renamed from `allocation_demonstrated_preference`
      after reading the text). Trusted base = `World` +
      `urgency_principle`. Text-verified findings: the one-step
      proof is faithful — Rothbard's own derivation is one step from
      an ASSERTED premise; the law is strict in Rothbard too;
      he presupposes a linear value scale we don't need;
      determinacy of the drop is not in the axiom; the indifference
      language is in his own definition of supply (p. 23). Notes:
      `_notes/2026-08-02-marginal-utility-design.md`,
      `_notes/2026-09-04-mes-ch1-marginal-utility-reading.md`.
- [ ] Verso chapter "The Action Axiom" written from the notes.
- [x] Bundle encoding decided 2026-09-04: ONE preference relation,
      over `Set End`; an ordinary end is a singleton (`PrefersEnd`).
      Human's argument: all ends are composites at some grain, so
      "atomic" is action-relative like unit size. Library switched;
      receipt unchanged; review of the changed docstrings reopened.
      Notes: `_notes/2026-09-04-bundle-encoding-choice.md`.
- [x] Urgency principle DERIVED 2026-09-04 (`Urgency.lean`). Base is
      now `World` + `actual_disposition` (opaque predicate: which
      plan is the agent's) + `ends_distinguishable` (decidable
      identity of ends, data axiom) + `swap_dominance`
      (counterfactual demonstrated preference, one-swap form, for
      the actual disposition); `actual_disposition A`, independence
      of uses, and `n ≤ supply` are hypotheses of the law. Findings:
      the actual-action bridge is still uncited (Nozick's target
      carries the whole load); the general same-size-bundle bridge
      is not needed; the old axiom over-claimed beyond the supply;
      an axiom quantified over the disposition TYPE is refutable by
      a rival plan (same shape as the ∀-frame crash) — hence
      `actual_disposition`. Human approved the approach in chat;
      docstrings not yet human-read.
      Notes: `_notes/2026-09-04-urgency-derivation.md`,
      `_notes/2026-09-04-swap-dominance-overquantifies.md`.
- [ ] Route through ACTUAL action? Needs `Action` with bundle
      choices + a disposition-realization axiom. Shape decision,
      presented, not taken (OPEN.md).
- [ ] Milestone 1 completion — the honest units treatment:
      sub-stock-indexed disposition with homogeneity as an explicit
      axiom (currently enforced silently by the ℕ index type); unit
      size is action-relative (MES p. 28); document the p. 23/24
      indifference tension.
- [ ] Write-up of findings to date before attempting exchange.

## Sources of record

Mises, *Human Action* (esp. chs. 1–7); Rothbard, *Man, Economy, and
State* (esp. ch. 1); Nozick, "On Austrian Methodology" (1977) as the
adversarial reader. When citing, verify wording against the Mises
Institute editions — do not quote from memory.
