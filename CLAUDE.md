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
- Every `axiom` declaration carries a /-- docstring -/ with three
  required fields: `Source:` (citation to Mises/Rothbard, or "tacit"),
  `Status:` (explicit-in-tradition / suppressed-premise /
  our-reconstruction), and `Does not say:` (the nearby stronger
  claims it omits). Pedigree lives in the docstring, not in a
  separate hand-authored catalog — the axiom-by-axiom catalog is the
  source itself plus the Verso document. Docstrings are PEDIGREE
  ONLY (human decision 2026-09-04): no dates, no note paths, no
  "was tried before", no commit hashes. History lives in `_notes/`
  and `_notes/`; the result part quotes
  docstrings live and must read as verdicts.
- When Lean forces a decision the verbal tradition never made
  (totality? transitivity? divisibility into units?), that is a
  FINDING. Log it in `_notes/` in the session it happens; it is
  promoted to the findings chapter of the Verso document at editorial
  cadence.
- Three-tier record. `_notes/` is the contemporaneous lab notebook:
  every design decision, rejected alternative, dead end, and open
  question gets a dated entry in `_notes/` IN THE SESSION IT HAPPENS
  — low ceremony, no quality bar, never refactored for elegance.
  Only those four kinds (human decision 2026-09-05): an explainer
  or an assessment that changes no decision and answers no OPEN.md
  item stays in chat. Docstrings carry
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
  them is a COMMITMENT to be flagged (Rothbard's
  demonstrated-preference doctrine, formalized).
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
  - Apodictic/Commitments.lean — the COMPLETE set of praxeological
    assertions. Nothing assertion-like anywhere else. Auditable at a
    glance. The library declares NO `axiom` (2026-09-06): a claim is
    a structure, carried by a theorem as a named hypothesis.
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
  the vocabulary, the commitment, the hypotheses, the theorems and
  the receipt — the human's review surface, and the only part
  emitted to the site. It is written from `_notes/` at editorial
  cadence
  (human decision 2026-09-04) and may lag the Lean, never
  contradict it. `generate-doc` does NOT produce Verso's own HTML:
  `ApodicticDoc/Emit/Eleventy.lean` replaces Verso's page layer and
  writes an Eleventy input tree (`lake exe generate-doc --output
  ../site/verso`, run after any document change; the tree is
  committed). It does NOT delete pages that leave the document:
  dropping or renaming a part needs a manual sweep of
  `site/verso/pages/`.
- **site/** — the doc site: an Eleventy consumer of Supramental Gold
  (wired per SG `wire-consumer`; ch-ai-tanya is the analog) that
  renders `site/verso/` into one page per Verso part. `bun run serve`
  to view; `.github/workflows/pages.yml` deploys to GitHub Pages
  without a Lean toolchain.

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
- Commitments are honest and legible: every universal claim is a
  named structure in Commitments.lean and appears in the signature of
  every theorem that uses it. None may be folded into a field of the
  vocabulary, where no signature shows it. The receipt IS the
  signature, and `#lint only unusedArguments` — mandatory, never
  silenced without a recorded reason — keeps it tight. `_`-prefixing
  a hypothesis is how "this does no work" is recorded, and each such
  case is a finding.
- Commitments enter at point of first use. Nothing lives in
  Commitments.lean unless some theorem's signature carries it; doctrinally
  central axioms no theorem yet needs are parked with their
  pedigree in `_notes/2026-09-04-parked-axioms.md`. (Human
  decision 2026-09-04: no reviewing axioms that do no work.)
- Constructive by default (human decision 2026-09-04). No
  `Classical.choice` on a theorem's receipt. When a proof stalls
  for want of a case split, ask whether the split is praxeological
  content (then it is a named commitment) or logical background;
  never let mathlib's classical lemmas answer that question
  silently. Check with `#print axioms` — on a library theorem it
  must print `[propext, Quot.sound]` and nothing else.
- Consistency lives in Lean, not in notes (human decision
  2026-09-04): every commitment is satisfied by the toy frame in
  `Consistency.lean`, together with the properties we intend to add
  (asymmetry) and the theorems' hypotheses (non-vacuity). It is an
  INSTANCE: `toy_law_applies` hands the toy plan to the law itself,
  so no transcription step stands between the model and what the
  theorems consume.
- Universal claims about "the agent's X" must not quantify over
  the TYPE of X-shaped structures: given one, rivals are definable
  and a claim about all of them is refutable by construction.
  Assert the claim OF the structure a theorem is handed, and let
  uniqueness be a theorem where it holds.
- Tactic style: plain tactics (intro/apply/exact/cases/constructor/
  simp). No heavy automation (no `decide`/`polyrith`-style closes)
  on philosophically load-bearing steps — the proof should be
  readable enough to audit which axioms did the work.
- Each commit message notes any change to Commitments.lean.

## Current state

Not here. `_notes/WORKLIST.md` is the worklist — what is done and
what is next. `_notes/OPEN.md` is the list of unresolved questions.
`_notes/debriefs/` is the session-close handoff. This file is
instructions only: it should change when a RULE changes, not from
session to session.

## Sources of record

Mises, *Human Action* (esp. chs. 1–7); Rothbard, *Man, Economy, and
State* (esp. ch. 1). When citing, verify wording against the Mises
Institute editions — do not quote from memory.
