# Worked register — Mises's regress

Condensed from a blind trial run 2026-09-21: a fresh agent, given
only the passage and the two upstream skills, with no sight of this
repository. Recast here in this skill's format; the propositions and
IDs are the trial's, renumbered without zero-padding. The
reconciliation (Part C) was done afterwards against
`Apodictic/Apodictic/TimePreference.lean` and `Dated.lean`.

It is Claude's reading throughout.

## A2. The source

*Human Action*, ch. XVIII, §2.

**Conclusion (T).** "No mode of action can be thought of in which
satisfaction within a nearer period of the future is not—other things
being equal—preferred to that in a later period." Shape kept: ¬∃M ¬P(M).

- `SRC-1` "The very act of gratifying a desire implies that
  gratification at the present instant is preferred to that at a later
  instant."
- `SRC-2` "He who consumes a nonperishable good instead of postponing
  consumption for an indefinite later moment thereby reveals a higher
  valuation of present satisfaction as compared with later
  satisfaction."
- `SRC-3` "If he were not to prefer satisfaction in a nearer period of
  the future to that in a remoter period, he would never consume and
  so satisfy wants."
- `SRC-4` "He would always accumulate, he would never consume and
  enjoy."
- `SRC-5` "He would not consume today, but he would not consume
  tomorrow either, as the morrow would confront him with the same
  alternative."

Transcription assumptions: (1) the counterfactual of `SRC-3` is read
as an implication under an `ASSUME`; (2) "never consume and so satisfy
wants" takes its weakest parse, never [consume-and-thereby-satisfy];
(3) "he" is an arbitrary agent.

## A3. Rendering

```text
⟨1⟩1. Gratifying a desire implies present gratification is
      preferred to later.                                   [SRC-1]
        Proof: OPEN — GAP-1, GAP-2.
⟨1⟩2. Consuming a nonperishable good instead of postponing
      reveals a higher valuation of the present.            [SRC-2]
        Proof: OPEN — GAP-1.  Relation to ⟨1⟩1 unstated: AMB-5.
⟨1⟩3. ASSUME: he does not prefer the nearer to the remoter. [SRC-3; AMB-4]
      PROVE:  he never consumes.
  ⟨2⟩1. He does not consume today.                          [SRC-5]
          Proof: OPEN — GAP-1 (contrapositive), GAP-3.
  ⟨2⟩2. The morrow confronts him with the same alternative. [SRC-5]
          Proof: OPEN — GAP-6.
  ⟨2⟩3. He does not consume tomorrow either.                [SRC-5]
          Proof: by ⟨2⟩2, with ⟨2⟩1 ("either").
  ⟨2⟩4. He never consumes.                             [SRC-3, SRC-4]
          Proof: OPEN — GAP-7.
  ⟨2⟩5. He always accumulates.                              [SRC-4]
          Proof: OPEN — GAP-5.
  ⟨2⟩6. Q.E.D.  by ⟨2⟩4.
⟨1⟩4. Q.E.D. (of T)
        Proof: AMB-5 — no closing sentence; OPEN — GAP-4, GAP-3.
```

## A4. Register

- `AMB-1` "can be thought of": a plain universal, or a claim that the
  contrary is unthinkable — which needs a contradiction, not a
  behavioural consequence. (`SRC-3`–`SRC-5` think the excluded mode of
  action through.) Bites at T. load-bearing: yes.
- `AMB-2` "mode of action": one act, a whole conduct through time, or
  a kind of acting. `SRC-1` says "the very act"; `SRC-3`–`SRC-5` follow
  one man across days. load-bearing: yes.
- `AMB-3` "other things being equal": the same satisfaction differing
  only in date; all circumstances at both dates; or whatever excludes
  every case where the later is preferred, which makes T unfalsifiable.
  The clause never recurs in the argument. load-bearing: yes.
- `AMB-4` scope over periods and occasions: nearer preferred for every
  pair always, or at least sometimes. The `ASSUME` inherits it.
  load-bearing: yes.
- `AMB-5` architecture: (A) T directly from `SRC-1`; (B) a reductio
  from `SRC-3`–`SRC-5`; (C) `SRC-3`–`SRC-5` as the support for `SRC-1`.
  load-bearing: yes.
- `GAP-1` choosing a over an available b implies a is preferred to b.
  Named by "implies" and "thereby reveals"; used a third time, in
  contrapositive, at ⟨2⟩1. load-bearing: yes, under every route.
- `GAP-2` every act of gratification forgoes the same gratification
  later. `SRC-2` stipulates it for one case; `SRC-1` is unrestricted.
  load-bearing: yes (A, C).
- `GAP-3` (i) the present counts as a "nearer period of the future";
  (ii) present-versus-later extends to every nearer/later pair T
  covers. load-bearing: yes.
- `GAP-4` the consequent is never denied: nothing says a man must at
  some time consume. load-bearing: yes — a reductio with no absurdity.
- `GAP-5` "always accumulate": more than "never consume".
  load-bearing: no.
- `GAP-6` "the same alternative": the same good, the same later
  option, AND the same absence of preference. load-bearing: yes.
- `GAP-7` from today and tomorrow to "never": induction over a
  succession of days that nothing supplies. load-bearing: yes.

## A5. Backward

```text
C0 <- RA (AND: C1, GAP-3ii, GAP-4 [an act exists], AMB-1..4)
C0 <- RB (AND: C3, GAP-4 [no one never consumes], AMB-1..4)
C1 <- R1 (AND: GAP-1, GAP-2)
C1 <- RC (AND: C3, contraposition [classical], independence of C3)
C3 <- R3 (AND: O5, GAP-6, GAP-7)
O5 <- (AND: GAP-1 contrapositive, GAP-3i)
```

- **circular** (reading C): `C1 <- C3 <- O5 <- GAP-1`, and `GAP-1` is
  the content of `C1`. On A and B the two halves of the passage are
  not two arguments: they share one unsupported premise.
- **too strong** (route B): the iteration needs the assumption to hold
  on every day, so denying it yields only the weak reading of `AMB-4`.
  **What the argument reaches**, every leaf granted: *no mode of
  action is one in which the nearer is never preferred, in the
  today-versus-later comparison.*

## A6. Logic

1. T is ¬∃¬, and the reductio ends there. The positive "is preferred"
   of `SRC-1` and `SRC-2` needs ¬¬P → P. load-bearing: for the positive
   form only.
2. Reading C needs (¬P → ¬C) ⊢ (C → P), classical. The direction used
   at O5 is constructive.
3. Route A needs an actual act, ∃; denying "never" gives ¬∀¬.
4. "Not prefer" read as "prefers to postpone" is a trichotomy on the
   ranking. Not load-bearing.

## C. Reconciliation against `regress`

| Signature hypothesis / structure field | Register | Outcome |
| --- | --- | --- |
| `demonstrated : DemonstratedTimePreference act` | `GAP-1` | matched |
| `consumes : morrows.ConsumesAt n act` — an act at date `n` | `GAP-4` | matched |
| — its conjunct `offer (n+1) ∈ act.forgone` | `GAP-2` | matched, cut to the one act |
| `sameAlternative` | `GAP-6`, first two thirds | matched |
| `carries : NoPreferenceCarries` | `GAP-6`, last third | matched; the Lean cut one gap into two conditions |
| `Morrows.date : ℕ → Time`, `successive` | `GAP-7` | matched; absorbed by the ℕ index of a carried structure, visible as `morrows` |
| `Morrows.dated` — an offer is attained at its date | none | the encoding forced it: the prose never gives a satisfaction a date of its own |
| conclusion at `date 0` of one sequence | `GAP-3ii`, `AMB-4`, "what the argument reaches" | no hypothesis, and rightly: the theorem claims only what the route reaches |
| `Before`, not "present" | `GAP-3i` | sidestepped: the claim speaks of sooner only (`DemonstratedTimePreference`, *Does not say* 2) |
| `SameSatisfaction` | `AMB-3` | ruled, `_notes/2026-09-18-time-preference-rulings.md` |
| the regress as a theorem, `SRC-1`/`SRC-2` as the claim | `AMB-5`, the circle | reading B taken; "one premise used twice" is in `_notes/OPEN.md` |
| conclusion `¬ ¬ PrefersEnd …`; `#print axioms`: none | A6.1 | matched — the theorem is the ¬¬ form, as its docstring says |
| — | `AMB-1`, `AMB-2` | no ruling found in `_notes/` |
| — | `GAP-5` | idle in the prose, absent from the Lean |

Every hypothesis the Lean forced is in the blind register, and one
field (`dated`) is ours. Nothing load-bearing was absorbed unseen.
