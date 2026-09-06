import Apodictic.Allocation

/-!
# Commitments — the COMPLETE set of praxeological assertions

Every substantive claim the theorems rest on lives in this file and
nowhere else. Nothing assertion-like — no claim folded into a
structure field of the vocabulary, no premise smuggled into a proof —
may live in any other module. The file is meant to be auditable at a
glance.

Each commitment carries a docstring with three fields:

- `Source:` citation to Mises / Rothbard, or "tacit"
- `Status:` explicit-in-tradition / suppressed-premise /
  our-reconstruction
- `Does not say:` the nearby stronger claims it deliberately omits

Docstrings are pedigree, not history. What was tried before and what
refuted it is in `_notes/`.

## Architecture: assertions are structures, not axioms

There are NO `axiom` declarations in this library. A praxeological
claim is a `structure` over an arbitrary frame, and a theorem that
needs it takes it as a named hypothesis. Two consequences, both
deliberate:

- **`#print axioms` on any theorem here prints only Lean's own
  background** (`propext`, `Quot.sound`). That is itself the report:
  we have added nothing to Lean's logic. The praxeological
  commitments are read off the theorem's SIGNATURE instead.
- **The receipt is enforced by the unused-argument linter**, not by
  the proof term. `#lint only unusedArguments` fails the build on any
  hypothesis that did no work, so a listed commitment is a used one.
  It is silenceable (`_`-prefix, `@[nolint unusedArguments]`) — so
  not silencing it is a standing policy, and any write-up must say
  so.

A claim about a given frame and a given plan quantifies over nothing
that can be constructed to refute it, and consistency is exhibited by
building an instance (`Apodictic.Consistency`).

## Policy: commitments enter at point of first use

No commitment lives here unless some theorem's signature carries it.
Doctrinally central claims that no theorem yet needs — the bridge
from actual action to preference (demonstrated preference), the
existence claim (humans act) — are parked with their pedigree in
`_notes/2026-09-04-parked-axioms.md` and re-enter with the theorem
that forces them.

## What is NOT here

Situational applicability conditions are not commitments: they are
named hypotheses stated where they apply, so that a theorem is silent
rather than false where they fail. `IndependentUses`
(`Apodictic.Action`) and `AllocationDisposition.Homogeneous`
(`Apodictic.Allocation`) are of that kind. Decidable identity of ends
travels as the instance argument `[DecidableEq F.End]`; it is a data
condition on the frame, not a claim about action.
-/

namespace Apodictic

/-- **Swap dominance** — the agent's plan beats every one-swap
alternative to it.

Take any sub-stock `U` of the units on hand, and the ends the agent
would serve with it. Now make one swap: drop a served end `e`, and
put in its place some end `e'` that the good could have served but
the plan left out. The claim is that the agent prefers the bundle he
would have served to the swapped bundle.

It is asserted of one given plan, and it is subjunctive throughout —
it speaks of sub-stocks the agent may not hold and swaps he does not
make.

Source: Rothbard, *MES*, ch. 1, §5.B, pp. 24–27 (Mises Institute
ed.): "action uses scarce means to satisfy the most urgent of the
not yet satisfied wants" (p. 24); the counterfactual framing is
Rothbard's own ("suppose ... faced with the necessity of giving up
one horse"; "he gives up the least urgent of the wants which the
larger stock would have satisfied", p. 25), backed by the
reallocation argument (p. 27: "follows from the defined
interchangeability of units and from disregard of past events").
Mises, *Human Action*, ch. VII.1.

Status: explicit-in-tradition as doctrine; the one-swap form and the
splitting-apart are our-reconstruction. Rothbard's premise fuses two
claims in one sentence: that ACTION employs the means, and that the
wants served are "the most urgent of the not yet satisfied wants"
(*MES* p. 24). This commitment keeps the ordering half and states it
subjunctively, over what the agent WOULD serve. The subjunctive is
Rothbard's own — his derivation compares a stock of six with a stock
of five and asks which want "the larger stock would have satisfied"
(p. 25), a comparison no single actual allocation delivers. The
action half is dropped, not discharged: nothing here bridges an act
to a preference. That is where the collision lives, and it is
internal to Rothbard. His own restriction is that praxeology "may
deal with utilities only as deduced from the concrete actions of
human beings" (*MES* p. 882 n. 8) — and the premise his law needs is
not one that restriction admits.

Asserted of ONE plan, not of every plan of that type. This is not a
hedge. Given one plan, rival plans can be defined, so a claim about
all of them can be refuted by construction. Stated of the single plan
a theorem is handed, the question does not arise — and that a rival
cannot also be swap-dominant becomes a theorem
(`no_rival_swap_dominant`, `Apodictic.Urgency`) rather than a
premise.

Does not say:

1. Anything about actual action. The bridge from action to
   preference appears nowhere in the library.
2. Anything about alternatives that differ by more than one swap.
3. Anything about independence of uses — that is the theorems'
   hypothesis `IndependentUses`.
4. Anything about units not on hand (`U ⊆ s.units`), which is all
   the plan is data for.
5. Anything about interchangeability of units. That two sub-stocks
   of the same size would serve the same ends is the hypothesis
   `Homogeneous`, and no part of this claim.
6. That such a plan exists, or that it is unique without further
   properties of `Prefers`. -/
structure SwapDominant {F : ActionFrame} {agent : F.Agent} {t : F.Time}
    {s : Stock F agent t} (A : AllocationDisposition s) : Prop where
  /-- The one-swap dominance itself. -/
  swap : ∀ U ⊆ s.units, ∀ e ∈ A.wouldServe U, ∀ e' ∈ s.serves,
    e' ∉ A.wouldServe U →
      F.Prefers agent t (↑(A.wouldServe U))
        (insert e' ((↑(A.wouldServe U) : Set F.End) \ {e}))

end Apodictic
