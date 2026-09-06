import Apodictic.Urgency

/-!
# Marginal Utility — Rothbard's allocation version

The law is stated about the *marginal utility of a supply* in
Rothbard's own sense — the end(s) that would be given up on the
loss of one unit (*MES* p. 27) — via the definition `marginalEnds`
below, in two forms:

- `marginal_utility_chain`: along a chain of specific units, what the
  second unit adds is less urgent than what the first added. Needs
  no interchangeability of units.
- `marginal_utility`: Rothbard's wording, by supply SIZE — "the
  greater the supply, the lower the marginal utility". Needs
  `plan.Homogeneous` (interchangeability), used exactly once: to say
  what "the plan at `n` units" is. Without it the supply-size form
  cannot be stated: interchangeability is a condition on STATING the
  law by size, not a premise of the ordering.

`#print axioms marginal_utility` = `[propext, Quot.sound]` —
Lean's own background (both arrive with the quotient-based `Finset`,
and with set extensionality), and nothing else: the library declares
no axioms. The
praxeological content is read off the SIGNATURE instead, and it is
one commitment plus three situational conditions: `SwapDominant plan`
(the commitment), `IndependentUses` and `plan.Homogeneous` (situational;
the latter for the supply-size form only), `[DecidableEq frame.End]` (a
data condition on the frame), and the sub-stocks being on hand. That
every one of them does real work is enforced by
`#lint only unusedArguments`, not by the proof term — see
`Apodictic.Commitments`.

What the receipt shows is read in the Verso document (part I,
findings). In brief: no axiom about ACTUAL action is cited — the law
rests on the subjunctive disposition alone; independence of uses and
interchangeability of units are hypotheses, not axioms; no
structural property of `Prefers` is forced; the law is strict, as
Rothbard's is; determinacy of the drop is not assumed; and the
marginality of the end at the smaller supply is unused by the proof
— the law holds for every end served there.
-/

namespace Apodictic

/-- One more unit always serves some new end: there is an end served
with `more` that is not served with `fewer`. Pure counting, carrying no
philosophical weight — it just keeps the law from being about
nothing. -/
theorem exists_marginal {frame : ActionFrame} {agent : frame.Agent}
    {time : frame.Time} {stock : Stock frame agent time}
    (plan : AllocationPlan stock)
    (fewer more : Finset frame.Means) (step : stock.OneMore fewer more) :
    ∃ added ∈ plan.wouldServe more, added ∉ plan.wouldServe fewer := by
  by_contra h
  have hsub : plan.wouldServe more ⊆ plan.wouldServe fewer := by
    intro want hwant
    by_contra hnew
    exact h ⟨want, hwant, hnew⟩
  have hle := Finset.card_le_card hsub
  have onHand : fewer ⊆ stock.units := fun u hu => step.2.1 (step.1 hu)
  rw [plan.oneUnitOneEnd more step.2.1, plan.oneUnitOneEnd fewer onHand,
    step.2.2] at hle
  exact Nat.not_succ_le_self fewer.card hle

/-- **Marginal utility of the step `U → V`** — of going up by one
unit — in Rothbard's own sense: the ends the extra unit adds, which
are the same as the ends that would be given up if it were lost.
"The marginal utility of the supply is the end that must be given up
as the result of a loss of the unit" (*MES* p. 27); "he gives up the
least urgent of the wants which the larger stock would have
satisfied" (p. 25).

A set of ends rather than a single end, because it is not assumed
that exactly one end drops (see the module docstring). A `Set` rather
than a `Finset` for a mechanical reason: subtracting one `Finset`
from another needs decidable equality on `frame.End`, which an arbitrary
frame does not give us, and reaching for `Classical` would put
`Classical.choice` on the receipt for no praxeological reason at all.

A definition, not a claim — Rothbard introduces it as one ("is
called", "is known as"). What licenses calling this the utility of
the *unit* is imputation of value from ends back to means: "actors
value means strictly in accordance with their valuation of the ends
that they believe the means can serve" (p. 19).

Indexed by the step rather than by a size, because which ends a unit
adds can depend on which units are already on hand — unless the plan
is `Homogeneous`. -/
def marginalEnds {frame : ActionFrame} {agent : frame.Agent}
    {time : frame.Time} {stock : Stock frame agent time}
    (plan : AllocationPlan stock)
    (fewer more : Finset frame.Means) : Set frame.End :=
  {want | want ∈ plan.wouldServe more ∧ want ∉ plan.wouldServe fewer}

/-- **The law of marginal utility, along a chain of named units.**
Take `U ⊂ V ⊂ W`, each one unit more than the last. Every end the
first step adds is preferred to every end the second step adds.

No interchangeability of units is needed, because the chain says
which units are involved. One application of `urgency_principle`; the
fact that the first step's end is marginal there goes unused
(`_notNeeded`). -/
theorem marginal_utility_chain
    {frame : ActionFrame} [DecidableEq frame.End]
    {agent : frame.Agent} {time : frame.Time}
    {stock : Stock frame agent time}
    (plan : AllocationPlan stock) (dominance : SwapDominant plan)
    (independent : frame.IndependentUses agent time)
    (small medium large : Finset frame.Means)
    (_firstStep : stock.OneMore small medium)
    (secondStep : stock.OneMore medium large) :
    ∀ addedFirst ∈ marginalEnds plan small medium,
      ∀ addedSecond ∈ marginalEnds plan medium large,
        frame.PrefersEnd agent time addedFirst addedSecond := by
  intro addedFirst hfirst addedSecond hsecond
  obtain ⟨hservedAtMedium, _notNeeded⟩ := hfirst
  obtain ⟨hservedAtLarge, hnotAtMedium⟩ := hsecond
  exact urgency_principle plan dominance independent medium large secondStep
    addedFirst hservedAtMedium addedSecond hservedAtLarge hnotAtMedium

/-- **The law of marginal utility** (Rothbard, *MES*, ch. 1, p. 27):
"The greater the supply of a good, the lower the marginal utility;
the smaller the supply, the higher the marginal utility."

This is the version stated by supply SIZE. Every end that is marginal
at a supply of `n` units is preferred to every end marginal at a
supply of `n + 1` — and that holds for ANY two one-unit steps
reaching those sizes, which need not have a single unit in common.

`plan.Homogeneous` is needed exactly once, to say that the plan with the
`n` units below the second step is the plan with the `n` units of the
first. The fact that the end at `n` is marginal there goes unused
(`_notNeeded`). -/
theorem marginal_utility
    {frame : ActionFrame} [DecidableEq frame.End]
    {agent : frame.Agent} {time : frame.Time}
    {stock : Stock frame agent time}
    (plan : AllocationPlan stock) (dominance : SwapDominant plan)
    (independent : frame.IndependentUses agent time)
    (interchangeable : plan.Homogeneous)
    (belowSmaller smaller belowLarger larger : Finset frame.Means)
    (stepToSmaller : stock.OneMore belowSmaller smaller)
    (stepToLarger : stock.OneMore belowLarger larger)
    (n : ℕ) (smallerSize : smaller.card = n)
    (largerSize : larger.card = n + 1) :
    ∀ atSmaller ∈ marginalEnds plan belowSmaller smaller,
      ∀ atLarger ∈ marginalEnds plan belowLarger larger,
        frame.PrefersEnd agent time atSmaller atLarger := by
  intro atSmaller hsmaller atLarger hlarger
  obtain ⟨hservedAtSmaller, _notNeeded⟩ := hsmaller
  obtain ⟨hservedAtLarger, hnotBelowLarger⟩ := hlarger
  have smallerOnHand : smaller ⊆ stock.units := stepToSmaller.2.1
  have belowLargerOnHand : belowLarger ⊆ stock.units :=
    fun u hu => stepToLarger.2.1 (stepToLarger.1 hu)
  have sameSize : smaller.card = belowLarger.card := by
    have := stepToLarger.2.2
    omega
  rw [interchangeable smaller smallerOnHand belowLarger belowLargerOnHand
    sameSize] at hservedAtSmaller
  exact urgency_principle plan dominance independent belowLarger larger
    stepToLarger atSmaller hservedAtSmaller atLarger hservedAtLarger
    hnotBelowLarger

#print axioms marginal_utility_chain
#print axioms marginal_utility

end Apodictic

#lint only unusedArguments
