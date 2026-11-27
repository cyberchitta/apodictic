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
- `marginal_utility`: Rothbard's wording, by supply SIZE — "The
  greater the supply of a good, the lower the marginal utility".
  Needs
  `plan.Homogeneous` (interchangeability), used exactly once: to say
  what "the plan at `n` units" is. Without it the supply-size form
  cannot be stated: interchangeability is a condition on STATING the
  law by size, not a premise of the ordering.

`#print axioms marginal_utility` = `[propext, Quot.sound]` —
Lean's own background (both arrive with the quotient-based `Finset`,
and with set extensionality), and nothing else: the library declares
no axioms. The
praxeological content is read off the SIGNATURE instead, and it is
one praxeological claim plus three situational conditions: `SwapDominant plan`
(the claim), `IndependentUses` and `plan.Homogeneous` (situational;
the latter for the supply-size form only), `[DecidableEq praxis.End]` (a
data condition on the frame), and the sub-stocks being on hand. That
every one of them does real work is enforced by
`#lint only unusedArguments`, not by the proof term — see
`Apodictic.Praxeology`.

What the manifest shows is read in the Verso document (part I,
findings). In brief: no axiom about ACTUAL action is cited — the law
rests on the subjunctive disposition alone; independence of uses and
interchangeability of units are hypotheses, not axioms; no
structural property of `Prefers` is forced; the law is strict, as
Rothbard's is; determinacy of the drop is not assumed; and the
marginality of the end at the smaller supply is unused by the proof
— the law holds for every end served there.
-/

namespace Apodictic

/-- **Marginal utility of a one-unit step**, from `fewer` to `more`,
in Rothbard's own sense. It is the ends the extra unit adds. These are
the same ends that would be given up if it were lost.
"The marginal utility of the supply is the end that must be given up
as the result of a loss of the unit" (*MES* p. 27); "he gives up the
least urgent of the wants which the larger stock would have
satisfied" (p. 25).

It is a set of ends rather than a single end, because nothing here
assumes that exactly one end drops. Determinacy of the drop is not
among the law's premises. It is a `Set` (a collection given by a condition on its members)
rather than a `Finset` (a finite collection listed member by member)
for a mechanical reason. Subtracting one `Finset` from another requires
being able to decide when two ends are the same end. An arbitrary
frame does not give us that. Lean's classical axiom
(`Classical.choice`) would supply the test. No theorem outside
`Consistency.lean`, the file of small frames, uses that axiom. Using it here would add it to the
logical background of every theorem stated with this definition, for
no praxeological reason at all.

It is a definition, not a claim. Rothbard introduces it as a
definition ("is called", "is known as"). What licenses calling this
the utility of the *unit* is imputation of value from ends back to
means: "actors value means strictly in accordance with their valuation
of the ends that they believe the means can serve" (p. 19).

It is indexed by the step rather than by a size. The reason is that
which ends a unit adds can depend on which units are already on hand,
unless interchangeability of units (`plan.Homogeneous`) holds. -/
def marginalEnds {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} {stock : Stock praxis agent time}
    (plan : AllocationPlan stock)
    (fewer more : Finset praxis.Means) : Set praxis.End :=
  {want | want ∈ plan.wouldServe more ∧ want ∉ plan.wouldServe fewer}

/-- **The law of marginal utility, along a chain of named units.**
Take three sub-stocks, `small` inside `medium` inside `large`. Each is
one unit more than the last (`stock.OneMore`). Every
end the first step adds is preferred to every end the second step
adds.

No interchangeability of units (`plan.Homogeneous`) is needed, because
the chain names which units are involved. The theorem is one
application of `urgency_principle`.

Two things go unused. The first is `_firstStep`. It is listed in the
statement and does no work at all. The underscore records that. Each
hypothesis that does no work is recorded as a finding. This one shows
that the chain form needs nothing of how `small` stands to `medium`:
not that the first step adds one unit, nor even that `small` lies
inside `medium`. The second is half of a hypothesis: that an end is
marginal at the first step, that is, among the ends that step adds
(`marginalEnds plan small medium`). That has two halves. Only one is
used: that the end is served at `medium`. That it is not served at `small` is not used. The
proof records this by naming that half `_notNeeded`. That name is
inside the proof, not in the statement.

The linter (`#lint only unusedArguments`) catches neither. The
underscore silences it on `_firstStep`. And it judges each hypothesis
whole, so it cannot see that half of one goes unused. -/
theorem marginal_utility_chain
    {praxis : ActionFrame} [DecidableEq praxis.End]
    {agent : praxis.Agent} {time : praxis.Time}
    {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) (dominance : SwapDominant plan)
    (independent : praxis.IndependentUses agent time)
    (small medium large : Finset praxis.Means)
    (_firstStep : stock.OneMore small medium)
    (secondStep : stock.OneMore medium large) :
    ∀ addedFirst ∈ marginalEnds plan small medium,
      ∀ addedSecond ∈ marginalEnds plan medium large,
        praxis.PrefersEnd agent time addedFirst addedSecond := by
  intro addedFirst hfirst addedSecond hsecond
  obtain ⟨hservedAtMedium, _notNeeded⟩ := hfirst
  obtain ⟨hservedAtLarge, hnotAtMedium⟩ := hsecond
  exact urgency_principle plan dominance independent medium large secondStep
    addedFirst hservedAtMedium addedSecond hservedAtLarge hnotAtMedium

/-- **The law of marginal utility** (Rothbard, *MES*, ch. 1, p. 27):
"The greater the supply of a good, the lower the marginal utility;
the smaller the supply, the higher the marginal utility."

This is the version stated by supply SIZE. The first step runs from
`belowSmaller` to `smaller`, which has `n` units. The second runs from
`belowLarger` to `larger`, which has `n + 1`. Every end that is
marginal at a supply of `n` units (one the first step adds) is
preferred to every end marginal at a supply of `n + 1` (one the second
step adds). That holds for ANY two one-unit steps reaching
those sizes. The two steps need not have a single unit in common.

Interchangeability of units (`plan.Homogeneous`) is needed exactly
once. It is needed to say that the plan at the `n` units below the
second step is the same as the plan at the `n` units of the first.
Without it, the plan at `smaller` and the plan at `belowLarger` need
not serve the same ends, though both have `n` units. Then this proof
has no way to pass from the first step to the second.

Here too only half of the marginality hypothesis is used: that the end
is served at `smaller`. That it is not served at `belowSmaller` is not
used. The proof names that half `_notNeeded`. That name is inside the
proof, not in the statement. Every hypothesis the statement lists is
used. -/
theorem marginal_utility
    {praxis : ActionFrame} [DecidableEq praxis.End]
    {agent : praxis.Agent} {time : praxis.Time}
    {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) (dominance : SwapDominant plan)
    (independent : praxis.IndependentUses agent time)
    (interchangeable : plan.Homogeneous)
    (belowSmaller smaller belowLarger larger : Finset praxis.Means)
    (stepToSmaller : stock.OneMore belowSmaller smaller)
    (stepToLarger : stock.OneMore belowLarger larger)
    (n : ℕ) (smallerSize : smaller.card = n)
    (largerSize : larger.card = n + 1) :
    ∀ atSmaller ∈ marginalEnds plan belowSmaller smaller,
      ∀ atLarger ∈ marginalEnds plan belowLarger larger,
        praxis.PrefersEnd agent time atSmaller atLarger := by
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
