import Apodictic.Praxeology

/-!
# The urgency principle — derived, not asserted

Rothbard says the urgency principle "follows from" action (*MES*
p. 24) without showing how. Here it is a theorem, from one
praxeological claim and two hypotheses.

What the derivation needs, and what it does not:

- `SwapDominant plan` — the counterfactual bridge: what the agent WOULD
  serve is preferred to any one-swap alternative. Subjunctive — and
  so is Rothbard's own derivation (*MES* p. 25), which compares the
  stock he has with a stock he does not.
- `IndependentUses agent t` — as a HYPOTHESIS: the end-level
  conclusion is read off a bundle-level preference, which is licit
  only where uses are independent. The theorem does not apply where
  they are not; the law of marginal utility inherits the condition.
- `[DecidableEq praxis.End]` — to form "the bundle minus a want"
  constructively.
- NOT the actual-action bridge from action to preference (nowhere in
  the library). The action half of Rothbard's fused premise (*MES*
  p. 24) is dropped rather than discharged; what does the work is
  the ordering half, extended subjunctively as his own argument
  extends it.
- NOT interchangeability of units (`Homogeneous`): the ordering is
  about one sub-stock at a time and never compares two of the same
  size. That condition enters only when the law is stated by supply
  SIZE (`MarginalUtility.lean`).
- NOT any structural property of `Prefers`; NOT determinacy of the
  drop; NOT the general "preferred to every same-size bundle" form.
- Only for units on hand (`U ⊆ s.units`).
-/

namespace Apodictic

/-- Taking a member out of a set and putting it straight back leaves
the set alone. Proved here rather than borrowed because mathlib's
`Set.insert_sdiff_singleton` is classical; with decidable equality
this version is constructive. -/
theorem insert_sdiff_self_of_mem {α : Type} [DecidableEq α]
    {bundle : Set α} {want : α} (h : want ∈ bundle) :
    bundle = insert want (bundle \ {want}) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    by_cases hxWant : x = want
    · exact Or.inl hxWant
    · exact Or.inr ⟨hx, hxWant⟩
  · intro hx
    cases hx with
    | inl hxWant => rw [hxWant]; exact h
    | inr hx' => exact hx'.1

/-- **Served over unserved** — the workhorse. Take any sub-stock on
hand. Every end the agent would serve with it is preferred to every
end the good could serve but he would leave unserved.

It needs the hypothesis of independence of uses
(`IndependentUses agent time`). That hypothesis is what carries a
preference between two bundles down to a preference between two ends.

This theorem is everything `SwapDominant` gives about single ends.
Swap dominance says nothing beyond its single swaps. Each swap
it speaks of yields a preference between two bundles that differ in
exactly one place. Independence of uses turns that into a preference between the
two ends: the served end over the unserved one. This theorem covers
every such swap: every sub-stock on hand, every served end, every
unserved end the good could serve. It is more than Rothbard says. It
sets a served end against ANY unserved end the good could serve, not
only against the one the next unit would reach.

How the proof goes. Swap dominance says the served bundle beats the
bundle with `unserved` swapped in for `served`. Write the served bundle
as the end `served` together with the rest of the bundle
(`insert_sdiff_self_of_mem`). The swapped bundle is the end `unserved`
together with that same rest. Neither end is in the rest. `served`
was taken out of it. `unserved` is not served at this sub-stock, and
the rest is part of what is served there. So the two
bundles differ in exactly one place. Independence of uses reads the
preference between those two ends off that. -/
theorem served_over_unserved {praxis : ActionFrame} [DecidableEq praxis.End]
    {agent : praxis.Agent} {time : praxis.Time}
    {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) (dominance : SwapDominant plan)
    (independent : praxis.IndependentUses agent time)
    (subStock : Finset praxis.Means) (onHand : subStock ⊆ stock.units) :
    ∀ served ∈ plan.wouldServe subStock, ∀ unserved ∈ stock.serves,
      unserved ∉ plan.wouldServe subStock →
        praxis.PrefersEnd agent time served unserved := by
  intro served hserved unserved hcanServe hnotServed
  have hbeats := dominance.swap subStock onHand served hserved
    unserved hcanServe hnotServed
  have hmem : served ∈ (↑(plan.wouldServe subStock) : Set praxis.End) :=
    Finset.mem_coe.mpr hserved
  have hsplit := insert_sdiff_self_of_mem hmem
  apply independent
    ((↑(plan.wouldServe subStock) : Set praxis.End) \ {served})
    served unserved
  · intro h
    exact h.2 rfl
  · intro h
    exact hnotServed (Finset.mem_coe.mp h.1)
  · rw [← hsplit]
    exact hbeats

/-- **The urgency principle** (Rothbard), stated as a loss. Suppose the
agent had `more` units and drops to `fewer`, one unit fewer
(`stock.OneMore fewer more`). Every end he would still serve at
`fewer` is preferred to every end he has to abandon on the way down.
The loss falls on the least urgent want.

It is one application of `served_over_unserved`, at the sub-stock
`fewer`. An abandoned end is one the plan would serve at `more` and
not at `fewer`. So it is an end the good can serve, since the plan only ever puts a
unit to an end the good is believed able to serve. That is a field of
the plan itself (`plan.servesOnlyWhatItCan`), not a hypothesis. And
the plan leaves it unserved at `fewer`.
From `stock.OneMore fewer more` the proof uses only that `fewer` is
on hand: it lies inside `more`, which lies inside the stock. That
`more` has exactly one unit more than `fewer` is not used. -/
theorem urgency_principle {praxis : ActionFrame} [DecidableEq praxis.End]
    {agent : praxis.Agent} {time : praxis.Time}
    {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) (dominance : SwapDominant plan)
    (independent : praxis.IndependentUses agent time)
    (fewer more : Finset praxis.Means) (step : stock.OneMore fewer more) :
    ∀ kept ∈ plan.wouldServe fewer, ∀ lost, lost ∈ plan.wouldServe more →
      lost ∉ plan.wouldServe fewer →
        praxis.PrefersEnd agent time kept lost := by
  intro kept hkept lost hlost hnotKept
  have onHand : fewer ⊆ stock.units := fun u hu => step.2.1 (step.1 hu)
  exact served_over_unserved plan dominance independent fewer onHand
    kept hkept lost (plan.servesOnlyWhatItCan more lost hlost) hnotKept

/-- **No rival plan, one swap away.** Suppose preference is
asymmetric. Then two plans over the same stock cannot both be
swap-dominant while differing by a single swap at some sub-stock.

Rothbard writes of "the" value scale — "the" marginal unit, "the"
least urgent want (*MES* pp. 24–27) — without arguing there is only
one. This is a narrow piece of that: not uniqueness, only that no
rival a single swap away at some sub-stock is also swap-dominant.
Swap dominance (`SwapDominant`) plus asymmetry delivers it. Asymmetry is the
praxeological claim `AsymmetricPreference`. This theorem uses it. So
does `Apodictic.Contrast.rothbard_entails_servedInOrder`, shown under
Mises's route. The docstring of `AsymmetricPreference` lists the other
theorems that use it. Apart from asymmetry, the man's ranking of
bundles (`Prefers`) has no properties assumed of it. -/
theorem no_rival_swap_dominant {praxis : ActionFrame} [DecidableEq praxis.End]
    {agent : praxis.Agent} {time : praxis.Time}
    {stock : Stock praxis agent time}
    (asymmetry : AsymmetricPreference praxis agent time)
    (plan rival : AllocationPlan stock)
    (dominance : SwapDominant plan) (rivalDominance : SwapDominant rival)
    (subStock : Finset praxis.Means) (onHand : subStock ⊆ stock.units)
    (served unserved : praxis.End)
    (hserved : served ∈ plan.wouldServe subStock)
    (hservedPossible : served ∈ stock.serves)
    (hunservedPossible : unserved ∈ stock.serves)
    (hunserved : unserved ∉ plan.wouldServe subStock)
    (hswap : (↑(rival.wouldServe subStock) : Set praxis.End)
              = insert unserved
                  ((↑(plan.wouldServe subStock) : Set praxis.End) \ {served})) :
    False := by
  have hne : served ≠ unserved := fun h => hunserved (h ▸ hserved)
  have hplanBeats := dominance.swap subStock onHand served hserved
    unserved hunservedPossible hunserved
  rw [← hswap] at hplanBeats
  have hunservedInRival : unserved ∈ rival.wouldServe subStock := by
    have hm : unserved ∈ (↑(rival.wouldServe subStock) : Set praxis.End) := by
      rw [hswap]; exact Set.mem_insert _ _
    exact Finset.mem_coe.mp hm
  have hservedNotInRival : served ∉ rival.wouldServe subStock := by
    intro hmem
    have hm : served ∈ (↑(rival.wouldServe subStock) : Set praxis.End) :=
      Finset.mem_coe.mpr hmem
    rw [hswap] at hm
    rcases hm with h | h
    · exact hne h
    · exact h.2 rfl
  have hrivalBeats := rivalDominance.swap subStock onHand unserved
    hunservedInRival served hservedPossible hservedNotInRival
  have hback : insert served
      ((↑(rival.wouldServe subStock) : Set praxis.End) \ {unserved})
      = (↑(plan.wouldServe subStock) : Set praxis.End) := by
    rw [hswap]
    apply Set.ext
    intro x
    constructor
    · rintro (rfl | ⟨hx, hxUnserved⟩)
      · exact hserved
      · rcases hx with rfl | hx
        · exact absurd rfl hxUnserved
        · exact hx.1
    · intro hx
      by_cases hxServed : x = served
      · exact Or.inl hxServed
      · refine Or.inr ⟨Or.inr ⟨hx, hxServed⟩, ?_⟩
        rintro rfl
        exact hunserved (Finset.mem_coe.mp hx)
  rw [hback] at hrivalBeats
  exact asymmetry.asym _ _ hplanBeats hrivalBeats

#print axioms served_over_unserved
#print axioms urgency_principle
#print axioms no_rival_swap_dominant

end Apodictic

#lint only unusedArguments
