import Apodictic.Commitments

/-!
# The urgency principle — derived, not asserted

Rothbard says the urgency principle "follows from" action (*MES*
p. 24) without showing how. Here it is a theorem, from one
commitment and two hypotheses.

What the derivation needs, and what it does not:

- `SwapDominant plan` — the counterfactual bridge: what the agent WOULD
  serve is preferred to any one-swap alternative. Subjunctive — and
  so is Rothbard's own derivation (*MES* p. 25), which compares the
  stock he has with a stock he does not.
- `IndependentUses agent t` — as a HYPOTHESIS: the end-level
  conclusion is read off a bundle-level preference, which is licit
  only where uses are independent. The theorem does not apply where
  they are not; the law of marginal utility inherits the condition.
- `[DecidableEq frame.End]` — to form "the bundle minus a want"
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

This is everything `SwapDominant` gives, and it is more than Rothbard
claims: it sets a served end against ANY unserved end the good could
serve, not only against the one the next unit would reach. It needs
the hypothesis that uses are independent (see the module docstring
above).

How the proof goes: swap the `served` want for the `unserved` one, and
the plan beats the result. The served bundle is that one want together
with the rest (`insert_sdiff_self_of_mem`), so the two bundles differ
in exactly one place — and independence reads the preference between
those two wants off that. -/
theorem served_over_unserved {frame : ActionFrame} [DecidableEq frame.End]
    {agent : frame.Agent} {time : frame.Time}
    {stock : Stock frame agent time}
    (plan : AllocationPlan stock) (dominance : SwapDominant plan)
    (independent : frame.IndependentUses agent time)
    (subStock : Finset frame.Means) (onHand : subStock ⊆ stock.units) :
    ∀ served ∈ plan.wouldServe subStock, ∀ unserved ∈ stock.serves,
      unserved ∉ plan.wouldServe subStock →
        frame.PrefersEnd agent time served unserved := by
  intro served hserved unserved hcanServe hnotServed
  have hbeats := dominance.swap subStock onHand served hserved
    unserved hcanServe hnotServed
  have hmem : served ∈ (↑(plan.wouldServe subStock) : Set frame.End) :=
    Finset.mem_coe.mpr hserved
  have hsplit := insert_sdiff_self_of_mem hmem
  apply independent
    ((↑(plan.wouldServe subStock) : Set frame.End) \ {served})
    served unserved
  · intro h
    exact h.2 rfl
  · intro h
    exact hnotServed (Finset.mem_coe.mp h.1)
  · rw [← hsplit]
    exact hbeats

/-- **The urgency principle** (Rothbard), stated as a loss. Suppose the
agent had `more` units and drops to `fewer`, one unit fewer. Every end
he would still serve at `fewer` is preferred to every end he has to
abandon on the way down: the loss falls on the least urgent want.

One application of `served_over_unserved`. An abandoned end is one the
good can serve and the plan does not serve at `fewer` — and beyond
supplying that much, the fact that `more` is exactly one unit larger
does no work here. -/
theorem urgency_principle {frame : ActionFrame} [DecidableEq frame.End]
    {agent : frame.Agent} {time : frame.Time}
    {stock : Stock frame agent time}
    (plan : AllocationPlan stock) (dominance : SwapDominant plan)
    (independent : frame.IndependentUses agent time)
    (fewer more : Finset frame.Means) (step : stock.OneMore fewer more) :
    ∀ kept ∈ plan.wouldServe fewer, ∀ lost, lost ∈ plan.wouldServe more →
      lost ∉ plan.wouldServe fewer →
        frame.PrefersEnd agent time kept lost := by
  intro kept hkept lost hlost hnotKept
  have onHand : fewer ⊆ stock.units := fun u hu => step.2.1 (step.1 hu)
  exact served_over_unserved plan dominance independent fewer onHand
    kept hkept lost (plan.servesOnlyWhatItCan more lost hlost) hnotKept

/-- **No rival plan, one swap away.** If preference is asymmetric,
then two plans over the same stock cannot both be swap-dominant while
differing by a single swap at some sub-stock.

This is what Rothbard means by "the" value scale, and here it is
derived rather than presupposed. He writes as though the actor's
ranking were simply given — "the" marginal unit, "the" least urgent
want (*MES* pp. 24–27) — and never argues that there is only one.
Swap dominance plus asymmetry delivers it. Asymmetry rides along as a
hypothesis because `Prefers` has no properties assumed of it. -/
theorem no_rival_swap_dominant {frame : ActionFrame} [DecidableEq frame.End]
    {agent : frame.Agent} {time : frame.Time}
    {stock : Stock frame agent time}
    (asymmetry : ∀ X Y : Set frame.End,
      frame.Prefers agent time X Y → ¬ frame.Prefers agent time Y X)
    (plan rival : AllocationPlan stock)
    (dominance : SwapDominant plan) (rivalDominance : SwapDominant rival)
    (subStock : Finset frame.Means) (onHand : subStock ⊆ stock.units)
    (served unserved : frame.End)
    (hserved : served ∈ plan.wouldServe subStock)
    (hservedPossible : served ∈ stock.serves)
    (hunservedPossible : unserved ∈ stock.serves)
    (hunserved : unserved ∉ plan.wouldServe subStock)
    (hswap : (↑(rival.wouldServe subStock) : Set frame.End)
              = insert unserved
                  ((↑(plan.wouldServe subStock) : Set frame.End) \ {served})) :
    False := by
  have hne : served ≠ unserved := fun h => hunserved (h ▸ hserved)
  have hplanBeats := dominance.swap subStock onHand served hserved
    unserved hunservedPossible hunserved
  rw [← hswap] at hplanBeats
  have hunservedInRival : unserved ∈ rival.wouldServe subStock := by
    have hm : unserved ∈ (↑(rival.wouldServe subStock) : Set frame.End) := by
      rw [hswap]; exact Set.mem_insert _ _
    exact Finset.mem_coe.mp hm
  have hservedNotInRival : served ∉ rival.wouldServe subStock := by
    intro hmem
    have hm : served ∈ (↑(rival.wouldServe subStock) : Set frame.End) :=
      Finset.mem_coe.mpr hmem
    rw [hswap] at hm
    rcases hm with h | h
    · exact hne h
    · exact h.2 rfl
  have hrivalBeats := rivalDominance.swap subStock onHand unserved
    hunservedInRival served hservedPossible hservedNotInRival
  have hback : insert served
      ((↑(rival.wouldServe subStock) : Set frame.End) \ {unserved})
      = (↑(plan.wouldServe subStock) : Set frame.End) := by
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
  exact asymmetry _ _ hplanBeats hrivalBeats

#print axioms served_over_unserved
#print axioms urgency_principle
#print axioms no_rival_swap_dominant

end Apodictic

#lint only unusedArguments
