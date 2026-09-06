import Apodictic.Commitments

/-!
# The urgency principle — derived, not asserted

Rothbard says the urgency principle "follows from" action (*MES*
p. 24) without showing how. Here it is a theorem, from one
commitment and two hypotheses.

What the derivation needs, and what it does not:

- `SwapDominant A` — the counterfactual bridge: what the agent WOULD
  serve is preferred to any one-swap alternative. Subjunctive — and
  so is Rothbard's own derivation (*MES* p. 25), which compares the
  stock he has with a stock he does not.
- `IndependentUses agent t` — as a HYPOTHESIS: the end-level
  conclusion is read off a bundle-level preference, which is licit
  only where uses are independent. The theorem does not apply where
  they are not; the law of marginal utility inherits the condition.
- `[DecidableEq F.End]` — to form "the bundle minus `e`"
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

/-- Withdrawing a member and putting it back is the identity.
Constructive given decidable equality — mathlib's
`Set.insert_sdiff_singleton` is classical. -/
theorem insert_sdiff_self_of_mem {α : Type} [DecidableEq α] {S : Set α}
    {e : α} (h : e ∈ S) : S = insert e (S \ {e}) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    by_cases hxe : x = e
    · exact Or.inl hxe
    · exact Or.inr ⟨hx, hxe⟩
  · intro hx
    cases hx with
    | inl hxe => rw [hxe]; exact h
    | inr hx' => exact hx'.1

/-- **Served over unserved** — the workhorse: with any sub-stock on
hand, every end the agent would serve is preferred to every
serviceable end the agent would not. This is all `SwapDominant`
delivers, and it is more than Rothbard states: it compares a served
end with ANY unserved serviceable end, not only with the one the
next unit would reach. Derived under the hypothesis that uses are
independent (module docstring).

Proof shape: swapping the served `e` for the unserved `e'` is
dominated; the served bundle is `e` plus the rest
(`insert_sdiff_self_of_mem`); the two bundles now differ in one slot,
and independence reads off `e ≻ e'`. -/
theorem served_over_unserved {F : ActionFrame} [DecidableEq F.End]
    {agent : F.Agent} {t : F.Time} {s : Stock F agent t}
    (A : AllocationDisposition s) (hA : SwapDominant A)
    (hI : F.IndependentUses agent t)
    (U : Finset F.Means) (hU : U ⊆ s.units) :
    ∀ e ∈ A.wouldServe U, ∀ e' ∈ s.serves, e' ∉ A.wouldServe U →
      F.PrefersEnd agent t e e' := by
  intro e he e' hserv hne
  have hpref := hA.swap U hU e he e' hserv hne
  have hmem : e ∈ (↑(A.wouldServe U) : Set F.End) := Finset.mem_coe.mpr he
  have hrw := insert_sdiff_self_of_mem hmem
  apply hI ((↑(A.wouldServe U) : Set F.End) \ {e}) e e'
  · intro h
    exact h.2 rfl
  · intro h
    exact hne (Finset.mem_coe.mp h.1)
  · rw [← hrw]
    exact hpref

/-- **The urgency principle** (Rothbard), in counterfactual-loss form:
for an agent's allocation disposition over a stock, every end that
would still be served with the units `U` is preferred to every end
that would be abandoned in the step down from `V`, one unit more —
the loss falls on the least urgent want. One application of
`served_over_unserved`: the abandoned end is serviceable and
unserved at `U`; that `V` is `U` plus one unit is not used beyond
that. -/
theorem urgency_principle {F : ActionFrame} [DecidableEq F.End]
    {agent : F.Agent} {t : F.Time} {s : Stock F agent t}
    (A : AllocationDisposition s) (hA : SwapDominant A)
    (hI : F.IndependentUses agent t)
    (U V : Finset F.Means) (hUV : s.OneMore U V) :
    ∀ e ∈ A.wouldServe U, ∀ e', e' ∈ A.wouldServe V →
      e' ∉ A.wouldServe U → F.PrefersEnd agent t e e' := by
  intro e he e' he' hne
  have hU : U ⊆ s.units := fun x hx => hUV.2.1 (hUV.1 hx)
  exact served_over_unserved A hA hI U hU e he e' (A.serves_subset V e' he') hne

/-- **At most one swap-dominant plan, up to one swap.** Given
asymmetry of preference, two plans over the same stock cannot both be
swap-dominant while differing by a single swap at some sub-stock.

This is what Rothbard means by "the" value scale: that there is one
is derived here, not presupposed. Rothbard writes as though the
actor's ranking were simply given ("the" marginal unit, "the" least
urgent want, *MES* pp. 24–27) and never argues for uniqueness;
swap dominance plus asymmetry delivers it. Asymmetry travels as a
hypothesis because `Prefers` has no assumed properties. -/
theorem no_rival_swap_dominant {F : ActionFrame} [DecidableEq F.End]
    {agent : F.Agent} {t : F.Time} {s : Stock F agent t}
    (hasym : ∀ X Y : Set F.End, F.Prefers agent t X Y → ¬ F.Prefers agent t Y X)
    (A A' : AllocationDisposition s) (hA : SwapDominant A) (hA' : SwapDominant A')
    (U : Finset F.Means) (hU : U ⊆ s.units)
    (e e' : F.End)
    (heA : e ∈ A.wouldServe U) (hes : e ∈ s.serves)
    (he's : e' ∈ s.serves) (he'A : e' ∉ A.wouldServe U)
    (hswap : (↑(A'.wouldServe U) : Set F.End)
              = insert e' ((↑(A.wouldServe U) : Set F.End) \ {e})) :
    False := by
  have hne : e ≠ e' := fun h => he'A (h ▸ heA)
  have h1 := hA.swap U hU e heA e' he's he'A
  rw [← hswap] at h1
  have he'A' : e' ∈ A'.wouldServe U := by
    have hm : e' ∈ (↑(A'.wouldServe U) : Set F.End) := by
      rw [hswap]; exact Set.mem_insert _ _
    exact Finset.mem_coe.mp hm
  have heA' : e ∉ A'.wouldServe U := by
    intro hmem
    have hm : e ∈ (↑(A'.wouldServe U) : Set F.End) := Finset.mem_coe.mpr hmem
    rw [hswap] at hm
    rcases hm with h | h
    · exact hne h
    · exact h.2 rfl
  have h2 := hA'.swap U hU e' he'A' e hes heA'
  have hback : insert e ((↑(A'.wouldServe U) : Set F.End) \ {e'})
      = (↑(A.wouldServe U) : Set F.End) := by
    rw [hswap]
    apply Set.ext
    intro x
    constructor
    · rintro (rfl | ⟨hx, hxe'⟩)
      · exact heA
      · rcases hx with rfl | hx
        · exact absurd rfl hxe'
        · exact hx.1
    · intro hx
      by_cases hxe : x = e
      · exact Or.inl hxe
      · refine Or.inr ⟨Or.inr ⟨hx, hxe⟩, ?_⟩
        rintro rfl
        exact he'A (Finset.mem_coe.mp hx)
  rw [hback] at h2
  exact hasym _ _ h1 h2

#print axioms served_over_unserved
#print axioms urgency_principle
#print axioms no_rival_swap_dominant

end Apodictic

#lint only unusedArguments
