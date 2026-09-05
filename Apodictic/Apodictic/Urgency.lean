import Apodictic.Axioms

/-!
# The urgency principle — derived, not asserted

Rothbard says the urgency principle "follows from" action (*MES*
p. 24) without showing how. Here it is a theorem, from the
subjunctive premise `swap_dominance` and two hypotheses.

What the derivation needs, and what it does not:

- `swap_dominance` — the counterfactual bridge: what the agent WOULD
  serve is preferred to any one-swap alternative. Subjunctive
  preference in Nozick's sense (1977, pp. 373–374) — the notion
  Rothbard's demonstrated-preference doctrine forbids and Nozick
  says the Austrians need — now a single named axiom.
- `actual_disposition A` — as a HYPOTHESIS: the plan is the agent's,
  not a rival of the same type. Without it the axiom over-quantified
  (see its docstring).
- `ends_distinguishable` — to form "the bundle minus `e`"
  constructively.
- `IndependentUses agent t` — as a HYPOTHESIS: the end-level
  conclusion is read off a bundle-level preference, which is licit
  only where uses are independent. The theorem does not apply where
  they are not; the law of marginal utility inherits the condition.
- NOT the actual-action bridge from action to preference (not in
  the base): the principle rests on the subjunctive extension alone.
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
serviceable end the agent would not. This is all `swap_dominance`
delivers, and it is more than Rothbard states: it compares a served
end with ANY unserved serviceable end, not only with the one the
next unit would reach. Derived under the hypothesis that uses are
independent (module docstring).

Proof shape: swapping the served `e` for the unserved `e'` is
dominated (`swap_dominance`); the served bundle is `e` plus the rest
(`insert_sdiff_self_of_mem`); the two bundles now differ in one slot,
and independence reads off `e ≻ e'`. -/
theorem served_over_unserved
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : AllocationDisposition s) (hA : actual_disposition A)
    (hI : World.IndependentUses agent t)
    (U : Finset World.Means) (hU : U ⊆ s.units) :
    ∀ e ∈ A.wouldServe U, ∀ e' ∈ s.serves, e' ∉ A.wouldServe U →
      World.PrefersEnd agent t e e' := by
  intro e he e' hserv hne
  have hpref := swap_dominance A hA U hU e he e' hserv hne
  have hmem : e ∈ (↑(A.wouldServe U) : Set World.End) := Finset.mem_coe.mpr he
  have hrw := insert_sdiff_self_of_mem hmem
  apply hI ((↑(A.wouldServe U) : Set World.End) \ {e}) e e'
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
theorem urgency_principle
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : AllocationDisposition s) (hA : actual_disposition A)
    (hI : World.IndependentUses agent t)
    (U V : Finset World.Means) (hUV : s.OneMore U V) :
    ∀ e ∈ A.wouldServe U, ∀ e', e' ∈ A.wouldServe V →
      e' ∉ A.wouldServe U → World.PrefersEnd agent t e e' := by
  intro e he e' he' hne
  have hU : U ⊆ s.units := fun x hx => hUV.2.1 (hUV.1 hx)
  exact served_over_unserved A hA hI U hU e he e' (A.serves_subset V e' he') hne

#print axioms served_over_unserved
#print axioms urgency_principle

end Apodictic
