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
- NOT any structural property of `Prefers`; NOT determinacy of the
  drop; NOT the general "preferred to every same-size bundle" form.
- Only within the supply (`n ≤ s.units.card`).
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

/-- **The urgency principle** (Rothbard), in counterfactual-loss form:
for an agent's allocation disposition over a stock, every end that
would still be served with `n` units is preferred to every end that
would be abandoned in the step down from `n + 1` — the loss falls on
the least urgent want. Derived from `swap_dominance` under the
hypothesis that uses are independent (module docstring).

Proof shape: at supply `n`, swapping the served `e` for the unserved
`e'` is dominated (`swap_dominance`); the served bundle is `e` plus
the rest (`insert_sdiff_self_of_mem`); the two bundles now differ in
one slot, and independence reads off `e ≻ e'`. -/
theorem urgency_principle
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : AllocationDisposition s) (hA : actual_disposition A)
    (hI : World.IndependentUses agent t)
    (n : ℕ) (hn : n ≤ s.units.card) :
    ∀ e ∈ A.wouldServe n, ∀ e', e' ∈ A.wouldServe (n + 1) →
      e' ∉ A.wouldServe n → World.PrefersEnd agent t e e' := by
  intro e he e' he1 hne
  have hserv : e' ∈ s.serves := A.serves_subset (n + 1) e' he1
  have hpref := swap_dominance A hA n hn e he e' hserv hne
  have hmem : e ∈ (↑(A.wouldServe n) : Set World.End) := Finset.mem_coe.mpr he
  have hrw := insert_sdiff_self_of_mem hmem
  apply hI ((↑(A.wouldServe n) : Set World.End) \ {e}) e e'
  · intro h
    exact h.2 rfl
  · intro h
    exact hne (Finset.mem_coe.mp h.1)
  · rw [← hrw]
    exact hpref

#print axioms urgency_principle

end Apodictic
