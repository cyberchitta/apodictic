import Apodictic.MarginalUtility

/-!
# Consistency — a machine-checked model

The library asserts no axioms; its praxeological content travels as
hypotheses (`Apodictic.Commitments`). So consistency is an INSTANCE.
Build a concrete frame, a stock, and a plan; prove the plan satisfies
`SwapDominant`; hand the whole thing to `marginal_utility_chain`. If
that type-checks, the commitment and every hypothesis are jointly
satisfiable, and the theorems are not vacuous. Nothing is
transcribed: `toy_swapDominant` proves the very proposition
`marginal_utility_chain` consumes.

This module is EVIDENCE, not theory: nothing else depends on it, and
no praxeological claim is made here. Its proofs may use whatever
mathlib offers (classical lemmas included); the
constructive-by-default rule governs the library's theorems, not the
bookkeeping of a model.

What the toy frame establishes:

1. `SwapDominant` holds of an actual plan together with ASYMMETRY of
   `Prefers` — the strict reading intended throughout, and the
   property `no_rival_swap_dominant` needs.
2. The hypotheses of `urgency_principle` / `marginal_utility` are
   JOINTLY satisfiable: uses are independent, the plan is
   homogeneous, ends are decidable, and one-unit steps exist within
   the stock. `toy_law_applies` is the law itself, instantiated.
-/

namespace Apodictic
namespace Model

/-- Asymmetry of preference: if `X` is preferred to `Y` then `Y` is
not preferred to `X`. This is the "strict" reading intended all
along, and it is not yet a commitment (OPEN.md). The model has to
survive it. -/
def Asymmetric (F : ActionFrame) : Prop :=
  ∀ (a : F.Agent) (t : F.Time) (X Y : Set F.End),
    F.Prefers a t X Y → ¬ F.Prefers a t Y X

/-- The toy preference. `X ≻ Y` exactly when the two differ by one
swap and the end `X` has instead is the more urgent one — which here
just means the smaller number. -/
def swapPrefers (X Y : Set ℕ) : Prop :=
  ∃ e e', e ∈ X ∧ e' ∈ Y ∧ e ∉ Y ∧ e' ∉ X ∧ e < e' ∧ X \ {e} = Y \ {e'}

/-- The toy frame: one agent, one instant, ends and means are
numbers, everything believed serviceable, preference as above. -/
abbrev Toy : ActionFrame where
  Agent := Unit
  End := ℕ
  Means := ℕ
  Time := Unit
  Believes := fun _ _ _ _ => True
  Prefers := fun _ _ X Y => swapPrefers X Y

/-- A stock of `k` units, serviceable for every end. -/
def toyStock (k : ℕ) : Stock Toy () () where
  units := Finset.range k
  serves := Set.univ
  homog := by
    intro _ _ _
    exact ⟨fun _ => Set.mem_univ _, fun _ => trivial⟩

/-- The plan that serves the most urgent ends, as many as there are
units — whichever units they are. -/
def toyPlan (k : ℕ) : AllocationDisposition (toyStock k) where
  wouldServe := fun U => Finset.range U.card
  serves_subset := by
    intro _ _ _
    trivial
  card_eq := by
    intro U _
    exact Finset.card_range U.card

/-- The toy plan is homogeneous: it depends on the count alone. -/
theorem toy_homogeneous (k : ℕ) : (toyPlan k).Homogeneous := by
  intro U _ V _ h
  show Finset.range U.card = Finset.range V.card
  rw [h]

/-- Ends are decidable in the toy frame — the instance the theorems
take as `[DecidableEq F.End]`. -/
instance : DecidableEq Toy.End := inferInstanceAs (DecidableEq ℕ)

theorem toy_asymmetric : Asymmetric Toy := by
  intro _ _ X Y h1 h2
  obtain ⟨e, e', heX, he'Y, heY, he'X, hlt, heq⟩ := h1
  obtain ⟨f, f', hfY, hf'X, hfX, hf'Y, hlt', heq'⟩ := h2
  -- f must be e': it is in Y, not in X, so not in Y \ {e'} = X \ {e}
  have hf : f = e' := by
    by_contra hne
    have : f ∈ Y \ {e'} := ⟨hfY, hne⟩
    exact hfX ((Set.ext_iff.mp heq f).mpr this).1
  -- f' must be e, symmetrically
  have hf' : f' = e := by
    by_contra hne
    have : f' ∈ X \ {e} := ⟨hf'X, hne⟩
    exact hf'Y ((Set.ext_iff.mp heq f').mp this).1
  subst hf hf'
  omega

/-- **The toy plan is swap-dominant** — the commitment itself, proved
of this frame and this plan. -/
theorem toy_swapDominant (k : ℕ) : SwapDominant (toyPlan k) where
  swap := by
    intro U _ e he e' _ hne
    have hen : e < U.card := Finset.mem_range.mp he
    have he'n : ¬ e' < U.card := fun h => hne (Finset.mem_range.mpr h)
    show swapPrefers (↑(Finset.range U.card))
      (insert e' ((↑(Finset.range U.card) : Set ℕ) \ {e}))
    refine ⟨e, e', Finset.mem_coe.mpr (Finset.mem_range.mpr hen),
      Set.mem_insert e' _, ?_, ?_,
      Nat.lt_of_lt_of_le hen (Nat.le_of_not_lt he'n), ?_⟩
    · intro h
      rcases h with h | h
      · exact he'n (h ▸ hen)
      · exact h.2 rfl
    · intro h
      exact he'n (Finset.mem_range.mp (Finset.mem_coe.mp h))
    · have hnm : e' ∉ ((↑(Finset.range U.card) : Set ℕ) \ {e}) := by
        intro h
        exact he'n (Finset.mem_range.mp (Finset.mem_coe.mp h.1))
      rw [Set.insert_sdiff_self_of_notMem hnm]

theorem toy_independent (a : Toy.Agent) (t : Toy.Time) :
    Toy.IndependentUses a t := by
  intro S e e' heS he'S h
  obtain ⟨f, f', hf, hf', hfY, hf'X, hlt, _⟩ := h
  -- f ∈ insert e S but ∉ insert e' S, so f = e
  have hfe : f = e := by
    rcases hf with h | h
    · exact h
    · exact absurd (Set.mem_insert_of_mem e' h) hfY
  have hf'e : f' = e' := by
    rcases hf' with h | h
    · exact h
    · exact absurd (Set.mem_insert_of_mem e h) hf'X
  subst hfe hf'e
  refine ⟨f, f', rfl, rfl, ?_, ?_, hlt, ?_⟩
  · intro h
    have : f = f' := h
    omega
  · intro h
    have : f' = f := h
    omega
  · rw [Set.sdiff_self, Set.sdiff_self]

/-- One-unit steps exist within the stock: `range n → range (n+1)`
for `n < k`, so the theorems apply to the toy plan non-vacuously. -/
theorem toy_one_more (k n : ℕ) (h : n < k) :
    (toyStock k).OneMore (Finset.range n) (Finset.range (n + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.le_succ n))
  · show Finset.range (n + 1) ⊆ Finset.range k
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hx) h)
  · rw [Finset.card_range, Finset.card_range]

/-- The conclusion is not trivial: the step `n → n + 1` has a
marginal end, namely `n` — served with `n + 1` units, not with `n`
(the membership `marginalEnds` is defined by, spelled out). -/
theorem toy_marginal_nonempty (k n : ℕ) :
    n ∈ (toyPlan k).wouldServe (Finset.range (n + 1)) ∧
      n ∉ (toyPlan k).wouldServe (Finset.range n) := by
  constructor
  · show n ∈ Finset.range (Finset.range (n + 1)).card
    rw [Finset.card_range]
    exact Finset.mem_range.mpr (Nat.lt_succ_self n)
  · show n ∉ Finset.range (Finset.range n).card
    rw [Finset.card_range]
    exact fun h => Nat.lt_irrefl n (Finset.mem_range.mp h)

/-- **The law itself, applied.** Every hypothesis of
`marginal_utility_chain` is discharged at the toy frame. So the
commitment and the situational conditions can all hold at once, and
the law is not about nothing. That is the whole consistency argument:
this type-checks, therefore they fit together. -/
theorem toy_law_applies (k n : ℕ) (h : n < k) (h' : n + 1 < k) :
    ∀ e ∈ marginalEnds (toyPlan k) (Finset.range n) (Finset.range (n + 1)),
      ∀ e' ∈ marginalEnds (toyPlan k)
        (Finset.range (n + 1)) (Finset.range (n + 2)),
      Toy.PrefersEnd () () e e' :=
  marginal_utility_chain (toyPlan k) (toy_swapDominant k)
    (toy_independent () ()) _ _ _
    (toy_one_more k n h) (toy_one_more k (n + 1) h')

#print axioms toy_law_applies

end Model
end Apodictic
