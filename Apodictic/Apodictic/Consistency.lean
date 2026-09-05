import Apodictic.Urgency

/-!
# Consistency — a machine-checked model of the trusted base

The axioms in `Apodictic.Axioms` speak of `World`, a sealed constant
that cannot be constructed. So they cannot be shown consistent by
building `World`. What CAN be built is a model of the general
vocabulary: a concrete `ActionFrame` in which every axiom's
STATEMENT (with `World` replaced by the frame) is true, together
with the properties we intend to add later and the hypotheses the
theorems assume. If such a frame exists, the axioms cannot prove
`False` — anything they prove holds in the frame.

This module is EVIDENCE, not theory: nothing in `Axioms.lean`
depends on it, and no praxeological claim is made here. Its proofs
may use whatever mathlib offers (classical lemmas included); the
constructive-by-default rule governs the receipts of the library's
theorems, not the bookkeeping of a model.

What the toy frame establishes (2026-09-04):

1. `swap_dominance` and `ends_distinguishable`, as properties of a
   frame with an `actual` predicate, hold together with ASYMMETRY of
   `Prefers` — the property that made the over-quantified version
   inconsistent (`_notes/2026-09-04-swap-dominance-overquantifies.md`).
2. The hypotheses of `urgency_principle` / `marginal_utility` are
   JOINTLY satisfiable: there is an actual disposition, uses are
   independent, the plan is homogeneous, and one-unit steps exist
   within the stock — so the theorems are not vacuous; and the
   conclusion is not trivial: a step's marginal ends are nonempty.

Human decision 2026-09-04 ("wouldn't it defeat the purpose to NOT
build it in Lean?"): the consistency ledger lives here, not in notes.
-/

namespace Apodictic
namespace Model

/-- `swap_dominance` as a property of a frame `F` and a predicate
`actual` picking out the agent's disposition. Mirrors the axiom
statement exactly, with `World` replaced by `F`. -/
def SwapDominance (F : ActionFrame)
    (actual : ∀ {a : F.Agent} {t : F.Time} {s : Stock F a t},
      AllocationDisposition s → Prop) : Prop :=
  ∀ {a : F.Agent} {t : F.Time} {s : Stock F a t}
    (A : AllocationDisposition s), actual A →
    ∀ U, U ⊆ s.units →
    ∀ e ∈ A.wouldServe U, ∀ e' ∈ s.serves, e' ∉ A.wouldServe U →
      F.Prefers a t (↑(A.wouldServe U))
        (insert e' ((↑(A.wouldServe U) : Set F.End) \ {e}))

/-- Asymmetry of preference — the intended "strict" reading, not yet
an axiom (OPEN.md). The model must survive it. -/
def Asymmetric (F : ActionFrame) : Prop :=
  ∀ (a : F.Agent) (t : F.Time) (X Y : Set F.End),
    F.Prefers a t X Y → ¬ F.Prefers a t Y X

/-- The toy preference: `X ≻ Y` iff they differ by exactly one swap
and `X`'s element is the more urgent (smaller number). -/
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

/-- "Actual" in the toy: the disposition IS the urgency plan. -/
def toyActual {a : Toy.Agent} {t : Toy.Time} {s : Stock Toy a t}
    (A : AllocationDisposition s) : Prop :=
  ∀ U, A.wouldServe U = Finset.range U.card

theorem toy_actual_exists (k : ℕ) : toyActual (toyPlan k) := by
  intro U
  rfl

/-- The toy plan is homogeneous: it depends on the count alone. -/
theorem toy_homogeneous (k : ℕ) : (toyPlan k).Homogeneous := by
  intro U _ V _ h
  show Finset.range U.card = Finset.range V.card
  rw [h]

def toy_ends_distinguishable : DecidableEq Toy.End :=
  inferInstanceAs (DecidableEq ℕ)

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

theorem toy_swap_dominance : SwapDominance Toy (fun A => toyActual A) := by
  intro _ _ s A hA U _ e he e' _ hne
  rw [hA U] at he hne ⊢
  set n := U.card
  have hen : e < n := Finset.mem_range.mp he
  have he'n : ¬ e' < n := fun h => hne (Finset.mem_range.mpr h)
  refine ⟨e, e', Finset.mem_coe.mpr he, Set.mem_insert e' _, ?_, ?_,
    Nat.lt_of_lt_of_le hen (Nat.le_of_not_lt he'n), ?_⟩
  · intro h
    rcases h with h | h
    · exact he'n (h ▸ hen)
    · exact h.2 rfl
  · intro h
    exact he'n (Finset.mem_range.mp (Finset.mem_coe.mp h))
  · have : e' ∉ ((↑(Finset.range n) : Set ℕ) \ {e}) := by
      intro h
      exact he'n (Finset.mem_range.mp (Finset.mem_coe.mp h.1))
    rw [Set.insert_sdiff_self_of_notMem this]

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
(the membership `marginalEnds` is defined by, spelled out because
that definition is over `World`). -/
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

end Model
end Apodictic
