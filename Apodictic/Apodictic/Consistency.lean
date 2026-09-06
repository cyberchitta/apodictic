import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Apodictic.MarginalUtility

/-!
# Consistency — Rothbard's horses, machine-checked

The library asserts no axioms; its praxeological content travels as
hypotheses (`Apodictic.Commitments`). So consistency is an INSTANCE.
Build a concrete frame, a stock, and a plan; prove the plan satisfies
`SwapDominant`; hand the whole thing to the law. If that type-checks,
the commitment and every hypothesis are jointly satisfiable, and the
theorems are not vacuous. Nothing is transcribed:
`horses_swapDominant` proves the very proposition
`marginal_utility_chain` consumes.

The frame is Rothbard's own worked case, not an invented one (*MES*
pp. 25–27). A man has six interchangeable horses. There are ten ends
the horses could serve, ranked in order of importance; the six he
holds serve the first six, and ends 7–10 go unserved. He is faced
with giving up one horse, and "he gives up the least urgent of the
wants which the larger stock would have satisfied" (p. 25) — end 6,
which Rothbard names: pleasure riding.

Two theorems here are more than bookkeeping, because they reproduce
Rothbard's own conclusions:

- `loss_of_a_horse_ends_pleasure_riding` — his p. 25 result. The end
  given up when the sixth horse goes is the sixth-ranked end.
- `which_horse_does_not_matter` — his p. 27 result, the one he names
  two horses to make. Losing Man o' War (leading a wagon) and losing
  Seabiscuit (pleasure riding) leave the agent serving the same ends,
  because Seabiscuit is simply moved to the wagon. This is what
  interchangeability MEANS, and it is why the plan is indexed by
  which sub-stock while `Homogeneous` is a separate named condition.

This module is EVIDENCE, not theory: nothing else depends on it, and
no praxeological claim is made here. Its proofs may use whatever
mathlib offers (classical lemmas included); the
constructive-by-default rule governs the library's theorems, not the
bookkeeping of a model.

Two places where the model is not Rothbard's, both harmless and both
recorded rather than papered over:

1. **No ceiling of ten ends.** Rothbard's ten are "for simplicity",
   to fit a diagram. Capping the scale would drag a side condition
   through every theorem and buy nothing, so the good here serves
   every rank on the scale. His six served ends are still the first
   six.
2. **Which horse is Man o' War is arbitrary.** Rothbard says only
   that he "had arrived earlier" than Seabiscuit, so any earlier
   horse does. Horses carry no claim beyond their identity, which is
   the point of the theorem they appear in.
-/

namespace Apodictic
namespace Model

/-- Asymmetry of preference: if `X` is preferred to `Y` then `Y` is
not preferred to `X`. This is the "strict" reading intended all
along, and it is not yet a commitment (OPEN.md). The model has to
survive it. -/
def Asymmetric (frame : ActionFrame) : Prop :=
  ∀ (agent : frame.Agent) (time : frame.Time) (X Y : Set frame.End),
    frame.Prefers agent time X Y → ¬ frame.Prefers agent time Y X

/-- A want the horses can serve, named by its place on the man's value
scale: rank 1 is the most urgent, and the lower the number the more
urgent the want. There is no rank 0 — the scale starts at one, as
Rothbard's does. -/
abbrev Want := ℕ

/-- An individual horse. Horses are told apart only by identity —
nothing else about them enters any claim, which is exactly Rothbard's
point in naming two of them. -/
abbrev Horse := ℕ

/-- The sixth-ranked end: pleasure riding. Rothbard names it as the
least urgent of the wants the six horses serve, and so as the one
given up when a horse is lost (*MES* p. 25). -/
def pleasureRiding : Want := 6

/-- Seabiscuit — the horse Rothbard names as the sixth acquired, put
to pleasure riding (*MES* p. 27). -/
def seabiscuit : Horse := 5

/-- Man o' War — the horse Rothbard names as having arrived earlier,
engaged in "the more important duty (to him) of leading a wagon"
(*MES* p. 27). Which of the earlier horses he is makes no difference
to anything claimed here. -/
def manOWar : Horse := 1

/-- Preference between bundles of wants. `X` is preferred to `Y`
exactly when the two differ by a single swap, and the want `X` has in
place of `Y`'s is the more urgent of the two — which here just means
the lower rank. -/
def rankPrefers (X Y : Set Want) : Prop :=
  ∃ w w', w ∈ X ∧ w' ∈ Y ∧ w ∉ Y ∧ w' ∉ X ∧ w < w' ∧ X \ {w} = Y \ {w'}

/-- The frame: one man, one instant, horses for means, ranked wants
for ends, and every horse able to serve any want on the scale. -/
abbrev Horses : ActionFrame where
  Agent := Unit
  End := Want
  Means := Horse
  Time := Unit
  Believes := fun _ _ _ want => 1 ≤ want
  Prefers := fun _ _ X Y => rankPrefers X Y

/-- A stable of `k` horses. Rothbard's case is `horseStock 6`. -/
def horseStock (k : ℕ) : Stock Horses () () where
  units := Finset.range k
  serves := {want | 1 ≤ want}
  unitsAlike := by
    intro _ _ _
    exact ⟨fun h => h, fun h => h⟩

/-- The man's plan: with any `n` horses he serves the `n` most urgent
wants — ranks `1` through `n`. Which horses they are does not enter,
which is what makes the plan homogeneous below. -/
def horsePlan (k : ℕ) : AllocationPlan (horseStock k) where
  wouldServe := fun sub => Finset.Icc 1 sub.card
  servesOnlyWhatItCan := by
    intro _ want hwant
    exact (Finset.mem_Icc.mp hwant).1
  oneUnitOneEnd := by
    intro sub _
    rw [Nat.card_Icc]
    omega

/-- Wants are decidable in this frame — the instance the theorems
take as `[DecidableEq frame.End]`. -/
instance : DecidableEq Horses.End := inferInstanceAs (DecidableEq ℕ)

/-- **Interchangeability holds of the plan**: it depends on how many
horses there are, never on which. -/
theorem horses_homogeneous (k : ℕ) : (horsePlan k).Homogeneous := by
  intro fewer _ more _ hcard
  show Finset.Icc 1 fewer.card = Finset.Icc 1 more.card
  rw [hcard]

theorem horses_asymmetric : Asymmetric Horses := by
  intro _ _ X Y h1 h2
  obtain ⟨w, w', hwX, hw'Y, hwY, hw'X, hlt, heq⟩ := h1
  obtain ⟨v, v', hvY, hv'X, hvX, hv'Y, hlt', heq'⟩ := h2
  -- `v` must be `w'`: it is in `Y`, not in `X`, so not in `Y \ {w'}`
  have hv : v = w' := by
    by_contra hne
    have : v ∈ Y \ {w'} := ⟨hvY, hne⟩
    exact hvX ((Set.ext_iff.mp heq v).mpr this).1
  -- `v'` must be `w`, symmetrically
  have hv' : v' = w := by
    by_contra hne
    have : v' ∈ X \ {w} := ⟨hv'X, hne⟩
    exact hv'Y ((Set.ext_iff.mp heq v').mp this).1
  subst hv hv'
  exact Nat.lt_asymm hlt hlt'

/-- **The man's plan is swap-dominant** — the commitment itself, proved
of this frame and this plan. Serving the `n` most urgent wants beats
any one-swap alternative, because any want swapped in ranks below
every want swapped out. -/
theorem horses_swapDominant (k : ℕ) : SwapDominant (horsePlan k) where
  swap := by
    intro sub _ served hserved unserved hpossible hnot
    have hs := Finset.mem_Icc.mp hserved
    have hu : ¬ (1 ≤ unserved ∧ unserved ≤ sub.card) :=
      fun h => hnot (Finset.mem_Icc.mpr h)
    have hlt : served < unserved := by
      rcases Nat.lt_or_ge sub.card unserved with hbig | hsmall
      · exact Nat.lt_of_le_of_lt hs.2 hbig
      · exact absurd (Finset.mem_Icc.mpr ⟨hpossible, hsmall⟩) hnot
    show rankPrefers (↑(Finset.Icc 1 sub.card))
      (insert unserved ((↑(Finset.Icc 1 sub.card) : Set Want) \ {served}))
    refine ⟨served, unserved, Finset.mem_coe.mpr hserved,
      Set.mem_insert unserved _, ?_, ?_, hlt, ?_⟩
    · intro h
      rcases h with h | h
      · exact absurd h (Nat.ne_of_lt hlt)
      · exact h.2 rfl
    · intro h
      exact hnot (Finset.mem_coe.mp h)
    · have hnm : unserved ∉ ((↑(Finset.Icc 1 sub.card) : Set Want) \ {served}) := by
        intro h
        exact hnot (Finset.mem_coe.mp h.1)
      rw [Set.insert_sdiff_self_of_notMem hnm]

/-- Uses are independent in this frame: the horses' jobs do not
complement one another. -/
theorem horses_independent (agent : Horses.Agent) (time : Horses.Time) :
    Horses.IndependentUses agent time := by
  intro rest want other hwant hother h
  obtain ⟨v, v', hv, hv', hvY, hv'X, hlt, _⟩ := h
  have hvw : v = want := by
    rcases hv with h | h
    · exact h
    · exact absurd (Set.mem_insert_of_mem other h) hvY
  have hv'o : v' = other := by
    rcases hv' with h | h
    · exact h
    · exact absurd (Set.mem_insert_of_mem want h) hv'X
  subst hvw hv'o
  refine ⟨v, v', rfl, rfl, ?_, ?_, hlt, ?_⟩
  · intro h
    exact absurd (h : v = v') (Nat.ne_of_lt hlt)
  · intro h
    exact absurd (h : v' = v).symm (Nat.ne_of_lt hlt)
  · rw [Set.sdiff_self, Set.sdiff_self]

/-- One-horse steps exist inside the stable, so the theorems apply
here non-vacuously. -/
theorem horses_one_more (k n : ℕ) (h : n < k) :
    (horseStock k).OneMore (Finset.range n) (Finset.range (n + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_range.mpr
      (Nat.lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.le_succ n))
  · show Finset.range (n + 1) ⊆ Finset.range k
    intro x hx
    exact Finset.mem_range.mpr
      (Nat.lt_of_lt_of_le (Finset.mem_range.mp hx) h)
  · rw [Finset.card_range, Finset.card_range]

/-- The conclusion is not empty: the step from `n` horses to `n + 1`
has a marginal end, namely rank `n + 1` — served with `n + 1` horses
and not with `n`. -/
theorem horses_marginal_nonempty (k n : ℕ) :
    n + 1 ∈ (horsePlan k).wouldServe (Finset.range (n + 1)) ∧
      n + 1 ∉ (horsePlan k).wouldServe (Finset.range n) := by
  constructor
  · show n + 1 ∈ Finset.Icc 1 (Finset.range (n + 1)).card
    rw [Finset.card_range]
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le n), Nat.le_refl _⟩
  · show n + 1 ∉ Finset.Icc 1 (Finset.range n).card
    rw [Finset.card_range]
    intro h
    exact Nat.not_succ_le_self n (Finset.mem_Icc.mp h).2

/-- **Rothbard's own conclusion, p. 25.** With six horses the man
serves the six most urgent wants. Lose one, and what he gives up is
the sixth-ranked want — pleasure riding, in Rothbard's telling: "the
loss of a horse will cause him to give up pleasure riding".

Here it is a calculation about the plan, not a further assumption. -/
theorem loss_of_a_horse_ends_pleasure_riding :
    pleasureRiding ∈ marginalEnds (horsePlan 6)
      (Finset.range 5) (Finset.range 6) := by
  constructor
  · show pleasureRiding ∈ Finset.Icc 1 (Finset.range 6).card
    rw [Finset.card_range]
    exact Finset.mem_Icc.mpr ⟨by norm_num [pleasureRiding],
      by norm_num [pleasureRiding]⟩
  · show pleasureRiding ∉ Finset.Icc 1 (Finset.range 5).card
    rw [Finset.card_range]
    intro h
    have := (Finset.mem_Icc.mp h).2
    norm_num [pleasureRiding] at this

/-- **Rothbard's own conclusion, p. 27** — the one he names two
horses to make. Losing Man o' War, who was leading a wagon, leaves
the man serving exactly the ends he would serve after losing
Seabiscuit, who was out for pleasure riding: he simply moves
Seabiscuit to the wagon. Which horse goes makes no difference to
which end is surrendered.

This is what interchangeability amounts to, and it is why the plan is
indexed by WHICH horses while `Homogeneous` is a separate named
condition: the claim has to be statable before it can be true. -/
theorem which_horse_does_not_matter :
    (horsePlan 6).wouldServe ((Finset.range 6).erase manOWar)
      = (horsePlan 6).wouldServe ((Finset.range 6).erase seabiscuit) := by
  have hman : manOWar ∈ Finset.range 6 := by
    simp [manOWar]
  have hsea : seabiscuit ∈ Finset.range 6 := by
    simp [seabiscuit]
  have hcard : ((Finset.range 6).erase manOWar).card
      = ((Finset.range 6).erase seabiscuit).card := by
    rw [Finset.card_erase_of_mem hman, Finset.card_erase_of_mem hsea]
  exact horses_homogeneous 6 _ (Finset.erase_subset _ _) _
    (Finset.erase_subset _ _) hcard

/-- **The law itself, applied to the horses.** Every hypothesis of
`marginal_utility_chain` is met at this frame. So the commitment and
the conditions on the situation can all hold at once, and the law is
not empty. That is the whole consistency argument: this type-checks,
therefore they fit together. -/
theorem horses_law_applies (k n : ℕ) (h : n < k) (h' : n + 1 < k) :
    ∀ addedFirst ∈ marginalEnds (horsePlan k)
        (Finset.range n) (Finset.range (n + 1)),
      ∀ addedSecond ∈ marginalEnds (horsePlan k)
        (Finset.range (n + 1)) (Finset.range (n + 2)),
      Horses.PrefersEnd () () addedFirst addedSecond :=
  marginal_utility_chain (horsePlan k) (horses_swapDominant k)
    (horses_independent () ()) _ _ _
    (horses_one_more k n h) (horses_one_more k (n + 1) h')

#print axioms horses_law_applies
#print axioms loss_of_a_horse_ends_pleasure_riding
#print axioms which_horse_does_not_matter

end Model
end Apodictic
