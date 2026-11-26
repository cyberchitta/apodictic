import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Apodictic.MarginalUtility
import Apodictic.Mises
import Apodictic.Temporal
import Apodictic.MutualBenefit
import Apodictic.TimePreference
import Apodictic.Regression
import Apodictic.PureInterest

/-!
# Consistency — Rothbard's horses, machine-checked

The library asserts no axioms; its praxeological content travels as
hypotheses (`Apodictic.Praxeology`). So consistency is an INSTANCE.
Build a concrete frame, a stock, and a plan; prove the plan satisfies
`SwapDominant`; hand the whole thing to the law. If that type-checks,
the praxeological claim and every hypothesis are jointly satisfiable, and the
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
exactly when two things hold. The two bundles differ by a single swap.
And the want `X` has in place of `Y`'s is the more urgent of the two.
Here more urgent just means a smaller rank number. -/
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

/-- Wants are decidable in this frame — the instance the theorems
take as `[DecidableEq praxis.End]`. -/
instance : DecidableEq Horses.End := inferInstanceAs (DecidableEq ℕ)

/-- **Interchangeability holds of the plan.** The plan depends on how
many horses there are. It never depends on which. -/
theorem horses_homogeneous (k : ℕ) : (horsePlan k).Homogeneous := by
  intro fewer _ more _ hcard
  show Finset.Icc 1 fewer.card = Finset.Icc 1 more.card
  rw [hcard]

/-- **Preference is asymmetric in this frame.** Ranks are compared by
`<`, so no two bundles are each preferred to the other. This is what
lets the claim hold somewhere preference is strict, which is the
reading intended throughout and what `no_rival_swap_dominant`
needs. -/
theorem horses_asymmetric (agent : Horses.Agent) (time : Horses.Time) :
    AsymmetricPreference Horses agent time := by
  refine ⟨?_⟩
  intro X Y h1 h2
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

/-- **The man's plan is swap-dominant.** This is the claim itself,
proved of this frame and this plan. Serving the `n` most urgent wants
beats any one-swap alternative. That is because a want a horse can
serve, but the plan would leave out, is less urgent than every want the
plan would serve. It has a larger rank number. -/
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
would serve the six most urgent wants. With five he would not serve
the sixth-ranked want. So the sixth-ranked want is one he gives up
when a horse goes. In Rothbard's telling it is pleasure riding: "the
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

/-- **Rothbard's own conclusion, p. 27.** It is the one he names two
horses to make. Man o' War was leading a wagon. Seabiscuit was out for
pleasure riding. After losing Man o' War, the man would serve exactly
the ends he would serve after losing Seabiscuit. In Rothbard's
telling, he simply moves Seabiscuit to the wagon. Which of the two
goes makes no difference to which end is given up.

This is what interchangeability amounts to. It is why the plan is
indexed by *which* horses, while `Homogeneous` is a separate named
condition. Rothbard's point has to be statable before it can be
true. -/
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
`marginal_utility_chain` is met at this frame. So the claim and the
conditions on the situation can all hold at once, and the law is not
empty. That is the whole consistency argument. This type-checks, so
they fit together. -/
theorem horses_law_applies (k n : ℕ) (h : n < k) (h' : n + 1 < k) :
    ∀ addedFirst ∈ marginalEnds (horsePlan k)
        (Finset.range n) (Finset.range (n + 1)),
      ∀ addedSecond ∈ marginalEnds (horsePlan k)
        (Finset.range (n + 1)) (Finset.range (n + 2)),
      Horses.PrefersEnd () () addedFirst addedSecond :=
  marginal_utility_chain (horsePlan k) (horses_swapDominant k)
    (horses_independent () ()) _ _ _
    (horses_one_more k n h) (horses_one_more k (n + 1) h')

/-! ## Serviceability does not deliver interchangeability

A counter-model, and it settles a question the document had to leave
open. Rothbard grounds interchangeability in his DEFINITION of a
supply: units "equally capable of rendering the same service to the
actor" (*MES* p. 23). That is `Stock.unitsAlike`. What the
supply-size form of the law needs is `AllocationPlan.Homogeneous` —
that two stables of the same size would be put to the same uses. The
two are not the same claim, and the first does not give the second.

The reason is structural, and the counter-model only makes it
concrete: `unitsAlike` is a field of `Stock`, so EVERY stock in this
library already satisfies it. `Homogeneous` is a condition on the
PLAN, a separate structure. No condition on the stock can constrain
the plan, because the plan is not determined by the stock — the same
six horses admit many plans, and `horsePlan` and `pickyPlan` below
are two of them over one stock.

That the proof is easy is not a warning sign here; the ease IS the
finding. Nothing was smuggled in to make it go through. What Rothbard
folds into one word, "supply", comes apart into a fact about horses
and a fact about the man's plan for them, and only the first is
carried by his definition. -/

/-- A plan for two horses that DOES depend on which horse it has. With
horse 0 in the stable the man serves the most urgent wants; without it
he serves different ones. Every horse can still serve every want —
`horseStock` proves `unitsAlike` for any size — so nothing about the
horses distinguishes this man from Rothbard's. What differs is his
plan. -/
def pickyPlan : AllocationPlan (horseStock 2) where
  wouldServe := fun sub =>
    if 0 ∈ sub then Finset.Icc 1 sub.card else Finset.Icc 2 (sub.card + 1)
  servesOnlyWhatItCan := by
    intro sub want hwant
    by_cases h : 0 ∈ sub
    · rw [if_pos h] at hwant
      exact (Finset.mem_Icc.mp hwant).1
    · rw [if_neg h] at hwant
      exact le_trans (by norm_num) (Finset.mem_Icc.mp hwant).1

/-- **Interchangeability fails for this plan.** One horse alone serves
want 1; the other alone serves want 2. Same size, different uses. -/
theorem picky_not_homogeneous : ¬ pickyPlan.Homogeneous := by
  intro h
  have h0 : ({0} : Finset Horse) ⊆ (horseStock 2).units :=
    Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr (by norm_num))
  have h1 : ({1} : Finset Horse) ⊆ (horseStock 2).units :=
    Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr (by norm_num))
  have heq := h {0} h0 {1} h1 rfl
  rw [show pickyPlan.wouldServe {0} = Finset.Icc 1 1 from rfl,
    show pickyPlan.wouldServe {1} = Finset.Icc 2 2 from rfl] at heq
  have : (1 : ℕ) ∈ Finset.Icc 2 2 := heq ▸ Finset.mem_Icc.mpr ⟨le_refl 1, le_refl 1⟩
  exact absurd (Finset.mem_Icc.mp this).1 (by norm_num)

/-- **The non-entailment, stated.** ONE stock — and since `unitsAlike`
is one of its fields, a stock whose every unit is equally serviceable
— carries a homogeneous plan AND a plan that is not. Two horses,
each able to serve any want, and two men who might own them.

So `unitsAlike` does not entail `Homogeneous`. Nothing about the
horses settles it, because the plan is a separate structure and the
stock does not determine it. Rothbard's definition of a supply
(*MES* p. 23) reaches the horses; the supply-size form of the law
needs something about the man, and his definition does not supply it
once p. 24 withdraws the equal-valuation half. That is why
interchangeability is a hypothesis to assume here and not a fact to
derive. -/
theorem unitsAlike_not_entail_homogeneous :
    ∃ stock : Stock Horses () (),
      (∃ plan : AllocationPlan stock, plan.Homogeneous) ∧
      (∃ plan : AllocationPlan stock, ¬ plan.Homogeneous) :=
  ⟨horseStock 2, ⟨horsePlan 2, horses_homogeneous 2⟩,
    ⟨pickyPlan, picky_not_homogeneous⟩⟩

#print axioms horses_law_applies
#print axioms loss_of_a_horse_ends_pleasure_riding
#print axioms which_horse_does_not_matter
#print axioms unitsAlike_not_entail_homogeneous

/-! ## Mises's dilemma: two frames

Mises derives the law from a dilemma (*Human Action*, ch. VII, §1).
Two frames here bracket it. The first shows his refutation of the
second horn does not go through on the premise he names. The second
shows that even granting him the horn, the law does not follow.

Evidence, not theory, like everything in this module. Both frames are
built as small as `Action` permits; neither models anything. -/

/-! ### The second horn is compatible with "there is action" -/

/-- A frame admitting exactly one action. Two ends so that something
can be given up (action is choice, so `forgone` must be nonempty and
must exclude the chosen end); everything else a single point, and
belief satisfied only by the chosen end, so that no second action can
be assembled. `Prefers` is empty: nothing here is about preference. -/
def Solitary : ActionFrame where
  Agent := Unit
  End := Bool
  Means := Unit
  Time := Unit
  Believes := fun _ _ _ want => want = true
  Prefers := fun _ _ _ _ => False

/-- The one action the frame admits: aim at `true`, give up `false`. -/
def solitaryAction : Action Solitary where
  agent := ()
  time := ()
  chosen := true
  means := ()
  forgone := {false}
  forgone_nonempty := ⟨false, rfl⟩
  chosen_not_forgone := by intro h; exact Bool.noConfusion h
  belief := rfl

/-- Every action of the frame IS that one. The chosen end is forced
by belief; the forgone set is forced by being nonempty and excluding
the chosen end; every other component lives in a one-point type. -/
theorem solitary_action_unique (act : Action Solitary) :
    act = solitaryAction := by
  obtain ⟨agent, time, chosen, means, forgone, hne, hnf, hb⟩ := act
  have hchosen : chosen = true := hb
  subst hchosen
  have hforgone : forgone = {false} := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      cases x
      · rfl
      · exact absurd hx hnf
    · intro hx
      obtain ⟨y, hy⟩ := hne
      cases y
      · cases hx; exact hy
      · exact absurd hy hnf
  subst hforgone
  cases agent
  cases time
  cases means
  rfl

/-- Bare existence holds. -/
theorem solitary_actionOccurs : Mises.ActionOccurs Solitary :=
  ⟨solitaryAction⟩

/-- And so does Mises's second horn. -/
theorem solitary_atMostOneAction : Mises.AtMostOneAction Solitary := by
  intro first second
  rw [solitary_action_unique first, solitary_action_unique second]

/-- **Existence does not refute the second horn.** Mises calls one
action followed by a terminal state "manifestly incompatible with our
assumption that there is action". The frame `Solitary` admits exactly
one action. It satisfies both halves he calls incompatible. So the
step is not valid as stated.

What his argument needs is `Mises.ActionRecurs`: that two distinct
actions occur. Nothing in "there is action" delivers it. His own
wording gestures past bare existence ("this case no longer implies the
general conditions presupposed in the category of action"). It does
not say what those conditions are. Naming them is the suppressed
premise of his derivation. -/
theorem existence_does_not_refute_second_horn :
    ¬ Mises.ExistenceRefutesSecondHorn := by
  intro promise
  exact promise Solitary solitary_actionOccurs solitary_atMostOneAction

/-! ### And winning the dilemma does not deliver the law

Grant Mises the first horn. Action is plural; there are intermediate
stages. Does the ladder follow? Not by itself: the frame below has
action plural — so the second horn is refuted and the dilemma is won
— and `LadderHolds` is false in it.

The gap is the one his next sentence papers over: "It is nothing else
than the reverse of the statement that what satisfies more is
preferred to what gives smaller satisfaction." Degrees of satisfaction
are one thing; an ORDERING OVER THE EMPLOYMENTS OF UNITS is another,
and nothing carries the first to the second. -/

/-- Action is plural here — belief is unrestricted, so either end may
be chosen.

Preference is NOT empty, and that is the point of this frame. `true`
is the urgent end and `false` the less urgent one: a bundle is
preferred exactly when it secures `true` and the rival does not. So
`PrefersEnd true false` holds, `PrefersEnd false true` does not, and
the relation is asymmetric (`plural_asymmetric`). The ladder will
fail here for a reason about the ORDERING, not because nothing is
preferred to anything. -/
def Plural : ActionFrame where
  Agent := Unit
  End := Bool
  Means := Unit
  Time := Unit
  Believes := fun _ _ _ _ => True
  Prefers := fun _ _ X Y => true ∈ X ∧ true ∉ Y

/-- Aim at `true`, give up `false`. -/
def pluralActionTrue : Action Plural where
  agent := (); time := (); chosen := true; means := ()
  forgone := {false}
  forgone_nonempty := ⟨false, rfl⟩
  chosen_not_forgone := by intro h; exact Bool.noConfusion h
  belief := trivial

/-- Aim at `false`, give up `true` — the second action the frame
admits, and the one `Solitary` was built to exclude. -/
def pluralActionFalse : Action Plural where
  agent := (); time := (); chosen := false; means := ()
  forgone := {true}
  forgone_nonempty := ⟨true, rfl⟩
  chosen_not_forgone := by intro h; exact Bool.noConfusion h
  belief := trivial

/-- Mises wins his dilemma in this frame: action is plural, so the
second horn is refuted. -/
theorem plural_actionRecurs : Mises.ActionRecurs Plural :=
  ⟨pluralActionTrue, pluralActionFalse,
    fun h => Bool.noConfusion (congrArg Action.chosen h)⟩

/-- Preference here is asymmetric — the frame survives the property
the library intends but does not yet assume. -/
theorem plural_asymmetric (agent : Plural.Agent) (time : Plural.Time) :
    AsymmetricPreference Plural agent time := by
  refine ⟨?_⟩
  intro X Y hXY hYX
  exact hXY.2 hYX.1

/-- And it is not empty: the urgent end really is preferred to the
less urgent one. Without this the counter-model below would prove
nothing, since a vacuous `Prefers` falsifies every ordering claim. -/
theorem plural_prefers_nontrivial :
    Plural.PrefersEnd () () true false :=
  ⟨rfl, fun h => Bool.noConfusion h⟩

/-- Decidable identity of ends, so that a two-element `Finset` of them
can be written down at all. -/
instance : DecidableEq Plural.End := inferInstanceAs (DecidableEq Bool)

/-- One unit; the good is believed to serve everything. -/
def pluralStock : Stock Plural () () where
  units := {()}
  serves := Set.univ
  unitsAlike := by
    intro _ _ want
    exact ⟨fun _ => Set.mem_univ want, fun _ => trivial⟩

/-- **A badly ordered plan.** With no units the agent would serve
`false`, the LESS urgent end; the extra unit is what brings in `true`,
the more urgent one.

Nothing in the vocabulary forbids this. `AllocationPlan` requires only
that a unit be put to an end the good can serve — it does not require
the agent to serve his most urgent wants first. That requirement is
exactly what `SwapDominant` supplies, and this plan is what its
absence looks like. -/
def pluralPlan : AllocationPlan pluralStock where
  wouldServe := fun subStock => if subStock.card = 0 then {false} else {false, true}
  servesOnlyWhatItCan := by
    intro _ want _
    exact Set.mem_univ want

theorem pluralPlan_empty : pluralPlan.wouldServe ∅ = {false} := by
  simp [pluralPlan]

theorem pluralPlan_full : pluralPlan.wouldServe {()} = {false, true} := by
  simp only [pluralPlan]
  rw [if_neg (by exact fun h => Finset.singleton_ne_empty () (Finset.card_eq_zero.mp h))]

/-- **Refuting the second horn does not deliver the ladder.** Take a
frame where action is plural. Mises's dilemma is won outright there.
In that frame the ladder fails.

And it fails for a substantive reason, not a degenerate one.
Preference here is asymmetric (`plural_asymmetric`) and non-empty
(`plural_prefers_nontrivial`). What goes wrong is the agent's plan. It
serves the less urgent end first. So the unit he adds brings in
something MORE urgent than what he was already serving. Mises's
sentence is false of this agent. Everything the dilemma establishes
is true of him.

So the step from "there are intermediate stages" to the law is not
valid on its own. What has to be added is that the plan respects the
ordering. The library reconstructs it as `ServedInOrder`. That is
strictly weaker than Rothbard's premises (`SwapDominant`, with
independence of uses and asymmetry). In Mises's own text the addition
is a single unargued sentence: "It is nothing else than the reverse of the
statement that what satisfies more is preferred to what gives smaller
satisfaction."

This does not show Mises's derivation is unsalvageable. It shows the
dilemma is not the premise. -/
theorem recurs_does_not_deliver_ladder :
    Mises.ActionRecurs Plural ∧ ¬ Mises.LadderHolds pluralPlan := by
  refine ⟨plural_actionRecurs, ?_⟩
  intro ladder
  have step : pluralStock.OneMore ∅ {()} :=
    ⟨Finset.empty_subset _, Finset.Subset.refl _, rfl⟩
  have hleast : Mises.LeastUrgentServed pluralPlan ∅ false := by
    rw [Mises.LeastUrgentServed, pluralPlan_empty]
    refine ⟨Finset.mem_singleton_self false, ?_⟩
    intro other hother hne
    exact absurd (Finset.mem_singleton.mp hother) hne
  have hadded : true ∈ Mises.marginalEmployment pluralPlan ∅ {()} := by
    constructor
    · rw [pluralPlan_full]; decide
    · rw [pluralPlan_empty]; decide
  have hbad := ladder ∅ {()} step false hleast true hadded
  exact Bool.noConfusion hbad.1

#print axioms existence_does_not_refute_second_horn
#print axioms recurs_does_not_deliver_ladder

/-! ## The converse fails: serving in order does not deliver swap dominance

`Contrast.rothbard_entails_servedInOrder` shows Rothbard's premises
entail Mises's bridge. This frame shows the entailment does not run
back, so Rothbard's premise set is STRICTLY stronger.

The separating feature is the one the two premises actually differ
over. `ServedInOrder` is a claim about ENDS — which of them the plan
admits. `SwapDominant` is a claim about BUNDLES — that the served
bundle beats each one-swap rival. A frame can rank ends perfectly
well and still be too coarse to rank the bundles, and then the second
claim fails while the first holds.

Preference here is asymmetric and non-trivial; nothing is vacuous. -/

/-- Ends are numbered by urgency, lower being more urgent, and the
good can serve the first three. A bundle is preferred when it has a
member beating EVERY member of the rival — a coarse but perfectly
ordinal relation, and one the library permits, since it imposes no
property on `Prefers`. -/
abbrev Coarse : ActionFrame where
  Agent := Unit
  End := ℕ
  Means := Unit
  Time := Unit
  Believes := fun _ _ _ want => want ≤ 2
  Prefers := fun _ _ X Y => ∃ x ∈ X, ∀ y ∈ Y, x < y

/-- Asymmetric: two bundles cannot each have a member beating all of
the other's. -/
theorem coarse_asymmetric (agent : Coarse.Agent) (time : Coarse.Time) :
    AsymmetricPreference Coarse agent time := by
  refine ⟨?_⟩
  intro X Y hXY hYX
  obtain ⟨x, hx, hxall⟩ := hXY
  obtain ⟨y, hy, hyall⟩ := hYX
  exact absurd (hxall y hy) (Nat.not_lt.mpr (Nat.le_of_lt (hyall x hx)))

/-- And non-trivial: the more urgent end really is preferred. -/
theorem coarse_prefers_nontrivial : Coarse.PrefersEnd () () 0 1 :=
  ⟨0, rfl, by intro y hy; cases hy; norm_num⟩

/-- Decidable identity of ends, so the `Finset` literals below can be
written at all. -/
instance : DecidableEq Coarse.End := inferInstanceAs (DecidableEq ℕ)

/-- One unit; the good serves ends 0, 1 and 2. -/
def coarseStock : Stock Coarse () () where
  units := {()}
  serves := {want | want ≤ 2}
  unitsAlike := by intro _ _ _; exact Iff.rfl

/-- The agent serves ends 0 and 1, leaving 2 unserved. -/
def coarsePlan : AllocationPlan coarseStock where
  wouldServe := fun _ => {0, 1}
  servesOnlyWhatItCan := by
    intro _ want hwant
    have hcase : want = 0 ∨ want = 1 := by simpa using hwant
    rcases hcase with rfl | rfl
    · show (0 : ℕ) ≤ 2
      norm_num
    · show (1 : ℕ) ≤ 2
      norm_num

/-- **Serving in order holds — and not vacuously.** End 1 is served,
end 0 is more urgent, and end 0 is served too. -/
theorem coarse_servedInOrder : ServedInOrder coarsePlan := by
  refine ⟨?_⟩
  intro _ _ served hserved better _ hbetter
  obtain ⟨x, hx, hall⟩ := hbetter
  cases hx
  have hlt : better < served := hall served rfl
  have hcase : served = 0 ∨ served = 1 := by
    simpa [coarsePlan] using hserved
  show better ∈ ({0, 1} : Finset ℕ)
  rcases hcase with rfl | rfl
  · exact absurd hlt (Nat.not_lt_zero better)
  · have hb : better = 0 := Nat.lt_one_iff.mp hlt
    subst hb
    simp

/-- **Swap dominance fails.** Swap the served end 1 for the unserved
end 2: the rival bundle is `{0, 2}`, and this frame cannot rank
`{0, 1}` above it, because neither bundle has a member beating every
member of the other — both contain 0.

Nothing is wrong with the agent here. He serves his most urgent
wants, in order, leaving the least urgent unserved. It is the
BUNDLE-level comparison that fails, and that is precisely the extra
thing swap dominance demands. -/
theorem coarse_not_swapDominant : ¬ SwapDominant coarsePlan := by
  intro dominance
  have hswap := dominance.swap ∅ (Finset.empty_subset _) 1 (by simp [coarsePlan])
    2 (by norm_num [coarseStock]) (by simp [coarsePlan])
  obtain ⟨x, _, hall⟩ := hswap
  have hzero : (0 : ℕ) ∈ insert 2 ((↑(coarsePlan.wouldServe ∅) : Set Coarse.End) \ {1}) := by
    refine Or.inr ⟨?_, ?_⟩
    · simp [coarsePlan]
    · norm_num
  exact absurd (hall 0 hzero) (Nat.not_lt_zero x)

/-- **The two premise sets are not equivalent.** Rothbard's set
entails Mises's bridge, `ServedInOrder`
(`Contrast.rothbard_entails_servedInOrder`). This frame shows the
converse fails. Reconstruct the Mises route as generously as the
vocabulary allows. It then rests on a STRICTLY WEAKER allocation
premise than Rothbard's set. It pays for that with
comparability of ends (`ComparableServiceable`), which Rothbard's
route never needs. -/
theorem servedInOrder_not_entail_swapDominant :
    ServedInOrder coarsePlan ∧ ¬ SwapDominant coarsePlan :=
  ⟨coarse_servedInOrder, coarse_not_swapDominant⟩

#print axioms servedInOrder_not_entail_swapDominant

/-! ## Where Mises's law is silent and Rothbard's premise holds

If `ComparableServiceable` is a situational CONDITION rather than a
claim, then the Mises route applies to fewer situations than the
Rothbard route. This frame is one of them: Rothbard's premise, swap
dominance, holds, and Mises's condition fails.

The frame is not arbitrary, and the constraint on building it is
itself the finding. Swap dominance compares the served bundle with
each ONE-SWAP rival. With independence of uses (`IndependentUses`)
that forces a comparison between every served end and every unserved
serviceable one (`served_over_unserved`). Where both hold,
comparability can therefore only fail for a pair of ends that NEVER straddles the margin — two
ends that are both always unserved, or both always served, at every
sub-stock. Here that pair is ends 3 and 4: the stock is two units, so
only ends 1 and 2 are ever served, and 3 and 4 sit permanently
outside.

So the gap between the two conditions is exactly the pairs of ends
that never sit on either side of a margin — which is a narrow gap,
and worth knowing it is narrow. -/

/-- Urgency as a PARTIAL order: lower rank is more urgent, except
that ends 3 and 4 are left incomparable. Nothing in the library
requires `Prefers` to rank every pair, and this is what declining to
looks like. -/
def urgent (want other : ℕ) : Prop :=
  want < other ∧ ¬(want = 3 ∧ other = 4)

/-- The horses' one-swap preference, over `urgent` instead of `<`. -/
def marginPrefers (X Y : Set ℕ) : Prop :=
  ∃ w w', w ∈ X ∧ w' ∈ Y ∧ w ∉ Y ∧ w' ∉ X ∧ urgent w w' ∧ X \ {w} = Y \ {w'}

/-- Four serviceable ends, of which two are never reached. -/
abbrev Margin : ActionFrame where
  Agent := Unit
  End := ℕ
  Means := ℕ
  Time := Unit
  Believes := fun _ _ _ want => 1 ≤ want ∧ want ≤ 4
  Prefers := fun _ _ X Y => marginPrefers X Y

instance : DecidableEq Margin.End := inferInstanceAs (DecidableEq ℕ)

/-- Two units, four serviceable ends. -/
def marginStock : Stock Margin () () where
  units := {1, 2}
  serves := {want | 1 ≤ want ∧ want ≤ 4}
  unitsAlike := by intro _ _ _; exact Iff.rfl

/-- Serve the most urgent ends first, as many as there are units —
capped at two, so ends 3 and 4 are never served. -/
def marginPlan : AllocationPlan marginStock where
  wouldServe := fun subStock => Finset.Icc 1 (min subStock.card 2)
  servesOnlyWhatItCan := by
    intro subStock want hwant
    rw [Finset.mem_Icc] at hwant
    exact ⟨hwant.1, le_trans hwant.2 (le_trans (min_le_right _ _) (by norm_num))⟩

/-- **Swap dominance holds.** Every served end has rank at most two,
every unserved serviceable end has a strictly greater rank, and the
excluded pair (3, 4) never arises because 3 is never served. -/
theorem margin_swapDominant : SwapDominant marginPlan where
  swap := by
    intro subStock _ served hserved unserved hcanServe hnotServed
    have hserved : 1 ≤ served ∧ served ≤ min subStock.card 2 :=
      Finset.mem_Icc.mp hserved
    have hcap : min subStock.card 2 ≤ 2 := min_le_right _ _
    have hservedLe : served ≤ 2 := le_trans hserved.2 hcap
    have hgt : min subStock.card 2 < unserved := by
      by_contra hle
      exact hnotServed (Finset.mem_Icc.mpr ⟨hcanServe.1, Nat.le_of_not_lt hle⟩)
    have hlt : served < unserved := lt_of_le_of_lt hserved.2 hgt
    have hne : served ≠ unserved := Nat.ne_of_lt hlt
    have hservedMem : served ∈ (↑(marginPlan.wouldServe subStock) : Set ℕ) :=
      Finset.mem_coe.mpr (Finset.mem_Icc.mpr hserved)
    have hunservedNot : unserved ∉ (↑(marginPlan.wouldServe subStock) : Set ℕ) :=
      fun h => hnotServed (Finset.mem_coe.mp h)
    refine ⟨served, unserved, hservedMem, Or.inl rfl, ?_, hunservedNot,
      ⟨hlt, ?_⟩, ?_⟩
    · rintro (heq | ⟨_, hne'⟩)
      · exact hne heq
      · exact hne' rfl
    · rintro ⟨h3, _⟩
      rw [h3] at hservedLe
      exact absurd hservedLe (by norm_num)
    · apply Set.ext
      intro x
      constructor
      · rintro ⟨hx, hxne⟩
        refine ⟨Or.inr ⟨hx, hxne⟩, ?_⟩
        intro hxu
        exact hunservedNot (hxu ▸ hx)
      · rintro ⟨hx | ⟨hx, hxne⟩, hxu⟩
        · exact absurd hx hxu
        · exact ⟨hx, hxne⟩

/-- **Mises's condition fails.** Ends 3 and 4 are both serviceable and
neither is preferred to the other, because `urgent` declines to rank
them. -/
theorem margin_not_comparable :
    ¬ marginStock.ComparableServiceable := by
  intro comparable
  rcases comparable 3 (by norm_num [marginStock]) 4 (by norm_num [marginStock])
      (by norm_num) with h | h
  · obtain ⟨w, w', hw, hw', _, _, hurgent, _⟩ := h
    cases hw; cases hw'
    exact hurgent.2 ⟨rfl, rfl⟩
  · obtain ⟨w, w', hw, hw', _, _, hurgent, _⟩ := h
    cases hw; cases hw'
    exact absurd hurgent.1 (by norm_num)

/-- **A situation where Rothbard's premise holds and Mises's route
does not apply.**

Swap dominance (`SwapDominant`) holds for this agent. Comparability
(`ComparableServiceable`) fails. So `Mises.ladder_from_order` does not
apply at all: its premise is unavailable.

Comparability is a condition. So this is what "Mises's law covers
fewer situations" means concretely. It means an agent with two ends he
has never had occasion to rank against each other. Suppose
comparability were a claim. Then praxeology would assert that no such
agent exists. This frame would then be a counter-example to the claim,
not a gap in the theorem's reach. -/
theorem rothbard_premise_holds_where_mises_is_silent :
    SwapDominant marginPlan ∧ ¬ marginStock.ComparableServiceable :=
  ⟨margin_swapDominant, margin_not_comparable⟩

#print axioms rothbard_premise_holds_where_mises_is_silent

/-! ## The temporal reading: a scale that reverses between two times

`Apodictic.Temporal` reads Mises's ladder as a history and proves it on
the earlier scale. The frame below is where the later-scale version
fails. Two times, two ends, a stock that grows from one unit to two.
At the earlier time the urgent end is `true` and the one unit serves
it; at the later time the urgent end is `false`, and both are served.
Every one-time premise holds at both times. The ladder judged on the
later scale asks that `true` — served first — still outrank `false`,
the increment's want. It does not.

Nothing here is exotic. The scale changed between the two times, which
is the case both authors say a value scale cannot be assumed not to
be: "value judgments are not immutable" (*Human Action*, ch. V, §4);
"the ranking on his preference scale shifts" (*MES* p. 18). -/

/-- The end that is urgent at a time: `true` at the earlier time
(`false`), `false` at the later (`true`). -/
def urgentAt (time : Bool) : Bool := !time

/-- Two times, two ends, two possible units. A bundle is preferred
exactly when it secures the end urgent at that time and the rival
does not. Belief is unrestricted. -/
def Reversal : ActionFrame where
  Agent := Unit
  End := Bool
  Means := Bool
  Time := Bool
  Believes := fun _ _ _ _ => True
  Prefers := fun _ time X Y => urgentAt time ∈ X ∧ urgentAt time ∉ Y

instance : DecidableEq Reversal.End := inferInstanceAs (DecidableEq Bool)
instance : DecidableEq Reversal.Means := inferInstanceAs (DecidableEq Bool)

/-- Preference is asymmetric at both times. -/
theorem reversal_asymmetric (agent : Reversal.Agent) (time : Reversal.Time) :
    AsymmetricPreference Reversal agent time := by
  refine ⟨?_⟩
  intro X Y hXY hYX
  exact hXY.2 hYX.1

/-- And it reverses: `true` outranks `false` at the earlier time, and
`false` outranks `true` at the later. -/
theorem reversal_reverses :
    Reversal.PrefersEnd () false true false ∧
      Reversal.PrefersEnd () true false true := by
  constructor
  · exact ⟨rfl, fun h => Bool.noConfusion h⟩
  · exact ⟨rfl, fun h => Bool.noConfusion h⟩

/-- The stock at the earlier time: one unit. -/
def earlierStock : Stock Reversal () false where
  units := {false}
  serves := Set.univ
  unitsAlike := fun _ _ _ => ⟨fun _ => Set.mem_univ _, fun _ => trivial⟩

/-- The stock at the later time: the same unit and one more. -/
def laterStock : Stock Reversal () true where
  units := {false, true}
  serves := Set.univ
  unitsAlike := fun _ _ _ => ⟨fun _ => Set.mem_univ _, fun _ => trivial⟩

/-- The supply grew by one. -/
theorem reversal_grows : earlierStock.Grows laterStock := by
  refine ⟨?_, ?_⟩
  · intro u hu
    exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hu))
  · decide

/-- What the one unit served at the earlier time: the end urgent
then. -/
def beforeAllocation : Allocation earlierStock where
  served := {true}
  servesOnlyWhatItCan := fun _ _ => Set.mem_univ _

/-- What the two units serve at the later time: both ends. -/
def afterAllocation : Allocation laterStock where
  served := {true, false}
  servesOnlyWhatItCan := fun _ _ => Set.mem_univ _

/-- The earlier allocation acts in order: nothing more urgent than
`true` at the earlier time was passed over, because nothing is. -/
theorem before_actsInOrder : ActsInOrder beforeAllocation := by
  refine ⟨?_⟩
  intro served hserved better _ hbetter
  have hservedTrue : served = true := Finset.mem_singleton.mp hserved
  subst hservedTrue
  obtain ⟨hmem, _⟩ := hbetter
  -- `hmem : urgentAt false ∈ {better}`, i.e. `true = better`
  exact Finset.mem_singleton.mpr hmem.symm

/-- The later allocation acts in order: everything is served. -/
theorem after_actsInOrder : ActsInOrder afterAllocation := by
  refine ⟨?_⟩
  intro _ _ better _ _
  cases better with
  | true => exact Finset.mem_insert.mpr (Or.inl rfl)
  | false => exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))

/-- The good's ends are comparable at both times. -/
theorem reversal_comparable_earlier : earlierStock.ComparableServiceable := by
  intro one _ other _ hne
  cases one <;> cases other
  · exact absurd rfl hne
  · exact Or.inr ⟨rfl, fun h => Bool.noConfusion h⟩
  · exact Or.inl ⟨rfl, fun h => Bool.noConfusion h⟩
  · exact absurd rfl hne

theorem reversal_comparable_later : laterStock.ComparableServiceable := by
  intro one _ other _ hne
  cases one <;> cases other
  · exact absurd rfl hne
  · exact Or.inl ⟨rfl, fun h => Bool.noConfusion h⟩
  · exact Or.inr ⟨rfl, fun h => Bool.noConfusion h⟩
  · exact absurd rfl hne

/-- On the earlier scale the ladder holds here — the library's theorem
applied, not re-proved. -/
theorem reversal_ladder_judged_earlier :
    Temporal.Ladder beforeAllocation afterAllocation false :=
  Temporal.ladder_judged_earlier beforeAllocation afterAllocation
    before_actsInOrder reversal_comparable_earlier (fun _ h => h)

/-- On the later scale it fails: `true` was the least urgent (the only)
want served before, `false` is what the increment serves, and at the
later time `false` outranks `true`. -/
theorem reversal_ladder_judged_later_fails :
    ¬ Temporal.Ladder beforeAllocation afterAllocation true := by
  intro ladder
  have hleast : Temporal.LeastUrgentServed beforeAllocation true := by
    refine ⟨Finset.mem_singleton.mpr rfl, ?_⟩
    intro other hother hne
    exact absurd (Finset.mem_singleton.mp hother) hne
  have h := ladder true hleast false
    (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
    (fun hmem => Bool.noConfusion (Finset.mem_singleton.mp hmem))
  -- `h.1 : urgentAt true ∈ {true}`, i.e. `false = true`
  exact Bool.noConfusion h.1

/-- **The later-judged ladder does not follow from one-time premises.**
Every hypothesis of `Temporal.LadderJudgedLaterFromOrder` holds in
this frame. Its conclusion does not. What is missing is a relation
between the two scales. This frame is exactly a case where there is
none. -/
theorem later_judged_ladder_fails : ¬ Temporal.LadderJudgedLaterFromOrder := by
  intro h
  exact reversal_ladder_judged_later_fails
    (h Reversal () false true earlierStock laterStock beforeAllocation
      afterAllocation reversal_grows rfl before_actsInOrder after_actsInOrder
      reversal_comparable_earlier reversal_comparable_later
      (reversal_asymmetric () false) (reversal_asymmetric () true))

#print axioms reversal_ladder_judged_earlier
#print axioms later_judged_ladder_fails

/-! ## Exchange: the vase and the typewriter

Rothbard's own unique-goods case (*MES* p. 86): "If A has a vase and B
a typewriter, if each knows of the other's asset, and if A values the
typewriter more highly, and B values the vase more highly, there will
be an exchange."

One frame, three variants. Agents, times, goods and ends are all
`Bool`: agent `false` is A, `true` is B; good `false` is the vase,
`true` the typewriter; end `false` is decoration, `true` is typing;
time `false` is the trade, `true` is afterwards. Each agent cares for
one end at a time (`wanted`), and prefers any bundle with it to any
without.

- `barterOk` — both parties trade, and nothing changes afterwards.
  Every claim and every condition of `Apodictic.MutualBenefit` holds;
  both parties' trades are handed to the theorems.
- `barterFraud` — afterwards the typewriter is believed to serve
  nothing. The ranking holds; A is not better off by his later lights.
- `barterRegret` — afterwards each wants what he gave away. The beliefs
  hold; A is not better off by his later lights. -/

/-- The barter frame, given who believes what and who wants what. -/
abbrev barterFrame (believes : Bool → Bool → Bool → Bool → Prop)
    (wanted : Bool → Bool → Bool) : ActionFrame where
  Agent := Bool
  End := Bool
  Means := Bool
  Time := Bool
  Believes := believes
  Prefers := fun agent time X Y => wanted agent time ∈ X ∧ wanted agent time ∉ Y

/-- Each good serves the end that shares its name: the vase decoration,
the typewriter typing. -/
def honestBeliefs : Bool → Bool → Bool → Bool → Prop :=
  fun _ _ good want => good = want

/-- A wants typing and B wants decoration, at every time. -/
def steadyWants : Bool → Bool → Bool := fun agent _ => !agent

/-- Everything holds. -/
abbrev barterOk : ActionFrame := barterFrame honestBeliefs steadyWants

/-- Afterwards the typewriter is believed to serve nothing. -/
abbrev barterFraud : ActionFrame :=
  barterFrame (fun _ time good want => good = want ∧ (time = false ∨ good = false))
    steadyWants

/-- Afterwards each wants what he gave away. -/
abbrev barterRegret : ActionFrame :=
  barterFrame honestBeliefs (fun agent time => if time then agent else !agent)

/-- Agent `agent`'s side: he gives the good named like himself and gets
the other, keeping nothing else. Refusing leaves him his own good. -/
def barterTrade (believes : Bool → Bool → Bool → Bool → Prop)
    (wanted : Bool → Bool → Bool) (agent : Bool) :
    Trade (barterFrame believes wanted) where
  agent := agent
  time := false
  gives := agent
  gets := !agent
  kept := ∅
  refusal := (barterFrame believes wanted).ServedBy agent false (insert agent ∅)

theorem barter_voluntary (believes : Bool → Bool → Bool → Bool → Prop)
    (wanted : Bool → Bool → Bool) (agent : Bool) :
    (barterTrade believes wanted agent).Voluntary := rfl

theorem barter_asymmetric (believes : Bool → Bool → Bool → Bool → Prop)
    (wanted : Bool → Bool → Bool) (agent : Bool) (time : Bool) :
    AsymmetricPreference (barterFrame believes wanted) agent time :=
  ⟨fun _ _ hXY hYX => hYX.2 hXY.1⟩

theorem barter_separable (believes : Bool → Bool → Bool → Bool → Prop)
    (wanted : Bool → Bool → Bool) (agent : Bool) :
    (barterTrade believes wanted agent).SeparableFromRest := by
  intro X Y _ _ h
  refine ⟨?_, fun hY => h.2 (Or.inl hY)⟩
  rcases h.1 with hX | hrest
  · exact hX
  · exact absurd (Or.inr hrest) h.2

theorem barter_kept_other (believes : Bool → Bool → Bool → Bool → Prop)
    (wanted : Bool → Bool → Bool) (agent : Bool) :
    (barterTrade believes wanted agent).KeptServesOtherEnds := by
  have hempty : (barterFrame believes wanted).ServedBy agent false ∅ = ∅ := by
    ext want
    simp [ActionFrame.ServedBy]
  constructor
  · show Disjoint _ ((barterFrame believes wanted).ServedBy agent false ∅)
    rw [hempty]
    exact Set.disjoint_empty _
  · show Disjoint _ ((barterFrame believes wanted).ServedBy agent false ∅)
    rw [hempty]
    exact Set.disjoint_empty _

/-- **Demonstrated preference holds of both trades** in the honest,
steady frame: each wants the end the good he gets serves. -/
theorem barterOk_demonstrated (agent : Bool) :
    DemonstratedPreference (barterTrade honestBeliefs steadyWants agent) := by
  refine ⟨?_⟩
  cases agent <;>
    simp [barterTrade, Trade.after, ActionFrame.ServedBy, honestBeliefs, steadyWants]

/-- The exchange: A's vase for B's typewriter. -/
def barterExchange : Exchange barterOk where
  first := barterTrade honestBeliefs steadyWants false
  second := barterTrade honestBeliefs steadyWants true
  swap_gives := rfl
  swap_gets := rfl

/-- **Non-vacuity: the exchange is handed to `reverse_valuations`.** -/
theorem barter_reverse_valuations_applies :
    barterOk.Prefers false false (barterOk.ServedBy false false {true})
        (barterOk.ServedBy false false {false}) ∧
      barterOk.Prefers true false (barterOk.ServedBy true false {false})
        (barterOk.ServedBy true false {true}) :=
  MutualBenefit.reverse_valuations barterExchange
    (barterOk_demonstrated false) (barterOk_demonstrated true)
    (barter_voluntary _ _ false) (barter_voluntary _ _ true)
    (barter_separable _ _ false) (barter_separable _ _ true)
    (barter_kept_other _ _ false) (barter_kept_other _ _ true)

/-- **Non-vacuity: the later-judged theorem applies** where beliefs and
ranking both hold. -/
theorem barter_better_off_later_applies (agent : Bool) :
    barterOk.Prefers agent true
      ((barterTrade honestBeliefs steadyWants agent).after true)
      ((barterTrade honestBeliefs steadyWants agent).before true) :=
  MutualBenefit.better_off_judged_later
    (barterTrade honestBeliefs steadyWants agent) true
    (barterOk_demonstrated agent) (barter_voluntary _ _ agent)
    (fun _ _ _ => Iff.rfl) (fun h => h)

/-- **Without the beliefs condition, the later-judged statement fails.** A
trades freely. He ranks as before. But he learns the typewriter serves
nothing. So he is not better off by his later lights. -/
theorem later_without_beliefs_fails : ¬ MutualBenefit.BetterOffLaterWithoutBeliefs := by
  intro promise
  have demonstrated :
      DemonstratedPreference (barterTrade (barterFraud.Believes) steadyWants false) := by
    refine ⟨?_⟩
    simp [barterTrade, Trade.after, ActionFrame.ServedBy, steadyWants]
  have h := promise barterFraud (barterTrade (barterFraud.Believes) steadyWants false) true
    demonstrated (barter_voluntary _ _ false) (fun h => h)
  simp [barterTrade, Trade.after, Trade.before, ActionFrame.ServedBy, steadyWants] at h

/-- **Without the ranking condition, the later-judged statement fails.** A
trades freely. He believes as before. But he now wants decoration. So
he is not better off by his later lights. -/
theorem later_without_ranking_fails : ¬ MutualBenefit.BetterOffLaterWithoutRanking := by
  intro promise
  have h := promise barterRegret (barterTrade honestBeliefs _ false) true
    (by
      refine ⟨?_⟩
      simp [barterTrade, Trade.after, ActionFrame.ServedBy, honestBeliefs])
    (barter_voluntary _ _ false) (fun _ _ _ => Iff.rfl)
  simp [barterTrade, Trade.after, Trade.before, ActionFrame.ServedBy, honestBeliefs] at h

#print axioms barter_reverse_valuations_applies
#print axioms barter_better_off_later_applies
#print axioms later_without_beliefs_fails
#print axioms later_without_ranking_fails

/-! ## Time preference — a frame where it holds, and one where nobody prefers

`Waiting`: ends are a kind of satisfaction together with a date;
same kind, same satisfaction; of two ends of one kind, the earlier is
preferred, and nothing else is. `Patient`: the same dated ends, and no
preference at all. -/

/-- One man; ends are (kind, date); times are dates. The earlier of
two same-kind single ends is preferred; no other bundle is ranked. -/
abbrev Waiting : DatedFrame where
  Agent := Unit
  End := ℕ × ℕ
  Means := Unit
  Time := ℕ
  Believes := fun _ _ _ _ => True
  Prefers := fun _ _ X Y =>
    ∃ a b, X = {a} ∧ Y = {b} ∧ a.1 = b.1 ∧ a.2 < b.2
  Before := fun t t' => t < t'
  attained := Prod.snd
  SameSatisfaction := fun _ a b => a.1 = b.1

theorem waiting_asymmetric (agent : Waiting.Agent) (time : Waiting.Time) :
    AsymmetricPreference Waiting.toActionFrame agent time := by
  refine ⟨?_⟩
  rintro X Y ⟨a, b, rfl, rfl, _, hab⟩ ⟨c, d, hc, hd, _, hcd⟩
  rw [Set.singleton_eq_singleton_iff] at hc hd
  subst hc hd
  exact absurd (lt_trans hab hcd) (lt_irrefl _)

theorem waiting_timePreference (now : ℕ) : TimePreference Waiting () now :=
  ⟨fun soon late same sooner _ => ⟨soon, late, rfl, rfl, same, sooner⟩⟩

/-- **Non-vacuity: the durability corollary applies.** -/
theorem waiting_less_durable_applies :
    Waiting.Prefers () 0 (insert ((0 : ℕ), (1 : ℕ)) ∅) (insert (0, 2) ∅) :=
  TimePreference.less_durable_preferred ∅ (0, 1) (0, 2)
    (waiting_timePreference 0) rfl (by decide) (by decide)
    (fun h => by
      have e : ∀ a : ℕ × ℕ, insert a (∅ : Set (ℕ × ℕ)) = {a} := fun a => by
        ext; simp
      rw [e, e]
      exact h)

/-- One satisfaction on offer at every date. -/
def waitingMorrows : Morrows Waiting () where
  date := fun n => n
  offer := fun n => (0, n)
  dated := fun _ => rfl
  successive := fun n => Nat.lt_succ_self n

/-- Consuming at date `n`, forgoing the morrow. -/
def waitingConsume (n : ℕ) : Action Waiting.toActionFrame where
  agent := ()
  time := n
  chosen := (0, n)
  means := ()
  forgone := {(0, n + 1)}
  forgone_nonempty := Set.singleton_nonempty _
  chosen_not_forgone := by simp
  belief := trivial

theorem waiting_demonstrated (n : ℕ) :
    DemonstratedTimePreference (waitingConsume n) :=
  ⟨fun _ _ same sooner => ⟨_, _, rfl, rfl, same, sooner⟩⟩

/-- **Non-vacuity: consuming reveals, in `Waiting`.** -/
theorem waiting_consumption_reveals_applies (n : ℕ) :
    Waiting.PrefersEnd () n (0, n) (0, n + 1) :=
  TimePreference.consumption_reveals waitingMorrows n (waitingConsume n)
    ⟨rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (waiting_demonstrated n)

/-- The same dated ends, and no preference at all. -/
abbrev Patient : DatedFrame where
  Agent := Unit
  End := ℕ × ℕ
  Means := Unit
  Time := ℕ
  Believes := fun _ _ _ _ => True
  Prefers := fun _ _ _ _ => False
  Before := fun t t' => t < t'
  attained := Prod.snd
  SameSatisfaction := fun _ a b => a.1 = b.1

/-- **Non-vacuity: the regress applies in `Waiting`.** There the agent
prefers the sooner at every date. So no absence of preference has
anything to carry. -/
theorem waiting_regress_applies (n : ℕ) :
    ¬ ¬ Waiting.PrefersEnd () 0 (0, 0) (0, 1) :=
  TimePreference.regress waitingMorrows n (waitingConsume n)
    ⟨rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (waiting_demonstrated n)
    (fun k h => absurd ⟨_, _, rfl, rfl, rfl, Nat.lt_succ_self k⟩ h)

/-- **On the valuation reading, the strict half of time preference is
not free.** It fails where nothing is ranked. There every pair counts as
the same satisfaction by valuation. And the sooner is not preferred. -/
theorem valuation_reading_strict_half_fails :
    ¬ ∀ (praxis : DatedFrame) (agent : praxis.Agent) (now : praxis.Time)
        (soon late : praxis.End),
      TimePreference.SameByValuation praxis agent now soon late →
      praxis.Before (praxis.attained soon) (praxis.attained late) →
      ¬ praxis.Before (praxis.attained soon) now →
      praxis.PrefersEnd agent now soon late := by
  intro promise
  exact promise Patient () 0 (0, 1) (0, 2) id (by decide) (by decide)

#print axioms waiting_less_durable_applies
#print axioms waiting_consumption_reveals_applies
#print axioms waiting_regress_applies
#print axioms valuation_reading_strict_half_fails

/-!
## The regression theorem: a medium with a past

One frame
in which the claim `AppraisalFromPast` and every condition the regression
theorems carry hold together, AND a medium exists — so the regress
theorems are not true for want of a case. Nothing depends on it.

One agent, one good, two ends: `false` (eat it) and `true` (pass it on).
On day 0 the good is believed to serve only eating; from day 1 on, also
passing on. The good is exchanged every day (against itself: `Trade`
does not require two goods).
-/

namespace Barter



/-- The toy frame. -/
def frame : MediumFrame where
  Agent := Unit
  End := Bool
  Means := Unit
  Time := ℕ
  Believes := fun _ t _ e => e = false ∨ (0 < t ∧ e = true)
  Prefers := fun _ _ _ _ => False
  Onward := fun _ e => e = true

theorem twoDemands : TwoPartialDemands frame () :=
  ⟨fun e => by
    cases e with
    | false => exact Or.inr Bool.false_ne_true
    | true => exact Or.inl rfl⟩

/-- The day's exchange. -/
def dayExchange (k : ℕ) : Exchange frame.toActionFrame where
  first := ⟨(), k, (), (), ∅, ∅⟩
  second := ⟨(), k, (), (), ∅, ∅⟩
  swap_gives := rfl
  swap_gets := rfl

/-- The toy record: one exchange each day. -/
def history : History frame where
  date := fun k => k
  exchanges := fun k => {dayExchange k}

theorem appraisal : AppraisalFromPast history () :=
  ⟨fun _ _ _ => ⟨0, Nat.zero_le _, dayExchange 0, rfl, Or.inl rfl⟩⟩

theorem begins : history.BeginsBeforeMedium () := by
  rintro ⟨_, e, honward, hfalse | ⟨hpos, _⟩⟩
  · have h1 : e = true := honward
    rw [h1] at hfalse
    exact Bool.noConfusion hfalse
  · exact Nat.lt_irrefl 0 hpos

theorem purposive (n : ℕ) : history.AcquisitionsPurposive () n :=
  fun _ _ _ _ _ => ⟨false, Or.inl rfl⟩

theorem medium : history.MediumAt 1 () :=
  ⟨(), true, rfl, Or.inr ⟨Nat.zero_lt_one, rfl⟩⟩

theorem barter : history.FormedInBarter () 1 := by
  intro k hk _ _ _ hmedium
  have hk0 : k = 0 := Nat.lt_one_iff.mp hk
  rw [hk0] at hmedium
  exact begins hmedium

theorem narrowReading :
    history.OtherEmploymentsNarrow (fun e => e = false) () 1 := by
  intro _ _ _ _ _ e hnot hbelief
  rcases hbelief with hfalse | ⟨_, htrue⟩
  · exact hfalse
  · exact absurd htrue hnot

/-- **Non-vacuity** — the claim and every condition of the barter and
narrow theorems hold, together with a medium on day 1, and the positive
theorem finds the direct acquisition. -/
theorem toy_nonvacuous :
    ∃ k < 1, ∃ agent g, history.AcquiredAgainst k () agent g ∧
      frame.ValuesDirectly agent (history.date k) () ∧ ¬ history.MediumAt k g :=
  Regression.barter_origin history () 1 twoDemands appraisal begins (purposive 1) barter medium

theorem toy_narrow : ∃ k < 1, history.NarrowAcquisitionAt (fun e => e = false) k () :=
  Regression.narrow_acquisition_before history (fun e => e = false) () 1 twoDemands appraisal begins
    (purposive 1) narrowReading medium



#print axioms toy_nonvacuous
#print axioms toy_narrow

end Barter

/-!
## Pure interest: a lender at a positive rate

One frame in which the claim `MoreMoneyPreferredWhenSpent`, asymmetry,
time preference, and every condition `PureInterest.struck_rate_positive`
carries hold together, and the theorem is handed the toy loan — so the
interest theorems are not true for want of a case. Nothing depends on
it.

A lender has a use for an ounce now. He lends one ounce for a promise of
two, repaid at date 1. Ends are (kind, date); one end is preferred to
another by a score that ranks kind first and date second, so same-kind
ends are the same satisfaction and the sooner is preferred. The ranking
does not change with the date, so he ranks at the spending as he ranks
now. The promises pay in full: the promised money is the promises' own
stock, counted alike.
-/

namespace Loan

/-- The goods: a present ounce, two promises of an ounce at date 1, and
two goods standing for whole holdings in the loan — the purse (one
ounce) and the bond (a promise of two). -/
inductive Good
  | ounce | promiseA | promiseB | purse | bond
  deriving DecidableEq

/-- Kind first, date second: lower is better. -/
def score (e : ℕ × ℕ) : ℕ := e.1 * 10 + e.2

/-- An ounce's worth now. -/
def soon : ℕ × ℕ := (1, 0)
/-- An ounce's worth at date 1: the same satisfaction, later. -/
def late : ℕ × ℕ := (1, 1)
/-- Two ounces' worth at date 1. -/
def plenty : ℕ × ℕ := (0, 1)

/-- What the lender believes each good serves. -/
def beliefs : Good → ℕ × ℕ → Prop
  | .ounce, e => e = soon
  | .promiseA, e => e = late ∨ e = plenty
  | .promiseB, e => e = late ∨ e = plenty
  | .purse, e => e = soon
  | .bond, e => e = plenty

/-- The toy frame. -/
abbrev frame : MoneyFrame where
  Agent := Unit
  End := ℕ × ℕ
  Means := Good
  Time := ℕ
  Believes := fun _ _ g e => beliefs g e
  Prefers := fun _ _ X Y => ∃ x ∈ X, ∀ y ∈ Y, score x < score y
  Before := fun t t' => t < t'
  attained := Prod.snd
  SameSatisfaction := fun _ a b => a.1 = b.1
  Money := fun _ => True
  FreeToHold := fun _ _ _ => True

theorem timePreference (now : ℕ) : TimePreference frame.toDatedFrame () now :=
  ⟨fun soon late same sooner _ => ⟨soon, rfl, fun y hy => by
    have hy : y = late := hy
    subst hy
    show soon.1 * 10 + soon.2 < y.1 * 10 + y.2
    have same : soon.1 = y.1 := same
    have sooner : soon.2 < y.2 := sooner
    rw [same]
    exact Nat.add_lt_add_left sooner _⟩⟩

theorem asymmetric (now : ℕ) : AsymmetricPreference frame.toActionFrame () now :=
  ⟨fun _ _ ⟨x, hx, hxY⟩ ⟨y, hy, hyX⟩ => Nat.lt_asymm (hxY y hy) (hyX x hx)⟩

theorem transitive (now : ℕ) (X Y Z : Set (ℕ × ℕ)) :
    frame.TransitiveOn () now X Y Z :=
  fun ⟨x, hx, hxY⟩ ⟨y, hy, hyZ⟩ =>
    ⟨x, hx, fun z hz => Nat.lt_trans (hxY y hy) (hyZ z hz)⟩

/-- What a promise of `n` ounces at date 1 buys. -/
def futureBuys : ℕ → Finset (ℕ × ℕ)
  | 0 => ∅
  | 1 => {late}
  | _ => {plenty}

/-- Promises of an ounce at date 1, weighed at date 0. -/
def futureStock : Stock frame.toActionFrame () 0 where
  units := {.promiseA, .promiseB}
  serves := {late, plenty}
  unitsAlike := fun unit h e => by
    rcases Finset.mem_insert.1 h with rfl | h
    · exact Iff.rfl
    · rw [Finset.mem_singleton.1 h]; exact Iff.rfl

/-- What he would buy with promises: by count only. -/
def futurePlan : AllocationPlan futureStock where
  wouldServe s := futureBuys s.card
  servesOnlyWhatItCan s want h := by
    show want ∈ ({late, plenty} : Set (ℕ × ℕ))
    unfold futureBuys at h
    split at h
    · exact absurd h (Finset.notMem_empty _)
    · exact Or.inl (Finset.mem_singleton.1 h)
    · exact Or.inr (Finset.mem_singleton.1 h)

theorem homogeneous : futurePlan.Homogeneous :=
  fun fewer _ more _ same => by
    show futureBuys fewer.card = futureBuys more.card
    rw [same]

theorem futureBuys_more (a b : ℕ) (h : a < b) (h2 : b ≤ 2) :
    ∃ x ∈ (↑(futureBuys b) : Set (ℕ × ℕ)),
      ∀ y ∈ (↑(futureBuys a) : Set (ℕ × ℕ)), score x < score y := by
  match a, b, h, h2 with
  | 0, 1, _, _ => exact ⟨late, Finset.mem_singleton_self _, fun _ hy =>
      absurd hy (Finset.notMem_empty _)⟩
  | 0, 2, _, _ => exact ⟨plenty, Finset.mem_singleton_self _, fun _ hy =>
      absurd hy (Finset.notMem_empty _)⟩
  | 1, 2, _, _ => exact ⟨plenty, Finset.mem_singleton_self _, fun y hy => by
      have hy : y = late := Finset.mem_singleton.1 hy
      subst hy
      exact Nat.lt_of_sub_eq_succ rfl⟩
  | 0, 0, h, _ => exact absurd h (Nat.lt_irrefl _)
  | 1, 0, h, _ => exact absurd h (Nat.not_lt_zero _)
  | 1, 1, h, _ => exact absurd h (Nat.lt_irrefl _)
  | a + 2, _, h, h2 => exact absurd (Nat.lt_of_lt_of_le h h2) (by omega)
  | _, b + 3, _, h2 => exact absurd h2 (by omega)

/-- **The claim holds**, at the spending date 1. -/
theorem moreMoney : MoreMoneyPreferredWhenSpent (praxis := frame) futurePlan 1 :=
  ⟨fun fewer more proper inStock _ _ _ _ =>
    futureBuys_more fewer.card more.card (Finset.card_lt_card proper)
      (Finset.card_le_card inStock)⟩

/-- One promise buys more than no promises. -/
theorem buysMore :
    BuysMoreThanItsParts (praxis := frame) futurePlan {Good.promiseA} := by
  intro part proper same
  have small : part.card = 0 := by
    have := Finset.card_lt_card proper
    simp at this
    simpa using this
  change futureBuys ({Good.promiseA} : Finset Good).card = futureBuys part.card at same
  rw [small] at same
  exact Finset.singleton_ne_empty _ same

/-- The present ounce, at date 0. -/
def presentStock : Stock frame.toActionFrame () 0 where
  units := {.ounce}
  serves := {soon}
  unitsAlike := fun unit h e => by
    rw [Finset.mem_singleton.1 h]
    exact Iff.rfl

/-- What he would buy with present ounces. -/
def presentPlan : AllocationPlan presentStock where
  wouldServe s := if s.card = 0 then ∅ else {soon}
  servesOnlyWhatItCan s want h := by
    show want ∈ ({soon} : Set (ℕ × ℕ))
    split at h
    · exact absurd h (Finset.notMem_empty _)
    · exact Finset.mem_singleton.1 h

/-- The lender's side: he gives the purse (one ounce), gets the bond
(a promise of two ounces), keeps nothing else. -/
def lend : Trade frame.toActionFrame :=
  ⟨(), 0, .purse, .bond, ∅, {soon}⟩

/-- The borrower's side; one person plays both (`Exchange` does not
ask for two). -/
def borrow : Trade frame.toActionFrame :=
  ⟨(), 0, .bond, .purse, ∅, ∅⟩

def loan : Exchange frame.toActionFrame :=
  ⟨lend, borrow, rfl, rfl⟩

theorem servedBy_one (g : Good) :
    frame.ServedBy () 0 (insert g ∅) = {e | beliefs g e} := by
  ext e
  constructor
  · rintro ⟨g', hg', he⟩
    rcases hg' with rfl | hg'
    · exact he
    · exact absurd hg' (Set.notMem_empty _)
  · intro he
    exact ⟨g, Set.mem_insert _ _, he⟩

theorem lend_before : lend.before 0 = {soon} := by
  rw [Trade.before, show lend.kept = ∅ from rfl, servedBy_one]
  ext e; exact Iff.rfl

theorem lend_after : lend.after 0 = {plenty} := by
  rw [Trade.after, show lend.kept = ∅ from rfl, servedBy_one]
  ext e; exact Iff.rfl

theorem lend_voluntary : lend.Voluntary := lend_before.symm

theorem lend_before_planned : lend.BeforeCountsAsPlanned presentPlan {.ounce} := by
  show lend.before 0 = _
  rw [lend_before]
  exact (coe_single _).symm

theorem lend_after_planned :
    lend.AfterCountsAsPlanned futurePlan {.promiseA, .promiseB} := by
  show lend.after 0 = _
  rw [lend_after]
  exact (coe_single _).symm

/-- **Non-vacuity: every rate struck is positive, applied.** The lender
lends one ounce and is repaid two. Every claim of S5 holds. So does
every condition. The promised money is its own stock. -/
theorem struck_rate_positive_applies :
    ({.ounce} : Finset Good).card < ({.promiseA, .promiseB} : Finset Good).card :=
  PureInterest.struck_rate_positive loan presentPlan futurePlan futurePlan
    {Good.ounce} {Good.promiseA} {Good.promiseA} {Good.promiseA, Good.promiseB}
    soon late 1
    (timePreference 0)
    ⟨rfl, rfl, rfl⟩
    rfl
    ⟨Nat.zero_lt_one, Nat.lt_irrefl 0⟩
    rfl
    (fun _ h => by rw [Finset.mem_singleton.1 h]; exact Finset.mem_insert_self _ _)
    (fun _ h => h)
    homogeneous
    moreMoney
    (fun h => h)
    buysMore
    (fun _ _ => trivial)
    (fun _ _ => trivial)
    (transitive 0 _ _ _)
    (asymmetric 0)
    lend_voluntary
    lend_before_planned
    lend_after_planned
    ⟨by
      show frame.Prefers () 0 (lend.after 0) {soon}
      rw [lend_after]
      exact ⟨plenty, rfl, fun y hy => by
        have hy : y = soon := hy
        subst hy
        exact Nat.lt_of_sub_eq_succ rfl⟩⟩

#print axioms struck_rate_positive_applies

end Loan

/-!
## Pure interest: each half of the certainty split failing alone

The promise pays (`PromisePays`) and the money buys as much later
(`SamePurchasingPower`, between the present sum and the promised
money) are separate conditions. Here each fails while the other holds.
In both cases the promise's plan is the same, so a single condition
asserted between the present sum and the promise cannot tell them apart.

One agent, at date 0, holds three one-unit stocks: an ounce of cash, a
promise of an ounce at date 1, and the ounce it promises, as he
would spend it were it in hand at date 1. Ends are (kind, date); kind 1
is an ounce's worth, kind 2 is less. Same kind, same satisfaction.
-/

namespace CertaintySplit

/-- The goods: an ounce now, a promise of an ounce at date 1, and the
ounce it promises. -/
inductive Good
  | cash | promise | promised
  deriving DecidableEq

/-- Kind first, date second: lower is better. -/
def score (e : ℕ × ℕ) : ℕ := e.1 * 10 + e.2

/-- An ounce's worth now. -/
def soon : ℕ × ℕ := (1, 0)
/-- An ounce's worth at date 1: the same satisfaction, later. -/
def late : ℕ × ℕ := (1, 1)
/-- Less than an ounce's worth, at date 1. -/
def worse : ℕ × ℕ := (2, 1)

/-- The frame, given what the agent believes each good serves. -/
abbrev frame (believes : Good → ℕ × ℕ → Prop) : MoneyFrame where
  Agent := Unit
  End := ℕ × ℕ
  Means := Good
  Time := ℕ
  Believes := fun _ _ g e => believes g e
  Prefers := fun _ _ X Y => ∃ x ∈ X, ∀ y ∈ Y, score x < score y
  Before := fun t t' => t < t'
  attained := Prod.snd
  SameSatisfaction := fun _ a b => a.1 = b.1
  Money := fun _ => True
  FreeToHold := fun _ _ _ => True

/-- Cash buys `soon`; the promise and the promised ounce buy what the
agent believes they buy. -/
def beliefs (promiseBuys promisedBuys : ℕ × ℕ) : Good → ℕ × ℕ → Prop
  | .cash, e => e = soon
  | .promise, e => e = promiseBuys
  | .promised, e => e = promisedBuys

/-- What some units of a one-unit stock buy. -/
def buys (worth : ℕ × ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  if n = 0 then ∅ else {worth}

/-- A one-unit stock of `g`, weighed at date 0. -/
def stock (promiseBuys promisedBuys : ℕ × ℕ) (g : Good) (worth : ℕ × ℕ)
    (alike : ∀ e, beliefs promiseBuys promisedBuys g e ↔ e ∈ ({worth} : Set (ℕ × ℕ))) :
    Stock (frame (beliefs promiseBuys promisedBuys)).toActionFrame () 0 where
  units := {g}
  serves := {worth}
  unitsAlike unit h e := by
    obtain rfl := Finset.mem_singleton.1 h
    exact alike e

/-- His plan for it: by count only. -/
def plan (promiseBuys promisedBuys : ℕ × ℕ) (g : Good) (worth : ℕ × ℕ) alike :
    AllocationPlan (stock promiseBuys promisedBuys g worth alike) where
  wouldServe s := buys worth s.card
  servesOnlyWhatItCan s want h := by
    show want ∈ ({worth} : Set (ℕ × ℕ))
    unfold buys at h
    split at h
    · exact absurd h (Finset.notMem_empty _)
    · exact Finset.mem_singleton.1 h

theorem plan_single (promiseBuys promisedBuys : ℕ × ℕ) (g g' : Good)
    (worth : ℕ × ℕ) alike :
    (plan promiseBuys promisedBuys g worth alike).wouldServe {g'} = {worth} := by
  show buys worth ({g'} : Finset Good).card = {worth}
  rw [Finset.card_singleton]
  rfl

theorem late_ne_worse : late ≠ worse := fun h => by
  have : (1 : ℕ) = 2 := congrArg Prod.fst h
  omega

/-- Same purchasing power fails between cash buying `soon` and any
good buying `worse`, whatever ends it is asked of. -/
theorem not_same_of_worse (promiseBuys promisedBuys : ℕ × ℕ) (g : Good)
    cashAlike otherAlike (s l : ℕ × ℕ) :
    ¬ SamePurchasingPower (praxis := frame (beliefs promiseBuys promisedBuys))
      (plan promiseBuys promisedBuys Good.cash soon cashAlike)
      (plan promiseBuys promisedBuys g worse otherAlike)
      {Good.cash} {g} s l := by
  rintro ⟨buysSoon, buysLate, same⟩
  rw [plan_single] at buysSoon buysLate
  have hs : soon = s := Finset.singleton_injective buysSoon
  have hl : worse = l := Finset.singleton_injective buysLate
  have same : s.1 = l.1 := same
  rw [← hs, ← hl] at same
  have : (1 : ℕ) = 2 := same
  omega

/-- Default risk: he doubts the promise; the promised ounce buys an
ounce's worth. -/
abbrev doubt := beliefs worse late

def doubtCash := plan worse late .cash soon (fun _ => Iff.rfl)
def doubtPromise := plan worse late .promise worse (fun _ => Iff.rfl)
def doubtPromised := plan worse late .promised late (fun _ => Iff.rfl)

/-- **Default risk: purchasing power holds, the promise does not pay.** -/
theorem doubt_power_but_not_pays :
    SamePurchasingPower (praxis := frame doubt) doubtCash doubtPromised
      {.cash} {.promised} soon late ∧
    ¬ PromisePays (praxis := frame doubt) doubtPromise doubtPromised
      {.promise} {.promised} := by
  refine ⟨⟨plan_single _ _ _ _ _ _, plan_single _ _ _ _ _ _, rfl⟩, ?_⟩
  intro counts
  have counts : ({worse} : Finset (ℕ × ℕ)) = {late} :=
    (plan_single worse late .promise .promise worse _).symm.trans
      (counts.trans (plan_single worse late .promised .promised late _))
  exact late_ne_worse (Finset.singleton_injective counts).symm

/-- Inflation: he is sure of the promise; the promised ounce buys less. -/
abbrev inflation := beliefs worse worse

def inflationCash := plan worse worse .cash soon (fun _ => Iff.rfl)
def inflationPromise := plan worse worse .promise worse (fun _ => Iff.rfl)
def inflationPromised := plan worse worse .promised worse (fun _ => Iff.rfl)

/-- **Inflation: the promise pays, purchasing power does not hold.** -/
theorem inflation_pays_but_not_power (s l : ℕ × ℕ) :
    PromisePays (praxis := frame inflation) inflationPromise inflationPromised
      {.promise} {.promised} ∧
    ¬ SamePurchasingPower (praxis := frame inflation) inflationCash
      inflationPromised {.cash} {.promised} s l :=
  ⟨(plan_single _ _ _ _ _ _).trans (plan_single _ _ _ _ _ _).symm,
    not_same_of_worse worse worse .promised _ _ s l⟩

/-- **The merged condition fails in both cases alike.** Same
purchasing power (`SamePurchasingPower`) is asserted between the cash
and the promise. It fails under
default risk. It fails under inflation. The promise's plan is the same
in both. -/
theorem merged_fails_in_both (s l : ℕ × ℕ) :
    ¬ SamePurchasingPower (praxis := frame doubt) doubtCash doubtPromise
      {.cash} {.promise} s l ∧
    ¬ SamePurchasingPower (praxis := frame inflation) inflationCash
      inflationPromise {.cash} {.promise} s l :=
  ⟨not_same_of_worse worse late .promise _ _ s l,
    not_same_of_worse worse worse .promise _ _ s l⟩

#print axioms doubt_power_but_not_pays
#print axioms inflation_pays_but_not_power
#print axioms merged_fails_in_both

end CertaintySplit

/-!
## Pure interest: a man whose valuations change

One ounce of cash, which he believes would buy an impulse at date 1. At
date 0 he prefers not having the impulse to having it; at date 1, the
impulse to nothing. Asymmetry holds at every date, the claim dated at
the spending holds of him, and both the condition that he ranks the
purchase now as he will then and the undated reading of the claim fail.
The preference relation is written by hand for the case.
-/

namespace Impulse

/-- The good: one ounce of cash. -/
inductive Good
  | ounce
  deriving DecidableEq

/-- What an ounce of cash at hand would buy, on impulse, at date 1. -/
def impulse : ℕ × ℕ := (3, 1)

/-- At date 0 he prefers not having the impulse to having it; at date
1, the impulse to nothing. No other preference. -/
def prefers (t : ℕ) (X Y : Set (ℕ × ℕ)) : Prop :=
  (t = 0 ∧ X = ∅ ∧ Y = {impulse}) ∨ (t = 1 ∧ X = {impulse} ∧ Y = ∅)

/-- The frame. -/
abbrev frame : MoneyFrame where
  Agent := Unit
  End := ℕ × ℕ
  Means := Good
  Time := ℕ
  Believes := fun _ _ _ e => e = impulse
  Prefers := fun _ t X Y => prefers t X Y
  Before := fun t t' => t < t'
  attained := Prod.snd
  SameSatisfaction := fun _ a b => a.1 = b.1
  Money := fun _ => True
  FreeToHold := fun _ _ _ => True

/-- His cash at hand, at date 0. -/
def cash : Stock frame.toActionFrame () 0 where
  units := {.ounce}
  serves := {impulse}
  unitsAlike := fun _ _ _ => Iff.rfl

/-- What he would buy with cash: the impulse, with any. -/
def plan : AllocationPlan cash where
  wouldServe s := if s.card = 0 then ∅ else {impulse}
  servesOnlyWhatItCan s want h := by
    show want ∈ ({impulse} : Set (ℕ × ℕ))
    split at h
    · exact absurd h (Finset.notMem_empty _)
    · exact Finset.mem_singleton.1 h

theorem impulse_ne_empty : ({impulse} : Set (ℕ × ℕ)) ≠ ∅ := fun h => by
  have mem : impulse ∈ ({impulse} : Set (ℕ × ℕ)) := rfl
  rw [h] at mem
  exact mem

theorem asymmetric (t : ℕ) : AsymmetricPreference frame.toActionFrame () t :=
  ⟨fun X Y forward backward => by
    rcases forward with ⟨t0, _, hY⟩ | ⟨t1, hX, _⟩ <;>
      rcases backward with ⟨t0', hY', _⟩ | ⟨t1', _, hX'⟩
    · rw [hY] at hY'
      exact impulse_ne_empty hY'
    · rw [t0] at t1'
      exact Nat.zero_ne_one t1'
    · rw [t1] at t0'
      exact Nat.zero_ne_one t0'.symm
    · rw [hX] at hX'
      exact impulse_ne_empty hX'⟩

/-- The only strict part of his cash is no cash. -/
theorem part_of_cash (fewer more : Finset Good) (part : fewer ⊂ more)
    (inStock : more ⊆ cash.units) : fewer = ∅ ∧ more = {.ounce} := by
  have more_le : more.card ≤ 1 := Finset.card_le_card inStock
  have fewer_lt : fewer.card < more.card := Finset.card_lt_card part
  have fewer_zero : fewer.card = 0 := by omega
  have more_one : more.card = 1 := by omega
  refine ⟨Finset.card_eq_zero.1 fewer_zero, ?_⟩
  exact Finset.eq_of_subset_of_card_le inStock (by rw [more_one]; rfl)

theorem coe_none : ((∅ : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) = ∅ :=
  Set.ext fun _ => ⟨fun h => absurd h (Finset.notMem_empty _), fun h => absurd h id⟩

theorem buys_empty : plan.wouldServe ∅ = ∅ := rfl

theorem buys_ounce : plan.wouldServe {.ounce} = {impulse} := rfl

/-- At date 1 he ranks what an ounce buys above what no cash buys. -/
theorem ranked_at_spending :
    frame.Prefers () 1 ↑(plan.wouldServe {.ounce}) ↑(plan.wouldServe ∅) := by
  rw [buys_empty, buys_ounce]
  exact Or.inr ⟨rfl, coe_single impulse, coe_none⟩

/-- At date 0 he does not. -/
theorem not_ranked_now :
    ¬ frame.Prefers () 0 ↑(plan.wouldServe {.ounce}) ↑(plan.wouldServe ∅) := by
  rw [buys_empty, buys_ounce]
  rintro (⟨_, hX, _⟩ | ⟨one, _, _⟩)
  · exact impulse_ne_empty (by rw [← coe_single]; exact hX)
  · exact Nat.zero_ne_one one

/-- **The claim, dated at the spending, holds of him.** -/
theorem whenSpent : MoreMoneyPreferredWhenSpent (praxis := frame) plan (1 : ℕ) :=
  ⟨fun fewer more part inStock _ _ _ _ => by
    obtain ⟨hf, hm⟩ := part_of_cash fewer more part inStock
    subst hf hm
    exact ranked_at_spending⟩

/-- **He is not ranked alike now**, for his ounce against no cash. -/
theorem not_rankedAlikeNow :
    ¬ RankedAlikeNowOf (praxis := frame) plan (1 : ℕ) {.ounce} ∅ :=
  fun alike => not_ranked_now (alike ranked_at_spending)

/-- **The undated reading of the claim is false of him**, though the
dated claim holds and asymmetry holds at every date. -/
theorem now_reading_fails :
    ¬ PureInterest.MoreMoneyPreferredNow (praxis := frame) plan := fun rule =>
  not_ranked_now (rule ∅ {.ounce}
    (Finset.ssubset_iff_subset_ne.2
      ⟨Finset.empty_subset _, (Finset.singleton_ne_empty _).symm⟩)
    (fun _ h => h) (fun _ _ => trivial) trivial trivial
    (by rw [buys_empty, buys_ounce]; exact Finset.singleton_ne_empty impulse))

#print axioms asymmetric
#print axioms whenSpent
#print axioms not_rankedAlikeNow
#print axioms now_reading_fails

end Impulse

/-!
## Pure interest: a saver who lends at a zero rate

A Christmas club saver. Two ounces of cash at hand he would spend now
on an impulse. The club takes the two ounces and pays two back at date
1, which buy what he saves for. He lends at a zero rate, voluntarily,
and time preference, asymmetry, the claim that more money is preferred
and demonstrated preference of the deposit all hold of him. Spent
sooner holds too. What fails is same purchasing power: his cash would
not buy the same satisfaction as the club's payment, so the zero-rate
theorem does not reach him. What the frame does not model is his
preferring less cash at hand to more: a sum of cash here buys one end
however large (for that, `Impulse` above).
-/

namespace ChristmasClub

/-- Two ounces now, two promises of an ounce at date 1, and two goods
standing for whole holdings in the deposit: the hoard (two ounces) and
the bond (the club's promise of two). -/
inductive Good
  | ounce | ounce' | promiseA | promiseB | hoard | bond
  deriving DecidableEq

/-- Kind first, date second: lower is better. -/
def score (e : ℕ × ℕ) : ℕ := e.1 * 10 + e.2

/-- An ounce's worth at date 1. -/
def late : ℕ × ℕ := (1, 1)
/-- Two ounces' worth at date 1: what he saves for. -/
def plenty : ℕ × ℕ := (0, 1)
/-- What cash at hand would buy now: an impulse, ranked below both. -/
def impulse : ℕ × ℕ := (3, 0)

/-- What he believes each good serves. -/
def beliefs : Good → ℕ × ℕ → Prop
  | .ounce, e => e = impulse
  | .ounce', e => e = impulse
  | .promiseA, e => e = late ∨ e = plenty
  | .promiseB, e => e = late ∨ e = plenty
  | .hoard, e => e = impulse
  | .bond, e => e = plenty

/-- The frame. -/
abbrev frame : MoneyFrame where
  Agent := Unit
  End := ℕ × ℕ
  Means := Good
  Time := ℕ
  Believes := fun _ _ g e => beliefs g e
  Prefers := fun _ _ X Y => ∃ x ∈ X, ∀ y ∈ Y, score x < score y
  Before := fun t t' => t < t'
  attained := Prod.snd
  SameSatisfaction := fun _ a b => a.1 = b.1
  Money := fun _ => True
  FreeToHold := fun _ _ _ => True

theorem timePreference (now : ℕ) : TimePreference frame.toDatedFrame () now :=
  ⟨fun soon late same sooner _ => ⟨soon, rfl, fun y hy => by
    have hy : y = late := hy
    subst hy
    show soon.1 * 10 + soon.2 < y.1 * 10 + y.2
    have same : soon.1 = y.1 := same
    have sooner : soon.2 < y.2 := sooner
    rw [same]
    exact Nat.add_lt_add_left sooner _⟩⟩

theorem asymmetric (now : ℕ) : AsymmetricPreference frame.toActionFrame () now :=
  ⟨fun _ _ ⟨x, hx, hxY⟩ ⟨y, hy, hyX⟩ => Nat.lt_asymm (hxY y hy) (hyX x hx)⟩

/-- What a promise of `n` ounces at date 1 buys. -/
def futureBuys : ℕ → Finset (ℕ × ℕ)
  | 0 => ∅
  | 1 => {late}
  | _ => {plenty}

/-- The club's promises, weighed at date 0. -/
def futureStock : Stock frame.toActionFrame () 0 where
  units := {.promiseA, .promiseB}
  serves := {late, plenty}
  unitsAlike := fun unit h e => by
    rcases Finset.mem_insert.1 h with rfl | h
    · exact Iff.rfl
    · rw [Finset.mem_singleton.1 h]; exact Iff.rfl

/-- What he would buy with promises: by count only. -/
def futurePlan : AllocationPlan futureStock where
  wouldServe s := futureBuys s.card
  servesOnlyWhatItCan s want h := by
    show want ∈ ({late, plenty} : Set (ℕ × ℕ))
    unfold futureBuys at h
    split at h
    · exact absurd h (Finset.notMem_empty _)
    · exact Or.inl (Finset.mem_singleton.1 h)
    · exact Or.inr (Finset.mem_singleton.1 h)

theorem futureBuys_more (a b : ℕ) (h : a < b) (h2 : b ≤ 2) :
    ∃ x ∈ (↑(futureBuys b) : Set (ℕ × ℕ)),
      ∀ y ∈ (↑(futureBuys a) : Set (ℕ × ℕ)), score x < score y := by
  match a, b, h, h2 with
  | 0, 1, _, _ => exact ⟨late, Finset.mem_singleton_self _, fun _ hy =>
      absurd hy (Finset.notMem_empty _)⟩
  | 0, 2, _, _ => exact ⟨plenty, Finset.mem_singleton_self _, fun _ hy =>
      absurd hy (Finset.notMem_empty _)⟩
  | 1, 2, _, _ => exact ⟨plenty, Finset.mem_singleton_self _, fun y hy => by
      have hy : y = late := Finset.mem_singleton.1 hy
      subst hy
      exact Nat.lt_of_sub_eq_succ rfl⟩
  | 0, 0, h, _ => exact absurd h (Nat.lt_irrefl _)
  | 1, 0, h, _ => exact absurd h (Nat.not_lt_zero _)
  | 1, 1, h, _ => exact absurd h (Nat.lt_irrefl _)
  | a + 2, _, h, h2 => exact absurd (Nat.lt_of_lt_of_le h h2) (by omega)
  | _, b + 3, _, h2 => exact absurd h2 (by omega)

theorem moreMoney : MoreMoneyPreferredWhenSpent (praxis := frame) futurePlan 1 :=
  ⟨fun fewer more proper inStock _ _ _ _ =>
    futureBuys_more fewer.card more.card (Finset.card_lt_card proper)
      (Finset.card_le_card inStock)⟩

/-- His two ounces at hand, at date 0. -/
def presentStock : Stock frame.toActionFrame () 0 where
  units := {.ounce, .ounce'}
  serves := {impulse}
  unitsAlike := fun unit h e => by
    rcases Finset.mem_insert.1 h with rfl | h
    · exact Iff.rfl
    · rw [Finset.mem_singleton.1 h]; exact Iff.rfl

/-- What he would buy with cash at hand: the impulse, with any. -/
def presentPlan : AllocationPlan presentStock where
  wouldServe s := if s.card = 0 then ∅ else {impulse}
  servesOnlyWhatItCan s want h := by
    show want ∈ ({impulse} : Set (ℕ × ℕ))
    split at h
    · exact absurd h (Finset.notMem_empty _)
    · exact Finset.mem_singleton.1 h

/-- The deposit: he gives the hoard, gets the bond, keeps nothing else;
refusing would have left him the cash, spent on the impulse. -/
def deposit : Trade frame.toActionFrame :=
  ⟨(), 0, .hoard, .bond, ∅, {impulse}⟩

theorem servedBy_one (g : Good) :
    frame.ServedBy () 0 (insert g ∅) = {e | beliefs g e} := by
  ext e
  constructor
  · rintro ⟨g', hg', he⟩
    rcases hg' with rfl | hg'
    · exact he
    · exact absurd hg' (Set.notMem_empty _)
  · intro he
    exact ⟨g, Set.mem_insert _ _, he⟩

theorem deposit_before : deposit.before 0 = {impulse} := by
  rw [Trade.before, show deposit.kept = ∅ from rfl, servedBy_one]
  ext e; exact Iff.rfl

theorem deposit_after : deposit.after 0 = {plenty} := by
  rw [Trade.after, show deposit.kept = ∅ from rfl, servedBy_one]
  ext e; exact Iff.rfl

/-- **A zero rate, struck voluntarily, with every claim holding.** Two
ounces lent, a promise of two got. -/
theorem zero_rate_with_every_claim :
    TimePreference frame.toDatedFrame () 0 ∧
    AsymmetricPreference frame.toActionFrame () 0 ∧
    MoreMoneyPreferredWhenSpent (praxis := frame) futurePlan 1 ∧
    DemonstratedPreference deposit ∧ deposit.Voluntary ∧
    ({.promiseA, .promiseB} : Finset Good).card = ({.ounce, .ounce'} : Finset Good).card :=
  ⟨timePreference 0, asymmetric 0, moreMoney,
    ⟨by
      show frame.Prefers () 0 (deposit.after 0) {impulse}
      rw [deposit_after]
      exact ⟨plenty, rfl, fun y hy => by
        have hy : y = impulse := hy
        subst hy
        exact Nat.lt_of_sub_eq_succ rfl⟩⟩,
    deposit_before.symm, rfl⟩

/-- **Spent sooner holds for him**: the cash would be spent now,
before the club pays. -/
theorem spent_sooner :
    SpentSooner (praxis := frame) (now := (0 : ℕ)) impulse plenty :=
  ⟨Nat.zero_lt_one, Nat.lt_irrefl 0⟩

/-- **Same purchasing power fails** between his cash and the club's
promise, whatever ends it is asked of. -/
theorem not_same_purchasing_power (s l : ℕ × ℕ) :
    ¬ SamePurchasingPower (praxis := frame) (now := (0 : ℕ)) presentPlan futurePlan
      {.ounce, .ounce'} {.promiseA, .promiseB} s l := by
  rintro ⟨buysSoon, buysLate, same⟩
  have hs : ({impulse} : Finset (ℕ × ℕ)) = {s} := buysSoon
  have hl : ({plenty} : Finset (ℕ × ℕ)) = {l} := buysLate
  rw [Finset.singleton_inj] at hs hl
  subst hs hl
  have : (3 : ℕ) = 0 := same
  exact Nat.succ_ne_zero 2 this

/-- **So the zero-rate theorem does not reach him.** Take any money the
club's promise pays in. Same purchasing power (`SamePurchasingPower`)
between his cash and that money fails. -/
theorem outside_zero_rate {promised : Stock frame.toActionFrame () 0}
    (promisedPlan : AllocationPlan promised) (money : Finset Good) (s l : ℕ × ℕ)
    (pays : PromisePays (praxis := frame) futurePlan promisedPlan
      ({Good.promiseA, Good.promiseB} : Finset Good) money) :
    ¬ SamePurchasingPower (praxis := frame) presentPlan promisedPlan
      ({Good.ounce, Good.ounce'} : Finset Good) money s l :=
  fun power => by
    have merged := PureInterest.samePurchasingPower_of_promisePays
      (praxis := frame) (agent := ()) (now := (0 : ℕ))
      presentPlan futurePlan promisedPlan ({Good.ounce, Good.ounce'} : Finset Good)
      ({Good.promiseA, Good.promiseB} : Finset Good) money s l power pays
    exact not_same_purchasing_power s l merged

#print axioms zero_rate_with_every_claim
#print axioms spent_sooner
#print axioms outside_zero_rate

end ChristmasClub

end Model
end Apodictic
