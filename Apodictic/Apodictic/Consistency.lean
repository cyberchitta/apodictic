import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Apodictic.MarginalUtility
import Apodictic.Mises

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

/-- Wants are decidable in this frame — the instance the theorems
take as `[DecidableEq praxis.End]`. -/
instance : DecidableEq Horses.End := inferInstanceAs (DecidableEq ℕ)

/-- **Interchangeability holds of the plan**: it depends on how many
horses there are, never on which. -/
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

/-- **The man's plan is swap-dominant** — the claim itself, proved
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
`marginal_utility_chain` is met at this frame. So the claim and
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
assumption that there is action". The frame above satisfies both
halves he calls incompatible, so the step is not valid as stated.

What his argument needs is `Mises.ActionRecurs` — that two distinct
actions occur — and nothing in "there is action" delivers it. His own
wording gestures past bare existence ("this case no longer implies the
general conditions presupposed in the category of action") without
saying what those conditions are. Naming them is the suppressed
premise of his derivation. -/
theorem existence_does_not_refute_second_horn :
    ¬ Mises.ExistenceRefutesSecondHorn := by
  intro claim
  exact claim Solitary solitary_actionOccurs solitary_atMostOneAction

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

/-- **Refuting the second horn does not deliver the ladder.** In a
frame where action is plural — Mises's dilemma won outright — the
ladder fails.

And it fails for a substantive reason, not a degenerate one.
Preference here is asymmetric (`plural_asymmetric`) and non-empty
(`plural_prefers_nontrivial`); what goes wrong is that the agent's
plan serves the less urgent end first, so the unit he adds brings in
something MORE urgent than what he was already serving. Mises's
sentence is false of this agent, and everything the dilemma
establishes is true of him.

So the step from "there are intermediate stages" to the law is not
valid on its own. What has to be added is that the plan respects the
ordering — which is `SwapDominant`, Rothbard's premise, arriving with
Rothbard's circular warrant. In Mises's own text the addition is a
single unargued sentence: "It is nothing else than the reverse of the
statement that what satisfies more is preferred to what gives smaller
satisfaction."

This does not show Mises's derivation is unsalvageable. It shows the
dilemma is not the premise, and that whatever is has not been stated
by him or by anyone since. -/
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

/-- **The two premise sets are not equivalent.** Rothbard's entails
Mises's bridge (`Contrast.rothbard_entails_servedInOrder`); this frame
shows the converse fails. So the Mises route, reconstructed as
generously as the vocabulary allows, rests on a STRICTLY WEAKER
allocation premise than Rothbard's — while paying for it with
comparability of ends, which Rothbard's route never needs. -/
theorem servedInOrder_not_entail_swapDominant :
    ServedInOrder coarsePlan ∧ ¬ SwapDominant coarsePlan :=
  ⟨coarse_servedInOrder, coarse_not_swapDominant⟩

#print axioms servedInOrder_not_entail_swapDominant

/-! ## Where Mises's law is silent and Rothbard's is not

If `ComparableServiceable` is a situational CONDITION rather than a
claim, then the Mises route applies to fewer situations than the
Rothbard route. This frame is one of them: swap dominance holds, the
law goes through Rothbard's way, and Mises's condition fails.

The frame is not arbitrary, and the constraint on building it is
itself the finding. Swap dominance compares the served bundle with
each ONE-SWAP rival, so it forces a comparison between every served
end and every unserved serviceable one. Comparability can therefore
only fail for a pair of ends that NEVER straddles the margin — two
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

/-- **A situation where Rothbard's law applies and Mises's does not.**

Swap dominance holds, so `marginal_utility_chain` and the Rothbard
route apply to this agent in full. `ComparableServiceable` fails, so
`Mises.ladder_from_order` does not apply at all — its premise is
unavailable.

If comparability is ruled a CONDITION, this is what "Mises's law
covers fewer situations" means concretely: an agent with two ends he
has never had occasion to rank against each other. If it is ruled a
CLAIM, then praxeology asserts no such agent exists, and this frame
is a counter-example to the claim rather than a gap in the theorem's
reach. The Lean is the same either way; the ruling decides what it
means. -/
theorem rothbard_applies_where_mises_is_silent :
    SwapDominant marginPlan ∧ ¬ marginStock.ComparableServiceable :=
  ⟨margin_swapDominant, margin_not_comparable⟩

#print axioms rothbard_applies_where_mises_is_silent

end Model
end Apodictic
