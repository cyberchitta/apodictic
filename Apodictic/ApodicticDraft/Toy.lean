import ApodicticDraft.Interest

/-!
# Toy — non-vacuity of the T1 draft, and a negative rate (evidence, not theory)

The draft counterpart of `Apodictic.Consistency`, for T1 only. Nothing
depends on it.

One frame builder, two agents' worth of beliefs:

- **The lender** has a use for an ounce now. He lends one ounce for a
  claim to two, and every claim and every condition of
  `struck_rate_positive` holds: the theorems are not true for want of
  a case.
- **The saver** has no use for money before the date the bond pays,
  and holding cash costs him: his two ounces, kept to that date, buy
  less than one ounce claimed. He lends two ounces for a claim to one —
  a negative rate, struck voluntarily and held to maturity (I-12). Every
  CLAIM holds of him: `TimePreference`, `AsymmetricPreference`,
  `DemonstratedPreference`, `MoreMoneyPreferred`. What fails is a
  condition, `SpentSooner` — and with it the theorem is silent, not
  false.

Ends are (kind, date); one end is preferred to another by a score
that ranks kind first and date second, so same-kind ends are the same
satisfaction and the sooner is preferred.
-/

namespace ApodicticDraft
namespace Toy

open Apodictic

/-- The goods: two present ounces, two claims to an ounce at date 1,
and four goods standing for whole holdings in the two loans — the
lender's purse (one ounce) and bond (a claim to two), the saver's hoard
(two ounces) and note (a claim to one). -/
inductive Good
  | ounce | ounce' | claimA | claimB | purse | bond | hoard | note
  deriving DecidableEq

/-- Kind first, date second: lower is better. -/
def score (e : ℕ × ℕ) : ℕ := e.1 * 10 + e.2

/-- An ounce's worth now. -/
def soon : ℕ × ℕ := (1, 0)
/-- An ounce's worth at date 1: the same satisfaction, later. -/
def late : ℕ × ℕ := (1, 1)
/-- Two ounces' worth at date 1. -/
def plenty : ℕ × ℕ := (0, 1)
/-- Two ounces held to date 1, less what holding them cost. -/
def diminished : ℕ × ℕ := (2, 1)

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

section Claims

variable (believes : Good → ℕ × ℕ → Prop)

theorem timePreference (now : ℕ) :
    TimePreference (frame believes).toDatedFrame () now :=
  ⟨fun soon late same sooner _ => ⟨soon, rfl, fun y hy => by
    have hy : y = late := hy
    subst hy
    show soon.1 * 10 + soon.2 < y.1 * 10 + y.2
    have same : soon.1 = y.1 := same
    have sooner : soon.2 < y.2 := sooner
    rw [same]
    exact Nat.add_lt_add_left sooner _⟩⟩

theorem asymmetric (now : ℕ) :
    AsymmetricPreference (frame believes).toActionFrame () now :=
  ⟨fun _ _ ⟨x, hx, hxY⟩ ⟨y, hy, hyX⟩ =>
    Nat.lt_asymm (hxY y hy) (hyX x hx)⟩

theorem transitive (now : ℕ) (X Y Z : Set (ℕ × ℕ)) :
    (frame believes).TransitiveOn () now X Y Z :=
  fun ⟨x, hx, hxY⟩ ⟨y, hy, hyZ⟩ =>
    ⟨x, hx, fun z hz => Nat.lt_trans (hxY y hy) (hyZ z hz)⟩

end Claims

/-- What a claim to `n` ounces at date 1 buys. -/
def futureBuys : ℕ → Finset (ℕ × ℕ)
  | 0 => ∅
  | 1 => {late}
  | _ => {plenty}

/-- What a present sum buys, given what one ounce or more buys. -/
def presentBuys (worth : ℕ × ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  if n = 0 then ∅ else {worth}

/-- Ounces now serve `worth`; claims serve `late` or `plenty`. -/
def moneyBeliefs (worth : ℕ × ℕ) : Good → ℕ × ℕ → Prop
  | .ounce, e => e = worth
  | .ounce', e => e = worth
  | .claimA, e => e = late ∨ e = plenty
  | .claimB, e => e = late ∨ e = plenty
  | _, _ => False

/-- The lender's beliefs: an ounce now buys `soon`; the purse is one
ounce, the bond a claim to two. -/
def lenderBeliefs : Good → ℕ × ℕ → Prop
  | .purse, e => e = soon
  | .bond, e => e = plenty
  | g, e => moneyBeliefs soon g e

/-- The saver's beliefs: his ounces, held to date 1, buy `diminished`;
the hoard is his two ounces, the note a claim to one. -/
def saverBeliefs : Good → ℕ × ℕ → Prop
  | .hoard, e => e = diminished
  | .note, e => e = late
  | g, e => moneyBeliefs diminished g e

section Stocks

variable (believes : Good → ℕ × ℕ → Prop)

/-- Claims to an ounce at date 1, weighed at date 0. -/
def futureStock
    (alike : ∀ unit ∈ ({.claimA, .claimB} : Finset Good), ∀ e,
      believes unit e ↔ e ∈ ({late, plenty} : Set (ℕ × ℕ))) :
    Stock (frame believes).toActionFrame () 0 where
  units := {.claimA, .claimB}
  serves := {late, plenty}
  unitsAlike := alike

/-- What he would buy with claims: by count only. -/
def futurePlan alike : AllocationPlan (futureStock believes alike) where
  wouldServe s := futureBuys s.card
  servesOnlyWhatItCan s want h := by
    show want ∈ ({late, plenty} : Set (ℕ × ℕ))
    unfold futureBuys at h
    split at h
    · exact absurd h (Finset.notMem_empty _)
    · exact Or.inl (Finset.mem_singleton.1 h)
    · exact Or.inr (Finset.mem_singleton.1 h)

theorem future_homogeneous alike : (futurePlan believes alike).Homogeneous :=
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

theorem future_card_le alike (s : Finset Good)
    (h : s ⊆ (futureStock believes alike).units) : s.card ≤ 2 :=
  Finset.card_le_card h

theorem future_moreMoney alike :
    MoreMoneyPreferred (praxis := frame believes) (futurePlan believes alike) :=
  ⟨fun fewer more proper inStock _ _ _ =>
    futureBuys_more fewer.card more.card (Finset.card_lt_card proper)
      (future_card_le believes alike more inStock)⟩

/-- The present ounces, at date 0. -/
def presentStock (units : Finset Good) (worth : ℕ × ℕ)
    (alike : ∀ unit ∈ units, ∀ e, believes unit e ↔ e ∈ ({worth} : Set (ℕ × ℕ))) :
    Stock (frame believes).toActionFrame () 0 where
  units := units
  serves := {worth}
  unitsAlike := alike

/-- What he would buy with present ounces. -/
def presentPlan units worth alike :
    AllocationPlan (presentStock believes units worth alike) where
  wouldServe s := presentBuys worth s.card
  servesOnlyWhatItCan s want h := by
    show want ∈ ({worth} : Set (ℕ × ℕ))
    unfold presentBuys at h
    split at h
    · exact absurd h (Finset.notMem_empty _)
    · exact Finset.mem_singleton.1 h

end Stocks

/-! ## The lender: a positive rate, every condition holding -/

theorem lender_future_alike : ∀ unit ∈ ({.claimA, .claimB} : Finset Good), ∀ e,
    lenderBeliefs unit e ↔ e ∈ ({late, plenty} : Set (ℕ × ℕ)) := by
  intro unit h e
  rcases Finset.mem_insert.1 h with rfl | h
  · exact Iff.rfl
  · rw [Finset.mem_singleton.1 h]; exact Iff.rfl

theorem lender_present_alike : ∀ unit ∈ ({.ounce} : Finset Good), ∀ e,
    lenderBeliefs unit e ↔ e ∈ ({soon} : Set (ℕ × ℕ)) := by
  intro unit h e
  rw [Finset.mem_singleton.1 h]
  exact Iff.rfl

/-- The lender's side: he gives the purse (one ounce), gets the bond
(a claim to two ounces), keeps nothing else; refusing would have left
him an ounce's worth now. -/
def lend : Trade (frame lenderBeliefs).toActionFrame :=
  ⟨(), 0, .purse, .bond, ∅, {soon}⟩

/-- The borrower's side; one person plays both (`Exchange` does not
ask for two). -/
def borrow : Trade (frame lenderBeliefs).toActionFrame :=
  ⟨(), 0, .bond, .purse, ∅, ∅⟩

def loan : Exchange (frame lenderBeliefs).toActionFrame :=
  ⟨lend, borrow, rfl, rfl⟩

theorem servedBy_one (believes : Good → ℕ × ℕ → Prop) (g : Good) :
    (frame believes).ServedBy () 0 (insert g ∅) = {e | believes g e} := by
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

theorem lend_before_planned :
    lend.BeforeCountsAsPlanned
      (presentPlan lenderBeliefs {.ounce} soon lender_present_alike) {.ounce} := by
  show lend.before 0 = _
  rw [lend_before]
  exact (Interest.coe_single _).symm

theorem lend_after_planned :
    lend.AfterCountsAsPlanned
      (futurePlan lenderBeliefs lender_future_alike) {.claimA, .claimB} := by
  show lend.after 0 = _
  rw [lend_after]
  exact (Interest.coe_single _).symm

/-- **Non-vacuity: every rate struck is positive, applied.** The lender
lends one ounce and is repaid two; every claim and condition of S5
holds. -/
theorem struck_rate_positive_applies :
    ({.ounce} : Finset Good).card < ({.claimA, .claimB} : Finset Good).card :=
  Interest.struck_rate_positive loan
    (presentPlan lenderBeliefs {Good.ounce} soon lender_present_alike)
    (futurePlan lenderBeliefs lender_future_alike)
    {Good.ounce} {Good.claimA} {Good.claimA, Good.claimB} soon late
    (timePreference lenderBeliefs 0)
    ⟨rfl, rfl, rfl, rfl⟩
    ⟨Nat.zero_lt_one, Nat.lt_irrefl 0⟩
    (fun _ h => by rw [Finset.mem_singleton.1 h]; exact Finset.mem_insert_self _ _)
    (fun _ h => h)
    (future_homogeneous lenderBeliefs lender_future_alike)
    (future_moreMoney lenderBeliefs lender_future_alike)
    (fun _ _ => trivial)
    (fun _ _ => trivial)
    (transitive lenderBeliefs 0 _ _ _)
    (asymmetric lenderBeliefs 0)
    lend_voluntary
    lend_before_planned
    lend_after_planned
    ⟨by
      show (frame lenderBeliefs).Prefers () 0 (lend.after 0) {soon}
      rw [lend_after]
      exact ⟨plenty, rfl, fun y hy => by
        have hy : y = soon := hy
        subst hy
        exact Nat.lt_of_sub_eq_succ rfl⟩⟩

/-! ## The saver: a negative rate, every claim holding -/

theorem saver_future_alike : ∀ unit ∈ ({.claimA, .claimB} : Finset Good), ∀ e,
    saverBeliefs unit e ↔ e ∈ ({late, plenty} : Set (ℕ × ℕ)) := by
  intro unit h e
  rcases Finset.mem_insert.1 h with rfl | h
  · exact Iff.rfl
  · rw [Finset.mem_singleton.1 h]; exact Iff.rfl

theorem saver_present_alike : ∀ unit ∈ ({.ounce, .ounce'} : Finset Good), ∀ e,
    saverBeliefs unit e ↔ e ∈ ({diminished} : Set (ℕ × ℕ)) := by
  intro unit h e
  rcases Finset.mem_insert.1 h with rfl | h
  · exact Iff.rfl
  · rw [Finset.mem_singleton.1 h]; exact Iff.rfl

/-- The saver's side: he gives the hoard (two ounces), gets the note (a
claim to one), keeps nothing else; refusing would have left him the two
ounces held to date 1, less what holding them cost. -/
def save : Trade (frame saverBeliefs).toActionFrame :=
  ⟨(), 0, .hoard, .note, ∅, {diminished}⟩

theorem save_before : save.before 0 = {diminished} := by
  rw [Trade.before, show save.kept = ∅ from rfl, servedBy_one]
  ext e; exact Iff.rfl

theorem save_after : save.after 0 = {late} := by
  rw [Trade.after, show save.kept = ∅ from rfl, servedBy_one]
  ext e; exact Iff.rfl

theorem save_voluntary : save.Voluntary := save_before.symm

/-- The saver demonstrates his preference for the note: an ounce's
worth at date 1 over two ounces' worth at date 1 less the cost of
holding them. -/
theorem save_demonstrated : DemonstratedPreference save :=
  ⟨by
    show (frame saverBeliefs).Prefers () 0 (save.after 0) {diminished}
    rw [save_after]
    exact ⟨late, rfl, fun y hy => by
      have hy : y = diminished := hy
      subst hy
      exact Nat.lt_of_sub_eq_succ rfl⟩⟩

/-- **A negative rate, struck voluntarily, with every claim holding.**
The saver's frame satisfies `TimePreference`, `AsymmetricPreference`,
`MoreMoneyPreferred` (on his plan for claims) and
`DemonstratedPreference` (of his trade); the trade is voluntary; and he
is repaid one ounce for two. -/
theorem negative_rate_with_every_claim :
    TimePreference (frame saverBeliefs).toDatedFrame () 0 ∧
    AsymmetricPreference (frame saverBeliefs).toActionFrame () 0 ∧
    MoreMoneyPreferred (praxis := frame saverBeliefs)
      (futurePlan saverBeliefs saver_future_alike) ∧
    DemonstratedPreference save ∧ save.Voluntary ∧
    ({.note} : Finset Good).card < ({.ounce, .ounce'} : Finset Good).card :=
  ⟨timePreference saverBeliefs 0, asymmetric saverBeliefs 0,
    future_moreMoney saverBeliefs saver_future_alike, save_demonstrated,
    save_voluntary, Nat.lt_of_sub_eq_succ rfl⟩

/-- **What fails for the saver is `SpentSooner`.** Whatever his two
present ounces would buy, and whatever two claimed ounces would buy,
the first is not sooner than the second: he has no use for the money
before the bond pays. -/
theorem saver_not_spent_sooner (soonEnd lateEnd : ℕ × ℕ)
    (buysSoon : (presentPlan saverBeliefs {.ounce, .ounce'} diminished
      saver_present_alike).wouldServe {.ounce, .ounce'} = {soonEnd})
    (buysLate : (futurePlan saverBeliefs saver_future_alike).wouldServe
      {.claimA, .claimB} = {lateEnd}) :
    ¬ SpentSooner (praxis := frame saverBeliefs) (now := (0 : ℕ)) soonEnd lateEnd := by
  rintro ⟨sooner, _⟩
  have hs : ({diminished} : Finset (ℕ × ℕ)) = {soonEnd} := buysSoon
  have hl : ({plenty} : Finset (ℕ × ℕ)) = {lateEnd} := buysLate
  rw [Finset.singleton_inj] at hs hl
  subst hs hl
  exact Nat.lt_irrefl 1 sooner

#print axioms struck_rate_positive_applies
#print axioms negative_rate_with_every_claim
#print axioms saver_not_spent_sooner

end Toy
end ApodicticDraft

#lint only unusedArguments
