import Apodictic

/-!
# Toy — each half of the certainty split failing alone (evidence, not theory)

The toy counterpart of the certainty split in `Apodictic.Money`
(`ClaimPays` apart from `SamePurchasingPower`). Nothing depends on it.

One agent, at date 0, holds three one-unit stocks: an ounce of cash, a
claim to an ounce at date 1, and the ounce that claim promises, as he
would spend it were it in hand at date 1. Two sets of beliefs:

- **Default risk.** The promised ounce would buy what an ounce buys
  now, a date later: purchasing power holds. But he doubts the claim
  will pay, so he counts it for less than the ounce it promises:
  `ClaimPays` fails, alone.
- **Inflation.** He is sure the claim pays: it counts for exactly what
  the promised ounce counts for, and `ClaimPays` holds. But that ounce
  will buy less than an ounce buys now: `SamePurchasingPower` between
  the present sum and the promised money fails, alone.

In both, the merged condition, `SamePurchasingPower` asserted
between the present sum and the claim, fails — and the claim's plan is
the same function in both. The merged condition cannot tell the two
apart; the split can.

A case in which both halves hold and S5 applies is the library's
(`Apodictic.Model.Loan.struck_rate_positive_applies`).

Ends are (kind, date); kind 1 is an ounce's worth, kind 2 is less.
Two ends are the same satisfaction when their kinds agree.
-/

namespace ApodicticDraft
namespace CertaintySplitToy

open Apodictic

/-- The goods: an ounce now, a claim to an ounce at date 1, and the
ounce the claim promises. -/
inductive Good
  | cash | claim | promised
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

/-- Cash buys `soon`; the claim and the promised ounce buy what the
agent believes they buy. -/
def beliefs (claimBuys promisedBuys : ℕ × ℕ) : Good → ℕ × ℕ → Prop
  | .cash, e => e = soon
  | .claim, e => e = claimBuys
  | .promised, e => e = promisedBuys

/-- What some units of a one-unit stock buy. -/
def buys (worth : ℕ × ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  if n = 0 then ∅ else {worth}

/-- A one-unit stock of `g`, weighed at date 0. -/
def stock (claimBuys promisedBuys : ℕ × ℕ) (g : Good) (worth : ℕ × ℕ)
    (alike : ∀ e, beliefs claimBuys promisedBuys g e ↔ e ∈ ({worth} : Set (ℕ × ℕ))) :
    Stock (frame (beliefs claimBuys promisedBuys)).toActionFrame () 0 where
  units := {g}
  serves := {worth}
  unitsAlike unit h e := by
    obtain rfl := Finset.mem_singleton.1 h
    exact alike e

/-- His plan for it: by count only. -/
def plan (claimBuys promisedBuys : ℕ × ℕ) (g : Good) (worth : ℕ × ℕ) alike :
    AllocationPlan (stock claimBuys promisedBuys g worth alike) where
  wouldServe s := buys worth s.card
  servesOnlyWhatItCan s want h := by
    show want ∈ ({worth} : Set (ℕ × ℕ))
    unfold buys at h
    split at h
    · exact absurd h (Finset.notMem_empty _)
    · exact Finset.mem_singleton.1 h

theorem plan_single (claimBuys promisedBuys : ℕ × ℕ) (g g' : Good)
    (worth : ℕ × ℕ) alike :
    (plan claimBuys promisedBuys g worth alike).wouldServe {g'} = {worth} := by
  show buys worth ({g'} : Finset Good).card = {worth}
  rw [Finset.card_singleton]
  rfl

theorem one_ne_two : (1 : ℕ) ≠ 2 := fun h => Nat.zero_ne_one (Nat.succ.inj h)

theorem late_ne_worse : late ≠ worse := fun h => one_ne_two (congrArg Prod.fst h)

/-- Same purchasing power fails between cash buying `soon` and any
good buying `worse`, whatever ends it is asked of. -/
theorem not_same_of_worse (claimBuys promisedBuys : ℕ × ℕ) (g : Good)
    cashAlike otherAlike (s l : ℕ × ℕ) :
    ¬ SamePurchasingPower (praxis := frame (beliefs claimBuys promisedBuys))
      (plan claimBuys promisedBuys Good.cash soon cashAlike)
      (plan claimBuys promisedBuys g worse otherAlike)
      {Good.cash} {g} s l := by
  rintro ⟨_, buysSoon, buysLate, same⟩
  rw [plan_single] at buysSoon buysLate
  have hs : soon = s := Finset.singleton_injective buysSoon
  have hl : worse = l := Finset.singleton_injective buysLate
  have same : s.1 = l.1 := same
  rw [← hs, ← hl] at same
  exact one_ne_two same

/-! ## Default risk: purchasing power holds, the claim does not pay -/

/-- He doubts the claim; the promised ounce buys an ounce's worth. -/
abbrev doubt := beliefs worse late

def doubtCash := plan worse late .cash soon (fun _ => Iff.rfl)
def doubtClaim := plan worse late .claim worse (fun _ => Iff.rfl)
def doubtPromised := plan worse late .promised late (fun _ => Iff.rfl)

theorem doubt_power :
    SamePurchasingPower (praxis := frame doubt) doubtCash doubtPromised
      {.cash} {.promised} soon late :=
  ⟨rfl, plan_single _ _ _ _ _ _, plan_single _ _ _ _ _ _, rfl⟩

theorem doubt_not_pays :
    ¬ ClaimPays (praxis := frame doubt) doubtClaim doubtPromised
      {.claim} {.promised} := by
  rintro ⟨_, counts⟩
  have counts : ({worse} : Finset (ℕ × ℕ)) = {late} :=
    (plan_single worse late .claim .claim worse _).symm.trans
      (counts.trans (plan_single worse late .promised .promised late _))
  exact late_ne_worse (Finset.singleton_injective counts).symm

theorem doubt_merged_fails (s l : ℕ × ℕ) :
    ¬ SamePurchasingPower (praxis := frame doubt) doubtCash doubtClaim
      {.cash} {.claim} s l :=
  not_same_of_worse worse late .claim _ _ s l

/-! ## Inflation: the claim pays, purchasing power does not hold -/

/-- He is sure of the claim; the promised ounce buys less. -/
abbrev inflation := beliefs worse worse

def inflationCash := plan worse worse .cash soon (fun _ => Iff.rfl)
def inflationClaim := plan worse worse .claim worse (fun _ => Iff.rfl)
def inflationPromised := plan worse worse .promised worse (fun _ => Iff.rfl)

theorem inflation_pays :
    ClaimPays (praxis := frame inflation) inflationClaim inflationPromised
      {.claim} {.promised} :=
  ⟨rfl, (plan_single _ _ _ _ _ _).trans (plan_single _ _ _ _ _ _).symm⟩

theorem inflation_not_power (s l : ℕ × ℕ) :
    ¬ SamePurchasingPower (praxis := frame inflation) inflationCash
      inflationPromised {.cash} {.promised} s l :=
  not_same_of_worse worse worse .promised _ _ s l

theorem inflation_merged_fails (s l : ℕ × ℕ) :
    ¬ SamePurchasingPower (praxis := frame inflation) inflationCash
      inflationClaim {.cash} {.claim} s l :=
  not_same_of_worse worse worse .claim _ _ s l

#print axioms doubt_power
#print axioms doubt_not_pays
#print axioms doubt_merged_fails
#print axioms inflation_pays
#print axioms inflation_not_power
#print axioms inflation_merged_fails

end CertaintySplitToy
end ApodicticDraft

#lint only unusedArguments
