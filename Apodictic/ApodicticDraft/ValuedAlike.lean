import ApodicticDraft.Satiation
import ApodicticDraft.Toy

/-!
# Valued alike — ranking a plan's purchase now, by valuations it is made under later

The plan says what the agent WOULD buy with a sum, and he would buy it
when he spends it, by his valuations then. `MoreMoneyPreferredWhereDiffers`
ranks those purchases by his valuations at `now`. Where his valuations
change between the two dates, that fails: the Christmas Club saver now
prefers less cash at hand, because of what he would buy with more.

This module dates the claim at the spending
(`MoreMoneyPreferredWhenSpent`, in `Apodictic.Praxeology`) and names
the step back to `now` as a condition, `RankedAlikeNow`.

## What is proved

- `whereDiffers_of_whenSpent`: the dated claim and the condition give
  the approved claim. So every theorem in `ApodicticDraft.Satiation`
  follows from them.
- `whenSpent_now`: spending at `now`, the approved claim gives the
  dated one, and the condition holds trivially (`rankedAlike_self`).
  So the dated claim asserts no more where nothing is deferred.
- S3, S4, S5 with the dated claim and the condition
  (`present_sum_preferred_to_less_when_spent`,
  `no_loan_at_nonpositive_rate_when_spent`,
  `struck_rate_positive_when_spent`).
- `ImpulseToy`: a man whose valuations change between now and the
  spending. The dated claim holds of him, asymmetry holds at both
  dates, the condition fails, and the approved claim is false of him at
  `now`. The failure lands on the condition.
-/

namespace ApodicticDraft
namespace ValuedAlike

open Apodictic Interest Satiation

section Plans

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {stock : Stock praxis.toActionFrame agent now}

/-- **Ranked alike now** — a condition on the situation, NOT a claim.
Of two sums of money from the stock, one part of the other, the agent's
ranking of what they would buy, at the date `spend` he would spend
them, is also his ranking at `now`. His valuations of these purchases
do not change in between. Mises: "If the valuations change, acting must
change also" (*Human Action*, ch. V, §4). It fails for the man who now
prefers less cash at hand because of what he would do with more. -/
def RankedAlikeNow (plan : AllocationPlan stock) (spend : praxis.Time) : Prop :=
  ∀ fewer more : Finset praxis.Means, fewer ⊂ more → more ⊆ stock.units →
    praxis.Prefers agent spend ↑(plan.wouldServe more) ↑(plan.wouldServe fewer) →
    praxis.Prefers agent now ↑(plan.wouldServe more) ↑(plan.wouldServe fewer)

/-- The dated claim and the condition give the approved claim. -/
theorem whereDiffers_of_whenSpent (plan : AllocationPlan stock)
    (spend : praxis.Time) (moreMoney : MoreMoneyPreferredWhenSpent plan spend)
    (alike : RankedAlikeNow plan spend) :
    MoreMoneyPreferredWhereDiffers plan :=
  ⟨fun fewer more part inStock money freeFewer freeMore differ =>
    alike fewer more part inStock
      (moreMoney.more fewer more part inStock money freeFewer freeMore differ)⟩

/-- Spending now, the approved claim gives the dated one. -/
theorem whenSpent_now (plan : AllocationPlan stock)
    (moreMoney : MoreMoneyPreferredWhereDiffers plan) :
    MoreMoneyPreferredWhenSpent plan now :=
  ⟨moreMoney.more⟩

/-- Spending now, the condition holds of any plan. -/
theorem rankedAlike_self (plan : AllocationPlan stock) :
    RankedAlikeNow plan now :=
  fun _ _ _ _ ranked => ranked

end Plans

section Sums

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future : Stock praxis.toActionFrame agent now}

/-- **S3**, with the claim dated at the spending and the condition that
the future plan is ranked alike now. -/
theorem present_sum_preferred_to_less_when_spent
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum claim lesser : Finset praxis.Means) (soon late : praxis.End)
    (spend : praxis.Time)
    (timePreference : TimePreference praxis.toDatedFrame agent now)
    (power : SamePurchasingPower presentPlan futurePlan sum claim soon late)
    (sooner : SpentSooner (praxis := praxis) (now := now) soon late)
    (claimIn : claim ⊆ future.units) (lesserIn : lesser ⊆ future.units)
    (notMore : lesser.card ≤ claim.card)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferredWhenSpent futurePlan spend)
    (alike : RankedAlikeNow futurePlan spend)
    (buysMore : BuysMoreThanItsParts futurePlan claim)
    (money : ∀ unit ∈ claim, praxis.Money unit)
    (free : FreeToHoldWithin (agent := agent) (now := now) claim)
    (chain : praxis.TransitiveOn agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe claim) ↑(futurePlan.wouldServe lesser)) :
    praxis.Prefers agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe lesser) :=
  present_sum_preferred_to_less_where_differs presentPlan futurePlan sum claim
    lesser soon late timePreference power sooner claimIn lesserIn notMore
    homogeneous (whereDiffers_of_whenSpent futurePlan spend moreMoney alike)
    buysMore money free chain

end Sums

section Loans

variable {praxis : MoneyFrame}

/-- **S4**, with the claim dated at the spending and the condition. -/
theorem no_loan_at_nonpositive_rate_when_spent
    (trade : Trade praxis.toActionFrame)
    {present future : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum claim repaid : Finset praxis.Means) (soon late : praxis.End)
    (spend : praxis.Time)
    (timePreference : TimePreference praxis.toDatedFrame trade.agent trade.time)
    (power : SamePurchasingPower presentPlan futurePlan sum claim soon late)
    (sooner : SpentSooner (praxis := praxis) (now := trade.time) soon late)
    (claimIn : claim ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (nonPositive : repaid.card ≤ sum.card)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferredWhenSpent futurePlan spend)
    (alike : RankedAlikeNow futurePlan spend)
    (buysMore : BuysMoreThanItsParts futurePlan claim)
    (money : ∀ unit ∈ claim, praxis.Money unit)
    (free : FreeToHoldWithin (agent := trade.agent) (now := trade.time) claim)
    (chain : praxis.TransitiveOn trade.agent trade.time
      ↑(presentPlan.wouldServe sum) ↑(futurePlan.wouldServe claim)
      ↑(futurePlan.wouldServe repaid))
    (asymmetric : AsymmetricPreference praxis.toActionFrame trade.agent trade.time)
    (refusal : trade.RefusalKeepsSum presentPlan sum)
    (after : trade.AfterCountsAsPlanned futurePlan repaid) :
    ¬ DemonstratedPreference trade :=
  no_loan_at_nonpositive_rate_where_differs trade presentPlan futurePlan sum
    claim repaid soon late timePreference power sooner claimIn repaidIn
    nonPositive homogeneous
    (whereDiffers_of_whenSpent futurePlan spend moreMoney alike) buysMore
    money free chain asymmetric refusal after

/-- **S5**, with the claim dated at the spending and the condition. -/
theorem struck_rate_positive_when_spent
    (exchange : Exchange praxis.toActionFrame)
    {present future : Stock praxis.toActionFrame exchange.first.agent
      exchange.first.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum claim repaid : Finset praxis.Means) (soon late : praxis.End)
    (spend : praxis.Time)
    (timePreference : TimePreference praxis.toDatedFrame exchange.first.agent
      exchange.first.time)
    (power : SamePurchasingPower presentPlan futurePlan sum claim soon late)
    (sooner : SpentSooner (praxis := praxis) (now := exchange.first.time)
      soon late)
    (claimIn : claim ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferredWhenSpent futurePlan spend)
    (alike : RankedAlikeNow futurePlan spend)
    (buysMore : BuysMoreThanItsParts futurePlan claim)
    (money : ∀ unit ∈ claim, praxis.Money unit)
    (free : FreeToHoldWithin (agent := exchange.first.agent)
      (now := exchange.first.time) claim)
    (chain : praxis.TransitiveOn exchange.first.agent exchange.first.time
      ↑(presentPlan.wouldServe sum) ↑(futurePlan.wouldServe claim)
      ↑(futurePlan.wouldServe repaid))
    (asymmetric : AsymmetricPreference praxis.toActionFrame
      exchange.first.agent exchange.first.time)
    (voluntary : exchange.first.Voluntary)
    (before : exchange.first.BeforeCountsAsPlanned presentPlan sum)
    (after : exchange.first.AfterCountsAsPlanned futurePlan repaid)
    (demonstrated : DemonstratedPreference exchange.first) :
    sum.card < repaid.card :=
  struck_rate_positive_where_differs exchange presentPlan futurePlan sum claim
    repaid soon late timePreference power sooner claimIn repaidIn homogeneous
    (whereDiffers_of_whenSpent futurePlan spend moreMoney alike) buysMore
    money free chain asymmetric voluntary before after demonstrated

end Loans

/-! ## A man whose valuations change between now and the spending -/

namespace ImpulseToy

/-- One end: what an ounce of cash at hand would buy, on impulse, at
date 1. -/
def impulse : ℕ × ℕ := (3, 1)

/-- At date 0 he prefers not having the impulse to having it; at date
1, the impulse to nothing. No other preference. -/
def prefers (t : ℕ) (X Y : Set (ℕ × ℕ)) : Prop :=
  (t = 0 ∧ X = ∅ ∧ Y = {impulse}) ∨ (t = 1 ∧ X = {impulse} ∧ Y = ∅)

/-- The frame: one ounce of cash, which he believes serves the impulse. -/
abbrev frame : MoneyFrame where
  Agent := Unit
  End := ℕ × ℕ
  Means := Toy.Good
  Time := ℕ
  Believes := fun _ _ g e => g = .ounce ∧ e = impulse
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
  unitsAlike := fun unit h e => by
    have hu : unit = .ounce := Finset.mem_singleton.1 h
    subst hu
    exact ⟨fun ⟨_, he⟩ => he, fun he => ⟨rfl, he⟩⟩

/-- What he would buy with cash: the impulse, with any. -/
def plan : AllocationPlan cash where
  wouldServe s := Toy.presentBuys impulse s.card
  servesOnlyWhatItCan s want h := by
    show want ∈ ({impulse} : Set (ℕ × ℕ))
    unfold Toy.presentBuys at h
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
theorem part_of_cash (fewer more : Finset Toy.Good) (part : fewer ⊂ more)
    (inStock : more ⊆ cash.units) : fewer = ∅ ∧ more = {.ounce} := by
  have more_le : more.card ≤ 1 := Finset.card_le_card inStock
  have fewer_lt : fewer.card < more.card := Finset.card_lt_card part
  have fewer_zero : fewer.card = 0 := by omega
  have more_one : more.card = 1 := by omega
  refine ⟨Finset.card_eq_zero.1 fewer_zero, ?_⟩
  exact Finset.eq_of_subset_of_card_le inStock (by rw [more_one]; rfl)

/-- `coe_none` says the same with a classical proof. -/
theorem coe_none : ((∅ : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) = ∅ :=
  Set.ext fun _ => ⟨fun h => absurd h (Finset.notMem_empty _), fun h => absurd h id⟩

theorem buys_empty : plan.wouldServe ∅ = ∅ := rfl

theorem buys_ounce : plan.wouldServe {.ounce} = {impulse} := rfl

/-- **The dated claim holds of him**: at date 1, when he would spend
it, he prefers what an ounce buys to what no cash buys. -/
theorem whenSpent : MoreMoneyPreferredWhenSpent (praxis := frame) plan (1 : ℕ) :=
  ⟨fun fewer more part inStock _ _ _ _ => by
    obtain ⟨hf, hm⟩ := part_of_cash fewer more part inStock
    subst hf hm
    rw [buys_empty, buys_ounce]
    exact Or.inr ⟨rfl, coe_single impulse, coe_none⟩⟩

/-- **The condition fails**: his ranking at date 1 is not his ranking
at date 0. -/
theorem not_rankedAlike : ¬ RankedAlikeNow (praxis := frame) plan (1 : ℕ) := by
  intro alike
  have now := alike ∅ {.ounce} (Finset.ssubset_iff_subset_ne.2
      ⟨Finset.empty_subset _, (Finset.singleton_ne_empty _).symm⟩)
    (fun _ h => h)
    (by
      rw [buys_empty, buys_ounce]
      exact Or.inr ⟨rfl, coe_single impulse, coe_none⟩)
  rw [buys_empty, buys_ounce] at now
  rcases now with ⟨_, hX, _⟩ | ⟨one, _, _⟩
  · exact impulse_ne_empty (by rw [← coe_single]; exact hX)
  · exact Nat.zero_ne_one one

/-- **The approved claim is false of him at date 0**: he does not
prefer what an ounce buys to what no cash buys. -/
theorem not_whereDiffers : ¬ MoreMoneyPreferredWhereDiffers (praxis := frame) plan := fun claim =>
  not_rankedAlike (fun fewer more part inStock _ =>
    claim.more fewer more part inStock (fun _ _ => trivial) trivial trivial
      (by
        obtain ⟨hf, hm⟩ := part_of_cash fewer more part inStock
        subst hf hm
        rw [buys_empty, buys_ounce]
        exact (Finset.singleton_ne_empty impulse)))

end ImpulseToy

#print axioms whereDiffers_of_whenSpent
#print axioms whenSpent_now
#print axioms rankedAlike_self
#print axioms present_sum_preferred_to_less_when_spent
#print axioms no_loan_at_nonpositive_rate_when_spent
#print axioms struck_rate_positive_when_spent
#print axioms ImpulseToy.coe_none
#print axioms ImpulseToy.asymmetric
#print axioms ImpulseToy.whenSpent
#print axioms ImpulseToy.not_rankedAlike
#print axioms ImpulseToy.not_whereDiffers

end ValuedAlike
end ApodicticDraft

#lint only unusedArguments
