import Apodictic.PureInterest

/-!
# The count apart — S2–S5 with "the same amount" as its own condition

The library's `SamePurchasingPower` and `ClaimPays` each open with an
equality of counts: the present sum is as many units as the promised
money, and the claim as many as the money it promises. S2
(`Apodictic.PureInterest.present_sum_preferred`) carries both and uses
neither count, which `#lint only unusedArguments` cannot see, since it
checks whole hypotheses. S3 does not use them either. Only the loan
theorems do, to compare the repaid sum with the claim.

This module takes the counts out. `SamePurchasingPowerOf` and
`ClaimPaysOf` are the library's conditions without them, and
`SameCount` is the one count the loan theorems use: the claim is as
many units as the present sum.

## What is proved

- `split_of_both` and `both_of_split`: the old pair of conditions gives
  the new pair and `SameCount`, and the new pair with both old counts
  gives the old. The split asserts nothing the old conditions did not.
- `present_sum_preferred` (S2), `present_sum_preferred_to_less` (S3):
  the library's conclusions, with no count carried.
- `no_loan_at_zero_rate`, `no_loan_at_nonpositive_rate` (S4),
  `struck_rate_positive` (S5): the library's conclusions, with
  `SameCount` carried where the old counts were.

Rival not built: two counts kept apart, the present sum against the
promised money and the claim against it, as the old conditions had
them. The loan theorems use only their consequence, the claim against
the present sum, so one condition suffices.
-/

namespace ApodicticDraft
namespace CountApart

open Apodictic

section Sums

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future promised : Stock praxis.toActionFrame agent now}

/-- **Same purchasing power, without the count** — a condition on the
situation. Each sum would buy one satisfaction, the same satisfaction,
each at its own date. Asserted between the present sum and the money a
claim promises. It fails where the money buys less at the later date.
That the sums are the same number of units is not part of it: equal
counts are the same good at two dates only if they buy the same thing,
and that is what this says. -/
def SamePurchasingPowerOf (presentPlan : AllocationPlan present)
    (futurePlan : AllocationPlan future) (sum claim : Finset praxis.Means)
    (soon late : praxis.End) : Prop :=
  presentPlan.wouldServe sum = {soon} ∧
    futurePlan.wouldServe claim = {late} ∧
    praxis.SameSatisfaction agent soon late

/-- **The claim pays, without the count** — a condition on the
situation: Rothbard's world of certainty, for one claim. The agent's
plan counts the claim for exactly what it counts the money it promises
for. It fails where he believes the claim may not pay, or may pay in
part. -/
def ClaimPaysOf (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (claim money : Finset praxis.Means) : Prop :=
  futurePlan.wouldServe claim = promisedPlan.wouldServe money

/-- **The same count** — a condition on the situation, of bookkeeping:
the claim is as many units as the present sum. Rothbard's "the same
amount of future money" (*MES* p. 376), where it does work: in the loan
theorems, which compare the repaid sum with the claim. -/
def SameCount (sum claim : Finset praxis.Means) : Prop :=
  sum.card = claim.card

/-- The old conditions give the new ones and the count. -/
theorem split_of_both
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money : Finset praxis.Means) (soon late : praxis.End)
    (power : SamePurchasingPower presentPlan promisedPlan sum money soon late)
    (pays : ClaimPays futurePlan promisedPlan claim money) :
    SamePurchasingPowerOf presentPlan promisedPlan sum money soon late ∧
      ClaimPaysOf futurePlan promisedPlan claim money ∧
      SameCount sum claim := by
  obtain ⟨sumMoney, buysSoon, buysLate, same⟩ := power
  obtain ⟨claimMoney, countsAsMoney⟩ := pays
  exact ⟨⟨buysSoon, buysLate, same⟩, countsAsMoney,
    sumMoney.trans claimMoney.symm⟩

/-- The new conditions, with the two old counts, give the old ones. -/
theorem both_of_split
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money : Finset praxis.Means) (soon late : praxis.End)
    (power : SamePurchasingPowerOf presentPlan promisedPlan sum money soon late)
    (pays : ClaimPaysOf futurePlan promisedPlan claim money)
    (sumMoney : sum.card = money.card) (claimMoney : claim.card = money.card) :
    SamePurchasingPower presentPlan promisedPlan sum money soon late ∧
      ClaimPays futurePlan promisedPlan claim money :=
  ⟨⟨sumMoney, power⟩, ⟨claimMoney, pays⟩⟩

/-- **Present money is preferred to the same amount of future money**
(S2), with no count carried. -/
theorem present_sum_preferred
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame agent now)
    (power : SamePurchasingPowerOf presentPlan promisedPlan sum money soon late)
    (pays : ClaimPaysOf futurePlan promisedPlan claim money)
    (sooner : SpentSooner (praxis := praxis) (now := now) soon late) :
    praxis.Prefers agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe claim) := by
  obtain ⟨buysSoon, buysLate, same⟩ := power
  obtain ⟨before, notPast⟩ := sooner
  rw [buysSoon, pays, buysLate, coe_single, coe_single]
  exact timePreference.sooner soon late same before notPast

/-- **One ounce of present money is preferred to one ounce or less of
future money** (S3), with no count carried between the present sum and
the claim. -/
theorem present_sum_preferred_to_less
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money lesser : Finset praxis.Means) (soon late : praxis.End)
    (spend : praxis.Time)
    (timePreference : TimePreference praxis.toDatedFrame agent now)
    (power : SamePurchasingPowerOf presentPlan promisedPlan sum money soon late)
    (pays : ClaimPaysOf futurePlan promisedPlan claim money)
    (sooner : SpentSooner (praxis := praxis) (now := now) soon late)
    (claimIn : claim ⊆ future.units) (lesserIn : lesser ⊆ future.units)
    (notMore : lesser.card ≤ claim.card)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferredWhenSpent futurePlan spend)
    (alike : RankedAlikeNowOf futurePlan spend claim lesser)
    (buysMore : BuysMoreThanItsParts futurePlan claim)
    (isMoney : ∀ unit ∈ claim, praxis.Money unit)
    (free : FreeToHoldWithin (agent := agent) (now := now) claim)
    (chain : praxis.TransitiveOn agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe claim) ↑(futurePlan.wouldServe lesser)) :
    praxis.Prefers agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe lesser) := by
  have overSame := present_sum_preferred presentPlan futurePlan promisedPlan
    sum claim money soon late timePreference power pays sooner
  rcases Nat.eq_or_lt_of_le notMore with equal | fewer
  · rw [homogeneous lesser lesserIn claim claimIn equal]
    exact overSame
  · obtain ⟨part, partIn, partCard⟩ :=
      exists_part_of_card claim lesser.card (Nat.le_of_lt fewer)
    have same : futurePlan.wouldServe part = futurePlan.wouldServe lesser :=
      homogeneous part (fun _ h => claimIn (partIn h)) lesser lesserIn partCard
    have proper : part ⊂ claim := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨partIn, fun equal => ?_⟩
      rw [equal] at partCard
      rw [partCard] at fewer
      exact Nat.lt_irrefl _ fewer
    have atSpend := moreMoney.more part claim proper claimIn isMoney
      (free part partIn) (free claim (fun _ h => h)) (buysMore part proper)
    rw [same] at atSpend
    exact chain overSame (alike atSpend)

end Sums

section Loans

variable {praxis : MoneyFrame}

/-- **At a rate of exactly zero, he does not lend**, with the count
carried as `SameCount` and nowhere else. -/
theorem no_loan_at_zero_rate
    (trade : Trade praxis.toActionFrame)
    {present future promised : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money repaid : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame trade.agent trade.time)
    (power : SamePurchasingPowerOf presentPlan promisedPlan sum money soon late)
    (pays : ClaimPaysOf futurePlan promisedPlan claim money)
    (sooner : SpentSooner (praxis := praxis) (now := trade.time) soon late)
    (count : SameCount sum claim)
    (claimIn : claim ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (zero : repaid.card = sum.card)
    (homogeneous : futurePlan.Homogeneous)
    (asymmetric : AsymmetricPreference praxis.toActionFrame trade.agent trade.time)
    (refusal : trade.RefusalKeepsSum presentPlan sum)
    (after : trade.AfterCountsAsPlanned futurePlan repaid) :
    ¬ DemonstratedPreference trade := by
  intro demonstrated
  have chose := demonstrated.demonstrates
  rw [after, refusal] at chose
  have equal : repaid.card = claim.card := zero.trans count
  have kept := present_sum_preferred presentPlan futurePlan promisedPlan
    sum claim money soon late timePreference power pays sooner
  rw [← homogeneous repaid repaidIn claim claimIn equal] at kept
  exact asymmetric.asym _ _ kept chose

/-- **At a rate not above zero, he does not lend** (S4), with the count
carried as `SameCount`. -/
theorem no_loan_at_nonpositive_rate
    (trade : Trade praxis.toActionFrame)
    {present future promised : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money repaid : Finset praxis.Means) (soon late : praxis.End)
    (spend : praxis.Time)
    (timePreference : TimePreference praxis.toDatedFrame trade.agent trade.time)
    (power : SamePurchasingPowerOf presentPlan promisedPlan sum money soon late)
    (pays : ClaimPaysOf futurePlan promisedPlan claim money)
    (sooner : SpentSooner (praxis := praxis) (now := trade.time) soon late)
    (count : SameCount sum claim)
    (claimIn : claim ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (nonPositive : repaid.card ≤ sum.card)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferredWhenSpent futurePlan spend)
    (alike : RankedAlikeNowOf futurePlan spend claim repaid)
    (buysMore : BuysMoreThanItsParts futurePlan claim)
    (isMoney : ∀ unit ∈ claim, praxis.Money unit)
    (free : FreeToHoldWithin (agent := trade.agent) (now := trade.time) claim)
    (chain : praxis.TransitiveOn trade.agent trade.time
      ↑(presentPlan.wouldServe sum) ↑(futurePlan.wouldServe claim)
      ↑(futurePlan.wouldServe repaid))
    (asymmetric : AsymmetricPreference praxis.toActionFrame trade.agent trade.time)
    (refusal : trade.RefusalKeepsSum presentPlan sum)
    (after : trade.AfterCountsAsPlanned futurePlan repaid) :
    ¬ DemonstratedPreference trade := by
  intro demonstrated
  have chose := demonstrated.demonstrates
  rw [after, refusal] at chose
  have notMore : repaid.card ≤ claim.card := count ▸ nonPositive
  have kept := present_sum_preferred_to_less presentPlan futurePlan
    promisedPlan sum claim money repaid soon late spend timePreference power
    pays sooner claimIn repaidIn notMore homogeneous moreMoney alike buysMore
    isMoney free chain
  exact asymmetric.asym _ _ kept chose

/-- **Every rate struck is positive** (S5), with the count carried as
`SameCount`. -/
theorem struck_rate_positive
    (exchange : Exchange praxis.toActionFrame)
    {present future promised : Stock praxis.toActionFrame exchange.first.agent
      exchange.first.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money repaid : Finset praxis.Means) (soon late : praxis.End)
    (spend : praxis.Time)
    (timePreference : TimePreference praxis.toDatedFrame exchange.first.agent
      exchange.first.time)
    (power : SamePurchasingPowerOf presentPlan promisedPlan sum money soon late)
    (pays : ClaimPaysOf futurePlan promisedPlan claim money)
    (sooner : SpentSooner (praxis := praxis) (now := exchange.first.time)
      soon late)
    (count : SameCount sum claim)
    (claimIn : claim ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferredWhenSpent futurePlan spend)
    (alike : RankedAlikeNowOf futurePlan spend claim repaid)
    (buysMore : BuysMoreThanItsParts futurePlan claim)
    (isMoney : ∀ unit ∈ claim, praxis.Money unit)
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
  Nat.lt_of_not_le fun nonPositive =>
    no_loan_at_nonpositive_rate exchange.first presentPlan futurePlan
      promisedPlan sum claim money repaid soon late spend timePreference power
      pays sooner count claimIn repaidIn nonPositive homogeneous moreMoney
      alike buysMore isMoney free chain asymmetric (voluntary.trans before)
      after demonstrated

end Loans

#print axioms split_of_both
#print axioms both_of_split
#print axioms present_sum_preferred
#print axioms present_sum_preferred_to_less
#print axioms no_loan_at_zero_rate
#print axioms no_loan_at_nonpositive_rate
#print axioms struck_rate_positive

end CountApart
end ApodicticDraft

#lint only unusedArguments
