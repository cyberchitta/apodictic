import ApodicticDraft.Satiation

/-!
# Without the money label — what the restriction to money still does

The owner's I-4 ruling cut Rothbard's general rule to money, because
satiation and the cost of holding refute it for other goods. Both are
now named conditions (`BuysMoreThanItsParts`,
`MoneyFrame.FreeToHold`). This module rebuilds S3–S5 on
`MorePreferredWhereDiffers`, the weak claim without "money", to test
whether the restriction still does any work.

## What is proved

- `labelled_of_unlabelled`: the unlabelled claim gives the labelled
  one. So it asserts at least as much, and every theorem in
  `ApodicticDraft.Satiation` follows from it.
- `present_sum_preferred_to_less_unlabelled` (S3),
  `no_loan_at_nonpositive_rate_unlabelled` (S4),
  `struck_rate_positive_unlabelled` (S5): the same conclusions with no
  hypothesis that any unit is money.

So the label was used only to enter the claim. What it bought is
scope: the labelled claim is silent about every good that is not
money, and the unlabelled one is not.
-/

namespace ApodicticDraft
namespace NoMoneyLabel

open Apodictic Interest Satiation

section Plans

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {stock : Stock praxis.toActionFrame agent now}

/-- The unlabelled claim gives the labelled one. -/
theorem labelled_of_unlabelled (plan : AllocationPlan stock)
    (more : MorePreferredWhereDiffers plan) :
    MoreMoneyPreferredWhereDiffers plan :=
  ⟨fun fewer larger part inStock _ freeFewer freeMore differ =>
    more.more fewer larger part inStock freeFewer freeMore differ⟩

end Plans

section Sums

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future : Stock praxis.toActionFrame agent now}

/-- **One ounce of present money is preferred to one ounce or less of
future money** (S3), with `MorePreferredWhereDiffers`: no unit need be money. -/
theorem present_sum_preferred_to_less_unlabelled
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum claim lesser : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame agent now)
    (power : SamePurchasingPower presentPlan futurePlan sum claim soon late)
    (sooner : SpentSooner (praxis := praxis) (now := now) soon late)
    (claimIn : claim ⊆ future.units) (lesserIn : lesser ⊆ future.units)
    (notMore : lesser.card ≤ claim.card)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MorePreferredWhereDiffers futurePlan)
    (buysMore : BuysMoreThanItsParts futurePlan claim)
    (free : FreeToHoldWithin (agent := agent) (now := now) claim)
    (chain : praxis.TransitiveOn agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe claim) ↑(futurePlan.wouldServe lesser)) :
    praxis.Prefers agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe lesser) := by
  have overSame := present_sum_preferred presentPlan futurePlan sum claim
    soon late timePreference power sooner
  rcases Nat.eq_or_lt_of_le notMore with equal | fewer
  · rw [homogeneous lesser lesserIn claim claimIn equal]
    exact overSame
  · obtain ⟨part, partIn, partCard⟩ :=
      exists_part_of_card claim lesser.card (Nat.le_of_lt fewer)
    have alike : futurePlan.wouldServe part = futurePlan.wouldServe lesser :=
      homogeneous part (fun _ h => claimIn (partIn h)) lesser lesserIn partCard
    have proper : part ⊂ claim := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨partIn, fun same => ?_⟩
      rw [same] at partCard
      rw [partCard] at fewer
      exact Nat.lt_irrefl _ fewer
    have overLess := moreMoney.more part claim proper claimIn
      (free part partIn) (free claim (fun _ h => h)) (buysMore part proper)
    rw [alike] at overLess
    exact chain overSame overLess

end Sums

section Loans

variable {praxis : MoneyFrame}

/-- **At a rate not above zero, he does not lend** (S4), with
`MorePreferredWhereDiffers`: no unit need be money. -/
theorem no_loan_at_nonpositive_rate_unlabelled
    (trade : Trade praxis.toActionFrame)
    {present future : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum claim repaid : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame trade.agent trade.time)
    (power : SamePurchasingPower presentPlan futurePlan sum claim soon late)
    (sooner : SpentSooner (praxis := praxis) (now := trade.time) soon late)
    (count : SameCount sum claim)
    (claimIn : claim ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (nonPositive : repaid.card ≤ sum.card)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MorePreferredWhereDiffers futurePlan)
    (buysMore : BuysMoreThanItsParts futurePlan claim)
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
  have kept := present_sum_preferred_to_less_unlabelled presentPlan
    futurePlan sum claim repaid soon late timePreference power sooner claimIn
    repaidIn notMore homogeneous moreMoney buysMore free chain
  exact asymmetric.asym _ _ kept chose

/-- **Every rate struck is positive** (S5), with
`MorePreferredWhereDiffers`: no unit need be money. -/
theorem struck_rate_positive_unlabelled
    (exchange : Exchange praxis.toActionFrame)
    {present future : Stock praxis.toActionFrame exchange.first.agent
      exchange.first.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum claim repaid : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame exchange.first.agent
      exchange.first.time)
    (power : SamePurchasingPower presentPlan futurePlan sum claim soon late)
    (sooner : SpentSooner (praxis := praxis) (now := exchange.first.time)
      soon late)
    (count : SameCount sum claim)
    (claimIn : claim ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MorePreferredWhereDiffers futurePlan)
    (buysMore : BuysMoreThanItsParts futurePlan claim)
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
    no_loan_at_nonpositive_rate_unlabelled exchange.first presentPlan
      futurePlan sum claim repaid soon late timePreference power sooner count claimIn
      repaidIn nonPositive homogeneous moreMoney buysMore free chain
      asymmetric (voluntary.trans before) after demonstrated

end Loans

#print axioms labelled_of_unlabelled
#print axioms present_sum_preferred_to_less_unlabelled
#print axioms no_loan_at_nonpositive_rate_unlabelled
#print axioms struck_rate_positive_unlabelled

end NoMoneyLabel
end ApodicticDraft

#lint only unusedArguments
