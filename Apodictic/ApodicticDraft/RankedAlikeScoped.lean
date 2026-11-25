import ApodicticDraft.ValuedAlike

/-!
# Ranked alike, scoped to the one comparison a theorem makes

`RankedAlikeNow` (in `ApodicticDraft.ValuedAlike`) asks that the
agent's ranking at the spending be his ranking at `now` for every pair
of sums in the stock, one part of the other. S3–S5 use it once: for
the claim against the lesser sum (the repayment, in S4 and S5). This
module names only that step, as the condition `RankedAlikeNowOf`, a
rival to `RankedAlikeNow`.

## What is proved

- `rankedAlikeOf_of_rankedAlike`: the stock-wide condition gives the
  scoped one, with interchangeable units and asymmetry at the spending.
  So the scoped condition asks no more.
- S3, S4, S5 with the dated claim and the scoped condition
  (`present_sum_preferred_to_less_scoped`,
  `no_loan_at_nonpositive_rate_scoped`, `struck_rate_positive_scoped`).
- `ImpulseToy.not_rankedAlikeOf`: the man whose valuations change fails
  the scoped condition too, for his ounce against no cash. The failure
  still lands on a condition.

Not built: a case where the scoped condition holds and the stock-wide
one fails, which would show that the scoped one asks strictly less.
-/

namespace ApodicticDraft
namespace ValuedAlike

open Apodictic Interest Satiation

section Plans

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {stock : Stock praxis.toActionFrame agent now}

/-- **Ranked alike now, of one comparison** — a condition on the
situation, NOT a claim. If at the date `spend` the agent would spend
them he ranks what `claim` would buy above what `lesser` would buy, he
ranks them so at `now` too. His valuation of these two purchases does
not change in between. Mises: "If the valuations change, acting must
change also" (*Human Action*, ch. V, §4). It fails for the man who now
prefers to be repaid less because of what he would do with more. -/
def RankedAlikeNowOf (plan : AllocationPlan stock) (spend : praxis.Time)
    (claim lesser : Finset praxis.Means) : Prop :=
  praxis.Prefers agent spend ↑(plan.wouldServe claim) ↑(plan.wouldServe lesser) →
    praxis.Prefers agent now ↑(plan.wouldServe claim) ↑(plan.wouldServe lesser)

/-- The stock-wide condition gives the scoped one. -/
theorem rankedAlikeOf_of_rankedAlike (plan : AllocationPlan stock)
    (spend : praxis.Time) (claim lesser : Finset praxis.Means)
    (claimIn : claim ⊆ stock.units) (lesserIn : lesser ⊆ stock.units)
    (notMore : lesser.card ≤ claim.card)
    (homogeneous : plan.Homogeneous)
    (asymmetric : AsymmetricPreference praxis.toActionFrame agent spend)
    (alike : RankedAlikeNow plan spend) :
    RankedAlikeNowOf plan spend claim lesser := by
  intro atSpend
  rcases Nat.eq_or_lt_of_le notMore with equal | fewer
  · rw [homogeneous lesser lesserIn claim claimIn equal] at atSpend
    exact (asymmetric.asym _ _ atSpend atSpend).elim
  · obtain ⟨part, partIn, partCard⟩ :=
      exists_part_of_card claim lesser.card (Nat.le_of_lt fewer)
    have same : plan.wouldServe part = plan.wouldServe lesser :=
      homogeneous part (fun _ h => claimIn (partIn h)) lesser lesserIn partCard
    have proper : part ⊂ claim := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨partIn, fun equal => ?_⟩
      rw [equal] at partCard
      rw [partCard] at fewer
      exact Nat.lt_irrefl _ fewer
    rw [← same] at atSpend ⊢
    exact alike part claim proper claimIn atSpend

end Plans

section Sums

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future : Stock praxis.toActionFrame agent now}

/-- **S3**, with the claim dated at the spending and the condition that
the claim and the lesser sum are ranked alike now. -/
theorem present_sum_preferred_to_less_scoped
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
    (alike : RankedAlikeNowOf futurePlan spend claim lesser)
    (buysMore : BuysMoreThanItsParts futurePlan claim)
    (money : ∀ unit ∈ claim, praxis.Money unit)
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
    have same : futurePlan.wouldServe part = futurePlan.wouldServe lesser :=
      homogeneous part (fun _ h => claimIn (partIn h)) lesser lesserIn partCard
    have proper : part ⊂ claim := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨partIn, fun equal => ?_⟩
      rw [equal] at partCard
      rw [partCard] at fewer
      exact Nat.lt_irrefl _ fewer
    have atSpend := moreMoney.more part claim proper claimIn money
      (free part partIn) (free claim (fun _ h => h)) (buysMore part proper)
    rw [same] at atSpend
    exact chain overSame (alike atSpend)

end Sums

section Loans

variable {praxis : MoneyFrame}

/-- **S4**, with the claim dated at the spending and the scoped
condition, of the claim against the repayment. -/
theorem no_loan_at_nonpositive_rate_scoped
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
    (alike : RankedAlikeNowOf futurePlan spend claim repaid)
    (buysMore : BuysMoreThanItsParts futurePlan claim)
    (money : ∀ unit ∈ claim, praxis.Money unit)
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
  have notMore : repaid.card ≤ claim.card := power.1 ▸ nonPositive
  have kept := present_sum_preferred_to_less_scoped presentPlan futurePlan sum
    claim repaid soon late spend timePreference power sooner claimIn repaidIn
    notMore homogeneous moreMoney alike buysMore money free chain
  exact asymmetric.asym _ _ kept chose

/-- **S5**, with the claim dated at the spending and the scoped
condition, of the claim against the repayment. -/
theorem struck_rate_positive_scoped
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
    (alike : RankedAlikeNowOf futurePlan spend claim repaid)
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
  Nat.lt_of_not_le fun nonPositive =>
    no_loan_at_nonpositive_rate_scoped exchange.first presentPlan futurePlan
      sum claim repaid soon late spend timePreference power sooner claimIn
      repaidIn nonPositive homogeneous moreMoney alike buysMore money free
      chain asymmetric (voluntary.trans before) after demonstrated

end Loans

namespace ImpulseToy

/-- **The scoped condition fails too**: at date 1 he ranks what an
ounce buys above what no cash buys, and at date 0 he does not. -/
theorem not_rankedAlikeOf :
    ¬ RankedAlikeNowOf (praxis := frame) plan (1 : ℕ) {.ounce} ∅ := by
  intro alike
  have now := alike (by
    rw [buys_empty, buys_ounce]
    exact Or.inr ⟨rfl, coe_single impulse, coe_none⟩)
  rw [buys_empty, buys_ounce] at now
  rcases now with ⟨_, hX, _⟩ | ⟨one, _, _⟩
  · exact impulse_ne_empty (by rw [← coe_single]; exact hX)
  · exact Nat.zero_ne_one one

end ImpulseToy

#print axioms rankedAlikeOf_of_rankedAlike
#print axioms present_sum_preferred_to_less_scoped
#print axioms no_loan_at_nonpositive_rate_scoped
#print axioms struck_rate_positive_scoped
#print axioms ImpulseToy.not_rankedAlikeOf

end ValuedAlike
end ApodicticDraft

#lint only unusedArguments
