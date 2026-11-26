import ApodicticDraft.Interest

/-!
# Satiation — what `MoreMoneyPreferred` asserts beyond "more is better"

`MoreMoneyPreferred` concludes a strict preference between what two
sums would buy, and nothing makes the two purchases differ. Where an
extra unit would buy nothing else, the claim still ranks the purchase
above itself; with `AsymmetricPreference` that is a contradiction. So
the claim and asymmetry together assert that every extra unit of free
money buys something else: non-satiation, carried by no signature.

This module cuts it out. `MoreMoneyPreferredWhereDiffers` (in
`ApodicticDraft.Claims`) ranks only purchases that differ, and that
they differ is the library's condition `BuysMoreThanItsParts`, on the
theorems that need it.

## What is proved

- `buysMore_of_strong`: the old claim, with asymmetry, gives the
  condition. This is the hidden assertion, built.
- `weak_of_strong`: the old claim gives the weak one. So every theorem
  below follows from the old claim with asymmetry, and the weak
  version asserts no more.
- `present_sum_preferred_to_less_where_differs` (S3),
  `no_loan_at_nonpositive_rate_where_differs` (S4),
  `struck_rate_positive_where_differs` (S5): the same conclusions, with
  the weak claim and the condition in place of the old claim.
- `no_loan_at_zero_rate`: a loan repaying exactly the sum lent needs
  neither claim nor condition. Only a negative rate needs "more money
  is preferred", and with it non-satiation.

The converse of `weak_of_strong` is not proved: getting the old claim
back from the weak one needs excluded middle on whether two purchases
are equal, which the library does not assume.
-/

namespace ApodicticDraft
namespace Satiation

open Apodictic Interest

section Plans

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {stock : Stock praxis.toActionFrame agent now}

/-- The old claim gives the weak one. -/
theorem weak_of_strong (plan : AllocationPlan stock)
    (moreMoney : MoreMoneyPreferred plan) :
    MoreMoneyPreferredWhereDiffers plan :=
  ⟨fun fewer more part inStock money freeFewer freeMore _ =>
    moreMoney.more fewer more part inStock money freeFewer freeMore⟩

/-- **The hidden assertion** — the old claim, with asymmetry, says that
every strict part of a free sum of money buys other ends than the sum. -/
theorem buysMore_of_strong (plan : AllocationPlan stock)
    (moreMoney : MoreMoneyPreferred plan)
    (asymmetric : AsymmetricPreference praxis.toActionFrame agent now)
    (promise : Finset praxis.Means) (promiseIn : promise ⊆ stock.units)
    (money : ∀ unit ∈ promise, praxis.Money unit)
    (free : FreeToHoldWithin (agent := agent) (now := now) promise) :
    BuysMoreThanItsParts plan promise := by
  intro part proper same
  have overPart := moreMoney.more part promise proper promiseIn money
    (free part proper.1) (free promise (fun _ h => h))
  rw [same] at overPart
  exact asymmetric.asym _ _ overPart overPart

end Plans

section Sums

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future : Stock praxis.toActionFrame agent now}

/-- **One ounce of present money is preferred to one ounce or less of
future money** (S3), with the weak claim and the condition that the
future sum buys more than its parts in place of `MoreMoneyPreferred`. -/
theorem present_sum_preferred_to_less_where_differs
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum promise lesser : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame agent now)
    (power : SamePurchasingPower presentPlan futurePlan sum promise soon late)
    (sooner : SpentSooner (praxis := praxis) (now := now) soon late)
    (promiseIn : promise ⊆ future.units) (lesserIn : lesser ⊆ future.units)
    (notMore : lesser.card ≤ promise.card)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferredWhereDiffers futurePlan)
    (buysMore : BuysMoreThanItsParts futurePlan promise)
    (money : ∀ unit ∈ promise, praxis.Money unit)
    (free : FreeToHoldWithin (agent := agent) (now := now) promise)
    (chain : praxis.TransitiveOn agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe promise) ↑(futurePlan.wouldServe lesser)) :
    praxis.Prefers agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe lesser) := by
  have overSame := present_sum_preferred presentPlan futurePlan sum promise
    soon late timePreference power sooner
  rcases Nat.eq_or_lt_of_le notMore with equal | fewer
  · rw [homogeneous lesser lesserIn promise promiseIn equal]
    exact overSame
  · obtain ⟨part, partIn, partCard⟩ :=
      exists_part_of_card promise lesser.card (Nat.le_of_lt fewer)
    have alike : futurePlan.wouldServe part = futurePlan.wouldServe lesser :=
      homogeneous part (fun _ h => promiseIn (partIn h)) lesser lesserIn partCard
    have proper : part ⊂ promise := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨partIn, fun same => ?_⟩
      rw [same] at partCard
      rw [partCard] at fewer
      exact Nat.lt_irrefl _ fewer
    have overLess := moreMoney.more part promise proper promiseIn money
      (free part partIn) (free promise (fun _ h => h)) (buysMore part proper)
    rw [alike] at overLess
    exact chain overSame overLess

end Sums

section Loans

variable {praxis : MoneyFrame}

/-- **At a rate of exactly zero, he does not lend** — a loan repaying
exactly the sum lent demonstrates no preference. Neither "more money is
preferred" nor any condition on satiation is used: time preference,
equal purchasing power and interchangeable units carry it alone. -/
theorem no_loan_at_zero_rate
    (trade : Trade praxis.toActionFrame)
    {present future : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum promise repaid : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame trade.agent trade.time)
    (power : SamePurchasingPower presentPlan futurePlan sum promise soon late)
    (sooner : SpentSooner (praxis := praxis) (now := trade.time) soon late)
    (count : SameCount sum promise)
    (promiseIn : promise ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (zero : repaid.card = sum.card)
    (homogeneous : futurePlan.Homogeneous)
    (asymmetric : AsymmetricPreference praxis.toActionFrame trade.agent trade.time)
    (refusal : trade.RefusalKeepsSum presentPlan sum)
    (after : trade.AfterCountsAsPlanned futurePlan repaid) :
    ¬ DemonstratedPreference trade := by
  intro demonstrated
  have chose := demonstrated.demonstrates
  rw [after, refusal] at chose
  have equal : repaid.card = promise.card := count ▸ zero
  have kept := present_sum_preferred presentPlan futurePlan sum promise
    soon late timePreference power sooner
  rw [← homogeneous repaid repaidIn promise promiseIn equal] at kept
  exact asymmetric.asym _ _ kept chose

/-- **At a rate not above zero, he does not lend** (S4), with the weak
claim and the condition in place of `MoreMoneyPreferred`. -/
theorem no_loan_at_nonpositive_rate_where_differs
    (trade : Trade praxis.toActionFrame)
    {present future : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum promise repaid : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame trade.agent trade.time)
    (power : SamePurchasingPower presentPlan futurePlan sum promise soon late)
    (sooner : SpentSooner (praxis := praxis) (now := trade.time) soon late)
    (count : SameCount sum promise)
    (promiseIn : promise ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (nonPositive : repaid.card ≤ sum.card)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferredWhereDiffers futurePlan)
    (buysMore : BuysMoreThanItsParts futurePlan promise)
    (money : ∀ unit ∈ promise, praxis.Money unit)
    (free : FreeToHoldWithin (agent := trade.agent) (now := trade.time) promise)
    (chain : praxis.TransitiveOn trade.agent trade.time
      ↑(presentPlan.wouldServe sum) ↑(futurePlan.wouldServe promise)
      ↑(futurePlan.wouldServe repaid))
    (asymmetric : AsymmetricPreference praxis.toActionFrame trade.agent trade.time)
    (refusal : trade.RefusalKeepsSum presentPlan sum)
    (after : trade.AfterCountsAsPlanned futurePlan repaid) :
    ¬ DemonstratedPreference trade := by
  intro demonstrated
  have chose := demonstrated.demonstrates
  rw [after, refusal] at chose
  have notMore : repaid.card ≤ promise.card := count ▸ nonPositive
  have kept := present_sum_preferred_to_less_where_differs presentPlan
    futurePlan sum promise repaid soon late timePreference power sooner promiseIn
    repaidIn notMore homogeneous moreMoney buysMore money free chain
  exact asymmetric.asym _ _ kept chose

/-- **Every rate struck is positive** (S5), with the weak claim and the
condition in place of `MoreMoneyPreferred`. -/
theorem struck_rate_positive_where_differs
    (exchange : Exchange praxis.toActionFrame)
    {present future : Stock praxis.toActionFrame exchange.first.agent
      exchange.first.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum promise repaid : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame exchange.first.agent
      exchange.first.time)
    (power : SamePurchasingPower presentPlan futurePlan sum promise soon late)
    (sooner : SpentSooner (praxis := praxis) (now := exchange.first.time)
      soon late)
    (count : SameCount sum promise)
    (promiseIn : promise ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferredWhereDiffers futurePlan)
    (buysMore : BuysMoreThanItsParts futurePlan promise)
    (money : ∀ unit ∈ promise, praxis.Money unit)
    (free : FreeToHoldWithin (agent := exchange.first.agent)
      (now := exchange.first.time) promise)
    (chain : praxis.TransitiveOn exchange.first.agent exchange.first.time
      ↑(presentPlan.wouldServe sum) ↑(futurePlan.wouldServe promise)
      ↑(futurePlan.wouldServe repaid))
    (asymmetric : AsymmetricPreference praxis.toActionFrame
      exchange.first.agent exchange.first.time)
    (voluntary : exchange.first.Voluntary)
    (before : exchange.first.BeforeCountsAsPlanned presentPlan sum)
    (after : exchange.first.AfterCountsAsPlanned futurePlan repaid)
    (demonstrated : DemonstratedPreference exchange.first) :
    sum.card < repaid.card :=
  Nat.lt_of_not_le fun nonPositive =>
    no_loan_at_nonpositive_rate_where_differs exchange.first presentPlan
      futurePlan sum promise repaid soon late timePreference power sooner count promiseIn
      repaidIn nonPositive homogeneous moreMoney buysMore money free chain
      asymmetric (voluntary.trans before) after demonstrated

end Loans

#print axioms weak_of_strong
#print axioms buysMore_of_strong
#print axioms present_sum_preferred_to_less_where_differs
#print axioms no_loan_at_zero_rate
#print axioms no_loan_at_nonpositive_rate_where_differs
#print axioms struck_rate_positive_where_differs

end Satiation
end ApodicticDraft

#lint only unusedArguments
