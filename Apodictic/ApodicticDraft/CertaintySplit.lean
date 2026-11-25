import ApodicticDraft.Interest

/-!
# Certainty apart from purchasing power — a rival encoding

In `ApodicticDraft.Money` one condition, `SamePurchasingPower`, carries
two things reality pulls apart: that the claim is paid, and that the
money it pays buys the same satisfaction as the present sum. A rate
that fails it cannot say which of the two failed.

This module cuts them apart without changing any theorem of
`ApodicticDraft.Interest`. It adds a third stock, judged at `now` like
the other two: the money the claim promises, as the agent would spend
it were it in hand at the later date.

- `ClaimPays`: the agent counts the claim for exactly what he counts
  the promised money for, unit for unit. Certainty of payment.
- `SamePurchasingPower`, now asserted between the present sum and the
  PROMISED MONEY, not the claim: what money buys at the two dates.
- `samePurchasingPower_of_claimPays`: the two together give the merged
  condition, so every theorem of the chain applies with the two named
  separately. `present_sum_preferred_split` shows the signature for S2.

## Shape claims (audit)

- The third stock is not a holding at a later time. Like the stock of
  claims, its units are on offer at `now`, and its plan is the agent's
  plan at `now`. No stock is indexed by a later time here either.
- Certainty is read as how the agent counts the claim at `now`, not as
  what later happens. A claim he believes may not pay is one whose plan
  differs from the plan for the money it promises.
- Each condition failing alone, with the merged one failing in both:
  `ApodicticDraft.CertaintySplitToy` (default risk; inflation).
-/

namespace ApodicticDraft
namespace CertaintySplit

open Apodictic

section Sums

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future promised : Stock praxis.toActionFrame agent now}

/-- **The claim pays** — a condition on the situation: Rothbard's world
of certainty, for one claim. The claim is for as many units as the
money it promises, and the agent's plan counts the claim for exactly
what it counts that money for.

It fails where he believes the claim may not pay, or may pay in part:
the claim then counts for something other than the promised money
would buy. The credit premium lands here, and only here. -/
def ClaimPays (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (claim money : Finset praxis.Means) : Prop :=
  claim.card = money.card ∧
    futurePlan.wouldServe claim = promisedPlan.wouldServe money

/-- **The two conditions give the merged one.** Same purchasing power
between the present sum and the promised money, and a claim that pays,
give `SamePurchasingPower` between the present sum and the claim. -/
theorem samePurchasingPower_of_claimPays
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money : Finset praxis.Means) (soon late : praxis.End)
    (power : SamePurchasingPower presentPlan promisedPlan sum money soon late)
    (pays : ClaimPays futurePlan promisedPlan claim money) :
    SamePurchasingPower presentPlan futurePlan sum claim soon late := by
  obtain ⟨sameCount, buysSoon, buysLate, same⟩ := power
  obtain ⟨paidInFull, countsAsMoney⟩ := pays
  exact ⟨sameCount.trans paidInFull.symm, buysSoon,
    countsAsMoney.trans buysLate, same⟩

/-- **Present money is preferred to the same amount of future money**
(S2), with certainty and purchasing power named apart. -/
theorem present_sum_preferred_split
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame agent now)
    (power : SamePurchasingPower presentPlan promisedPlan sum money soon late)
    (pays : ClaimPays futurePlan promisedPlan claim money)
    (sooner : SpentSooner (praxis := praxis) (now := now) soon late) :
    praxis.Prefers agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe claim) :=
  Interest.present_sum_preferred presentPlan futurePlan sum claim soon late
    timePreference
    (samePurchasingPower_of_claimPays presentPlan futurePlan promisedPlan
      sum claim money soon late power pays)
    sooner

end Sums

#print axioms samePurchasingPower_of_claimPays
#print axioms present_sum_preferred_split

end CertaintySplit
end ApodicticDraft

#lint only unusedArguments
