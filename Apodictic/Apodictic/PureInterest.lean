import Apodictic.Praxeology
import Apodictic.TimePreference

/-!
# Pure interest — the pure time-preference theory of interest

Rothbard's conclusion (*MES* p. 382): "every man’s time preference is
positive, i.e., one ounce of present money will always be preferred to
one ounce or less of future money. Therefore, there will never be any
question of a zero or negative pure interest rate."

## What is proved, and what it costs

- `present_sum_preferred` (S2): present money over the same amount of
  future money. `TimePreference`, plus three conditions: the present
  sum and the money the claim promises buy the same satisfaction
  (`SamePurchasingPower`), the claim pays (`ClaimPays`), and the
  present sum would be spent sooner (`SpentSooner`).
- `present_sum_preferred_to_less` (S3): "one ounce or less". Adds the
  claim `MoreMoneyPreferredWhenSpent`, and conditions: the future units
  are interchangeable (`Homogeneous`), the claim buys more than its
  parts, the claim and the lesser sum are ranked now as at the
  spending, the claim is money and free to hold, and transitivity on
  the one chain.
- `no_loan_at_zero_rate`: a loan repaying exactly the sum lent
  demonstrates no preference. Neither "more money is preferred" nor
  any condition on satiation or on valuations at the spending is used.
- `no_loan_at_nonpositive_rate` (S4): a loan at a rate not above zero
  demonstrates no preference — under `DemonstratedPreference`, it is
  not made. Adds `AsymmetricPreference`, two conditions tying the
  trade's holdings to the sums, and `SameCount`: the claim is as many
  units as the sum lent. S2 and S3 carry no count between the present
  sum and the claim; S3's only count is the lesser sum against the
  claim.
- `struck_rate_positive` (S5): in a voluntary exchange the lender
  demonstrates a preference in, the repaid sum is larger than the sum
  lent. Only the lender's side is used.

- Rejected readings of "more money is preferred":
  `MoreMoneyPreferredUnrestricted`, which with asymmetry asserts that
  money never satiates (`buysMore_of_unrestricted`), and
  `MoreMoneyPreferredNow`, refuted by a man whose valuations change
  (`Apodictic.Model.Impulse`).

Only a negative rate needs "more money is preferred". Nothing here
needs a property of `Before`, and no classical step: the one case
split is `≤` on ℕ.
-/

namespace Apodictic
namespace PureInterest

section Sums

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future promised : Stock praxis.toActionFrame agent now}

/-- Same purchasing power with the promised money, and a claim that
pays, give the same between the present sum and the claim. -/
theorem samePurchasingPower_of_claimPays
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money : Finset praxis.Means) (soon late : praxis.End)
    (power : SamePurchasingPower presentPlan promisedPlan sum money soon late)
    (pays : ClaimPays futurePlan promisedPlan claim money) :
    SamePurchasingPower presentPlan futurePlan sum claim soon late := by
  obtain ⟨buysSoon, buysLate, same⟩ := power
  exact ⟨buysSoon, pays.trans buysLate, same⟩

/-- **Present money is preferred to the same amount of future money**
(S2; *MES* p. 376: "It follows from the law of time preference that
present money is worth more than present expectations of the same
amount of future money").

"The same amount" does no work here, and no count is carried: what
the sums would buy does (`SamePurchasingPower`), and that the claim
pays (`ClaimPays`). The count enters with the loans (`SameCount`). And the
conclusion needs the present sum to be spent sooner — the case
Rothbard's n. 11 sets aside. -/
theorem present_sum_preferred
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame agent now)
    (power : SamePurchasingPower presentPlan promisedPlan sum money soon late)
    (pays : ClaimPays futurePlan promisedPlan claim money)
    (sooner : SpentSooner (praxis := praxis) (now := now) soon late) :
    praxis.Prefers agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe claim) := by
  obtain ⟨buysSoon, buysLate, same⟩ :=
    samePurchasingPower_of_claimPays presentPlan futurePlan promisedPlan sum
      claim money soon late power pays
  obtain ⟨before, notPast⟩ := sooner
  rw [buysSoon, buysLate, coe_single, coe_single]
  exact timePreference.sooner soon late same before notPast

/-- **One ounce of present money is preferred to one ounce or less of
future money** (S3; *MES* p. 382: "one ounce of present money will
always be preferred to one ounce or less of future money").

`claim` is a future sum that buys what `sum` buys, of any size: no
count ties the two. `lesser` is any future sum no larger than `claim`,
so "or less" is measured against the claim, and against the present
sum only where `SameCount` is added, as in the loans. "Or less" chains S2 with
`MoreMoneyPreferredWhenSpent` on the future sums, and that chain is the
one place transitivity is needed. Interchangeability of the future
units carries a sum of any units to a part of `claim` of the same
size. -/
theorem present_sum_preferred_to_less
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money lesser : Finset praxis.Means) (soon late : praxis.End)
    (spend : praxis.Time)
    (timePreference : TimePreference praxis.toDatedFrame agent now)
    (power : SamePurchasingPower presentPlan promisedPlan sum money soon late)
    (pays : ClaimPays futurePlan promisedPlan claim money)
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

/-- **At a rate of exactly zero, he does not lend** — a loan repaying
exactly the sum lent demonstrates no preference. Neither "more money is
preferred" nor any condition on satiation or on valuations at the
spending is used: time preference and asymmetry carry it, with
purchasing power, a claim that pays, the present sum spent sooner, the
claim's count, interchangeable units and the two conditions on the
trade. -/
theorem no_loan_at_zero_rate
    (trade : Trade praxis.toActionFrame)
    {present future promised : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money repaid : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame trade.agent trade.time)
    (power : SamePurchasingPower presentPlan promisedPlan sum money soon late)
    (pays : ClaimPays futurePlan promisedPlan claim money)
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

/-- **At a rate not above zero, he does not lend** (S4; *MES* p. 386:
"at some minimum rate of interest the man will not save at all"; "A man
could not prefer 10 ounces or even less of future money to 10 ounces of
present money").

A loan — present `sum` given, a claim to `repaid` got — whose repaid
sum is no larger than the sum lent demonstrates no preference: if
`DemonstratedPreference` held of it, the lender would prefer the claim
to the kept sum, and S3 with asymmetry forbids that. Stated as the
negation of the bridge, since nothing in the library says a trade was
made except that the bridge is asserted of it. -/
theorem no_loan_at_nonpositive_rate
    (trade : Trade praxis.toActionFrame)
    {present future promised : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (sum claim money repaid : Finset praxis.Means) (soon late : praxis.End)
    (spend : praxis.Time)
    (timePreference : TimePreference praxis.toDatedFrame trade.agent trade.time)
    (power : SamePurchasingPower presentPlan promisedPlan sum money soon late)
    (pays : ClaimPays futurePlan promisedPlan claim money)
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

/-- **Every rate struck is positive** (S5) — in an exchange of present
money for a claim to future money, voluntary on the lender's side and
demonstrating his preference, the repaid sum is larger than the sum
lent.

Bilateral in form, one-sided in content: only the lender's trade
(`exchange.first`) is used, and nothing about the borrower. No market,
no aggregation, no equilibrium. `Voluntary` is what makes the lender's
alternative the sum he held; whatever set the price does not enter. -/
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
    (power : SamePurchasingPower presentPlan promisedPlan sum money soon late)
    (pays : ClaimPays futurePlan promisedPlan claim money)
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

section Rejected

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {stock : Stock praxis.toActionFrame agent now}

/-- "More money is preferred", as Rothbard's general rule states it
(*MES* p. 379: "more of a good will have greater utility than less of
it"), cut to money free to hold: of two sums of money, one part of the
other, the larger is preferred at `now`, whatever each would buy.
REJECTED as the library's claim; stated so the rejection is checked
(`buysMore_of_unrestricted`). -/
def MoreMoneyPreferredUnrestricted (plan : AllocationPlan stock) : Prop :=
  ∀ fewer more : Finset praxis.Means, fewer ⊂ more → more ⊆ stock.units →
    (∀ unit ∈ more, praxis.Money unit) →
    praxis.FreeToHold agent now fewer → praxis.FreeToHold agent now more →
      praxis.Prefers agent now ↑(plan.wouldServe more) ↑(plan.wouldServe fewer)

/-- "More money is preferred", restricted to sums whose purchases
differ, but ranked at `now` rather than at the date the sums would be
spent. REJECTED as the library's claim: a man whose valuations change
between now and the spending refutes it while the dated claim holds of
him (`Apodictic.Model.Impulse.now_reading_fails`). -/
def MoreMoneyPreferredNow (plan : AllocationPlan stock) : Prop :=
  ∀ fewer more : Finset praxis.Means, fewer ⊂ more → more ⊆ stock.units →
    (∀ unit ∈ more, praxis.Money unit) →
    praxis.FreeToHold agent now fewer → praxis.FreeToHold agent now more →
    plan.wouldServe more ≠ plan.wouldServe fewer →
      praxis.Prefers agent now ↑(plan.wouldServe more) ↑(plan.wouldServe fewer)

/-- **The unrestricted rule says money never satiates.** With
asymmetry, it gives `BuysMoreThanItsParts` of every free sum of money:
were a strict part to buy what the whole buys, the rule would have the
agent prefer one bundle to itself, which asymmetry forbids. So the rule
as stated asserts, unseen, that every extra unit of free money buys
something more. The library's claim ranks only purchases that differ,
and the theorems that need non-satiation carry it as a condition. -/
theorem buysMore_of_unrestricted (plan : AllocationPlan stock)
    (rule : MoreMoneyPreferredUnrestricted plan)
    (asymmetric : AsymmetricPreference praxis.toActionFrame agent now)
    (claim : Finset praxis.Means) (claimIn : claim ⊆ stock.units)
    (isMoney : ∀ unit ∈ claim, praxis.Money unit)
    (free : FreeToHoldWithin (agent := agent) (now := now) claim) :
    BuysMoreThanItsParts plan claim := by
  intro part proper same
  have overPart := rule part claim proper claimIn isMoney
    (free part proper.1) (free claim (fun _ h => h))
  rw [same] at overPart
  exact asymmetric.asym _ _ overPart overPart

/-- Where the sums would be spent at `now`, the undated reading gives
the dated claim: dating the claim at the spending asserts no more where
nothing is deferred. -/
theorem whenSpent_of_now (plan : AllocationPlan stock)
    (rule : MoreMoneyPreferredNow plan) :
    MoreMoneyPreferredWhenSpent plan now :=
  ⟨rule⟩

end Rejected

#print axioms exists_part_of_card
#print axioms coe_single
#print axioms samePurchasingPower_of_claimPays
#print axioms present_sum_preferred
#print axioms present_sum_preferred_to_less
#print axioms no_loan_at_zero_rate
#print axioms no_loan_at_nonpositive_rate
#print axioms struck_rate_positive
#print axioms buysMore_of_unrestricted
#print axioms whenSpent_of_now

end PureInterest
end Apodictic

#lint only unusedArguments
