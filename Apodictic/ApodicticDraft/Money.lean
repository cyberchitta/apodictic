import Apodictic

/-!
# Money — the draft vocabulary of the time market (T1)

Definitions ONLY: this file asserts nothing. The one unruled claim the
T1 theorems carry, `MoreMoneyPreferred`, is in `ApodicticDraft.Claims`;
the situational conditions are here, as definitions a theorem takes as
named hypotheses.

## What is added

- `MoneyFrame`: a dated frame with two supplied relations more.
  `Money m` — the unit `m` is an amount of money, or a claim to an
  amount of money at a later date. `FreeToHold agent t sum` — holding
  that sum costs the agent nothing. Both bare, like `SameSatisfaction`:
  no properties, no link to `Believes` or `Prefers`.
- Sums of money are sub-stocks of a `Stock` (`Apodictic.Allocation`),
  and what a sum is worth to the agent is what his `AllocationPlan`
  says he WOULD buy with exactly those units. Present money is one
  stock, claims to future money another, both judged at the one time
  `now`. No stock is indexed by a later time.

## Shape claims (audit)

- A sum counts for what the plan says it would buy, NOT for everything
  its units could buy. The library's count for goods in a trade
  (`ActionFrame.ServedBy`) is the other one: a holding counts for every
  end any of its goods is believed able to serve. For money the two
  part at once — an ounce can be spent now or kept for later, not both —
  so wherever a theorem passes from a trade's holdings to sums, it says
  so by a named condition (`Trade.BeforeCountsAsPlanned`,
  `Trade.AfterCountsAsPlanned`).
- The stock of future money lists the claims the agent is weighing,
  not claims he holds: a lender holds none before he lends. `Stock`'s
  own docstring reads its units as "on hand"; here they are on offer.
  Rothbard's reach over goods not held is his own ("If the actor has no
  units of some goods in his possession, this does not affect the
  principle", *MES* p. 32).
- The date a sum would be spent is the date of the end the plan says
  it would buy. Dates therefore enter as the dates of ends picked out by
  the agent's plan and beliefs at `now` — expected dates, not dates of
  delivery.
-/

namespace ApodicticDraft

open Apodictic

/-- A dated frame with money and the cost of holding it. -/
structure MoneyFrame extends DatedFrame where
  /-- `Money m`: the unit `m` is an amount of money, or a claim to an
  amount of money at a later date. Supplied; no properties. -/
  Money : Means → Prop
  /-- `FreeToHold agent t sum`: at `t`, holding exactly the units in
  `sum` costs the agent nothing — no storage, custody, tax or risk of
  loss eats into it. Supplied; no properties. -/
  FreeToHold : Agent → Time → Finset Means → Prop

/-- The agent, at that time, believes the good serves exactly the one
end `want`, and nothing else. The smallest case of a dated good: a
good whose service is one dated satisfaction. -/
def _root_.Apodictic.ActionFrame.ServesOnly (praxis : ActionFrame)
    (agent : praxis.Agent) (time : praxis.Time) (good : praxis.Means)
    (want : praxis.End) : Prop :=
  praxis.ServedBy agent time {good} = {want}

section Sums

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future : Stock praxis.toActionFrame agent now}

/-- **Same purchasing power** — a condition on the situation (I-7). The
present sum and the future sum are the same amount, and each would buy
one satisfaction, the same satisfaction, each at its own date.

Mises: "present goods are valued higher than future goods of the same
kind and quantity" (*Human Action*, ch. XIX, §1). Rothbard's "the same
amount of future money" (*MES* p. 376) does no work by itself: equal
counts of ounces are the same good at two dates only if they buy the
same thing. It fails in two ways reality pulls apart and this
vocabulary cannot: the money buys less at the later date (Rothbard's
purchasing-power component, *MES* p. 797; Mises's price premium), or
the claim may not pay (the credit premium). Both land here, because
"the claim pays" and "what paid money buys" would need a stock of money
indexed by the later date, which the vocabulary does not have: a claim
that may not pay is believed to buy an uncertain end, and an uncertain
end is not the same satisfaction as a certain one. -/
def SamePurchasingPower (presentPlan : AllocationPlan present)
    (futurePlan : AllocationPlan future) (sum claim : Finset praxis.Means)
    (soon late : praxis.End) : Prop :=
  sum.card = claim.card ∧ presentPlan.wouldServe sum = {soon} ∧
    futurePlan.wouldServe claim = {late} ∧
    praxis.SameSatisfaction agent soon late

/-- **Spent sooner** — a condition on the situation. The present sum
would be spent before the claim pays, and not on something already
past at `now`.

It is what Rothbard's footnote answers rather than grants: "It is not
valid to object that some might prefer to use the money in the future
rather than in the present. That is not the issue here, which is one of
availability for use" (*MES* p. 386 n. 11). The objector is the man for
whom this condition fails — he would hold the present sum until the
date the claim pays. -/
def SpentSooner (soon late : praxis.End) : Prop :=
  praxis.Before (praxis.attained soon) (praxis.attained late) ∧
    ¬ praxis.Before (praxis.attained soon) now

/-- **Held to the same use** — a condition on the situation, the case
Rothbard's footnote turns to: the agent would hold the present sum and
spend it on just what the claim would buy. Rothbard: "If a man wants to
“save” money for some future use, he may “hoard” it rather than spend
it on a future good, and thus have it always available" (*MES* p. 386
n. 11). It holds only where hoarding is free and the money keeps its
purchasing power; where holding costs, the hoarded sum buys less. -/
def HeldToTheSameUse (presentPlan : AllocationPlan present)
    (futurePlan : AllocationPlan future) (sum claim : Finset praxis.Means) :
    Prop :=
  presentPlan.wouldServe sum = futurePlan.wouldServe claim

/-- **Free to hold, within the claim** — a condition on the situation:
the restriction the monotonicity claim carries (I-4, "both amounts free
to hold"), on the future side. Every part of the claim, the whole
included, costs the agent nothing to hold. Rothbard abstracts from it in so many words: "We have
abstracted from hoarding, which will be dealt with in the chapter on
money" (*MES* p. 386 n. 11); his own banking pages price it — a
depositor "pays the owner of the warehouse a certain sum for the
service of storage" (p. 801). -/
def FreeToHoldWithin (claim : Finset praxis.Means) : Prop :=
  ∀ part ⊆ claim, praxis.FreeToHold agent now part

end Sums

/-- **Transitive on one chain** — a condition on the situation (I-5),
NOT a claim. For these three bundles only: if the first is preferred
to the second and the second to the third, the first is preferred to
the third.

Neither author states transitivity; Rothbard's "one ounce or less"
(*MES* p. 382) chains two preferences and needs it for the one chain
it uses. Promoted to a claim only when a second theorem needs it. -/
def _root_.Apodictic.ActionFrame.TransitiveOn (praxis : ActionFrame)
    (agent : praxis.Agent) (time : praxis.Time)
    (X Y Z : Set praxis.End) : Prop :=
  praxis.Prefers agent time X Y → praxis.Prefers agent time Y Z →
    praxis.Prefers agent time X Z

section Loans

variable {praxis : MoneyFrame}

/-- **The holding before counts as planned** — a condition on one
trade. What the lender's holding before the loan counts for, on the
library's count of goods, is what his plan says the present sum would
buy. It fails where his other goods add ends of their own, and where
the union count and the plan part (`ApodicticDraft.Money`, shape
claims). -/
def _root_.Apodictic.Trade.BeforeCountsAsPlanned
    (trade : Trade praxis.toActionFrame)
    {present : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (sum : Finset praxis.Means) :
    Prop :=
  trade.before trade.time = ↑(presentPlan.wouldServe sum)

/-- **The holding after counts as planned** — a condition on one
trade. What the lender's holding after the loan counts for is what his
plan says the repaid sum would buy. -/
def _root_.Apodictic.Trade.AfterCountsAsPlanned
    (trade : Trade praxis.toActionFrame)
    {future : Stock praxis.toActionFrame trade.agent trade.time}
    (futurePlan : AllocationPlan future) (repaid : Finset praxis.Means) :
    Prop :=
  trade.after trade.time = ↑(futurePlan.wouldServe repaid)

/-- **Refusing keeps the sum** — a condition on one trade (I-8, the
refusal supplied per case). Had the lender refused, he would have been
left with what the present sum would buy, at full value. Rothbard's
reading of a loan's alternative; Hülsmann's and Deist's lenders are
the cases where it fails — the kept sum would buy less than the plan
for it, or something other. -/
def _root_.Apodictic.Trade.RefusalKeepsSum
    (trade : Trade praxis.toActionFrame)
    {present : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (sum : Finset praxis.Means) :
    Prop :=
  trade.refusal = ↑(presentPlan.wouldServe sum)

end Loans

end ApodicticDraft
