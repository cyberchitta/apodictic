import Apodictic.Allocation
import Apodictic.Exchange
import Apodictic.Dated

/-!
# Money — the vocabulary of the time market

Definitions ONLY: this file asserts nothing. The one claim the interest
theorems carry, `MoreMoneyPreferredWhenSpent`, is in
`Apodictic.Praxeology`; the situational conditions are here, as
definitions a theorem takes as named hypotheses.

## What is added

- `MoneyFrame`: a dated frame with two supplied relations more.
  `Money m` — the unit `m` is an amount of money, or a promise of an
  amount of money at a later date. `FreeToHold agent t sum` — holding
  that sum costs the agent nothing. Both bare, like `SameSatisfaction`:
  no properties, no link to `Believes` or `Prefers`.
- Sums of money are sub-stocks of a `Stock` (`Apodictic.Allocation`),
  and what a sum is worth to the agent is what his `AllocationPlan`
  says he WOULD buy with exactly those units. Three stocks, all judged
  at the one time `now`: present money, promises of future money, and the
  money promised, as he would spend it were it in hand at the
  later date. No stock is indexed by a later time.

## Shape claims (audit)

- A sum counts for what the plan says it would buy, NOT for everything
  its units could buy. The library's count for goods in a trade
  (`ActionFrame.ServedBy`) is the other one: a holding counts for every
  end any of its goods is believed able to serve. For money the two
  part at once — an ounce can be spent now or kept for later, not both —
  so wherever a theorem passes from a trade's holdings to sums, it says
  so by a named condition (`Trade.BeforeCountsAsPlanned`,
  `Trade.AfterCountsAsPlanned`).
- The stock of future money lists the promises the agent is weighing,
  not promises he holds: a lender holds none before he lends. `Stock`'s
  own docstring reads its units as "on hand"; here they are on offer.
  Rothbard's reach over goods not held is his own ("If the actor has no
  units of some goods in his possession, this does not affect the
  principle", *MES* p. 32). The stock of promised money is on offer in
  the same sense.
- The date a sum would be spent is the date of the end the plan says
  it would buy. Dates therefore enter as the dates of ends picked out by
  the agent's plan and beliefs at `now` — expected dates, not dates of
  delivery.
- Certainty is read as how the agent counts the promise at `now`, not as
  what later happens: a promise he believes may not pay is one his plan
  counts for something other than the money it promises (`PromisePays`).
-/

namespace Apodictic

/-- A part of a finite set, of any size up to its own, taken without
choice: the first `n` elements of the list behind it. -/
theorem exists_part_of_card {α : Type*} (s : Finset α) (n : ℕ)
    (h : n ≤ s.card) : ∃ part ⊆ s, part.card = n := by
  rcases s with ⟨m, nd⟩
  revert nd h
  refine Quotient.inductionOn m ?_
  intro l nd h
  have nd' : (l.take n).Nodup := (Multiset.coe_nodup.1 nd).sublist (List.take_sublist _ _)
  refine ⟨⟨↑(l.take n), Multiset.coe_nodup.2 nd'⟩, ?_, ?_⟩
  · intro x hx
    exact Multiset.mem_coe.2 (List.mem_of_mem_take (Multiset.mem_coe.1 hx))
  · have hl : n ≤ l.length := h
    show (l.take n).length = n
    rw [List.length_take]
    exact Nat.min_eq_left hl

/-- A one-element finite set, read as a set, is the one-element set.
`Finset.coe_singleton` says the same with a classical proof. -/
theorem coe_single {α : Type*} (a : α) : ((({a} : Finset α)) : Set α) = {a} :=
  Set.ext fun _ => Finset.mem_coe.trans Finset.mem_singleton

/-- A dated frame with money and the cost of holding it. -/
structure MoneyFrame extends DatedFrame where
  /-- `Money m`: the unit `m` is an amount of money, or a promise of an
  amount of money at a later date. Money is Mises's: "the thing which
  serves as the generally accepted and commonly used medium of
  exchange" (*Human Action*, ch. XVII, §3). Supplied; no properties:
  whether a unit is money is a fact about the situation, checked by
  whoever applies a theorem, and each theorem that needs it names it as
  a hypothesis. -/
  Money : Means → Prop
  /-- `FreeToHold agent t sum`: at `t`, holding exactly the units in
  `sum` costs the agent nothing — no storage, custody, tax or risk of
  loss eats into it. Supplied; no properties. -/
  FreeToHold : Agent → Time → Finset Means → Prop

section Sums

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future promised stock : Stock praxis.toActionFrame agent now}

/-- **Same purchasing power** — a condition on the situation. Each of two
sums would buy one satisfaction. Each would buy it at its own date. The
two satisfactions are the same. The theorems assert this between the present sum and the
money promised.

Mises: "present goods are valued higher than future goods of the same
kind and quantity" (*Human Action*, ch. XIX, §1). Rothbard's "the same
amount of future money" (*MES* p. 376) is not part of it. Equal counts
of ounces are the same good at two dates only if they buy the same
thing. That is what this condition says. The count is a separate
condition (`SameCount`), carried only where it is used.

It fails where the money buys less at the later date. That is
Rothbard's purchasing-power component (*MES* p. 797) and Mises's price
premium. Whether the promise pays is a separate condition
(`PromisePays`). -/
def SamePurchasingPower (presentPlan : AllocationPlan present)
    (futurePlan : AllocationPlan future) (sum promise : Finset praxis.Means)
    (soon late : praxis.End) : Prop :=
  presentPlan.wouldServe sum = {soon} ∧
    futurePlan.wouldServe promise = {late} ∧
    praxis.SameSatisfaction agent soon late

/-- **The promise pays** — a condition on the situation. It is
Rothbard's world of certainty, for one promise. The agent's plan counts
the promise for exactly what it counts the promised money for.

It fails where he believes the promise may not pay, or may pay only in
part. The promise then counts for something other than the promised
money would buy. The credit premium lands here, and only here. -/
def PromisePays (futurePlan : AllocationPlan future)
    (promisedPlan : AllocationPlan promised)
    (promise money : Finset praxis.Means) : Prop :=
  futurePlan.wouldServe promise = promisedPlan.wouldServe money

/-- **The same count** — a condition on the situation, of bookkeeping.
The promise is as many units as the present sum. This is Rothbard's
"the same amount of future money" (*MES* p. 376), where it does work.
Only the loan theorems use it. They use it to compare the repaid sum
with the promise. -/
def SameCount (sum promise : Finset praxis.Means) : Prop :=
  sum.card = promise.card

/-- **Spent sooner** — a condition on the situation. The present sum
would be spent before the promise pays. It would not be spent on
something already past at `now`.

Rothbard's footnote answers this rather than grants it: "It is not
valid to object that some might prefer to use the money in the future
rather than in the present. That is not the issue here, which is one of
availability for use" (*MES* p. 386 n. 11). The objector is the man for
whom this condition fails. He would hold the present sum until the date
the promise pays. -/
def SpentSooner (soon late : praxis.End) : Prop :=
  praxis.Before (praxis.attained soon) (praxis.attained late) ∧
    ¬ praxis.Before (praxis.attained soon) now

/-- **Free to hold, within the promise** — a condition on the
situation. The "more money" claim (`MoreMoneyPreferredWhenSpent`)
carries this restriction, on the future side. Every part of the promise, the whole included, costs the
agent nothing to hold.

Rothbard abstracts from it in so many words: "We have abstracted from
hoarding, which will be dealt with in the chapter on money" (*MES*
p. 386 n. 11). His own banking pages put a price on it. A depositor
"pays the owner of the warehouse a certain sum for the service of
storage" (p. 801). -/
def FreeToHoldWithin (promise : Finset praxis.Means) : Prop :=
  ∀ part ⊆ promise, praxis.FreeToHold agent now part

/-- **Buys more than its parts** — a condition on the situation, NOT a
claim. Every strict part of `sum` would buy other ends than the whole
does. So the plan has a use for every unit of the sum. It fails for a
sum larger than anything the agent would spend or hold it on. -/
def BuysMoreThanItsParts (plan : AllocationPlan stock)
    (sum : Finset praxis.Means) : Prop :=
  ∀ part ⊂ sum, plan.wouldServe sum ≠ plan.wouldServe part

/-- **Ranked alike now, of one comparison** — a condition on the
situation, NOT a claim. Take the date `spend`, when the agent would
spend the two sums. Suppose he then ranks what `promise` would buy
above what `lesser` would buy. Then he ranks them so at `now` too. His
valuation of these two purchases does not change in between.

Mises: "If the valuations change, acting must change also" (*Human
Action*, ch. V, §4). It fails for the man who now prefers to be repaid
less. He prefers it because of what he would do with more. -/
def RankedAlikeNowOf (plan : AllocationPlan stock) (spend : praxis.Time)
    (promise lesser : Finset praxis.Means) : Prop :=
  praxis.Prefers agent spend ↑(plan.wouldServe promise) ↑(plan.wouldServe lesser) →
    praxis.Prefers agent now ↑(plan.wouldServe promise) ↑(plan.wouldServe lesser)

end Sums

/-- **Transitive on one chain** — a condition on the situation, NOT a
claim. It covers these three bundles only. If the first is preferred
to the second, and the second to the third, the first is preferred to
the third.

Neither author states transitivity. Rothbard's "one ounce or less"
(*MES* p. 382) chains two preferences. It needs transitivity for that
one chain. -/
def ActionFrame.TransitiveOn (praxis : ActionFrame)
    (agent : praxis.Agent) (time : praxis.Time)
    (X Y Z : Set praxis.End) : Prop :=
  praxis.Prefers agent time X Y → praxis.Prefers agent time Y Z →
    praxis.Prefers agent time X Z

section Loans

variable {praxis : MoneyFrame}

/-- **The holding before counts as planned** — a condition on one
trade. Before the loan, the lender holds some goods. The library counts
a holding by every end its goods are believed able to serve
(`ActionFrame.ServedBy`). Here that count must equal what his plan
says the present sum would buy.

It fails where his other goods add ends of their own. It also fails
where the two ways of counting differ (shape claims, above). -/
def Trade.BeforeCountsAsPlanned
    (trade : Trade praxis.toActionFrame)
    {present : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (sum : Finset praxis.Means) :
    Prop :=
  trade.before trade.time = ↑(presentPlan.wouldServe sum)

/-- **The holding after counts as planned** — a condition on one
trade. After the loan, the lender holds some goods. They count for what
his plan says the repaid sum would buy, and nothing else. -/
def Trade.AfterCountsAsPlanned
    (trade : Trade praxis.toActionFrame)
    {future : Stock praxis.toActionFrame trade.agent trade.time}
    (futurePlan : AllocationPlan future) (repaid : Finset praxis.Means) :
    Prop :=
  trade.after trade.time = ↑(futurePlan.wouldServe repaid)

/-- **Refusing keeps the sum** — a condition on one trade. The refusal
is supplied case by case. Had the lender refused, he would have been
left with what the present sum would buy, at full value. This is
Rothbard's reading of a loan's alternative.

Hülsmann's and Deist's lenders are the cases where it fails. There the
kept sum would buy less than the plan for it, or something else. -/
def Trade.RefusalKeepsSum
    (trade : Trade praxis.toActionFrame)
    {present : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (sum : Finset praxis.Means) :
    Prop :=
  trade.refusal = ↑(presentPlan.wouldServe sum)

end Loans

end Apodictic
