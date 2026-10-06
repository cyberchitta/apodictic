import ApodicticDraft.Money

/-!
# Claims — the draft library's unruled claims about action (T1)

The draft counterpart of `Apodictic.Praxeology`: every claim the T1
theorems carry that is not in the trusted library is here, and nowhere
else. Unruled as worded: the owner ruled the claim's scope (I-4, money
only, both amounts free to hold); the Lean wording below waits for
approval. A ruling moves it into `Apodictic.Praxeology`, or leaves it
here as a rejected encoding.
-/

namespace ApodicticDraft

open Apodictic

/-- **More money is preferred** — of two sums of money, the one being
part of the other and both free to hold, the agent prefers what the
larger would buy to what the smaller would buy.

Asserted of one plan for one stock, and only of sums whose every unit
is money and which cost nothing to hold. Subjunctive, like the plans
it is asserted of: it speaks of sums the agent may not hold.

Source: Rothbard, *MES* p. 379: "[T]o both present money and future
money there applies the general rule that more of a good will have
greater utility than less of it." Mises, *Human Action*, ch. VII, §1:
"what satisfies more is preferred to what gives smaller satisfaction".

Status: explicit-in-tradition as doctrine; the narrow form is
our-reconstruction. Rothbard states a general rule, of every good.
A known case refutes the general rule: a holding taxed at more than
its whole value, and at small scale any storage or custody cost, makes
more of a good worse than less. So the claim is cut to money and to
sums free to hold, and costly holding is the condition `FreeToHold`,
not an exception the claim absorbs.

Does not say:

1. Anything of goods that are not money. Satiation and the cost of
   holding refute it there; this claim is silent.
2. Anything of sums that cost something to hold.
3. How much more is preferred, or by how much: no rate.
4. Anything of two sums neither of which is part of the other. That two
   sums of the same size would buy the same is the condition
   `AllocationPlan.Homogeneous`, not part of this claim.
5. That the agent's preferences chain: transitivity is the condition
   `ActionFrame.TransitiveOn`, on one chain.
6. Anything about acts. It ranks what sums would buy; the bridge to a
   trade is `DemonstratedPreference`. -/
structure MoreMoneyPreferred {praxis : MoneyFrame} {agent : praxis.Agent}
    {now : praxis.Time} {stock : Stock praxis.toActionFrame agent now}
    (plan : AllocationPlan stock) : Prop where
  /-- The larger of two sums, one part of the other. -/
  more : ∀ fewer more : Finset praxis.Means, fewer ⊂ more →
    more ⊆ stock.units → (∀ unit ∈ more, praxis.Money unit) →
    praxis.FreeToHold agent now fewer → praxis.FreeToHold agent now more →
      praxis.Prefers agent now ↑(plan.wouldServe more) ↑(plan.wouldServe fewer)

end ApodicticDraft
