import ApodicticDraft.Money

/-!
# Claims — the draft library's unruled claims about action

The draft counterpart of `Apodictic.Praxeology`: every claim a draft
theorem carries that is not in the trusted library is here, and nowhere
else. A ruling moves a claim into `Apodictic.Praxeology`, or leaves it
here as a rejected encoding.

- `MoreMoneyPreferred` (T1). Unruled as worded: the owner ruled the
  claim's scope (money only, both amounts free to hold); the Lean
  wording waits for approval.
- `NoConsumingWithoutPreference` (the regress). Unruled: a weaker
  rival to the library's `DemonstratedTimePreference`.
- `MoreMoneyPreferredWhereDiffers` (T1). Unruled: a weaker rival to
  `MoreMoneyPreferred` that ranks only purchases that differ.
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

/-- **No consuming without a preference** — an act that takes a
satisfaction and forgoes the same satisfaction later is not the act of
an agent who, at the time of acting, lacks a preference for the sooner.

The weak form of `DemonstratedTimePreference`: that claim says the act
shows the preference; this one says only that the act refutes its
absence. Asserted of the act handed to a theorem, not of every act.

Source: Mises, *Human Action*, ch. XVIII, §2: "If he were not to prefer
satisfaction in a nearer period of the future to that in a remoter
period, he would never consume and so satisfy wants." Rothbard, *MES*,
p. 51: "If man, other things being equal, did not prefer satisfaction
in the present to satisfaction in the future, he would never consume".

Status: explicit-in-tradition. Both authors word the regress's first
step this way round, from the absence of the preference to not
consuming. Stated of one act at its own date is our-reconstruction:
both sentences say "never", of a whole course of conduct.

Does not say:

1. That the agent prefers the sooner. Getting the preference from the
   refutation of its absence needs excluded middle for that preference,
   which the library does not assume.
2. Anything about acts that forgo something other than the same
   satisfaction later.
3. That the chosen satisfaction is present, rather than merely sooner.
4. Anything about other acts or other times. "Never" is not in it: that
   a man without the preference would consume at no date is what the
   regress is for. -/
structure NoConsumingWithoutPreference {praxis : DatedFrame}
    (act : Action praxis.toActionFrame) : Prop where
  /-- The act refutes "no preference for what it took over the same
  satisfaction later". -/
  refutes : ∀ later ∈ act.forgone,
    praxis.SameSatisfaction act.agent act.chosen later →
    praxis.Before (praxis.attained act.chosen) (praxis.attained later) →
    ¬ ¬ praxis.PrefersEnd act.agent act.time act.chosen later

/-- **More money is preferred, where it would buy something else** —
of two sums of money, the one part of the other and both free to hold,
and the larger buying other ends than the smaller, the agent prefers
what the larger would buy to what the smaller would buy.

The weak form of `MoreMoneyPreferred`: that claim ranks the two
purchases even where they are the same, and so, with
`AsymmetricPreference`, asserts that every extra unit of free money
buys something else. This one ranks only purchases that differ; that
they differ is the condition `Satiation.BuysMoreThanItsParts`, on the
theorem that needs it. Asserted of one plan for one stock.

Source: Rothbard, *MES* p. 379: "[T]o both present money and future
money there applies the general rule that more of a good will have
greater utility than less of it." Mises, *Human Action*, ch. VII, §1:
"what satisfies more is preferred to what gives smaller satisfaction".

Status: explicit-in-tradition as doctrine; the narrow form is
our-reconstruction, as for `MoreMoneyPreferred`, and so is the cut
between this claim and the condition of differing purchases.

Does not say:

1. That an extra unit of money always buys something else: that is the
   condition, not the claim.
2. That a larger purchase is a superset of the smaller: only that the
   two differ.
3. Anything of goods that are not money, or of sums that cost
   something to hold.
4. How much more is preferred: no rate.
5. Anything of two sums neither of which is part of the other.
6. Anything about acts. -/
structure MoreMoneyPreferredWhereDiffers {praxis : MoneyFrame}
    {agent : praxis.Agent} {now : praxis.Time}
    {stock : Stock praxis.toActionFrame agent now}
    (plan : AllocationPlan stock) : Prop where
  /-- The larger of two sums, one part of the other, where they would
  buy different ends. -/
  more : ∀ fewer more : Finset praxis.Means, fewer ⊂ more →
    more ⊆ stock.units → (∀ unit ∈ more, praxis.Money unit) →
    praxis.FreeToHold agent now fewer → praxis.FreeToHold agent now more →
    plan.wouldServe more ≠ plan.wouldServe fewer →
      praxis.Prefers agent now ↑(plan.wouldServe more) ↑(plan.wouldServe fewer)

end ApodicticDraft
