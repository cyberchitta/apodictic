import ApodicticDraft.Claims

/-!
# Interest — the pure time-preference theory of interest (T1), draft

Rothbard's conclusion (*MES* p. 382): "every man’s time preference is
positive, i.e., one ounce of present money will always be preferred to
one ounce or less of future money. Therefore, there will never be any
question of a zero or negative pure interest rate." Mises's (*Human
Action*, ch. XIX, §2): "Originary interest is a category of human
action. It is operative in any valuation of external things and can
never disappear."

## What is proved, and what it costs

- `present_good_preferred` (S1): of two goods each serving one
  satisfaction, the same at two dates, the present one is preferred.
  `TimePreference` and nothing else; the rest is what the goods are
  believed to serve.
- `never_vanishes` (Mises's route): the regress, carried to goods.
  Not a rate, and only a double negation.
- `present_sum_preferred` (S2): present money over the same amount of
  future money. `TimePreference`, plus two conditions: the two sums buy
  the same satisfaction (`SamePurchasingPower`), and the present one
  would be spent sooner (`SpentSooner`).
- `hoarding_gives_no_strict_preference`: Rothbard's footnote guard
  (n. 11) gives no strict preference. Where the agent would hoard the
  present sum for the use the claim serves, asymmetry forbids
  preferring the one to the other.
- `present_sum_preferred_to_less` (S3): "one ounce or less". Adds the
  unruled claim `MoreMoneyPreferred`, interchangeability of the future
  units (`Homogeneous`), free holding within the claim, and
  transitivity on the one chain.
- `no_loan_at_nonpositive_rate` (S4): a loan at a rate not above zero
  demonstrates no preference — under `DemonstratedPreference`, it is
  not made. Adds `AsymmetricPreference` and two conditions tying the
  trade's holdings to the sums.
- `struck_rate_positive` (S5): in a voluntary exchange the lender
  demonstrates a preference in, the repaid sum is larger than the sum
  lent. Only the lender's side is used.

Nothing here needs a property of `Before`, and no classical step: the
one case split is `≤` on ℕ.
-/

namespace ApodicticDraft
namespace Interest

open Apodictic

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

/-- **A present good is preferred to the same good later** (S1; *MES*
pp. 375–76: "a particular good is worth more at present than is the
present prospect of its becoming available as a present good at some
time in the future"; *Human Action*, ch. XIX, §1, "of the same kind and
quantity").

Two goods, each believed to serve one end; the two ends the same
satisfaction, the present good's the sooner. The goods count for the
ends they are believed to serve, so the dates compared are the dates
of the ends the agent believes the goods will serve. -/
theorem present_good_preferred
    {praxis : DatedFrame} {agent : praxis.Agent} {now : praxis.Time}
    (presentGood futureGood : praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis agent now)
    (presentServes : praxis.ServesOnly agent now presentGood soon)
    (futureServes : praxis.ServesOnly agent now futureGood late)
    (same : praxis.SameSatisfaction agent soon late)
    (sooner : praxis.Before (praxis.attained soon) (praxis.attained late))
    (notPast : ¬ praxis.Before (praxis.attained soon) now) :
    praxis.Prefers agent now (praxis.ServedBy agent now {presentGood})
      (praxis.ServedBy agent now {futureGood}) := by
  rw [presentServes, futureServes]
  exact timePreference.sooner soon late same sooner notPast

/-- **Originary interest never vanishes, per agent** — Mises's route
(*Human Action*, ch. XIX, §2–3: "Originary interest cannot disappear as
long as there is scarcity and therefore action"; "The disappearance of
originary interest would be tantamount to the disappearance of
consumption").

Mises's regress (`Apodictic.TimePreference.regress`), carried from the
offers to two goods that serve them: an act of consuming that
demonstrates, with no preference carrying from date to date, refutes
"no preference for the present good over the future one at the first
date". What it reaches is a double negation, of one agent's ranking of
two goods at one date. It is not a rate, and no market enters. -/
theorem never_vanishes
    {praxis : DatedFrame} {agent : praxis.Agent}
    (morrows : Morrows praxis agent) (n : ℕ)
    (act : Action praxis.toActionFrame)
    (consumes : morrows.ConsumesAt n act)
    (sameAlternative : morrows.SameAlternative)
    (demonstrated : DemonstratedTimePreference act)
    (carries : morrows.NoPreferenceCarries)
    (presentGood futureGood : praxis.Means)
    (presentServes : praxis.ServesOnly agent (morrows.date 0) presentGood
      (morrows.offer 0))
    (futureServes : praxis.ServesOnly agent (morrows.date 0) futureGood
      (morrows.offer 1)) :
    ¬ ¬ praxis.Prefers agent (morrows.date 0)
      (praxis.ServedBy agent (morrows.date 0) {presentGood})
      (praxis.ServedBy agent (morrows.date 0) {futureGood}) := by
  rw [presentServes, futureServes]
  exact TimePreference.regress morrows n act consumes sameAlternative
    demonstrated carries

section Sums

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future : Stock praxis.toActionFrame agent now}

/-- **Present money is preferred to the same amount of future money**
(S2; *MES* p. 376: "It follows from the law of time preference that
present money is worth more than present expectations of the same
amount of future money").

"The same amount" does no work here: what the sums would buy does
(`SamePurchasingPower`). And the conclusion needs the present sum to be
spent sooner — the case Rothbard's n. 11 sets aside. -/
theorem present_sum_preferred
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum claim : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame agent now)
    (power : SamePurchasingPower presentPlan futurePlan sum claim soon late)
    (sooner : SpentSooner (praxis := praxis) (now := now) soon late) :
    praxis.Prefers agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe claim) := by
  obtain ⟨_, buysSoon, buysLate, same⟩ := power
  obtain ⟨before, notPast⟩ := sooner
  rw [buysSoon, buysLate, coe_single, coe_single]
  exact timePreference.sooner soon late same before notPast

/-- **Hoarding gives no strict preference** — Rothbard's footnote guard,
checked (*MES* p. 386 n. 11: "If a man wants to “save” money for some
future use, he may “hoard” it rather than spend it on a future good,
and thus have it always available").

Where the agent would hold the present sum and spend it on just what the
claim would buy, the two sums are worth the same bundle, and asymmetry
forbids preferring it to itself. The guard answers the objector by
equality, not by preference: the strict preference S2 concludes needs a
sooner use (`SpentSooner`), which the guard does not supply. -/
theorem hoarding_gives_no_strict_preference
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum claim : Finset praxis.Means)
    (asymmetric : AsymmetricPreference praxis.toActionFrame agent now)
    (held : HeldToTheSameUse presentPlan futurePlan sum claim) :
    ¬ praxis.Prefers agent now ↑(presentPlan.wouldServe sum)
      ↑(futurePlan.wouldServe claim) := by
  rw [held]
  intro h
  exact asymmetric.asym _ _ h h

/-- **The availability reading of the footnote — the rival encoding.**
Rothbard's n. 11 ranks money by "availability for use", not by the use
it would be put to. Read so, a present sum held free counts for both
its sooner use and the later one, and the claim for the later one only;
the preference then follows from `TimePreference` and a lift over
`{late}`.

Not the encoding the chain uses (`ApodicticDraft.Money`, shape claims):
`Prefers` ranks bundles of ends had TOGETHER, and a sum cannot be spent
both now and later, so `{soon, late}` here is a set of options read as
a bundle. The lift (`DatedFrame.LiftsOverRest` with rest `{late}`) is
where that misreading is paid for. Built so the choice is checked. -/
theorem availability_reading
    {praxis : DatedFrame} {agent : praxis.Agent} {now : praxis.Time}
    (presentSum claim : praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis agent now)
    (available : praxis.ServedBy agent now {presentSum} = insert soon {late})
    (claimServes : praxis.ServesOnly agent now claim late)
    (same : praxis.SameSatisfaction agent soon late)
    (sooner : praxis.Before (praxis.attained soon) (praxis.attained late))
    (notPast : ¬ praxis.Before (praxis.attained soon) now)
    (lifts : praxis.LiftsOverRest agent now {late} soon late) :
    praxis.Prefers agent now (praxis.ServedBy agent now {presentSum})
      (praxis.ServedBy agent now {claim}) := by
  have h := lifts (timePreference.sooner soon late same sooner notPast)
  have once : (insert late {late} : Set praxis.End) = {late} :=
    Set.ext fun _ => ⟨fun h => h.elim id id, Or.inr⟩
  rw [once] at h
  rw [available, claimServes]
  exact h

end Sums

section Sums'

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future : Stock praxis.toActionFrame agent now}

/-- **One ounce of present money is preferred to one ounce or less of
future money** (S3; *MES* p. 382: "one ounce of present money will
always be preferred to one ounce or less of future money").

`claim` is a future sum of the same amount as `sum`; `lesser` is any
future sum no larger. "Or less" chains S2 with `MoreMoneyPreferred` on
the future sums, and that chain is the one place transitivity is
needed. Interchangeability of the future units carries a sum of any
units to a part of `claim` of the same size. -/
theorem present_sum_preferred_to_less
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum claim lesser : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame agent now)
    (power : SamePurchasingPower presentPlan futurePlan sum claim soon late)
    (sooner : SpentSooner (praxis := praxis) (now := now) soon late)
    (claimIn : claim ⊆ future.units) (lesserIn : lesser ⊆ future.units)
    (notMore : lesser.card ≤ claim.card)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferred futurePlan)
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
    have alike : futurePlan.wouldServe part = futurePlan.wouldServe lesser :=
      homogeneous part (fun _ h => claimIn (partIn h)) lesser lesserIn partCard
    have proper : part ⊂ claim := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨partIn, fun same => ?_⟩
      rw [same] at partCard
      rw [partCard] at fewer
      exact Nat.lt_irrefl _ fewer
    have overLess := moreMoney.more part claim proper claimIn money
      (free part partIn) (free claim (fun _ h => h))
    rw [alike] at overLess
    exact chain overSame overLess

end Sums'

section Loans

variable {praxis : MoneyFrame}

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
    {present future : Stock praxis.toActionFrame trade.agent trade.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum claim repaid : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame trade.agent trade.time)
    (power : SamePurchasingPower presentPlan futurePlan sum claim soon late)
    (sooner : SpentSooner (praxis := praxis) (now := trade.time) soon late)
    (claimIn : claim ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (nonPositive : repaid.card ≤ sum.card)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferred futurePlan)
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
  have kept := present_sum_preferred_to_less presentPlan futurePlan sum claim
    repaid soon late timePreference power sooner claimIn repaidIn notMore
    homogeneous moreMoney money free chain
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
    {present future : Stock praxis.toActionFrame exchange.first.agent
      exchange.first.time}
    (presentPlan : AllocationPlan present) (futurePlan : AllocationPlan future)
    (sum claim repaid : Finset praxis.Means) (soon late : praxis.End)
    (timePreference : TimePreference praxis.toDatedFrame exchange.first.agent
      exchange.first.time)
    (power : SamePurchasingPower presentPlan futurePlan sum claim soon late)
    (sooner : SpentSooner (praxis := praxis) (now := exchange.first.time)
      soon late)
    (claimIn : claim ⊆ future.units) (repaidIn : repaid ⊆ future.units)
    (homogeneous : futurePlan.Homogeneous)
    (moreMoney : MoreMoneyPreferred futurePlan)
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
    no_loan_at_nonpositive_rate exchange.first presentPlan futurePlan sum
      claim repaid soon late timePreference power sooner claimIn repaidIn
      nonPositive homogeneous moreMoney money free chain asymmetric
      (voluntary.trans before) after demonstrated

end Loans

#print axioms exists_part_of_card
#print axioms coe_single
#print axioms present_good_preferred
#print axioms never_vanishes
#print axioms present_sum_preferred
#print axioms hoarding_gives_no_strict_preference
#print axioms availability_reading
#print axioms present_sum_preferred_to_less
#print axioms no_loan_at_nonpositive_rate
#print axioms struck_rate_positive

end Interest
end ApodicticDraft

#lint only unusedArguments
