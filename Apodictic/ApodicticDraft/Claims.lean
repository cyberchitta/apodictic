import ApodicticDraft.Medium

/-!
# Claims — the draft library's unruled claims about action (T2)

The draft counterpart of `Apodictic.Praxeology`: every claim the T2
theorems carry that is not in the trusted library is here, and nowhere
else. Unruled. A ruling moves it into `Apodictic.Praxeology` with its
Lean wording approved, or leaves it here as a rejected encoding.
-/

namespace ApodicticDraft

open Apodictic

/-- **Appraisal from the past, weak form** — nobody appraises a good as
a medium of exchange on a day unless that good changed hands, against
anything, on some earlier day.

Asserted of one record of exchanges and one good. "Appraises as a
medium" is a belief that the good serves an onward end
(`MediumFrame.AppraisesAsMedium`), so the claim is about what any
prospective acquirer or holder can believe, not only about acquirers.

Source: Mises, *Human Action*, ch. XVII, §4: "he who considers
acquiring or giving away money is, of course, first of all interested
in its future purchasing power and the future structure of prices. But
he cannot form a judgment about the future purchasing power of money
otherwise than by looking at its configuration in the immediate past."
Ch. XVII, §8: "A medium of exchange without a past is unthinkable."
Ch. XVII, §1: "For all that is to be predicated of money is valid for
every medium of exchange." Rothbard, *MES* p. 275: "Demand for a good
as a medium of exchange must be predicated on a previously existing
array of prices in terms of other goods." Rothbard, *Power and Market*
(*MES* ed. p. 1021): a money must be one that "can be exchanged for a
previously existing money".

Status: explicit-in-tradition as doctrine; the weak form is
our-reconstruction. Mises states the premise exclusively — the
judgment rests on the good's own price, from the immediate past, and on
nothing else. This form keeps only that an exchange of the good came
first, on any earlier day and against any good, money included.

Does not say:

1. That the earlier exchange was on the immediately preceding day.
2. That the appraisal rests on that exchange, or on that exchange
   alone — not that promises, edicts or cross rates play no part.
   Without quantities the vocabulary cannot say "rests on"; see
   `History.OwnPastPrice`.
3. That the earlier exchange was barter (`History.FormedInBarter`).
4. That the earlier acquirer wanted the good for itself; the regress
   derives that, from further conditions.
5. Anything about day 0. That nobody appraises the good as a medium on
   the first day of the record is the separate condition
   `History.BeginsBeforeMedium`, the termination Mises asserts. -/
structure AppraisalFromPast {praxis : MediumFrame} (history : History praxis)
    (m : praxis.Means) : Prop where
  /-- An appraisal as a medium on day `n + 1` has an exchange of the
  good on some day up to `n` behind it. -/
  fromPast : ∀ n agent,
    praxis.AppraisesAsMedium agent (history.date (n + 1)) m →
      ∃ k ≤ n, history.ExchangedOn k m

end ApodicticDraft
