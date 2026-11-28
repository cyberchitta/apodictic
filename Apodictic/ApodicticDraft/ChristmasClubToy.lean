import ApodicticDraft.Toy

/-!
# Christmas Club toy — a voluntary loan at a zero rate (evidence, not theory)

The hardest case found for `Interest.present_sum_preferred` (S2) and
`Satiation.no_loan_at_zero_rate` (SR-5): a Christmas Club saver. Cash
at hand he would spend now on an impulse he does not rank highly; the
club holds two ounces and pays two back at date 1, which buy the
Christmas he wants. He lends at a zero rate, voluntarily.

Built on `ApodicticDraft.Toy`'s frame. Every claim holds of him:
`TimePreference`, `AsymmetricPreference`, `DemonstratedPreference` of
his trade, `MoreMoneyPreferred` on his plan for promises. Unlike the
toy's saver, `SpentSooner` HOLDS: he would spend the cash before the
club pays. What fails is `BuysSameSatisfaction`: what his cash would buy
is not the same satisfaction as what the promise would buy. On the plan
reading (I-16), the theorems are silent about him, and the signature
says why.

What the toy does not model: that he prefers less cash at hand to
more. In this frame a sum of cash buys one end however large, so the
"more money" claim is not tested here
(`asks/2026-11-25-plan-valued-later-ranked-now`).
-/

namespace ApodicticDraft
namespace ChristmasClubToy

open Apodictic Toy

/-- What cash at hand would buy now: an impulse, a kind ranked below
both of an ounce's worth and two ounces' worth. -/
def impulse : ℕ × ℕ := (3, 0)

/-- The saver's beliefs: his ounces, spent now, buy `impulse`; the hoard
is his two ounces at hand, the bond the club's promise of two at date 1. -/
def clubBeliefs : Good → ℕ × ℕ → Prop
  | .hoard, e => e = impulse
  | .bond, e => e = plenty
  | g, e => moneyBeliefs impulse g e

theorem club_future_alike : ∀ unit ∈ ({.promiseA, .promiseB} : Finset Good), ∀ e,
    clubBeliefs unit e ↔ e ∈ ({late, plenty} : Set (ℕ × ℕ)) := by
  intro unit h e
  rcases Finset.mem_insert.1 h with rfl | h
  · exact Iff.rfl
  · rw [Finset.mem_singleton.1 h]; exact Iff.rfl

theorem club_present_alike : ∀ unit ∈ ({.ounce, .ounce'} : Finset Good), ∀ e,
    clubBeliefs unit e ↔ e ∈ ({impulse} : Set (ℕ × ℕ)) := by
  intro unit h e
  rcases Finset.mem_insert.1 h with rfl | h
  · exact Iff.rfl
  · rw [Finset.mem_singleton.1 h]; exact Iff.rfl

/-- The deposit: he gives the hoard (two ounces), gets the bond (a promise
to two), keeps nothing else; refusing would have left him the cash,
which he would spend on the impulse. -/
def deposit : Trade (frame clubBeliefs).toActionFrame :=
  ⟨(), 0, .hoard, .bond, ∅, {impulse}⟩

theorem deposit_before : deposit.before 0 = {impulse} := by
  rw [Trade.before, show deposit.kept = ∅ from rfl, servedBy_one]
  ext e; exact Iff.rfl

theorem deposit_after : deposit.after 0 = {plenty} := by
  rw [Trade.after, show deposit.kept = ∅ from rfl, servedBy_one]
  ext e; exact Iff.rfl

theorem deposit_voluntary : deposit.Voluntary := deposit_before.symm

/-- He demonstrates his preference for the club's promise: Christmas at
date 1 over the impulse now. -/
theorem deposit_demonstrated : DemonstratedPreference deposit :=
  ⟨by
    show (frame clubBeliefs).Prefers () 0 (deposit.after 0) {impulse}
    rw [deposit_after]
    exact ⟨plenty, rfl, fun y hy => by
      have hy : y = impulse := hy
      subst hy
      exact Nat.lt_of_sub_eq_succ rfl⟩⟩

/-- **A zero rate, struck voluntarily, with every claim holding.** Two
ounces lent, a promise of two got. -/
theorem zero_rate_with_every_claim :
    TimePreference (frame clubBeliefs).toDatedFrame () 0 ∧
    AsymmetricPreference (frame clubBeliefs).toActionFrame () 0 ∧
    MoreMoneyPreferred (praxis := frame clubBeliefs)
      (futurePlan clubBeliefs club_future_alike) ∧
    DemonstratedPreference deposit ∧ deposit.Voluntary ∧
    ({.promiseA, .promiseB} : Finset Good).card =
      ({.ounce, .ounce'} : Finset Good).card :=
  ⟨timePreference clubBeliefs 0, asymmetric clubBeliefs 0,
    future_moreMoney clubBeliefs club_future_alike, deposit_demonstrated,
    deposit_voluntary, rfl⟩

/-- **`SpentSooner` holds for him**, unlike the toy's saver: the cash
would be spent now, before the club pays. -/
theorem club_spent_sooner :
    SpentSooner (praxis := frame clubBeliefs) (now := (0 : ℕ)) impulse plenty :=
  ⟨Nat.zero_lt_one, Nat.lt_irrefl 0⟩

/-- **What fails for him is `BuysSameSatisfaction`.** Whatever his two
ounces at hand would buy and whatever the promise of two would buy, they
are not the same satisfaction. -/
theorem club_not_buys_same_satisfaction (soonEnd lateEnd : ℕ × ℕ) :
    ¬ BuysSameSatisfaction (praxis := frame clubBeliefs) (now := (0 : ℕ))
      (presentPlan clubBeliefs {.ounce, .ounce'} impulse club_present_alike)
      (futurePlan clubBeliefs club_future_alike)
      {.ounce, .ounce'} {.promiseA, .promiseB} soonEnd lateEnd := by
  rintro ⟨buysSoon, buysLate, same⟩
  have hs : ({impulse} : Finset (ℕ × ℕ)) = {soonEnd} := buysSoon
  have hl : ({plenty} : Finset (ℕ × ℕ)) = {lateEnd} := buysLate
  rw [Finset.singleton_inj] at hs hl
  subst hs hl
  have : (3 : ℕ) = 0 := same
  exact Nat.succ_ne_zero 2 this

#print axioms zero_rate_with_every_claim
#print axioms club_spent_sooner
#print axioms club_not_buys_same_satisfaction

end ChristmasClubToy
end ApodicticDraft

#lint only unusedArguments
