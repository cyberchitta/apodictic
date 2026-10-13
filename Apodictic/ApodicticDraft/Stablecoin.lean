import Apodictic.Regression

/-!
# Stablecoin — a medium with no past in the record (evidence, not theory)

One frame and one record in which a good is appraised as a medium of
exchange on a day with no earlier exchange of it in the record, and of
that case, which premises of `Apodictic.Regression.direct_acquisition_before`
hold and which fail. Nothing depends on it. It declares no claim.

Two parties, two goods, two ends. From day 1 on, everyone believes the
coin serves one end, spending it; nobody ever believes it serves the
other. On day 0 nobody believes anything of the coin, and the record of
day 0 is empty. On every later day the holder buys a coin from the
issuer for a dollar.

## What is proved

- The conclusion of the theorem fails: the coin is a medium on day 1,
  and on every later day, and no acquisition of it on any day was for
  an end other than passing it on (`medium_without_direct_acquisition`,
  `no_direct_acquisition`).
- One premise fails: `not_appraisalFromPast`. The appraisal on day 1
  has no exchange of the coin behind it.
- The other four hold: `twoDemands`, `begins`, `purposive`, and the
  medium itself (`medium`). `purposive` is not empty from day 2 on:
  the coin is acquired on day 1 (`acquired_day_one`).
- `not_appraisalFromPast_by_regress` reaches the same failure by
  handing the case to the theorem.
- `not_ownPastPrice`: the condition `History.OwnPastPrice` fails of it
  too, from day 2 on.

## What the case does NOT model

- The promise. Nothing here says why the coin is believed to serve
  spending: no redemption, no issuer's undertaking, no belief about
  one. The belief is supplied, as every belief in a frame is.
- The peg. No quantities, so no price of the coin in dollars, at par
  or below it.
- The prior money. The dollar is a good believed to serve the other
  end and nothing more; it is not appraised as a medium here, and it
  has no history of its own.
- That the record is complete. The claim is asserted of the record it
  is handed, and this record is built to have nothing in it on day 0.
-/

namespace ApodicticDraft
namespace Stablecoin

open Apodictic

/-- The two parties. -/
inductive Party
  | holder | issuer

/-- The two goods. -/
inductive Good
  | coin | dollar

/-- The two ends: spending a good onward, and using it up. -/
inductive Want
  | spend | consume

/-- The frame. The coin is believed, from day 1 on, to serve spending
and nothing else; the dollar is believed to serve consuming. -/
def frame : MediumFrame where
  Agent := Party
  End := Want
  Means := Good
  Time := ℕ
  Believes := fun _ t g e =>
    (g = Good.coin ∧ 0 < t ∧ e = Want.spend) ∨ (g = Good.dollar ∧ e = Want.consume)
  Prefers := fun _ _ _ _ => False
  Onward := fun g e => g = Good.coin ∧ e = Want.spend

/-- The day's issue: the holder gives a dollar and gets a coin. -/
def issue (k : ℕ) : Exchange frame.toActionFrame where
  first := ⟨Party.holder, k, Good.dollar, Good.coin, ∅, ∅⟩
  second := ⟨Party.issuer, k, Good.coin, Good.dollar, ∅, ∅⟩
  swap_gives := rfl
  swap_gets := rfl

/-- The record: nothing on day 0, one issue on each later day. -/
def history : History frame where
  date := fun k => k
  exchanges := fun k => {x | 0 < k ∧ x = issue k}

/-- The coin is appraised as a medium on every day after day 0. -/
theorem medium (n : ℕ) (hn : 0 < n) : history.MediumAt n Good.coin :=
  ⟨Party.holder, Want.spend, ⟨rfl, rfl⟩, Or.inl ⟨rfl, hn, rfl⟩⟩

/-- Nothing was exchanged on day 0. -/
theorem not_exchanged_day_zero (m : Good) : ¬ history.ExchangedOn 0 m := by
  rintro ⟨x, ⟨hpos, _⟩, _⟩
  exact Nat.lt_irrefl 0 hpos

/-- **The failing premise** — the claim `AppraisalFromPast` is false of
this record and the coin: the appraisal on day 1 has no exchange of the
coin on day 0 behind it. -/
theorem not_appraisalFromPast : ¬ AppraisalFromPast history Good.coin := by
  intro h
  obtain ⟨k, hk, hexchanged⟩ := h.fromPast 0 Party.holder
    ⟨Want.spend, ⟨rfl, rfl⟩, Or.inl ⟨rfl, Nat.zero_lt_one, rfl⟩⟩
  have hk0 : k = 0 := Nat.le_zero.mp hk
  rw [hk0] at hexchanged
  exact not_exchanged_day_zero Good.coin hexchanged

/-- Every end is onward for the coin, or not. -/
theorem twoDemands : TwoPartialDemands frame Good.coin :=
  ⟨fun e => by
    cases e with
    | spend => exact Or.inl ⟨rfl, rfl⟩
    | consume => exact Or.inr (fun h => Want.noConfusion h.2)⟩

/-- On day 0 nobody appraises the coin as a medium. -/
theorem begins : history.BeginsBeforeMedium Good.coin := by
  rintro ⟨_, _, _, ⟨_, hpos, _⟩ | ⟨hg, _⟩⟩
  · exact Nat.lt_irrefl 0 hpos
  · exact Good.noConfusion hg

/-- Whoever acquired the coin believed, that day, that it serves an
end: spending it. -/
theorem purposive (n : ℕ) : history.AcquisitionsPurposive Good.coin n := by
  rintro k _ _ _ ⟨_, ⟨hpos, _⟩, _⟩
  exact ⟨Want.spend, Or.inl ⟨rfl, hpos, rfl⟩⟩

/-- The coin is acquired on day 1, so `purposive` speaks of an
acquisition from day 2 on. -/
theorem acquired_day_one :
    history.AcquiredAgainst 1 Good.coin Party.holder Good.dollar :=
  ⟨issue 1, ⟨Nat.zero_lt_one, rfl⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- No acquisition of the coin, on any day, was for an end other than
passing it on. -/
theorem no_direct_acquisition (k : ℕ) : ¬ history.DirectAcquisitionAt k Good.coin := by
  rintro ⟨_, _, _, _, hnot, ⟨_, _, he⟩ | ⟨hg, _⟩⟩
  · exact hnot ⟨rfl, he⟩
  · exact Good.noConfusion hg

/-- **The conclusion fails** — the coin is a medium on day 1, with no
acquisition of it for an end other than passing it on before that
day. -/
theorem medium_without_direct_acquisition :
    history.MediumAt 1 Good.coin ∧ ∀ k < 1, ¬ history.DirectAcquisitionAt k Good.coin :=
  ⟨medium 1 Nat.zero_lt_one, fun k _ => no_direct_acquisition k⟩

/-- The same, on every later day: the conclusion of
`Regression.direct_acquisition_before` is false of the coin. -/
theorem no_direct_acquisition_before (n : ℕ) :
    ¬ ∃ k < n, history.DirectAcquisitionAt k Good.coin := by
  rintro ⟨k, _, hdirect⟩
  exact no_direct_acquisition k hdirect

/-- **The failing premise, found by the theorem** — the four premises
that hold, handed to `Regression.direct_acquisition_before` with the
claim, give an acquisition the case does not have. -/
theorem not_appraisalFromPast_by_regress : ¬ AppraisalFromPast history Good.coin := by
  intro h
  exact no_direct_acquisition_before 1
    (Regression.direct_acquisition_before history Good.coin 1 twoDemands h begins
      (purposive 1) (medium 1 Nat.zero_lt_one))

/-- The condition "own past price" fails of the coin from day 2 on. -/
theorem not_ownPastPrice (n : ℕ) (hn : 1 < n) : ¬ history.OwnPastPrice Good.coin n := by
  intro h
  obtain ⟨k, hk, hexchanged⟩ := h 0 hn Party.holder
    ⟨Want.spend, ⟨rfl, rfl⟩, Or.inl ⟨rfl, Nat.zero_lt_one, rfl⟩⟩
  have hk0 : k = 0 := Nat.le_zero.mp hk
  rw [hk0] at hexchanged
  exact not_exchanged_day_zero Good.coin hexchanged

#print axioms medium
#print axioms not_exchanged_day_zero
#print axioms not_appraisalFromPast
#print axioms twoDemands
#print axioms begins
#print axioms purposive
#print axioms acquired_day_one
#print axioms no_direct_acquisition
#print axioms medium_without_direct_acquisition
#print axioms no_direct_acquisition_before
#print axioms not_appraisalFromPast_by_regress
#print axioms not_ownPastPrice

end Stablecoin
end ApodicticDraft

#lint only unusedArguments
