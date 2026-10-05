import ApodicticDraft.PriorMoney

/-!
# Toy — non-vacuity of the T2 draft (evidence, not theory)

The draft counterpart of `Apodictic.Consistency`, for T2 only: one frame
in which the claim `AppraisalFromPast` and every condition the T2
theorems carry hold together, AND a medium exists — so the regress
theorems are not true for want of a case. Nothing depends on it.

One agent, one good, two ends: `false` (eat it) and `true` (pass it on).
On day 0 the good is believed to serve only eating; from day 1 on, also
passing on. The good is exchanged every day (against itself: `Trade`
does not require two goods).
-/

namespace ApodicticDraft
namespace Toy

open Apodictic

/-- The toy frame. -/
def frame : MediumFrame where
  Agent := Unit
  End := Bool
  Means := Unit
  Time := ℕ
  Believes := fun _ t _ e => e = false ∨ (0 < t ∧ e = true)
  Prefers := fun _ _ _ _ => False
  Onward := fun _ e => e = true

theorem twoDemands : TwoPartialDemands frame () :=
  ⟨fun e => by
    cases e with
    | false => exact Or.inr Bool.false_ne_true
    | true => exact Or.inl rfl⟩

/-- The day's exchange. -/
def dayExchange (k : ℕ) : Exchange frame.toActionFrame where
  first := ⟨(), k, (), (), ∅, ∅⟩
  second := ⟨(), k, (), (), ∅, ∅⟩
  swap_gives := rfl
  swap_gets := rfl

/-- The toy record: one exchange each day. -/
def history : History frame where
  date := fun k => k
  exchanges := fun k => {dayExchange k}

theorem appraisal : AppraisalFromPast history () :=
  ⟨fun _ _ _ => ⟨0, Nat.zero_le _, dayExchange 0, rfl, Or.inl rfl⟩⟩

theorem begins : history.BeginsBeforeMedium () := by
  rintro ⟨_, e, honward, hfalse | ⟨hpos, _⟩⟩
  · have h1 : e = true := honward
    rw [h1] at hfalse
    exact Bool.noConfusion hfalse
  · exact Nat.lt_irrefl 0 hpos

theorem purposive (n : ℕ) : history.AcquisitionsPurposive () n :=
  fun _ _ _ _ _ => ⟨false, Or.inl rfl⟩

theorem medium : history.MediumAt 1 () :=
  ⟨(), true, rfl, Or.inr ⟨Nat.zero_lt_one, rfl⟩⟩

theorem barter : history.FormedInBarter () 1 := by
  intro k hk _ _ _ hmedium
  have hk0 : k = 0 := Nat.lt_one_iff.mp hk
  rw [hk0] at hmedium
  exact begins hmedium

theorem narrowReading :
    history.OtherEmploymentsNarrow (fun e => e = false) () 1 := by
  intro _ _ _ _ _ e hnot hbelief
  rcases hbelief with hfalse | ⟨_, htrue⟩
  · exact hfalse
  · exact absurd htrue hnot

/-- **Non-vacuity** — the claim and every condition of the barter and
narrow theorems hold, together with a medium on day 1, and the positive
theorem finds the direct acquisition. -/
theorem toy_nonvacuous :
    ∃ k < 1, ∃ agent g, history.AcquiredAgainst k () agent g ∧
      frame.ValuesDirectly agent (history.date k) () ∧ ¬ history.MediumAt k g :=
  barter_origin history () 1 twoDemands appraisal begins (purposive 1) barter medium

theorem toy_narrow : ∃ k < 1, history.NarrowAcquisitionAt (fun e => e = false) k () :=
  narrow_acquisition_before history (fun e => e = false) () 1 twoDemands appraisal begins
    (purposive 1) narrowReading medium

#print axioms toy_nonvacuous
#print axioms toy_narrow

end Toy
end ApodicticDraft
