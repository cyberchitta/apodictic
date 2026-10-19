import ApodicticDraft.PriceControl

/-!
# PriceControlToy — non-vacuity of link 1, and two edge cases (evidence, not theory)

Nothing depends on it. Prices are whole numbers (ounces, say). Two
buyers, two sellers, each seller with one unit.

- **`ordinary`**: homogeneous units, a clearing price of 7, and someone
  between 5 and 7. Every condition of `supplied_lt_demanded` holds; the
  theorem is handed the market (`ordinary_shortage`).
- **`jobs`**: the same numbers read as labor. The buyers are employers,
  the sellers are workers, one unit is one worker's service. A minimum
  wage of 9, above the clearing wage of 7, gives more workers willing
  than employers (`jobs_surplus`). The reading is all there is to it:
  Lean sees the same market.
- **`wholeUnits`**: no price clears (`wholeUnits_never_clears`). One
  buyer would pay at most 1; two sellers would each take 1. At 0 there
  is one buyer and no seller; at 1, one buyer and two sellers; above 1,
  no buyer. Rothbard allows the case: "It is possible that the
  equilibrium point will not be uniquely determined at one definite
  price" (*MES* p. 116 n. 25), and rescues it by divisible units. So
  PC-5's hypothesis can fail of a market of whole units.
- **`unlike`**: units NOT homogeneous — one buyer would pay 10 for the
  first seller's unit and 3 for the second's — yet 7 clears and the
  static inequality applies (`unlike_not_homogeneous`,
  `unlike_shortage`). SUP-1 is not what the inequality rests on.
-/

namespace ApodicticDraft
namespace PriceControlToy

open Apodictic

/-- Two buyers and two sellers. -/
inductive Trader
  | buyerA | buyerB | sellerA | sellerB
  deriving DecidableEq

/-- A frame with traders and nothing else: the market's data are its
limit prices, given (I-10 (b)). -/
abbrev frame : ActionFrame where
  Agent := Trader
  End := Unit
  Means := Unit
  Time := Unit
  Believes _ _ _ _ := False
  Prefers _ _ _ _ := False

open Trader

/-- Buyer A would pay up to 10, buyer B up to 6, for either unit; seller
A would take 4, seller B 8. -/
def ordinary : Market frame () ℕ where
  buyers := {buyerA, buyerB}
  sellers := {sellerA, sellerB}
  topPrice buyer _ := match buyer with
    | buyerA => 10
    | _ => 6
  floorPrice seller := match seller with
    | sellerA => 4
    | _ => 8

/-- The same numbers, read as labor: employers A and B, workers A and B. -/
def jobs : Market frame () ℕ := ordinary

/-- One buyer who would pay up to 1; two sellers who would each take 1. -/
def wholeUnits : Market frame () ℕ where
  buyers := {buyerA}
  sellers := {sellerA, sellerB}
  topPrice _ _ := 1
  floorPrice _ := 1

/-- As `ordinary`, except that buyer A would pay only 3 for seller B's
unit. -/
def unlike : Market frame () ℕ where
  buyers := {buyerA, buyerB}
  sellers := {sellerA, sellerB}
  topPrice buyer seller := match buyer, seller with
    | buyerA, sellerA => 10
    | buyerA, _ => 3
    | _, _ => 6
  floorPrice seller := match seller with
    | sellerA => 4
    | _ => 8

theorem ordinary_homogeneous : ordinary.Homogeneous := by
  intro buyer _ seller _ other _
  rfl

theorem ordinary_clears : ordinary.Clears 7 := by unfold Market.Clears; decide

theorem ordinary_between : ordinary.Between 5 7 := by
  left
  exact ⟨buyerB, by decide, by decide, by decide⟩

/-- The strict static inequality, handed the toy. -/
theorem ordinary_shortage : ordinary.supplied 5 < ordinary.demanded 5 :=
  ordinary.supplied_lt_demanded ordinary_clears (by decide) ordinary_between

theorem jobs_between : jobs.Between 7 9 := by
  right
  exact ⟨sellerB, by decide, by decide, by decide⟩

/-- The mirror, read of labor: at a minimum wage of 9, fewer employers
than workers are willing. -/
theorem jobs_surplus : jobs.demanded 9 < jobs.supplied 9 :=
  jobs.demanded_lt_supplied ordinary_clears (by decide) jobs_between

theorem wholeUnits_never_clears (p : ℕ) : ¬ wholeUnits.Clears p := by
  match p with
  | 0 => unfold Market.Clears; decide
  | 1 => unfold Market.Clears; decide
  | n + 2 =>
    intro h
    have hd : wholeUnits.demanded (n + 2) = 0 := by
      unfold Market.demanded
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro buyer _ hwilling
      obtain ⟨_, _, hle⟩ := hwilling
      have : n + 2 ≤ 1 := hle
      omega
    have hs : wholeUnits.supplied (n + 2) = 2 := by
      unfold Market.supplied
      rw [Finset.filter_true_of_mem]
      · rfl
      · intro seller _
        show 1 ≤ n + 2
        omega
    unfold Market.Clears at h
    rw [hd, hs] at h
    exact absurd h (by decide)

theorem unlike_not_homogeneous : ¬ unlike.Homogeneous := by
  intro h
  have := h buyerA (by decide) sellerA (by decide) sellerB (by decide)
  exact absurd this (by decide)

theorem unlike_clears : unlike.Clears 7 := by unfold Market.Clears; decide

/-- The static inequality, with units that are not homogeneous. -/
theorem unlike_shortage : unlike.supplied 5 ≤ unlike.demanded 5 :=
  unlike.supplied_le_demanded unlike_clears (by decide)

#print axioms ordinary_shortage
#print axioms jobs_surplus
#print axioms wholeUnits_never_clears
#print axioms unlike_not_homogeneous
#print axioms unlike_shortage

end PriceControlToy
end ApodicticDraft

#lint only unusedArguments
