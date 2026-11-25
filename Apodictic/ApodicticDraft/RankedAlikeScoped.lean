import ApodicticDraft.ValuedAlike

/-!
# Ranked alike, scoped — the library's condition against the stock-wide rival

The library's S3–S5 (`Apodictic.PureInterest`) carry
`RankedAlikeNowOf`: the agent ranks the claim against the lesser sum
now as he would at the spending, for that one comparison. The rival,
`RankedAlikeNow` (in `ApodicticDraft.ValuedAlike`), asks it of every
pair of sums in the stock, one part of the other.

## What is proved

- `rankedAlikeOf_of_rankedAlike`: the stock-wide condition gives the
  scoped one, with interchangeable units and asymmetry at the spending.
  So the scoped condition asks no more.
- `ImpulseToy.not_rankedAlikeOf`: the man whose valuations change fails
  the scoped condition too, for his ounce against no cash. The failure
  still lands on a condition.

Not built: a case where the scoped condition holds and the stock-wide
one fails, which would show that the scoped one asks strictly less.
-/

namespace ApodicticDraft
namespace ValuedAlike

open Apodictic Interest Satiation

section Plans

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {stock : Stock praxis.toActionFrame agent now}

/-- The stock-wide condition gives the scoped one. -/
theorem rankedAlikeOf_of_rankedAlike (plan : AllocationPlan stock)
    (spend : praxis.Time) (claim lesser : Finset praxis.Means)
    (claimIn : claim ⊆ stock.units) (lesserIn : lesser ⊆ stock.units)
    (notMore : lesser.card ≤ claim.card)
    (homogeneous : plan.Homogeneous)
    (asymmetric : AsymmetricPreference praxis.toActionFrame agent spend)
    (alike : RankedAlikeNow plan spend) :
    RankedAlikeNowOf plan spend claim lesser := by
  intro atSpend
  rcases Nat.eq_or_lt_of_le notMore with equal | fewer
  · rw [homogeneous lesser lesserIn claim claimIn equal] at atSpend
    exact (asymmetric.asym _ _ atSpend atSpend).elim
  · obtain ⟨part, partIn, partCard⟩ :=
      exists_part_of_card claim lesser.card (Nat.le_of_lt fewer)
    have same : plan.wouldServe part = plan.wouldServe lesser :=
      homogeneous part (fun _ h => claimIn (partIn h)) lesser lesserIn partCard
    have proper : part ⊂ claim := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨partIn, fun equal => ?_⟩
      rw [equal] at partCard
      rw [partCard] at fewer
      exact Nat.lt_irrefl _ fewer
    rw [← same] at atSpend ⊢
    exact alike part claim proper claimIn atSpend

end Plans

namespace ImpulseToy

/-- **The scoped condition fails too**: at date 1 he ranks what an
ounce buys above what no cash buys, and at date 0 he does not. -/
theorem not_rankedAlikeOf :
    ¬ RankedAlikeNowOf (praxis := frame) plan (1 : ℕ) {.ounce} ∅ := by
  intro alike
  have now := alike (by
    rw [buys_empty, buys_ounce]
    exact Or.inr ⟨rfl, coe_single impulse, coe_none⟩)
  rw [buys_empty, buys_ounce] at now
  rcases now with ⟨_, hX, _⟩ | ⟨one, _, _⟩
  · exact impulse_ne_empty (by rw [← coe_single]; exact hX)
  · exact Nat.zero_ne_one one

end ImpulseToy

#print axioms rankedAlikeOf_of_rankedAlike
#print axioms ImpulseToy.not_rankedAlikeOf

end ValuedAlike
end ApodicticDraft

#lint only unusedArguments
