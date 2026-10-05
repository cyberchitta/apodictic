import ApodicticDraft.Indirect
import ApodicticDraft.Claims

/-!
# The two partial demands (T2, S2)

"Thus the demand for a medium of exchange is the composite of two
partial demands: the demand displayed by the intention to use it in
consumption and production and that displayed by the intention to use
it as a medium of exchange" (*Human Action*, ch. XVII, §4).

Here the two parts are the direct ends and the onward ends the agent
believes a good serves (`MediumFrame.DirectEnds`,
`MediumFrame.OnwardEnds`). "Direct" is "not onward", so the direct part
is the BROAD reading of Mises's "consumption and production" (M-2 (a));
the narrow reading is a condition, in `ApodicticDraft.Regress`.

## What is proved, and what it costs

- `partial_demands_within`: both parts lie inside what the good serves.
  Free.
- `partial_demands_not_not_exhaust`: every end the good serves is,
  not-not, in one part or the other. Free, and that is all that is free.
- `partial_demands_exhaust`: every end the good serves IS in one part
  or the other. It costs the claim `TwoPartialDemands`: every end is
  onward for `m` or not. Mises's "composite" is exhaustive only by
  excluded middle on the sort of an end, so the composite IS that
  excluded middle, carried as his claim (M-16).
- `only_onward_without_direct`: a good with no direct ends counts
  only for its onward ends. Same cost.
-/

namespace ApodicticDraft

open Apodictic

/-- **The two parts lie within what the good serves.** -/
theorem partial_demands_within {praxis : MediumFrame} (agent : praxis.Agent)
    (time : praxis.Time) (m : praxis.Means) :
    praxis.DirectEnds agent time m ∪ praxis.OnwardEnds agent time m ⊆
      praxis.ServedBy agent time {m} := by
  rw [servedBy_singleton]
  rintro e (⟨_, hbelief⟩ | ⟨_, hbelief⟩)
  · exact hbelief
  · exact hbelief

/-- **Not-not exhaustive** — without deciding the sort of an end, every
end the good serves is only not-not in one of the two parts. -/
theorem partial_demands_not_not_exhaust {praxis : MediumFrame}
    (agent : praxis.Agent) (time : praxis.Time) (m : praxis.Means) :
    ∀ e ∈ praxis.ServedBy agent time {m},
      ¬ ¬ (e ∈ praxis.DirectEnds agent time m ∪ praxis.OnwardEnds agent time m) := by
  rw [servedBy_singleton]
  intro e hbelief hout
  apply hout
  apply Or.inl
  refine ⟨?_, hbelief⟩
  intro honward
  exact hout (Or.inr ⟨honward, hbelief⟩)

/-- **The two partial demands exhaust what the good serves** — given
that every end is onward for `m` or not (`TwoPartialDemands`). -/
theorem partial_demands_exhaust {praxis : MediumFrame} (agent : praxis.Agent)
    (time : praxis.Time) (m : praxis.Means) (twoDemands : TwoPartialDemands praxis m) :
    praxis.ServedBy agent time {m} =
      praxis.DirectEnds agent time m ∪ praxis.OnwardEnds agent time m := by
  apply Set.Subset.antisymm
  · rw [servedBy_singleton]
    intro e hbelief
    rcases twoDemands.sorted e with honward | hdirect
    · exact Or.inr ⟨honward, hbelief⟩
    · exact Or.inl ⟨hdirect, hbelief⟩
  · exact partial_demands_within agent time m

/-- **Without direct ends, only onward ends** — a good the agent
believes serves no end other than passing it on counts, in his holding,
only for its onward ends. -/
theorem only_onward_without_direct {praxis : MediumFrame}
    (agent : praxis.Agent) (time : praxis.Time) (m : praxis.Means)
    (twoDemands : TwoPartialDemands praxis m)
    (noDirect : praxis.DirectEnds agent time m = ∅) :
    praxis.ServedBy agent time {m} = praxis.OnwardEnds agent time m := by
  rw [partial_demands_exhaust agent time m twoDemands, noDirect, Set.empty_union]

#print axioms partial_demands_within
#print axioms partial_demands_not_not_exhaust
#print axioms partial_demands_exhaust
#print axioms only_onward_without_direct

end ApodicticDraft

#lint only unusedArguments
