import Apodictic.Urgency
import Apodictic.Mises

/-!
# Contrast — the two routes compared

`Apodictic.Mises` is deliberately isolated: it cannot see Rothbard's
results, so that whatever the Mises route spends has to be stated
there and shows on the signature. This module is where the isolation
is lifted ON PURPOSE, and for one job only: relating the two premise
sets to each other.

Nothing here is a new derivation of the law. Both routes already
reach `Mises.LadderHolds` — `Mises.ladder_holds` from
`SwapDominant` + `IndependentUses`, and `Mises.ladder_from_order`
from `ServedInOrder` + `ComparableServiceable`. The question this
module answers is whether those two premise sets are independent.
-/

namespace Apodictic
namespace Contrast

/-- **Rothbard's premises entail Mises's bridge.**

Given swap dominance, independence of uses and asymmetry, the agent
serves in order of urgency — which is exactly `Mises.ServedInOrder`,
the premise the Misesian route was built on.

So the two routes are NOT independent. Whatever else is true of
Mises's derivation, its premise is available to anyone who already
has Rothbard's, and the second route buys no premise the first
lacked.

The proof is the contrapositive of `served_over_unserved`. Suppose
the more urgent end were left unserved. Then Rothbard's workhorse
says the served end is preferred to it — and asymmetry contradicts
the assumption that it was the more urgent of the two. The case split
on whether the end is served is decidable, not classical:
`plan.wouldServe subStock` is a `Finset`, so membership is decidable
given `[DecidableEq praxis.End]`, which the route already carries. -/
theorem rothbard_entails_servedInOrder
    {praxis : ActionFrame} [DecidableEq praxis.End]
    {agent : praxis.Agent} {time : praxis.Time}
    {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) (dominance : SwapDominant plan)
    (independent : praxis.IndependentUses agent time)
    (asymmetric : AsymmetricPreference praxis agent time) :
    ServedInOrder plan := by
  refine ⟨?_⟩
  intro subStock onHand served hserved better hbetterServes hbetterUrgent
  by_cases hmem : better ∈ plan.wouldServe subStock
  · exact hmem
  · exact absurd hbetterUrgent
      (asymmetric.asym _ _
        (served_over_unserved plan dominance independent subStock onHand
          served hserved better hbetterServes hmem))

#print axioms rothbard_entails_servedInOrder

end Contrast
end Apodictic

#lint only unusedArguments
