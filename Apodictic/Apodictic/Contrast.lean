import Apodictic.Urgency
import Apodictic.MarginalUtility
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

Grant swap dominance (`SwapDominant`), independence of uses
(`IndependentUses agent time`) and asymmetry of preference
(`AsymmetricPreference`). Then the agent serves in order of urgency.
That is exactly `ServedInOrder`, the premise the Misesian route was
built on.

So the two routes are NOT independent. Whatever else is true of
Mises's derivation, its premise is available to anyone who already
has Rothbard's. The second route's bridge (`ServedInOrder`)
therefore adds no premise the first route lacked.

The proof is the contrapositive of `served_over_unserved`. Suppose
the more urgent end were left unserved. Then Rothbard's workhorse,
`served_over_unserved`, says the served end is preferred to it. And
asymmetry contradicts the assumption that it was the more urgent of
the two. The case split on whether the end is served is decidable,
not classical. `plan.wouldServe subStock` is a `Finset`. So membership
is decidable given `[DecidableEq praxis.End]`, which the route already
carries. -/
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

/-- **The two definitions of the marginal ends coincide.** One is
Mises's "marginal employment" (`Mises.marginalEmployment`). It is the
employment a man makes at `n` units and would not make at `n–1`. The
other is Rothbard's marginal utility of a supply (`marginalEnds`). It
is the set of ends the larger stock serves and the smaller does not.
The two are the same set, definitionally. Each module states its own, because
`Apodictic.Mises` is isolated. That they agree is proved here, where
both are in scope. The agreement is what licenses saying the two
routes reach the same law. -/
theorem marginalEmployment_eq_marginalEnds
    {praxis : ActionFrame}
    {agent : praxis.Agent} {time : praxis.Time}
    {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) (fewer more : Finset praxis.Means) :
    Mises.marginalEmployment plan fewer more = marginalEnds plan fewer more :=
  rfl

#print axioms marginalEmployment_eq_marginalEnds

end Contrast
end Apodictic

#lint only unusedArguments
