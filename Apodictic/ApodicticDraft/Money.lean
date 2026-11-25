import Apodictic

/-!
# Money — what the draft adds to the library's vocabulary of the time market

Definitions ONLY: this file asserts nothing. The vocabulary of the
interest theorems (`MoneyFrame`, the sums, the conditions) is the
library's, in `Apodictic.Money`. What is here serves only the draft's
rival encodings and the theorems not promoted with S2–S5.

- `ActionFrame.ServesOnly`: a good believed to serve one end, and only
  it (S1, `never_vanishes`, the availability reading).
- `HeldToTheSameUse`: the case Rothbard's footnote turns to.
-/

namespace ApodicticDraft

open Apodictic

/-- The agent, at that time, believes the good serves exactly the one
end `want`, and nothing else. The smallest case of a dated good: a
good whose service is one dated satisfaction. -/
def _root_.Apodictic.ActionFrame.ServesOnly (praxis : ActionFrame)
    (agent : praxis.Agent) (time : praxis.Time) (good : praxis.Means)
    (want : praxis.End) : Prop :=
  praxis.ServedBy agent time {good} = {want}

section Sums

variable {praxis : MoneyFrame} {agent : praxis.Agent} {now : praxis.Time}
  {present future : Stock praxis.toActionFrame agent now}

/-- **Held to the same use** — a condition on the situation, the case
Rothbard's footnote turns to: the agent would hold the present sum and
spend it on just what the claim would buy. Rothbard: "If a man wants to
“save” money for some future use, he may “hoard” it rather than spend
it on a future good, and thus have it always available" (*MES* p. 386
n. 11). It holds only where hoarding is free and the money keeps its
purchasing power; where holding costs, the hoarded sum buys less. -/
def HeldToTheSameUse (presentPlan : AllocationPlan present)
    (futurePlan : AllocationPlan future) (sum claim : Finset praxis.Means) :
    Prop :=
  presentPlan.wouldServe sum = futurePlan.wouldServe claim

end Sums

end ApodicticDraft
