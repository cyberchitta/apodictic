import ApodicticDraft.Medium

/-!
# Indirect exchange (T2, S1)

A medium of exchange is wanted "to keep it as a medium of exchange and
to give it away at need in a later act of exchange" (*Human Action*,
ch. XVII, §4). In the library's vocabulary that is a trade whose
received good the agent believes serves onward ends.

## What is proved, and what it costs

- `indirect_ranks_onward_ends`: in a purely indirect trade, the agent
  ranks the ends he expects to reach by passing the good on above the
  ends of the good he gave. No new claim: it is
  `Apodictic.MutualBenefit.ranks_received_above_given`, applied, with
  `ServedBy` counting onward ends like any other. What indirect exchange
  adds is the condition `Trade.PurelyIndirect`, which turns the
  received good's bundle into its onward ends.
-/

namespace ApodicticDraft

open Apodictic

/-- A good counts, alone, for exactly the ends it is believed to serve.
Bookkeeping. -/
theorem servedBy_singleton {praxis : ActionFrame} (agent : praxis.Agent)
    (time : praxis.Time) (m : praxis.Means) :
    praxis.ServedBy agent time {m} = {e | praxis.Believes agent time m e} := by
  ext e
  constructor
  · rintro ⟨good, hgood, hbelief⟩
    rw [Set.mem_singleton_iff.mp hgood] at hbelief
    exact hbelief
  · intro hbelief
    exact ⟨m, Set.mem_singleton m, hbelief⟩

/-- **Indirect exchange ranks onward ends** — in a trade where the
agent wants the received good only to pass it on, he ranks the ends he
expects to reach by passing it on above the ends of the good he gave,
on his scale at the time of trading. -/
theorem indirect_ranks_onward_ends {praxis : MediumFrame}
    (trade : Trade praxis.toActionFrame)
    (demonstrated : DemonstratedPreference trade)
    (voluntary : trade.Voluntary)
    (separable : trade.SeparableFromRest)
    (unique : trade.KeptServesOtherEnds)
    (pure : Trade.PurelyIndirect trade) :
    praxis.Prefers trade.agent trade.time
      (praxis.OnwardEnds trade.agent trade.time trade.gets)
      (praxis.ServedBy trade.agent trade.time {trade.gives}) := by
  have hranks := MutualBenefit.ranks_received_above_given trade demonstrated
    voluntary separable unique
  have honward : praxis.ServedBy trade.agent trade.time {trade.gets} =
      praxis.OnwardEnds trade.agent trade.time trade.gets := by
    rw [servedBy_singleton]
    ext e
    constructor
    · intro hbelief
      exact ⟨pure e hbelief, hbelief⟩
    · rintro ⟨_, hbelief⟩
      exact hbelief
  rw [honward] at hranks
  exact hranks

#print axioms servedBy_singleton
#print axioms indirect_ranks_onward_ends

end ApodicticDraft

#lint only unusedArguments
