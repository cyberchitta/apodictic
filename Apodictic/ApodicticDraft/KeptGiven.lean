import Apodictic.Exchange

/-!
# A good both given and kept — what `KeptServesOtherEnds` leaves of it

`Trade` reads `kept` as the rest of the holding, but does not require
the given or the received good to be outside it. The substitutes
condition `KeptServesOtherEnds`, carried by every theorem that ranks the
two goods, nearly rules the case out: a traded good that is also kept
can satisfy it only by being believed to serve no end at all.

No claim. Checks a sentence of the *Exchange* page against the Lean.
-/

namespace ApodicticDraft

open Apodictic

theorem servedBy_mono {praxis : ActionFrame} (agent : praxis.Agent)
    (time : praxis.Time) {goods more : Set praxis.Means} (sub : goods ⊆ more) :
    praxis.ServedBy agent time goods ⊆ praxis.ServedBy agent time more :=
  fun _ ⟨good, mem, believed⟩ => ⟨good, sub mem, believed⟩

/-- A good given and also kept, under `KeptServesOtherEnds`, is believed
at the trade to serve nothing. -/
theorem given_kept_serves_nothing {praxis : ActionFrame} (trade : Trade praxis)
    (unique : trade.KeptServesOtherEnds) (givenKept : trade.gives ∈ trade.kept) :
    praxis.ServedBy trade.agent trade.time {trade.gives} = ∅ :=
  Set.eq_empty_of_subset_empty
    (unique.1 (le_refl _)
      (servedBy_mono trade.agent trade.time
        (fun x (h : x = trade.gives) => h ▸ givenKept)))

/-- A good received and already held, under `KeptServesOtherEnds`, is
believed at the trade to serve nothing. -/
theorem received_kept_serves_nothing {praxis : ActionFrame} (trade : Trade praxis)
    (unique : trade.KeptServesOtherEnds) (receivedKept : trade.gets ∈ trade.kept) :
    praxis.ServedBy trade.agent trade.time {trade.gets} = ∅ :=
  Set.eq_empty_of_subset_empty
    (unique.2 (le_refl _)
      (servedBy_mono trade.agent trade.time
        (fun x (h : x = trade.gets) => h ▸ receivedKept)))

#print axioms given_kept_serves_nothing
#print axioms received_kept_serves_nothing

end ApodicticDraft

#lint only unusedArguments
