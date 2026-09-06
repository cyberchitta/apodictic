import Mathlib.Data.Finset.Card
import Apodictic.Action

/-!
# Allocation — stocks of homogeneous units, allocation dispositions

Definitions ONLY (shape C): this file asserts nothing. Vocabulary for
the marginal-utility target: a stock of interchangeable units, and
the agent's counterfactual allocation disposition over it, indexed by
WHICH units — a sub-stock — not by how many.

Audit note (standing): commitments hide in field SHAPES, where
no signature shows. One lives here — see the docstring
of `AllocationPlan.oneUnitOneEnd`. Interchangeability of units no
longer does: it is the named condition `Homogeneous`, a hypothesis of
the theorems that need it.
-/

namespace Apodictic

/-- A stock of some good, held by one agent at one time: finitely many
units the agent believes will do the same jobs.

"The same jobs" is the whole of what homogeneity means here. Each
unit is believed to serve exactly the ends in `serves`, and that is a
claim about BELIEF, not about preference. Nowhere is it said that the
agent is indifferent between units. So preference can stay strict,
and Rothbard's denial that indifference is ever demonstrated in
action is not contradicted. Whether doing the same jobs is enough for
the law, or whether indifference between units is needed after all,
is then something to check rather than something assumed away.

What counts as a unit is left open: `units` lists whatever enters the
action as one thing. Rothbard holds that the law works "regardless of the
size of the unit considered. The size of the unit will be the one
that enters into concrete human action" (*MES* p. 28). Pairs of
horses make a different stock, with a "new and shorter scale of
ends", and a good that "cannot be divided into homogeneous units for
purposes of action" is a stock of exactly one unit. -/
structure Stock (frame : ActionFrame) (agent : frame.Agent)
    (time : frame.Time) where
  /-- The units of the good on hand. -/
  units : Finset frame.Means
  /-- The ends this good can serve, by the agent's lights. -/
  serves : Set frame.End
  /-- Every unit is believed to serve exactly the ends in
  `serves`. -/
  unitsAlike : ∀ unit ∈ units, ∀ want,
    frame.Believes agent time unit want ↔ want ∈ serves

/-- The agent's plan for the stock: for each `subStock` — each set
of units he might have — the ends he WOULD serve with exactly those
units, at the stock's single time.

This is something new, over and above `Action`, and it has to be. A
single act of allocating cannot tell the served ends apart from one
another — they all sit inside the one package chosen. So whatever the
law of marginal utility rests on, it is not action alone.

The plan is indexed by WHICH units, not by how many. To say it depends
only on the number of them is to say the units are interchangeable,
and that is not built in here: it is the named condition
`Homogeneous`, assumed only where a theorem needs it.

Field-shape commitment (audit): `oneUnitOneEnd` says one unit serves
one end. Take any sub-stock of the units on hand, and exactly as many
ends would be served as there are units — no unit split, pooled, or
left idle. Rothbard says "each unit of means is
capable of serving one of the ends", and flags it — "We assume for
simplicity" (*MES* p. 26). The shape of the definition is
our-reconstruction. -/
structure AllocationPlan {frame : ActionFrame} {agent : frame.Agent}
    {time : frame.Time} (stock : Stock frame agent time) where
  /-- The ends the agent would serve with exactly the units in
  `subStock`, and no others. -/
  wouldServe : Finset frame.Means → Finset frame.End
  /-- A unit is only ever put to an end the good is believed able to
  serve. -/
  servesOnlyWhatItCan : ∀ subStock, ∀ want ∈ wouldServe subStock,
    want ∈ stock.serves
  /-- One unit, one end; no idle units — within the actual stock. -/
  oneUnitOneEnd : ∀ subStock ⊆ stock.units,
    (wouldServe subStock).card = subStock.card

/-- **Interchangeability of units** — a condition on the situation,
NOT a commitment. The plan depends only on how many units there are,
not on which ones: any two sub-stocks of the same size would serve
the same ends.

Without it, the phrase "the plan at `n` units" — and so the marginal
utility of a supply of `n` — picks out nothing in particular. Rothbard
makes interchangeability part of what a supply IS: "If a specific unit
is differently evaluated from all other units, then the supply of that
good is only one unit" (*MES* p. 23). Where it fails, the units are
not one good, and the supply-size form of the law does not treat them
as one. Like the plan it constrains, it speaks of sub-stocks the agent
may not hold. -/
def AllocationPlan.Homogeneous {frame : ActionFrame} {agent : frame.Agent}
    {time : frame.Time} {stock : Stock frame agent time}
    (plan : AllocationPlan stock) : Prop :=
  ∀ fewer ⊆ stock.units, ∀ more ⊆ stock.units, fewer.card = more.card →
    plan.wouldServe fewer = plan.wouldServe more

/-- `more` is `fewer` plus one unit, both inside the stock. It is said
with an inclusion and a count rather than by naming the extra unit, so
that sub-stocks are only ever supposed and never constructed — which
is why nothing here needs to decide when two units are the same
unit. -/
def Stock.OneMore {frame : ActionFrame} {agent : frame.Agent}
    {time : frame.Time} (stock : Stock frame agent time)
    (fewer more : Finset frame.Means) : Prop :=
  fewer ⊆ more ∧ more ⊆ stock.units ∧ more.card = fewer.card + 1

end Apodictic
