import Mathlib.Data.Finset.Card
import Apodictic.Action

/-!
# Allocation — stocks of homogeneous units, allocation dispositions

Definitions ONLY (shape C): this file asserts nothing. Vocabulary for
the marginal-utility target: a stock of interchangeable units, and
the agent's counterfactual allocation disposition over it, indexed by
WHICH units — a sub-stock — not by how many.

Audit note (standing): praxeological claims hide in field SHAPES, where
no signature shows. Interchangeability of units was pulled out for
that reason and is now the named condition `Homogeneous`; one unit to
one end was pulled out and then dropped, no theorem needing it. What
is left in field position is `servesOnlyWhatItCan`, which cannot fail
of a real situation.
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
structure Stock (praxis : ActionFrame) (agent : praxis.Agent)
    (time : praxis.Time) where
  /-- The units of the good on hand. -/
  units : Finset praxis.Means
  /-- The ends this good can serve, by the agent's lights. -/
  serves : Set praxis.End
  /-- Every unit is believed to serve exactly the ends in
  `serves`. -/
  unitsAlike : ∀ unit ∈ units, ∀ want,
    praxis.Believes agent time unit want ↔ want ∈ serves

/-- The agent's plan for the stock: for each `subStock` — each set
of units he might have — the ends he WOULD serve with exactly those
units, at the stock's single time.

This is something new, over and above `Action`, and it has to be. A
single act of allocating cannot tell the served ends apart from one
another — they all sit inside the one package chosen. So what the law
of marginal utility rests on is not action at all: the plan is a
separate thing, and no act of the agent's exhibits it.

The plan is indexed by WHICH units, not by how many. To say it depends
only on the number of them is to say the units are interchangeable,
and that is not built in here: it is the named condition
`Homogeneous`, assumed only where a theorem needs it.

Field-shape claim (audit): `servesOnlyWhatItCan` is the one condition
left in field position, and it is definitional — a plan that puts a
unit to an end the good is not believed able to serve is not a
coherent plan, rather than a situation that might obtain.

One unit to one end is NOT here, and is nowhere: no theorem needs it.
Rothbard assumes it and says he is assuming it — "each unit of means
is capable of serving one of the ends", introduced with "We assume for
simplicity" (*MES* p. 26) — and the ordering the law asserts turns out
not to want it. Where an extra unit adds no new end, the law is
silent, which costs nothing. -/
structure AllocationPlan {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} (stock : Stock praxis agent time) where
  /-- The ends the agent would serve with exactly the units in
  `subStock`, and no others. -/
  wouldServe : Finset praxis.Means → Finset praxis.End
  /-- A unit is only ever put to an end the good is believed able to
  serve. -/
  servesOnlyWhatItCan : ∀ subStock, ∀ want ∈ wouldServe subStock,
    want ∈ stock.serves

/-- **Interchangeability of units** — a condition on the situation,
NOT a praxeological claim. The plan depends only on how many units there are,
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
def AllocationPlan.Homogeneous {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) : Prop :=
  ∀ fewer ⊆ stock.units, ∀ more ⊆ stock.units, fewer.card = more.card →
    plan.wouldServe fewer = plan.wouldServe more

/-- **Comparability of the ends a good can serve** — a condition on
the situation, NOT a praxeological claim (human ruling 2026-09-10).

Any two ends the good can serve are ranked one way or the other. It
is confined to one stock's serviceable ends, not asserted of every
pair of ends in the frame, because that is all any theorem needs.

Where it fails, a theorem carrying it is SILENT rather than false: an
agent may simply never have had occasion to rank two ends against each
other, and Rothbard's own doctrine — that scales are revealed in
action and nowhere else — makes such agents the normal case rather
than the exotic one. Mises says the same thing in almost the same
words: "the scale of values or wants manifests itself only in the
reality of action. These scales have no independent existence apart
from the actual behavior of individuals" (*Human Action*, ch. IV, §2).

Carried by the Mises route (`Apodictic.Mises.ladder_from_order`) and
by no theorem on the Rothbard route. That asymmetry is a finding:
swap dominance forces a comparison between every served end and every
unserved serviceable one, so this condition can only fail for a pair
that never straddles a margin — see
`Apodictic.Model.rothbard_applies_where_mises_is_silent`. -/
def Stock.ComparableServiceable {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} (stock : Stock praxis agent time) : Prop :=
  ∀ one ∈ stock.serves, ∀ other ∈ stock.serves, one ≠ other →
    praxis.PrefersEnd agent time one other ∨
      praxis.PrefersEnd agent time other one

/-- `more` is `fewer` plus one unit, both inside the stock. It is said
with an inclusion and a count rather than by naming the extra unit, so
that sub-stocks are only ever supposed and never constructed — which
is why nothing here needs to decide when two units are the same
unit. -/
def Stock.OneMore {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} (stock : Stock praxis agent time)
    (fewer more : Finset praxis.Means) : Prop :=
  fewer ⊆ more ∧ more ⊆ stock.units ∧ more.card = fewer.card + 1

/-- **An actual allocation** — what the agent does with the stock he
holds at its time: the ends he serves with it, and nothing else.

This is the object of the TEMPORAL reading of the law
(`Apodictic.Temporal`). Where `AllocationPlan` assigns served ends to
every sub-stock at once — the standing disposition the counterfactual
reading needs — this records one allocation of one stock at one
time. It is indexed by nothing: not by sub-stock, not by size. What
the agent would have done with fewer units is not in it and cannot be
asked of it. Mises's history — "if the supply available increases
from n–1 units to n units" — is then two of these at two times, not
one plan read at two sizes.

Field-shape claim (audit): `servesOnlyWhatItCan`, as for the plan, is
definitional — putting a unit to an end the good is not believed able
to serve is not an allocation of that good.

Like the plan, it is a thing over and above `Action`. An `Action` has
one chosen end; a stock of several units serving several ends is
several actions, or one action whose end is a bundle. Which of those
it is the library does not say, and no theorem asks. -/
structure Allocation {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} (stock : Stock praxis agent time) where
  /-- The ends the agent serves with the units he holds. -/
  served : Finset praxis.End
  /-- A unit is only ever put to an end the good is believed able to
  serve. -/
  servesOnlyWhatItCan : ∀ want ∈ served, want ∈ stock.serves

/-- **The supply grows by one** — Mises's "the supply available
increases from n–1 units to n units", read as a history: the stock at
the later time holds every unit of the stock at the earlier time and
one more.

Says nothing about the order of the two times. `Time` carries no
order, and this definition does not ask for one: "earlier" and
"later" are the names of the two arguments, not a relation between
their indices. Whether any theorem needs the order is exactly what
leaving it out will show. -/
def Stock.Grows {praxis : ActionFrame} {agent : praxis.Agent}
    {earlierTime laterTime : praxis.Time}
    (earlier : Stock praxis agent earlierTime)
    (later : Stock praxis agent laterTime) : Prop :=
  earlier.units ⊆ later.units ∧ later.units.card = earlier.units.card + 1

end Apodictic
