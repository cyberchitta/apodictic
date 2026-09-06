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
of `AllocationDisposition.card_eq`. Interchangeability of units no
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
action is not contradicted. Whether same-jobs homogeneity is enough
for the law, or whether indifference between units is needed after
all, stays something to check rather than something assumed away.

What a unit IS is left open: `units` lists whatever enters the action
as one thing. Rothbard holds that the law works "regardless of the
size of the unit considered. The size of the unit will be the one
that enters into concrete human action" (*MES* p. 28). Pairs of
horses make a different stock, with a "new and shorter scale of
ends", and a good that "cannot be divided into homogeneous units for
purposes of action" is a stock of exactly one unit. -/
structure Stock (F : ActionFrame) (agent : F.Agent) (t : F.Time) where
  /-- The units of the good on hand. -/
  units : Finset F.Means
  /-- The ends this good can serve, by the agent's lights. -/
  serves : Set F.End
  /-- Every unit is believed to serve exactly the ends in
  `serves`. -/
  homog : ∀ u ∈ units, ∀ e, F.Believes agent t u e ↔ e ∈ serves

/-- The agent's plan for the stock: for each sub-stock `U` — each set
of units he might have — the ends he WOULD serve with exactly those
units, at the stock's single time.

This is a new primitive, over and above `Action`, and it has to be.
One actual act of allocating cannot tell the served ends apart from
each other: they all sit inside the one package chosen. So whatever
the law of marginal utility rests on, it is not actual action alone.

The plan is indexed by WHICH units, not by how many. That it depends
only on the count is interchangeability of units, and that is not
built in here — it is the named condition `Homogeneous`, hypothesized
where a theorem needs it.

Field-shape commitment (audit): `card_eq` is the one-unit-per-end
idealization. With the units `U` (taken from the stock on hand),
exactly as many ends would be served as there are units: no unit is
split, pooled, or left idle. Rothbard says "each unit of means is
capable of serving one of the ends", and flags it — "We assume for
simplicity" (*MES* p. 26). The shape of the definition is
our-reconstruction. -/
structure AllocationDisposition {F : ActionFrame} {agent : F.Agent}
    {t : F.Time} (s : Stock F agent t) where
  /-- The ends that would be served with exactly the units `U`. -/
  wouldServe : Finset F.Means → Finset F.End
  /-- Units go only to ends the good is believed able to serve. -/
  serves_subset : ∀ U, ∀ e ∈ wouldServe U, e ∈ s.serves
  /-- One unit, one end; no idle units — within the actual stock. -/
  card_eq : ∀ U ⊆ s.units, (wouldServe U).card = U.card

/-- **Interchangeability of units** — a condition on the situation,
NOT a commitment. The plan depends only on how many units there are,
not on which ones: any two sub-stocks of the same size would serve
the same ends.

This is what makes "the plan at `n` units" — and so the marginal
utility of a supply of `n` — a function of `n` at all. Rothbard makes
it part of what a supply IS: "If a specific unit is differently
evaluated from all other units, then the supply of that good is only
one unit" (*MES* p. 23). Where it fails, the units are not one good,
and the supply-size form of the law does not treat them as one. Like
the plan it constrains, it speaks of sub-stocks the agent may not
hold. -/
def AllocationDisposition.Homogeneous {F : ActionFrame} {agent : F.Agent}
    {t : F.Time} {s : Stock F agent t} (A : AllocationDisposition s) : Prop :=
  ∀ U ⊆ s.units, ∀ V ⊆ s.units, U.card = V.card →
    A.wouldServe U = A.wouldServe V

/-- `V` is `U` plus one more unit, both inside the stock. Said with
inclusion and a count rather than by naming the extra unit, so that
sub-stocks are only ever hypothesized and never built — which is why
no decidable equality on units is needed anywhere. -/
def Stock.OneMore {F : ActionFrame} {agent : F.Agent} {t : F.Time}
    (s : Stock F agent t) (U V : Finset F.Means) : Prop :=
  U ⊆ V ∧ V ⊆ s.units ∧ V.card = U.card + 1

end Apodictic
