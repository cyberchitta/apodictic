import Mathlib.Data.Finset.Card
import Apodictic.Action

/-!
# Allocation — stocks of homogeneous units, allocation dispositions

Definitions ONLY (shape C): this file asserts nothing. Vocabulary for
the marginal-utility target: a stock of interchangeable units, and
the agent's counterfactual allocation disposition over it, indexed by
WHICH units — a sub-stock — not by how many.

Audit note (standing): commitments hide in field SHAPES, where
`#print axioms` cannot see them. One lives here — see the docstring
of `AllocationDisposition.card_eq`. Interchangeability of units no
longer does: it is the named condition `Homogeneous`, a hypothesis of
the theorems that need it.
-/

namespace Apodictic

/-- A stock of a good, for one agent at one time: finitely many
unit-means the agent believes equally serviceable. Homogeneity is
serviceability-homogeneity: each unit is believed to conduce to
exactly the ends in `serves` — a BELIEF notion, not a preference
notion. No indifference between units is asserted anywhere, so the
strict-only `Prefers` stands and Rothbard's denial that indifference
is demonstrable in action is not contradicted. Whether
serviceability-homogeneity suffices for the law — Nozick (1977,
p. 371) says the law needs indifference — stays checkable rather
than assumed away.

What a unit IS is not fixed here: `units` lists whatever enters the
action as one thing. Rothbard: the law holds "regardless of the size
of the unit considered. The size of the unit will be the one that
enters into concrete human action" (*MES* p. 28) — pairs of horses
are a different stock with a "new and shorter scale of ends", and a
good that "cannot be divided into homogeneous units for purposes of
action" is a stock of one unit. -/
structure Stock (F : ActionFrame) (agent : F.Agent) (t : F.Time) where
  /-- The units of the good on hand. -/
  units : Finset F.Means
  /-- The ends this good is serviceable for, by the agent's lights. -/
  serves : Set F.End
  /-- Equal serviceability: every unit is believed serviceable for
  exactly `serves`. -/
  homog : ∀ u ∈ units, ∀ e, F.Believes agent t u e ↔ e ∈ serves

/-- The agent's counterfactual allocation disposition over a stock:
for each sub-stock `U` — each set of units the agent might have — the
ends the agent would serve with exactly those units, at the stock's
single time. A NEW PRIMITIVE beyond `Action`, because a single actual
allocation action cannot discriminate among the served ends (they
are all inside the chosen package); whatever the law of marginal
utility rests on, it is not actual action alone.

Indexed by WHICH units, not how many: that the plan depends only on
the count is interchangeability of units, and it is not built in —
it is the named condition `Homogeneous`, hypothesized where a theorem
needs it.

Field-shape commitment (audit): `card_eq` is the one-unit-per-end
idealization — with the units `U` (within the stock on hand), exactly
as many ends would be served as there are units; units are not
split, pooled, or left idle. Rothbard: "each unit of means is capable
of serving one of the ends" — "We assume for simplicity" (*MES*
p. 26). The definitional shape is our-reconstruction. -/
structure AllocationDisposition {F : ActionFrame} {agent : F.Agent}
    {t : F.Time} (s : Stock F agent t) where
  /-- With exactly the units `U`, the ends that would be served. -/
  wouldServe : Finset F.Means → Finset F.End
  /-- Allocation only to ends the good is believed serviceable
  for. -/
  serves_subset : ∀ U, ∀ e ∈ wouldServe U, e ∈ s.serves
  /-- One unit, one end; no idle units — within the actual stock. -/
  card_eq : ∀ U ⊆ s.units, (wouldServe U).card = U.card

/-- **Interchangeability of units** — a situational applicability
condition, NOT an axiom: the plan depends only on how many units, not
which. Two sub-stocks of the same size would serve the same ends.
This is what makes "the plan at `n` units" — and so the marginal
utility of a supply of `n` — a function of `n`. Rothbard makes it
definitional of a supply: "If a specific unit is differently
evaluated from all other units, then the supply of that good is only
one unit" (*MES* p. 23) — where it fails, the units are not one good,
and the law in its supply-size form does not apply to them as one.
Subjunctive, like the disposition it constrains. -/
def AllocationDisposition.Homogeneous {F : ActionFrame} {agent : F.Agent}
    {t : F.Time} {s : Stock F agent t} (A : AllocationDisposition s) : Prop :=
  ∀ U ⊆ s.units, ∀ V ⊆ s.units, U.card = V.card →
    A.wouldServe U = A.wouldServe V

/-- `V` is `U` plus one unit, within the stock. Stated by inclusion
and cardinality, so that the sub-stocks are hypothesized, never
constructed — no decidable equality on units is needed anywhere. -/
def Stock.OneMore {F : ActionFrame} {agent : F.Agent} {t : F.Time}
    (s : Stock F agent t) (U V : Finset F.Means) : Prop :=
  U ⊆ V ∧ V ⊆ s.units ∧ V.card = U.card + 1

end Apodictic
