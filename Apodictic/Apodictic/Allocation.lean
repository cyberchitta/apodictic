import Mathlib.Data.Finset.Card
import Apodictic.Action

/-!
# Allocation — stocks of homogeneous units, allocation dispositions

Definitions ONLY (shape C): this file asserts nothing. Vocabulary for
the marginal-utility target: a stock of interchangeable units, and
the agent's counterfactual allocation disposition over it.

Audit note (standing): commitments hide in field SHAPES, where
`#print axioms` cannot see them. Two live here — see the docstrings
of `Stock` and `AllocationDisposition.wouldServe`.
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
than assumed away. -/
structure Stock (F : ActionFrame) (agent : F.Agent) (t : F.Time) where
  /-- The units of the good on hand. -/
  units : Finset F.Means
  /-- The ends this good is serviceable for, by the agent's lights. -/
  serves : Set F.End
  /-- Equal serviceability: every unit is believed serviceable for
  exactly `serves`. -/
  homog : ∀ u ∈ units, ∀ e, F.Believes agent t u e ↔ e ∈ serves

/-- The agent's counterfactual allocation disposition over a stock:
for each supply size `n`, the ends the agent would serve with `n`
units, at the stock's single time. A NEW PRIMITIVE beyond `Action`,
because a single actual allocation action cannot discriminate among
the served ends (they are all inside the chosen package); whatever
the law of marginal utility rests on, it is not actual action
alone.

Field-shape commitment (audit): `wouldServe` is indexed by the
NUMBER of units, not by which units — interchangeability is enforced
by the index type, invisible to `#print axioms`. The honest
deepening (index by sub-stock; homogeneity of the disposition as an
explicit axiom, grounded or not in `Stock.homog`) is an open
refinement.

`card_eq` is the one-unit-per-end idealization: with `n` units (up
to the stock on hand), exactly `n` ends would be served — units are
not split, pooled, or left idle. Tacit in Rothbard's grain-sacks
derivation; the definitional shape is our-reconstruction. -/
structure AllocationDisposition {F : ActionFrame} {agent : F.Agent}
    {t : F.Time} (s : Stock F agent t) where
  /-- With `n` units, the ends that would be served. -/
  wouldServe : ℕ → Finset F.End
  /-- Allocation only to ends the good is believed serviceable
  for. -/
  serves_subset : ∀ n, ∀ e ∈ wouldServe n, e ∈ s.serves
  /-- One unit, one end; no idle units — within the actual supply. -/
  card_eq : ∀ n ≤ s.units.card, (wouldServe n).card = n

end Apodictic
