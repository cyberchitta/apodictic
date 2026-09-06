import Mathlib.Data.Set.Basic

/-!
# Action — agents, ends, means, the action framework

Definitions ONLY: this file asserts nothing. The action structure is
encoded as a definition: being an action commits to all components
at once — the jointly constitutive reading — but a definition
carries no assertion. All
assertions, including any bridge from choice to the latent ranking,
are commitments in `Apodictic.Commitments`.

Audit note: commitments can hide in the *shape* of these structures
(which fields exist, and their types), where no signature will
surface them. Auditing the trusted base includes auditing these
fields.
-/

namespace Apodictic

/-- The vocabulary everything else is built from: bare types and bare
relations. Nothing here has any property. Preference is not assumed
transitive, not assumed to rank every pair, and `Time` is not assumed
ordered. A property gets added only when some theorem forces it, and
every such forcing is a finding. -/
structure ActionFrame where
  /-- Acting persons. -/
  Agent : Type
  /-- Ends: states of affairs an agent may value. -/
  End : Type
  /-- Means: scarce resources an agent may employ. -/
  Means : Type
  /-- When action happens. Explicit from the start; no order assumed
  yet. -/
  Time : Type
  /-- `Believes a t m e`: at time `t`, agent `a` believes that using
  means `m` helps bring about end `e`. Means and ends are linked only
  through what the agent believes; there is no means–ends data
  floating free of belief. -/
  Believes : Agent → Time → Means → End → Prop
  /-- `Prefers a t X Y`: at time `t`, agent `a` values the bundle of
  ends `X` above the bundle `Y`. This is the ranking behind the
  agent's choices, and it is strict. It is kept apart from what the
  agent actually does; any bridge between the two is a commitment in
  `Apodictic.Commitments`. No properties are assumed.

  It ranges over SETS of ends rather than single ends. The tradition
  draws no line between an end and a composite of ends — "atomic"
  only ever means "not divided further by this action", the same
  relativity as the size of a unit of supply (*MES* p. 28). So there
  is ONE ranking, over bundles at whatever grain the problem has, and
  an end in the ordinary sense is a bundle with one member
  (`PrefersEnd`). Ranging over bundles is what lets independence of
  uses — bundle preference breaking down into preference between
  ends — be a named hypothesis, rather than something the vocabulary
  quietly enforces.

  Shape commitment (audit): a bundle is a `Set`, so it carries no
  multiplicity and no order. -/
  Prefers : Agent → Time → Set End → Set End → Prop

/-- Preference between two single ends. This is bundle preference
between two one-member bundles — a definition, not a second
relation. -/
abbrev ActionFrame.PrefersEnd (frame : ActionFrame) (agent : frame.Agent)
    (time : frame.Time) (want other : frame.End) : Prop :=
  frame.Prefers agent time {want} {other}

/-- **Independence of uses** — a condition on the situation, NOT a
universal claim. If two bundles differ in exactly one slot, then
preferring one bundle to the other carries down to preferring the one
end to the other. It fails where uses are complementary: where B is
worth having only alongside A. It is named here so that the theorems
needing it can carry it as a hypothesis, and so it can be pointed at
where it does not hold.

This is NOT a premise Rothbard spends. He ranks wants against each
other directly, off a scale that is already ranked (*MES* p. 26,
Figure 3), and never argues from bundles at all. It is the cost of
OUR decomposition — a claim about bundles plus this condition, in
place of his one fused claim — and it is where complementarity ends
up once the pieces are pulled apart. Asserting it instead of
hypothesizing it would amount to asserting that complementarity never
happens. -/
def ActionFrame.IndependentUses (frame : ActionFrame) (agent : frame.Agent)
    (time : frame.Time) : Prop :=
  ∀ (rest : Set frame.End) (want other : frame.End),
    want ∉ rest → other ∉ rest →
      frame.Prefers agent time (insert want rest) (insert other rest) →
        frame.PrefersEnd agent time want other

/-- An action: an agent, at a time, uses means in the belief that they
will bring about a chosen end, giving up at least one alternative end
in doing so.

The fields hold together as a package — nothing with fewer parts
counts as an action — but this is a definition, so it asserts
nothing. Shape: our-reconstruction. No theorem uses it yet; the law
of marginal utility rests on the counterfactual plan alone. -/
structure Action (frame : ActionFrame) where
  /-- The acting person. -/
  agent : frame.Agent
  /-- When the action happens. -/
  time : frame.Time
  /-- The end aimed at. -/
  chosen : frame.End
  /-- The means employed. -/
  means : frame.Means
  /-- The ends given up by acting — the raw material of opportunity
  cost. Just a set: saying "the next-best alternative" would
  presuppose a ranking this file does not have. -/
  forgone : Set frame.End
  /-- Action is choice: something is always given up, if only doing
  nothing. -/
  forgone_nonempty : forgone.Nonempty
  /-- The chosen end is not among the forgone. -/
  chosen_not_forgone : chosen ∉ forgone
  /-- The agent believes the means used will bring about the chosen
  end. -/
  belief : frame.Believes agent time means chosen

end Apodictic
