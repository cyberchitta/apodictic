import Mathlib.Data.Set.Basic

/-!
# Action — agents, ends, means, the action framework

Definitions ONLY: this file asserts nothing. The action structure is
encoded as a definition: being an action commits to all components
at once — the jointly constitutive reading — but a definition
carries no assertion. All
assertions, including any bridge from choice to the latent ranking,
are praxeological claims in `Apodictic.Praxeology`.

Audit note: praxeological claims can hide in the *shape* of these structures
(which fields exist, and their types), where no signature will
surface them. Auditing the trusted base includes auditing these
fields.
-/

namespace Apodictic

/-- The vocabulary everything else is built from: bare types and bare
relations. Nothing here has any property. Preference is not assumed
transitive. It is not assumed to rank every pair. `Time` is not
assumed ordered. A property gets added only when some theorem forces
it. Every such forcing is a finding. -/
structure ActionFrame where
  /-- Acting persons. -/
  Agent : Type
  /-- Ends: states of affairs an agent may value. -/
  End : Type
  /-- Means: scarce resources an agent may employ. -/
  Means : Type
  /-- When action happens. It is explicit from the start. No order is
  assumed on it here. -/
  Time : Type
  /-- `Believes agent time means want`: at that time, the agent
  believes that using those means helps bring about that want. Nothing
  links a means to an end here except what the agent believes. -/
  Believes : Agent → Time → Means → End → Prop
  /-- `Prefers agent time X Y`: at that time, the agent values the
  bundle of ends `X` above the bundle `Y`. This is the ranking behind
  the agent's choices. It is read as strict. But that reading is not
  built in: NO properties are imposed on this relation, strict or
  otherwise. A theorem that needs one says so.

  The ranking is kept apart from what the agent actually does. Three
  claims tie the two. Two run from an act to the ranking.
  `DemonstratedPreference` is stated of a trade.
  `DemonstratedTimePreference` is stated of an act across dates. One
  runs the other way, from the ranking to what he does with a stock.
  `ActsInOrder` is stated of an actual allocation. Each is asserted of
  the one trade, act or allocation a theorem is handed, never of every
  act.

  The relation ranges over SETS of ends rather than single ends. The
  tradition draws no line between an end and a composite of ends. The
  word "atomic" only ever means "not divided further by this action".
  That is the same relativity as the size of a unit of supply (*MES*
  p. 28). So there
  is ONE ranking, over bundles at whatever grain the problem has. An
  end in the ordinary sense is a bundle with one member
  (`PrefersEnd`). Independence of uses (`IndependentUses`) is bundle
  preference breaking down into preference between ends. Ranging over
  bundles is what lets it be a named hypothesis, instead of something
  the vocabulary quietly enforces.

  Shape claim (audit): a bundle is a `Set`, so it carries no
  multiplicity and no order. -/
  Prefers : Agent → Time → Set End → Set End → Prop

/-- Preference between two single ends. It is bundle preference
between two one-member bundles. It is a definition, not a second
relation. -/
abbrev ActionFrame.PrefersEnd (praxis : ActionFrame) (agent : praxis.Agent)
    (time : praxis.Time) (want other : praxis.End) : Prop :=
  praxis.Prefers agent time {want} {other}

/-- **Independence of uses** — a condition on the situation, NOT a
universal claim. Take two bundles that differ in exactly one slot.
Then preferring one bundle to the other carries down to preferring the
one end to the other. It fails where uses are complementary: where B
is worth having only alongside A. It is named here so that the
theorems that need it carry it as a hypothesis. It is also named so
that a reader can point at it where it does not hold.

This is NOT a premise Rothbard spends. He ranks wants against each
other directly. He ranks them off a scale that is already ranked
(*MES* pp. 25–26, Figure 3). He never argues from bundles at all.
This condition is what OUR decomposition costs. Where he makes one
fused claim, we make a claim about bundles (`SwapDominant`) plus
this condition. His wording never has to face complementarity. Once the pieces are pulled
apart, complementarity lands here. To assert this condition rather
than hypothesize it would be to assert that complementarity never
happens. -/
def ActionFrame.IndependentUses (praxis : ActionFrame) (agent : praxis.Agent)
    (time : praxis.Time) : Prop :=
  ∀ (rest : Set praxis.End) (want other : praxis.End),
    want ∉ rest → other ∉ rest →
      praxis.Prefers agent time (insert want rest) (insert other rest) →
        praxis.PrefersEnd agent time want other

/-- An action: an agent, at a time, uses means in the belief that they
will bring about a chosen end, giving up at least one alternative end
in doing so.

The fields hold together as a package — nothing with fewer parts
counts as an action — but this is a definition, so it asserts
nothing. Shape: our-reconstruction. No derivation of the law uses it;
on both routes the law rests on the counterfactual plan alone. Where
it does appear is in Mises's dilemma (`Apodictic.Mises.ActionOccurs`,
`Apodictic.Mises.ActionRecurs`), which is machine-checked not to
deliver the law. -/
structure Action (praxis : ActionFrame) where
  /-- The acting person. -/
  agent : praxis.Agent
  /-- When the action happens. -/
  time : praxis.Time
  /-- The end aimed at. -/
  chosen : praxis.End
  /-- The means employed. -/
  means : praxis.Means
  /-- The ends given up by acting — the raw material of opportunity
  cost. Just a set: saying "the next-best alternative" would
  presuppose a ranking this file does not have. -/
  forgone : Set praxis.End
  /-- Action is choice: something is always given up, if only doing
  nothing. -/
  forgone_nonempty : forgone.Nonempty
  /-- The chosen end is not among the forgone. -/
  chosen_not_forgone : chosen ∉ forgone
  /-- The agent believes the means used will bring about the chosen
  end. -/
  belief : praxis.Believes agent time means chosen

end Apodictic
