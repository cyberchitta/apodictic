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
universal claim. A bundle is a set of ends. Take a set of ends, and
two ends outside it, `want` and `other`. Suppose he prefers the set
with `want` added to the set with `other` added. Then he prefers
`want` to `other`. So a preference between two bundles that differ in
exactly one end carries down to a preference between those two ends.
It fails where uses are complementary. Say end B is worth having only
alongside end A, and A is in the set. He may prefer the set with B
added to the set with some C added. Yet on their own he may not prefer
B to C. Then this condition fails. It is named here so that the theorems
that need it carry it as a hypothesis. It is also named so that a reader can point at it
where it does not hold.

This is NOT a premise Rothbard's argument uses. He ranks wants against
each other directly. He reads their ranking off his value scale
(*MES* pp. 25–26, Figure 3). He takes that ranking as given. He never
argues from bundles at all. Where he makes one fused claim, we split it in two: a claim about
bundles (swap dominance, `SwapDominant`) and this condition. The split
is OURS, and this condition is its cost. Complementarity never comes up
in his wording. Once the claim is split, it comes up here, as the case
where this condition fails. To assert this condition rather than
hypothesize it would be to assert that complementarity never
happens. -/
def ActionFrame.IndependentUses (praxis : ActionFrame) (agent : praxis.Agent)
    (time : praxis.Time) : Prop :=
  ∀ (rest : Set praxis.End) (want other : praxis.End),
    want ∉ rest → other ∉ rest →
      praxis.Prefers agent time (insert want rest) (insert other rest) →
        praxis.PrefersEnd agent time want other

/-- An action. An agent, at a time, uses means. He believes the means
will bring about a chosen end. By acting he gives up at least one
alternative end.

The fields hold together as a package. Nothing with fewer parts
counts as an action. But this is a definition, so it asserts nothing.
Shape: our-reconstruction.

No derivation of the law uses this structure. On both routes the law
rests on the counterfactual plan alone. The structure does appear in
Mises's dilemma (`Apodictic.Mises.ActionOccurs`,
`Apodictic.Mises.ActionRecurs`). The dilemma is machine-checked not to
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
