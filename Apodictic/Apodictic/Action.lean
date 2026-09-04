import Mathlib.Data.Set.Basic

/-!
# Action — agents, ends, means, the action framework

Definitions ONLY: this file asserts nothing. The action structure is
encoded as a definition (shape C, adopted 2026-08-02, provisional):
being an action commits to all components at once — the jointly
constitutive reading — but a definition carries no assertion. All
assertions, including any bridge from choice to the latent ranking,
are axioms in `Apodictic.Axioms`.

Audit note: commitments can hide in the *shape* of these structures
(which fields exist, and their types), where `#print axioms` will not
surface them. Auditing the trusted base includes auditing these
fields.
-/

namespace Apodictic

/-- The primitive vocabulary of the action framework: bare types and
bare relations. Nothing here has any structural property — no
transitivity, no totality, no order on `Time`. Strength is added only
when a theorem forces it, and each forcing is a finding. -/
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
  /-- `Believes a t m e`: at `t`, agent `a` believes that employing
  means `m` conduces to end `e`. Means–ends links go only through
  belief — there is no belief-independent means–ends data. -/
  Believes : Agent → Time → Means → End → Prop
  /-- `Prefers a t X Y`: at `t`, agent `a` values the bundle of ends
  `X` more highly than the bundle `Y`. The latent ordinal ranking,
  strict. Kept distinct from choice; any bridge between them is an
  axiom in `Apodictic.Axioms`. No properties assumed.

  Over SETS of ends, not ends (encoding decision 2026-09-04, human
  objection "are not all ends composites?"): the tradition draws no
  line between an end and a composite — "atomic" only ever means
  "not further divided by this action", the same relativity as the
  unit of supply (*MES* p. 28). So there is ONE ranking, over
  bundles at the grain of the problem, and an end in the ordinary
  sense is a singleton bundle (`PrefersEnd`). This is what makes
  independence of uses — bundle preference decomposing into
  end preference — statable as a named hypothesis instead of being
  enforced silently by the vocabulary. Shape commitment (audit): a
  bundle is a `Set` — no multiplicity, no order; and `Set` rather
  than `Finset` because the opaque `World.End` has no decidable
  equality. Notes: `_notes/2026-09-04-bundle-encoding-choice.md`. -/
  Prefers : Agent → Time → Set End → Set End → Prop

/-- Preference between ends in the ordinary sense: singleton-bundle
preference. Definition, not a second relation. -/
abbrev ActionFrame.PrefersEnd (F : ActionFrame) (a : F.Agent) (t : F.Time)
    (e e' : F.End) : Prop :=
  F.Prefers a t {e} {e'}

/-- An action: an agent, at a time, employs means in the belief that
they conduce to a chosen end, forgoing at least one alternative end.

The fields are jointly constitutive — nothing with fewer components
counts as an action — but this is a definition, not an assertion.
Shape: our-reconstruction, provisional (see notes 2026-08-02). -/
structure Action (F : ActionFrame) where
  agent : F.Agent
  time : F.Time
  /-- The end aimed at. -/
  chosen : F.End
  /-- The means employed. -/
  means : F.Means
  /-- Ends forgone in acting — the material of opportunity cost.
  A bare set: "the next-best alternative" would presuppose ranking
  structure this file does not have. -/
  forgone : Set F.End
  /-- Action is choice: something is always forgone (at minimum,
  inaction). -/
  forgone_nonempty : forgone.Nonempty
  /-- The chosen end is not among the forgone. -/
  chosen_not_forgone : chosen ∉ forgone
  /-- The agent believes the employed means conduce to the chosen
  end. -/
  belief : F.Believes agent time means chosen

end Apodictic
