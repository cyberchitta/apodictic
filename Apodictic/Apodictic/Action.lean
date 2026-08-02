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
  /-- `Prefers a t e₁ e₂`: at `t`, agent `a` values end `e₁` more
  highly than end `e₂`. The latent ordinal ranking, strict. Kept
  distinct from choice; any bridge between them is an axiom in
  `Apodictic.Axioms`. No properties assumed. -/
  Prefers : Agent → Time → End → End → Prop

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
