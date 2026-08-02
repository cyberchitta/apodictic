import Apodictic.Action

/-!
# Axioms — the COMPLETE trusted base

Every `axiom` of the formalization lives in this file and nowhere
else. Nothing axiom-like — no axioms disguised as instance
assumptions, no hypotheses smuggled into theorem statements — may
live in any other module. The file is meant to be auditable at a
glance: read it (together with the field shapes of the structures in
`Apodictic.Action`) and you have read everything the theorems rest
on.

Every axiom declaration carries a docstring with two required fields:

- `Source:` citation to Mises / Rothbard, or "tacit"
- `Status:` explicit-in-tradition / suppressed-premise /
  our-reconstruction
-/

namespace Apodictic

/-- **Demonstrated preference**: the agent of an action prefers, at
the time of the action, the chosen end over each forgone end. This is
the bridge from choice (the `Action` structure) to the latent ranking
(`ActionFrame.Prefers`) — the two are otherwise unconnected.

Source: Rothbard, *Man, Economy, and State*, ch. 1, and "Toward a
Reconstruction of Utility and Welfare Economics" (1956); Mises,
*Human Action*, ch. 4 (acting man chooses, and choice sets aside
what is valued less).

Status: explicit-in-tradition as doctrine; the formulation as a
one-way bridge from `Action` to `Prefers` is our-reconstruction.
This is the Nozick/Rothbard fault line formalized: the axiom claims
only that action *reveals* strict preference at the moment of action
— nothing about a ranking existing apart from action, and no
converse (preference does not imply action). -/
axiom demonstrated_preference {F : ActionFrame} (a : Action F) :
    ∀ e ∈ a.forgone, F.Prefers a.agent a.time a.chosen e

end Apodictic
