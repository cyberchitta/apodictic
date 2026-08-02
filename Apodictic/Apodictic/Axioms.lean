import Apodictic.Allocation

/-!
# Axioms — the COMPLETE trusted base

Every `axiom` of the formalization lives in this file and nowhere
else. Nothing axiom-like — no axioms disguised as instance
assumptions, no hypotheses smuggled into theorem statements — may
live in any other module. The file is meant to be auditable at a
glance: read it (together with the field shapes of the structures in
`Apodictic.Action` and `Apodictic.Allocation`) and you have read
everything the theorems rest on.

Every axiom declaration carries a docstring with two required fields:

- `Source:` citation to Mises / Rothbard, or "tacit"
- `Status:` explicit-in-tradition / suppressed-premise /
  our-reconstruction

## Architecture: the distinguished frame (adopted 2026-08-02)

Praxeological axioms speak only of `World`, a frame given
axiomatically. They must NOT quantify over all `ActionFrame`s:
frames and their actions are ordinary definable structures, so a
∀-frame axiom is refutable by constructing a pathological instance —
the original ∀-frame `demonstrated_preference` made the base
inconsistent (`False` derived 2026-08-02; see
`_notes/2026-08-02-trusted-base-inconsistency.md`). `World` is
opaque, so nothing over it is constructible: every action, stock, or
disposition is either supplied by an existence axiom or hypothesized
in a theorem statement. Reading: praxeology makes claims about
action as such — about the world — not about all conceivable
structures. The general `ActionFrame` vocabulary remains for stating
models, rejected encodings, and contrasts.
-/

namespace Apodictic

/-- **The world of human action** — the frame the praxeological
axioms speak of. Opaque by design: no instance of anything over
`World` is constructible, so axioms about its actions and
dispositions cannot be refuted by cooked-up instances (the
inconsistency that sank the ∀-frame formulation, 2026-08-02).

Source: tacit — Mises's theory is about actual purposeful behavior,
action as such, not about a class of models (*Human Action*,
chs. 1–2 passim).

Status: our-reconstruction. The distinguished-frame architecture is
a formalization decision, not a doctrine of the tradition. -/
axiom World : ActionFrame

/-- **Humans act**: there is action. Under the distinguished-frame
architecture this axiom is load-bearing in a precise, limited sense:
`World` is opaque, so without it no `Action World` exists and every
axiom and theorem quantifying over actions is potentially vacuous.
Its formal role is non-vacuity — it supplies the world with action;
it is not a premise inside derivations, and `#print axioms` of no
current theorem cites it. This resolves the open question of whether
the famous action axiom is formally needed: yes — as existence, not
as inference.

Source: Mises, *Human Action*, ch. 1 (action as purposeful
behavior); Rothbard, *MES*, ch. 1. (Exact wording to be verified
against the Mises Institute editions before quotation in the
document.)

Status: explicit-in-tradition — THE axiom of the tradition. The
non-vacuity reading of its formal role is our-reconstruction. -/
axiom humans_act : Nonempty (Action World)

/-- **Demonstrated preference**: the agent of an action prefers, at
the time of the action, the chosen end over each forgone end. This is
the bridge from choice (the `Action` structure) to the latent ranking
(`Prefers`) — the two are otherwise unconnected.

Source: Rothbard, *Man, Economy, and State*, ch. 1, and "Toward a
Reconstruction of Utility and Welfare Economics" (1956); Mises,
*Human Action*, ch. 4 (acting man chooses, and choice sets aside
what is valued less).

Status: explicit-in-tradition as doctrine; the formulation as a
one-way bridge from `Action` to `Prefers` is our-reconstruction.
This is the Nozick/Rothbard fault line formalized: the axiom claims
only that action *reveals* strict preference at the moment of action
— nothing about a ranking existing apart from action, and no
converse (preference does not imply action).

Restated 2026-08-02 over `World` only: the original form quantified
over every frame and every constructible action, and was inconsistent
(see `_notes/2026-08-02-trusted-base-inconsistency.md`). -/
axiom demonstrated_preference (a : Action World) :
    ∀ e ∈ a.forgone, World.Prefers a.agent a.time a.chosen e

/-- **Allocation demonstrates preference (counterfactual form)**:
for an agent's allocation disposition over a stock, every end that
would still be served with `n` units is preferred to every end that
would be abandoned in the step down from `n + 1` — the loss falls on
the least-valued use.

Source: Rothbard, *MES*, ch. 1 (units of a supply are allocated to
the most highly valued uses; a lost unit deprives only the least
important use served); Mises, *Human Action*, ch. VII.1.

Status: the doctrine — loss falls on the marginal use — is
explicit-in-tradition. The counterfactual-dispositional formulation
is our-reconstruction, and it COMPRESSES three distinct commitments
that a finer decomposition would separate into their own axioms
(logged 2026-08-02; decomposition is an open refinement):

1. the extension of demonstrated preference from actual action to
   counterfactual choice — exactly what Nozick contests: a single
   actual allocation cannot discriminate among the served ends;
2. independence of uses: end-level preference read off a choice
   between whole allocations differing in one end — the tacit
   non-complementarity in Rothbard's derivation;
3. determinacy of the drop-choice: with one unit fewer, exactly the
   dispositionally marginal end goes.

The law of marginal utility follows from this axiom in ONE step —
the theorem is shallow because the content lives here. That is a
finding, not a success. -/
axiom allocation_demonstrated_preference
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : AllocationDisposition s) (n : ℕ) :
    ∀ e ∈ A.wouldServe n, ∀ e', e' ∈ A.wouldServe (n + 1) →
      e' ∉ A.wouldServe n → World.Prefers agent t e e'

end Apodictic
