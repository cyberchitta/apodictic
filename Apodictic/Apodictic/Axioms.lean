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

## Policy: axioms enter at point of first use (adopted 2026-09-04)

No axiom lives here unless some theorem's `#print axioms` cites it.
An uncited axiom cannot help a proof; it can only make the base
inconsistent or consume review. Doctrinally central axioms that no
theorem yet needs — the bridge from actual action to preference
(`demonstrated_preference`), the existence axiom (`humans_act`) —
are parked with their pedigree in
`_notes/2026-09-04-parked-axioms.md` and re-enter with the theorem
that forces them.

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

/-- **The urgency principle** (Rothbard), in counterfactual-loss form:
for an agent's allocation disposition over a stock, every end that
would still be served with `n` units is preferred to every end that
would be abandoned in the step down from `n + 1` — the loss falls on
the least urgent want.

Source: Rothbard, *MES*, ch. 1, §5.B, pp. 24–27 (Mises Institute
ed.). The premise: "action uses scarce means to satisfy the most
urgent of the not yet satisfied wants" (p. 24), offered as a
"universal fact" that "follows from" action — one sentence, no
derivation shown. The loss form: "he gives up the least urgent of
the wants which the larger stock would have satisfied" (p. 25),
introduced with "Obviously", backed by the reallocation argument
(p. 27: "follows from the defined interchangeability of units and
from disregard of past events"). Mises, *Human Action*, ch. VII.1.

Status: explicit-in-tradition as doctrine. Its derivation from the
action axiom is ASSERTED by Rothbard, not shown; whether it can be
derived from a bridge between action and preference is a separate
research item (see notes 2026-09-04). The counterfactual-
dispositional formulation is our-reconstruction, and it carries two
commitments that a finer archaeology would separate:

1. the extension of preference from actual action to counterfactual
   choice — explicit in Rothbard's own framing ("suppose ... faced
   with the necessity of giving up one horse"), and exactly what
   Nozick contests;
2. independence of uses: end-level preference read off a comparison
   of whole allocations differing in one end — tacit; Rothbard's
   "we assume for simplicity" (p. 26) covers only one-unit-one-end.
   Since 2026-09-04 `Prefers` ranges over bundles and the conclusion
   here is singleton preference (`PrefersEnd`), so this commitment
   is now STATABLE as a hypothesis (`IndependentUses`, scratch-
   checked) and will leave the axiom when the urgency principle is
   derived rather than asserted.

NOT asserted here, contrary to the 2026-08-02 docstring: determinacy
of the drop (that exactly one end goes when one unit goes). This
axiom quantifies over every dropped end and says nothing about how
many there are; `exists_marginal` proves only that there is at
least one. Rothbard's "the marginal unit" presupposes determinacy;
our law is stated over all marginal ends and does not.

The law of marginal utility follows from this axiom in ONE step —
which is faithful to the text: Rothbard's own derivation is one
step from this premise too. The audit finding is upstream: his
"derived from the fundamental axiom of human action" (p. 27) rests
on a premise he asserts. -/
axiom urgency_principle
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : AllocationDisposition s) (n : ℕ) :
    ∀ e ∈ A.wouldServe n, ∀ e', e' ∈ A.wouldServe (n + 1) →
      e' ∉ A.wouldServe n → World.PrefersEnd agent t e e'

end Apodictic
