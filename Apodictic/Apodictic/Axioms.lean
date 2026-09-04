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

/-- **Ends are distinguishable**: identity of ends is decidable —
of any two ends it is settled whether they are the same end.

Source: tacit. The reallocation argument (*MES* p. 27) withdraws
one unit and asks which want is thereby given up; "the bundle minus
this end" is an operation on ends that presupposes each end either
is or is not the one withdrawn. Mises's actor chooses between
alternatives he tells apart; nothing in the tradition contemplates
ends whose identity is undecided.

Status: suppressed-premise. Entered 2026-09-04 at first use — the
derivation of the urgency principle rewrites the served bundle as
"`e` together with the rest" (`insert_sdiff_self_of_mem`), which
needs `x = e ∨ x ≠ e` for every end `x`. Without this axiom that
step is available only classically (mathlib's
`Set.insert_sdiff_singleton` puts `Classical.choice` on the
receipt). Human decision: the constructive route with the premise
NAMED, so it sits on the receipt beside `World` rather than hiding
as a frame field (a data axiom, like `World` itself). Note:
`_notes/2026-09-04-urgency-derivation.md`. -/
axiom ends_distinguishable : DecidableEq World.End

attribute [instance] ends_distinguishable

/-- **The agent's actual disposition** — which allocation plan is
the one the agent would follow. `AllocationDisposition s` is a type:
ANY function from supply to served ends meeting the bookkeeping
conditions inhabits it, and given one such plan, rivals are
definable. An axiom quantified over the whole type therefore speaks
of every conceivable plan, not the agent's — and `swap_dominance`
so stated, applied to a plan and to its one-swap rival, yields
`X ≻ Y` and `Y ≻ X`, which is `False` the day asymmetry of `Prefers`
enters (machine-checked 2026-09-04,
`_notes/scratch/2026-09-04-swap-dominance-clash.lean`; same shape
as the 2026-08-02 ∀-frame crash, one level down). This predicate is
the name for "the plan he would follow", so that the axiom can be
restricted to it.

Source: tacit. Rothbard's argument presupposes ONE value scale and
ONE allocation per actor ("the" marginal unit, "the" least urgent
want, *MES* pp. 24–27); the tradition never contemplates rival
plans for the same actor because it never quantifies over plans.

Status: our-reconstruction. Opaque, Prop-valued, on the receipt. It
asserts a fact of the matter about WHICH plan is the agent's and
asserts nothing about existence or uniqueness — whether a complete
counterfactual table exists at all is Nozick's question and stays
out of the base (parallel to `humans_act`, parked). The rejected
alternative, a data axiom handing over THE disposition for every
stock, would have asserted exactly that. Theorems about
dispositions take `actual_disposition A` as a hypothesis. -/
axiom actual_disposition
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t} :
    AllocationDisposition s → Prop

/-- **Swap dominance** — counterfactual demonstrated preference over
allocations, in one-swap form, for the agent's ACTUAL disposition
(`actual_disposition`; see its docstring for why the restriction is
load-bearing). For an allocation disposition over a
stock, at every supply `n` within the stock, the bundle the agent
would serve is preferred to the bundle obtained by withdrawing one
served end `e` and serving in its place a serviceable end `e'` that
was not served.

Source: Rothbard, *MES*, ch. 1, §5.B, pp. 24–27 (Mises Institute
ed.): "action uses scarce means to satisfy the most urgent of the
not yet satisfied wants" (p. 24); the counterfactual framing is
Rothbard's own ("suppose ... faced with the necessity of giving up
one horse"; "he gives up the least urgent of the wants which the
larger stock would have satisfied", p. 25), backed by the
reallocation argument (p. 27: "follows from the defined
interchangeability of units and from disregard of past events").
Mises, *Human Action*, ch. VII.1.

Status: explicit-in-tradition as doctrine; the one-swap form is
our-reconstruction. This is the Nozick fault line, isolated: the
axiom extends demonstrated preference from actual action to what
the agent WOULD choose at each supply level — a ranking no single
action exhibits. Three things it does NOT say. (1) Nothing about
actual action: the actual-action bridge `demonstrated_preference`
stays parked, uncited — the urgency principle needs only the
counterfactual extension, which is the finding. (2) Nothing about
alternatives differing by more than one swap: the general form
"preferred to every same-size bundle" was tried first and is not
needed (its cardinality bookkeeping would also have been classical
in mathlib). (3) Nothing about independence of uses: reading an
end-level preference off this bundle-level one is the situational
hypothesis `IndependentUses` of `urgency_principle`, not part of
the axiom. Restricted to `n ≤ s.units.card` because the disposition
is data only within the actual supply (`card_eq`); the former
axiom `urgency_principle` (commit cffc321) claimed all `n`, which
was more than the tradition's argument delivers. Supersedes that
axiom 2026-09-04. -/
axiom swap_dominance
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : AllocationDisposition s) (hA : actual_disposition A)
    (n : ℕ) (hn : n ≤ s.units.card) :
    ∀ e ∈ A.wouldServe n, ∀ e' ∈ s.serves, e' ∉ A.wouldServe n →
      World.Prefers agent t (↑(A.wouldServe n))
        (insert e' ((↑(A.wouldServe n) : Set World.End) \ {e}))

end Apodictic
