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

Every axiom declaration carries a docstring with three fields:

- `Source:` citation to Mises / Rothbard, or "tacit"
- `Status:` explicit-in-tradition / suppressed-premise /
  our-reconstruction
- `Does not say:` the nearby stronger claims the axiom deliberately
  omits

Docstrings are pedigree, not history. How an axiom came to be
stated this way, what was tried before it, and what refuted the
alternatives is the archaeology part of the Verso document, written
from the dated notes.

## Policy: axioms enter at point of first use

No axiom lives here unless some theorem's `#print axioms` cites it.
An uncited axiom cannot help a proof; it can only make the base
inconsistent or consume review. Doctrinally central axioms that no
theorem yet needs — the bridge from actual action to preference
(demonstrated preference), the existence axiom (humans act) — are
parked with their pedigree in the document and re-enter with the
theorem that forces them.

## Architecture: the distinguished frame

Praxeological axioms speak only of `World`, a frame given
axiomatically. They must NOT quantify over all `ActionFrame`s:
frames and their actions are ordinary definable structures, so a
∀-frame axiom is refutable by constructing a pathological instance.
`World` is opaque, so nothing over it is constructible: every
action, stock, or disposition is either supplied by an existence
axiom or hypothesized in a theorem statement. The same rule applies
one level down: an axiom about "the agent's plan" must not quantify
over the type of plans, since given one plan, rivals are definable;
it names the actual one with an opaque predicate. The general
`ActionFrame` vocabulary remains for stating models, rejected
encodings, and contrasts.
-/

namespace Apodictic

/-- **The world of human action** — the frame the praxeological
axioms speak of. Opaque by design: nothing over `World` is
constructible, so an axiom about its actions and dispositions cannot
be refuted by a cooked-up instance. Every action, stock, or
disposition over it is either supplied by an axiom or hypothesized
in a theorem statement.

Source: tacit — Mises's theory is about actual purposeful behavior,
action as such, not about a class of models (*Human Action*,
chs. 1–2 passim).

Status: our-reconstruction. The distinguished-frame architecture is
a formalization decision, not a doctrine of the tradition. It was
chosen because it is the only arrangement under which
`#print axioms` keeps reporting the commitments; the Misesian
reading is a consequence one may accept, not the reason.

Does not say: that any action exists in `World`. Existence is a
separate claim, not in the base. -/
axiom World : ActionFrame

/-- **Ends are distinguishable**: identity of ends is decidable —
of any two ends it is settled whether they are the same end.

Source: tacit. The reallocation argument (*MES* p. 27) withdraws
one unit and asks which want is thereby given up; "the bundle minus
this end" presupposes that each end either is or is not the one
withdrawn. Mises's actor chooses between alternatives he tells
apart; nothing in the tradition contemplates ends whose identity is
undecided.

Status: suppressed-premise. A data axiom, like `World`. It is what
makes "the bundle minus `e`" constructible; without it that step is
available only classically, and the library keeps
`Classical.choice` off the receipt so that every case split is
either named praxeological content or absent.

Does not say: anything about preference. It is identity of ends,
not indifference between them. -/
axiom ends_distinguishable : DecidableEq World.End

attribute [instance] ends_distinguishable

/-- **The agent's actual disposition** — which allocation plan is
the one the agent would follow. `AllocationDisposition s` is a
type, inhabited by every function from supply to served ends that
meets the bookkeeping conditions; this predicate names the agent's
own plan, so that an axiom can be restricted to it instead of
speaking of every conceivable plan.

Source: tacit. Rothbard's argument presupposes ONE value scale and
ONE allocation per actor ("the" marginal unit, "the" least urgent
want, *MES* pp. 24–27); the tradition never contemplates rival
plans for the same actor because it never quantifies over plans.

Status: our-reconstruction. Opaque, Prop-valued, on the receipt. It
asserts a fact of the matter about WHICH plan is the agent's.

Does not say: that such a plan exists for every stock, or that it
is unique. On Nozick's subjunctive account of preference the
subjunctive may be undetermined (1977, p. 373), so whether a
complete counterfactual table exists is left open. Theorems about
dispositions take `actual_disposition A` as a hypothesis. -/
axiom actual_disposition
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t} :
    AllocationDisposition s → Prop

/-- **Swap dominance** — subjunctive preference over allocations, in
one-swap form, for the agent's actual disposition. At every supply
`n` within the stock, the bundle the agent would serve is preferred
to the bundle obtained by withdrawing one served end `e` and
serving in its place a serviceable end `e'` that was not served.

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
our-reconstruction. The preference asserted is subjunctive — what
the agent WOULD serve — which Rothbard's demonstrated-preference
doctrine says "makes no sense apart from an actual choice made"
(Nozick 1977, p. 370, thesis 3), and which Nozick argues the
Austrians need anyway (pp. 373–374). This axiom is where that
collision lives.

Does not say: (1) anything about actual action — the bridge from
action to preference is not in the base; (2) anything about
alternatives differing by more than one swap; (3) anything about
independence of uses, which is the hypothesis `IndependentUses` of
the theorems; (4) anything beyond the actual supply
(`n ≤ s.units.card`), which is all the disposition is data for. -/
axiom swap_dominance
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : AllocationDisposition s) (hA : actual_disposition A)
    (n : ℕ) (hn : n ≤ s.units.card) :
    ∀ e ∈ A.wouldServe n, ∀ e' ∈ s.serves, e' ∉ A.wouldServe n →
      World.Prefers agent t (↑(A.wouldServe n))
        (insert e' ((↑(A.wouldServe n) : Set World.End) \ {e}))

end Apodictic
