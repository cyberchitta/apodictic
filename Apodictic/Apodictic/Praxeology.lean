import Apodictic.Allocation

/-!
# Praxeology — the COMPLETE set of praxeological claims

Every substantive claim the theorems rest on lives in this file and
nowhere else. Nothing assertion-like — no claim folded into a
structure field of the vocabulary, no premise smuggled into a proof —
may live in any other module. The file is meant to be auditable at a
glance.

Each claim carries a docstring with three fields:

- `Source:` citation to Mises / Rothbard, or "tacit"
- `Status:` explicit-in-tradition / suppressed-premise /
  our-reconstruction
- `Does not say:` the nearby stronger claims it deliberately omits

Docstrings are pedigree, not history. What was tried before and what
refuted it is in `_notes/`.

## Architecture: assertions are structures, not axioms

There are NO `axiom` declarations in this library. A praxeological
claim is a `structure` over an arbitrary frame, and a theorem that
needs it takes it as a named hypothesis. Two consequences, both
deliberate:

- **`#print axioms` on any theorem here prints only Lean's own
  background** (`propext`, `Quot.sound`). That is itself the report:
  we have added nothing to Lean's logic. The praxeological
  claims are read off the theorem's SIGNATURE instead.
- **The manifest is enforced by the unused-argument linter**, not by
  the proof term. `#lint only unusedArguments` fails the build on any
  hypothesis that did no work, so a listed claim is a used one.
  It is silenceable (`_`-prefix, `@[nolint unusedArguments]`) — so
  not silencing it is a standing policy, and any write-up must say
  so.

A claim about a given frame and a given plan quantifies over nothing
that can be constructed to refute it, and consistency is exhibited by
building an instance (`Apodictic.Consistency`).

## Policy: claims enter at point of first use

No claim lives here unless some theorem's signature carries it.
Doctrinally central claims that no theorem yet needs — the bridge
from actual action to preference (demonstrated preference), the
existence claim (humans act) — are parked with their pedigree in
`_notes/2026-09-04-parked-axioms.md` and re-enter with the theorem
that forces them.

## What is NOT here

Situational applicability conditions are not praxeological claims: they are
named hypotheses stated where they apply, so that a theorem is silent
rather than false where they fail. `IndependentUses`
(`Apodictic.Action`) and `AllocationPlan.Homogeneous`
(`Apodictic.Allocation`) are of that kind. Decidable identity of ends
travels as the instance argument `[DecidableEq praxis.End]`; it is a data
condition on the frame, not a praxeological claim.
-/

namespace Apodictic

/-- **Swap dominance** — the agent's plan beats every one-swap
alternative to it.

Take any sub-stock of the units on hand, and the ends the agent
would serve with it. Now make one swap: drop a `served` end, and
put in its place an `unserved` one that the good could have served but
the plan left out. The claim is that the agent prefers the bundle he
would have served to the swapped bundle.

It is asserted of one given plan, and it is subjunctive throughout —
it speaks of sub-stocks the agent may not hold and swaps he does not
make.

Source: Rothbard, *MES*, ch. 1, §5.B, pp. 24–27 (Mises Institute
ed.): "action uses scarce means to satisfy the most urgent of the
not yet satisfied wants" (p. 24); the counterfactual framing is
Rothbard's own ("suppose ... faced with the necessity of giving up
one horse"; "he gives up the least urgent of the wants which the
larger stock would have satisfied", p. 25), backed by the
reallocation argument (p. 27: "follows from the defined
interchangeability of units and from disregard of past events").
Mises, *Human Action*, ch. VII.1.

Status: explicit-in-tradition as doctrine; the one-swap form, and the
pulling apart of the two halves below, are our-reconstruction. Rothbard's premise fuses two
claims in one sentence: that ACTION employs the means, and that the
wants served are "the most urgent of the not yet satisfied wants"
(*MES* p. 24). This claim keeps the ordering half and states it
subjunctively, over what the agent WOULD serve. The subjunctive is
Rothbard's own — his derivation compares a stock of six with a stock
of five and asks which want "the larger stock would have satisfied"
(p. 25), a comparison no single actual allocation delivers. The
action half is dropped rather than answered: nothing here bridges an
act to a preference.

A tension remains, and it is Rothbard's own. It is not that this claim
reaches stocks the agent does not hold; that reach is his (see
*Anything about units not on hand*, below). It is that the claim
attributes a STANDING disposition. The plan is one object, at one
time, assigning served ends to every sub-stock at once — a value
scale formulated in advance of the choices it covers. That is the
thing Rothbard says is not needed. He holds that praxeology "may deal
with utilities only as deduced from the concrete actions of human
beings" (*MES* p. 882 n. 8), and inside this very chapter he writes,
in words he introduces with "It must be reiterated", that "value
scales do not exist in a void apart from the concrete choices of
action", adding that "there is no need for him to formulate
hypothetical value scales" (*MES* p. 33). His actor needs no scale in
advance: it is revealed choice by concrete choice as he goes. This
claim gives him one up front.

Yet it is on that same page that he exempts this law from the
restriction, in a subordinate clause and without argument: choices
cannot be predicted "except that they will follow the law of marginal
utility, which was deduced from the axiom of action". So the one
thing that may be said in advance about the choices is that they
follow the law — which is what licenses attributing the standing plan
this claim is asserted of, and that plan is the premise the law is
derived from. The warrant for the premise is the conclusion.

The circle is in the WARRANT, not in the proof. Nothing in the Lean
is circular: `marginal_utility` derives the law from this claim, and
this claim is asserted, never proved. What is circular is Rothbard's
licence for asserting it.

Asserted of ONE plan, not of every plan of that shape — and that is
not a hedge. Given one plan, a rival can always be defined, so a claim
about all of them could be refuted just by building one. Asserted of
the single plan a theorem is handed, there is no such rival to build.
Whether a rival one swap away could also be swap-dominant then becomes
a theorem (`no_rival_swap_dominant`, `Apodictic.Urgency`) instead of a
premise.

Does not say:

1. Anything about actual action. The bridge from action to
   preference appears nowhere in the library.
2. Anything about alternatives that differ by more than one swap.
3. Anything about independence of uses — that is the theorems'
   hypothesis `IndependentUses`.
4. Anything about units not on hand (`subStock ⊆ stock.units`), which
   is all the plan speaks about. The reach over stocks the agent does
   not hold is Rothbard's own, in both directions. He builds the law
   upward over stocks the actor lacks — the second unit, then the
   third "added to a stock of two units" (*MES* pp. 23–24) — and
   downward, six horses to five (p. 25). Holding none of a good is no
   obstacle either: "If the actor has no units of some goods in his
   possession, this does not affect the principle" (p. 32). The
   hypothetical scales he refuses on the next page are a different
   thing: scales for a wholly different multi-good endowment,
   (3X, 4Y, 2Z) against (6X, 8Y, 5Z), where what he permits inside
   the actual stock is "adding and subtracting" units of it (p. 33).
   That line is anchored to the stock the agent has, not drawn at
   some distance from it, and it is closed under the single-unit
   steps he iterates himself — first horse, then second, then third.
   Taken downward from a stock, those steps reach every sub-stock of
   it. So quantifying over all of `subStock ⊆ stock.units` is that
   region exactly, and not a reach beyond his text.

   Where this claim does depart from him is in INDEXING, not in
   reach: it speaks of arbitrary sub-stocks where he speaks of sizes.
   The gap between the two is interchangeability, which he assumes
   throughout and this claim does not: it is the hypothesis
   `Homogeneous`. Stated without that assumption, the claim
   distinguishes cases he never had to tell apart.
5. Anything about interchangeability of units. That two sub-stocks
   of the same size would serve the same ends is the hypothesis
   `Homogeneous`, and no part of this claim.
6. That such a plan exists, or that it is unique without further
   properties of `Prefers`. -/
structure SwapDominant {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) : Prop where
  /-- The one-swap dominance itself. -/
  swap : ∀ subStock ⊆ stock.units, ∀ served ∈ plan.wouldServe subStock,
    ∀ unserved ∈ stock.serves, unserved ∉ plan.wouldServe subStock →
      praxis.Prefers agent time (↑(plan.wouldServe subStock))
        (insert unserved
          ((↑(plan.wouldServe subStock) : Set praxis.End) \ {served}))

/-- **Served in order of urgency** — nothing serviceable and more
urgent is passed over for something less urgent.

If the good can serve an end, and that end is more urgent than
something the agent WOULD serve, then he would serve it too. Like
`SwapDominant` it is subjunctive throughout, and asserted of one given
plan.

This is the premise of MISES's route to the law
(`Apodictic.Mises.ladder_from_order`), where `SwapDominant` is the
premise of Rothbard's. The two are not equivalent: Rothbard's
premises entail this one given asymmetry
(`Apodictic.Contrast.rothbard_entails_servedInOrder`), and this one
does not entail his
(`Apodictic.Model.servedInOrder_not_entail_swapDominant`). Mises asks
less of the agent's allocation and more of his value scale.

Source: Mises, *Human Action*, ch. VII, §1: "If the supply available
increases from n–1 units to n units, the increment can be employed
only for the removal of a want which is less urgent or less painful
than the least urgent or least painful among all those wants which
could be removed by means of the supply n–1"; and the bridge sentence
the derivation turns on, "It is nothing else than the reverse of the
statement that what satisfies more is preferred to what gives smaller
satisfaction." Compare Mises ch. IV, §2: "Every action is always in
perfect agreement with the scale of values or wants". Rothbard states
the doctrine in the same family: "action uses scarce means to satisfy
the most urgent of the not yet satisfied wants" (*MES* p. 24).

Status: our-reconstruction. Mises argues for the law by a dilemma
about whether action terminates, not from a stated ordering premise;
this claim is what that argument needs and does not supply. The
dilemma is machine-checked NOT to deliver it
(`Apodictic.Model.recurs_does_not_deliver_ladder`), and his refutation
of his own second horn does not go through on the action axiom he
names (`Apodictic.Model.existence_does_not_refute_second_horn`).

The warrant problem is Mises's too, and not Rothbard's bookkeeping.
Mises restricts value scales exactly as Rothbard does — "These scales
have no independent existence apart from the actual behavior of
individuals" (ch. IV, §2) — and then, in ch. VII, §1, declares the
openly counterfactual definition licit without argument: "We do not
transcend the sphere of praxeological reasoning in establishing the
following definition". Rothbard exempts the law circularly; Mises
asserts the exemption. Neither warrants it.

Does not say:

1. Anything about bundles. That the served bundle beats each one-swap
   rival is `SwapDominant`, a different claim of a different shape.
2. That the ends a good can serve are comparable. That is the
   situational condition `Stock.ComparableServiceable`, and the route
   that uses this claim needs it separately.
3. Anything about actual action; no bridge from an act to a
   preference appears here or anywhere in the library.
4. Anything about units not on hand: `subStock ⊆ stock.units`, the
   same region `SwapDominant` speaks of. -/
structure ServedInOrder {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) : Prop where
  /-- The ordering itself. -/
  inOrder : ∀ subStock ⊆ stock.units, ∀ served ∈ plan.wouldServe subStock,
    ∀ better ∈ stock.serves,
      praxis.PrefersEnd agent time better served →
        better ∈ plan.wouldServe subStock

/-- **Asymmetry of preference** — if one bundle is preferred to
another, the other is not preferred to the first.

The "strict" reading of `Prefers` that the library has intended from
the start and never asserted, because no theorem needed it. One does
now: `Apodictic.Contrast.rothbard_entails_servedInOrder` argues by
contradiction from a preference running both ways, and without
asymmetry there is no contradiction to draw.

Source: tacit. No sentence in Mises or Rothbard asserts it. Rothbard's
value scales are built from acts of choice, and one act cannot
demonstrate a preference in both directions — but that is an argument
from the bridge we do not have (demonstrated preference, parked), not
a statement of his. The nearest explicit treatment is Nozick's
reconstruction (1977), which is a critic's formalization and not the
tradition's own words.

Status: our-reconstruction (human ruling 2026-09-10). Recorded as
ours rather than attributed, precisely because the search for a source
came back empty.

Does not say: not transitivity, not totality, not comparability of any
particular pair. It is asserted of one agent at one time, and of the
bundle-level relation, from which the end-level case follows since
`PrefersEnd` is `Prefers` on singletons. -/
structure AsymmetricPreference (praxis : ActionFrame) (agent : praxis.Agent)
    (time : praxis.Time) : Prop where
  /-- The asymmetry itself. -/
  asym : ∀ X Y : Set praxis.End,
    praxis.Prefers agent time X Y → ¬ praxis.Prefers agent time Y X

end Apodictic
