import VersoManual
import Apodictic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Apodictic

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "The Result" =>
%%%
tag := "result"
%%%

Mises said the theorems of praxeology are as certain as the theorems
of mathematics. They follow from the plain fact that people act, he
thought, as strictly as a theorem follows from its axioms, and no
experience could ever overturn one.

This is a test of that claim on a single theorem: Rothbard's law of
marginal utility, rebuilt in Lean 4, a proof assistant.

A proof assistant will not let you skip a step. Anything a spoken
argument passes over in silence has to be written down before the
proof will go through — and written into the theorem's own statement,
either as a listed assumption or in the type of one. So there is a
fixed place to look. Read the statement, then read the definitions it
names, and you have seen everything the result depends on. A few
claims sit one level down, inside a structure the theorem takes as an
argument, but nothing is off the page.

The list is not padded either. `#lint only unusedArguments` breaks the
build if an assumption is listed but the proof never uses it. That is
the whole reason to do this on a machine.

Every docstring below is pulled out of the library when this page is
built. What you read is what was checked.

# The finding

The law of marginal utility needs exactly one premise from praxeology,
and that premise is not about action.

It is about what the agent *would* do. For each smaller or larger pile
of units he might have, which wants would he serve? That is a plan
spanning piles he does not own, not a choice he makes.

Rothbard's own premise packs two claims into one sentence: that a man
acts with the means he has, and that the wants he serves are "the most
urgent of the not yet satisfied wants" (*MES* p. 24). Only the second
does any work here. And it does that work in the subjunctive,
stretched across piles the agent does not have — exactly as Rothbard
stretches it himself. He sets a stock of six horses beside a stock of
five and asks which want "the larger stock would have satisfied"
(p. 25). No single real act can answer that. You have to ask what
would have happened.

The trouble is Rothbard's own, not something imported from outside. He
says praxeology "may deal with utilities only as deduced from the
concrete actions of human beings" (*MES* p. 882 n. 8). The premise his
own law needs is not a premise of that kind.

The same trouble turns up a second time, in a place usually discussed
on its own. The law is expected to founder on units: to state it by
the size of a supply you seem to need units the agent values equally,
and Rothbard denies that anyone ever demonstrates indifference by
acting. Here it does not founder. Indifference is assumed nowhere, and
the law survives without it. What the size-based wording needs is
weaker — only that the plan not care *which* units, just how many. But
that condition also ranges over piles the agent does not hold. So
Rothbard's restriction rules out both the premise the law is derived
from and the condition that makes its usual wording well-formed.

Twice, though, and not once. These are two different claims, and the
encoding keeps them apart:

- The premise is a *commitment*. It rides on the signature of every
  theorem that uses it. If it is false, the law is false.
- The condition is a *hypothesis* of one theorem. Where it fails the
  law says nothing — it is silent, not wrong.

Telling which of the two gave way in a particular case is exactly what
an audit like this is for.

None of this refutes the law. Lean certifies that the reasoning is
valid and that it uses nothing beyond what the statement carries. What
is in question is where the one starting premise came from.

# Vocabulary

The basic vocabulary is deliberately bare. Preference is just a
relation: not assumed transitive, not assumed to rank every pair, and
time is not assumed ordered. Properties get added when a theorem
forces them, and so far none has.

{docstring Apodictic.ActionFrame}

{docstring Apodictic.ActionFrame.PrefersEnd}

The law is about a stock of units and what the agent would do with
more or fewer of them.

{docstring Apodictic.Stock}

{docstring Apodictic.AllocationPlan}

One claim sits a level down. `oneUnitOneEnd` — one unit serves one end, with
no unit left idle — is Rothbard's "we assume for simplicity" (p. 26).
It is a field of the plan rather than a listed assumption. Every
theorem below takes a plan `A : AllocationPlan s`, so the claim
is still on the page; you read it off the type of an argument instead
of the assumption list. That is the one place an audit has to look
past the signature.

Interchangeability of units is *not* down there. The plan is indexed
by which exact units the agent holds. That it depends only on how many
is a separate named condition, below.

{docstring Apodictic.AllocationPlan.Homogeneous}

{docstring Apodictic.Stock.OneMore}

# Commitments

The library contains no `axiom`. Every praxeological claim is a
structure, and a theorem that needs one takes it as a named
assumption, so what a theorem rests on is read off its signature. That
everything listed does real work is enforced by `#lint only
unusedArguments`, which breaks the build on an assumption the proof
never uses. The linter can be switched off, so keeping it on is a
policy and not a theorem. It is never switched off here.

Each commitment records three things. *Source* is a citation, or
"tacit". *Status* is one of three verdicts: explicit-in-tradition
(Rothbard or Mises say it), suppressed-premise (they use it without
saying it), or our-reconstruction (a decision the tradition never
faced). *Does not say* lists the stronger nearby claims it
deliberately avoids.

Two rules govern the list. A claim is added only when some theorem
first needs it, so nothing appears here that no theorem uses. And only
claims meant to hold universally are commitments; conditions saying
when a law applies are hypotheses instead, listed below.

There is exactly one.

{docstring Apodictic.SwapDominant}

# Hypotheses

The theorems take three assumptions besides the commitment. Each is a
condition on the situation rather than a universal claim about action,
and each stands in the statement so that it can be pointed at when it
fails. Where one fails the law is silent, not refuted.

- `stock.OneMore fewer more`: the two piles compared are both on hand and differ
  by exactly one unit. The plan is data only there, and the law holds
  only there.
- `IndependentUses agent t`: what an end is worth does not depend on
  which other ends are being served.
- `plan.Homogeneous`: the plan depends only on how many units, not which
  ones. Needed by the size-based form of the law alone.

Which plan is the agent's needs no assumption of its own. The theorems
talk about the plan they are handed, and the commitment is asserted of
that plan, so there is nothing quantified over rival plans for a rival
to refute.

{docstring Apodictic.ActionFrame.IndependentUses}

# Theorems

Rothbard's urgency principle says that losing a unit costs you the
least urgent want. Here that is a theorem rather than a premise. The
commitment in fact delivers something stronger, so that workhorse is
stated first and the principle follows from it.

{docstring Apodictic.served_over_unserved}

{docstring Apodictic.urgency_principle}

The law is stated using Rothbard's own definition of the marginal
utility of a supply: the ends you would give up on losing one unit. It
comes in two forms. Along a chain of named units it needs no
interchangeability. In Rothbard's own wording, by size of supply, it
does.

{docstring Apodictic.marginalEnds}

{docstring Apodictic.marginal_utility_chain}

{docstring Apodictic.marginal_utility}

# The receipt

```lean (name := receipt)
#print axioms marginal_utility
```
```leanOutput receipt
'Apodictic.marginal_utility' depends on axioms: [propext, Quot.sound]
```

`propext` and `Quot.sound` are Lean's own logical background. They
arrive with ordinary mathematics, not with anything praxeological:
mathlib's finite sets bring both, and so does extensionality for sets.
`Classical.choice` is absent — no proof here closes a gap by helping
itself to the principle that every question has a yes-or-no answer.
The proofs do split into cases, but only on whether two ends are the
same end, which is why that travels as a declared condition on the
frame rather than as a silent convenience.

This output says one thing: the library adds nothing to Lean's logic.
It is not the list of praxeological assumptions.

Those are in the statement. The law carries one commitment,
`SwapDominant plan`; three situational conditions — `IndependentUses`,
`plan.Homogeneous` (the size-based form only), and the two piles being on
hand; and one data condition on the frame, `[DecidableEq frame.End]`. The
urgency principle and the chain form carry the same list without
`Homogeneous`.

# The horses

Consistency is not a side-question here, and the model is not an
invented one. It is Rothbard's own worked case (*MES* pp. 25–27): a
man with six interchangeable horses, ten ends ranked in order of
importance, each horse able to serve one of them. The six horses serve
the first six ends; ends 7–10 go unserved.

Wants are ranks on the man's value scale, and the lower rank is the
more urgent want:

{docstring Apodictic.Model.rankPrefers}

The man's plan is the obvious one — with any `n` horses he serves the
`n` most urgent wants — and it satisfies the commitment. Wants can be
told apart, uses are independent, one-horse steps exist inside the
stable, each step has a marginal end, and preference is asymmetric. So
the commitment has a model in which preference is strict, which is the
reading intended throughout and what `no_rival_swap_dominant` needs.

Two of the theorems are Rothbard's own conclusions rather than
bookkeeping. The first is his p. 25 result:

{docstring Apodictic.Model.loss_of_a_horse_ends_pleasure_riding}

The second is the one he names two horses to make, and it is the
argument for how the plan is encoded here:

{docstring Apodictic.Model.which_horse_does_not_matter}

And the last step is the point:

{docstring Apodictic.Model.horses_law_applies}

That is the law itself, at the horse frame, with every assumption
discharged. Nothing is copied across by hand: `horses_swapDominant`
proves the very proposition the theorem consumes.

Two places where the model is not Rothbard's, both recorded rather
than papered over. His ten ends are "for simplicity", to fit a
diagram; capping the scale would drag a side condition through every
theorem and buy nothing, so the good here serves every rank. And which
earlier horse is Man o' War is arbitrary — Rothbard says only that he
arrived before Seabiscuit, and nothing about a horse but its identity
enters any claim.

# Not in the base

Two claims central to the doctrine are used by no theorem, and so are
not commitments. The first is the bridge from what a man actually does
to what he prefers — demonstrated preference, in Rothbard's sense.
It is written out here in the form it would take, and parked:

```lean
/-- PARKED: the bridge from actual action to preference. Carried by
no theorem; lives in the document, not the library. -/
structure DemonstratedPreference (frame : ActionFrame) : Prop where
  bridge : ∀ act : Action frame, ∀ givenUp ∈ act.forgone,
    frame.Prefers act.agent act.time {act.chosen} {givenUp}
```

The second is the claim that there is any action at all. Action itself
is a definition here, and no theorem uses it yet.

{docstring Apodictic.Action}

# Findings

What the derivation turned out to be, beyond the premise it rests on.

- Rothbard's derivation is one step from an asserted premise (p. 24).
  The one-step proof is faithful to him; the audit point is that
  "derived from the fundamental axiom of human action" (p. 27) rests
  on an assertion.
- The law is strict, as Rothbard's is. Non-increasing marginal utility
  is the neoclassical form, not his.
- Nothing assumes the drop is determinate. Rothbard's "the marginal
  unit" takes for granted that exactly one end goes; the law here
  holds over all of them.
- The proof never uses the fact that the end at the smaller supply is
  the marginal one. The law holds for every end served there against
  every end the next unit would add — and stronger still, a served end
  beats *any* unserved end that could be served, not only the one the
  next unit reaches. Rothbard's statement claims less than his premise
  delivers.

What the law does not need, which is most of what it usually gets.

- No structure on preference is forced: no transitivity, no
  completeness. Rothbard assumes a single ranked value scale
  (Figure 3, pp. 25–26). None is needed, because the plan carries the
  ordering.
- Interchangeability of units is not needed for the ordering. With the
  plan indexed by which units, both the urgency principle and the law
  along a chain of named units go through without it. It is needed
  exactly once, to state the law by size of supply: "the plan at `n`
  units" is a function of `n` only if two piles of the same size serve
  the same ends. So it bears on the wording, not on the derivation —
  which is why it is a hypothesis and not a commitment. Rothbard makes
  it part of what a supply *is* (p. 23), and where it fails the units
  are not one good.
- Indifference between units is needed nowhere. Rothbard defines a
  supply with the words "valued equally" and "regards ...
  indifferently" (p. 23), then takes them back on the next page:
  interchangeability "does not mean that the concrete units are
  actually valued equally" (p. 24). This follows p. 24.
- Independence of uses is a situational condition, and it can be
  stated only once preference ranges over bundles of ends rather than
  single ends. Where uses are complementary the law says nothing, and
  the statement admits it.

Findings about the formalizing rather than the doctrine.

- Being able to tell two ends apart is a suppressed premise of "this
  bundle, minus this end". Refusing classical logic surfaced it.
- The claim that people act splits into three: a definition, a bridge,
  and an existence claim. Only the bridge could do deductive work, and
  nothing has needed it.
- A universal claim about "the agent's X" must not be stated over all
  X-shaped structures. Given one, rivals are definable, and a claim
  about all of them can be refuted by construction. Asserted instead
  of the one plan a theorem is handed, the same construction is
  harmless and yields a uniqueness result: `no_rival_swap_dominant`,
  that two plans satisfying the commitment cannot differ by a single
  swap. So "the" value scale is a theorem here, not a premise.
