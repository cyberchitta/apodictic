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

How to read this page. A proof assistant will not let you skip a
step, and it makes you write the missing premise into the theorem's
own statement. So there is one fixed place to look. Read the
statement, then read the definitions it names, and you have seen
everything the result depends on. A few claims sit one level down,
inside a structure the theorem takes as an argument, but nothing is
off the page.

The list is not padded, either. `#lint only unusedArguments` breaks
the build if an assumption is listed but the proof never uses it. That
is the whole reason to do this on a machine: it will not let the list
grow, and it will not let it shrink.

Every docstring below is pulled out of the library when this page is
built. What you read is what was checked.

# The horses

The law of marginal utility is derived over three pages of *Man,
Economy, and State*, and Rothbard derives it on a worked case: a man
who owns six horses. This page follows that case throughout, and the
Lean at the end is about the same six horses. The point of working
that way is that you can hold his paragraph beside the formal
statement and judge for yourself whether they say the same thing.

He sets it up twice. First by acquisition (*MES* p. 24):

> The first horse will fulfill the most urgent wants that a horse can
> serve; this follows from the universal fact that action uses scarce
> means to satisfy the most urgent of the not yet satisfied wants.

Then, for the diagram, by counting the ends (pp. 25–26):

> We assume for simplicity that there are 10 ends which the means
> could fulfill, and that each unit of means is capable of serving one
> of the ends. If the supply of the good is 6 units, then the first
> six ends, ranked in order of importance by the valuing individual,
> are the ones that are being satisfied. Ends ranked 7–10 remain
> unsatisfied.

And then he takes a horse away (p. 25):

> Assume that a man has a supply of six (interchangeable) horses. …
> Suppose that he is now faced with the necessity of giving up one
> horse. … Obviously, he gives up the least urgent of the wants which
> the larger stock would have satisfied. Thus, if the individual was
> using one horse for pleasure riding, and he considers this the least
> important of his wants that were fulfilled by the six horses, the
> loss of a horse will cause him to give up pleasure riding.

That is the whole derivation. Everything below is an attempt to say it
in a form a machine will check.

Three pieces of vocabulary carry it, and they are worth naming now
because the shape of the argument turns on the third. There is a
**stock** — the six horses, and the ends a horse can serve at all.
There is a **plan** — for any number of horses he might have, which
wants he would serve with them. And there is the **preference** the
plan expresses, which ranks bundles of wants and is not assumed to do
anything else: not transitive, not complete, no numbers attached. The
full definitions are in the appendix; nothing before it depends on
reading them.

The plan is where the trouble starts, and it is worth seeing why now,
before the formal statement makes it look inevitable. Rothbard's
argument compares six horses with five. But the man has six. What he
would do with five is not anything he does — it is a plan covering
stocks he does not own. His own words give it away: "which the larger
stock *would have* satisfied".

There is a second horse passage, and it is the one that decides how
the plan has to be written down (p. 27):

> suppose that the sixth horse that he had previously acquired (named
> "Seabiscuit") he had placed in the service of pleasure riding.
> Suppose that he now must lose another horse ("Man o' War") which had
> arrived earlier, and which was engaged in the more important duty
> (to him) of leading a wagon. He will still give up end 6 by simply
> transferring Seabiscuit from this function to the wagon-leading end.

Rothbard names two horses in order to insist that *which* horse goes
makes no difference. That is only worth saying if the plan could have
depended on which — so here the plan is indexed by which horses, and
the claim that only the number matters is kept separate, as a named
condition. Both of these conclusions of his are proved below, of the
six horses.

# The finding

The law of marginal utility needs exactly one premise from praxeology,
and that premise is not about action.

It is about what the man *would* do. For each smaller or larger string
of horses he might have, which wants would he serve? That is a plan
covering stocks he does not own, not a choice he makes.

Rothbard's own premise packs two claims into one sentence: that a man
acts with the means he has, and that the wants he serves are "the most
urgent of the not yet satisfied wants" (*MES* p. 24). Only the second
does any work here. And it does that work in the subjunctive, across
stocks the man does not have — exactly as his own argument does, when
it sets six horses beside five and asks which want "the larger stock
would have satisfied" (p. 25). No single real act can answer that. You
have to ask what would have happened.

Rothbard also sets a rule for what praxeology may use. It "may deal
with utilities only as deduced from the concrete actions of human
beings" (*MES* p. 882 n. 8) — only what a man's actual choices show.
His own law breaks that rule. The man owns six horses; what he would
have done with five is not something any action of his shows.

This is not an objection from outside. The rule is Rothbard's, the
premise is Rothbard's, and the two do not fit.

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

None of this makes the law wrong. The machine checked the reasoning:
the conclusion follows, and the proof uses only what the statement
lists. One question is left, and it is a narrow one — may praxeology
use that premise at all?

# The one premise


The library contains no `axiom`. Every praxeological claim is written
as a structure, and a theorem that needs one takes it as a named
assumption. So to see what a theorem rests on, you read its statement.

A linter keeps that list honest. `#lint only unusedArguments` breaks
the build if an assumption is listed but the proof never uses it — so
nothing can be listed for show. The linter can be switched off, which
makes keeping it on a promise rather than something the machine
guarantees. It is never switched off here.

Each commitment records three things. *Source* is a citation, or
"tacit". *Status* is one of three verdicts: explicit-in-tradition
(Rothbard or Mises say it), suppressed-premise (they use it without
saying it), or our-reconstruction (a decision the tradition never
faced). *Does not say* lists the stronger nearby claims it
deliberately avoids.

Two rules govern the list. A claim is added only when some theorem
first needs it, so every claim here is one that some theorem actually
uses. And only claims meant to hold always are commitments; a
condition that says when a law applies is a hypothesis instead, and
those have a part of their own below.

There is exactly one.

{docstring Apodictic.SwapDominant}

# The conditions


The theorems take three assumptions besides the premise. Each says
something about the situation rather than about action as such, and
each is written into the statement, so a reader can point at it and
say: that is the one that did not hold. Where one fails, the law says
nothing — it is silent, not wrong.

- `stock.OneMore fewer more`: the two piles compared are both on hand
  and differ by exactly one unit. The plan says nothing about piles the
  man does not hold, and neither does the law.
- `IndependentUses agent time`: what one want is worth does not depend
  on which other wants are being served.
- `plan.Homogeneous`: the plan depends only on how many units there
  are, not on which ones. Only the size-based form of the law needs it.

Nothing here has to say which plan is the man's. A theorem is handed a
plan and makes its claim about that one, so there is no rival plan
anyone could build to refute it.

{docstring Apodictic.ActionFrame.IndependentUses}

# The theorems


Rothbard's urgency principle says that losing a unit costs you the
least urgent want. Here that is proved rather than assumed. The
premise turns out to give more than the principle needs, so the
stronger statement comes first and the principle follows from it.

{docstring Apodictic.served_over_unserved}

{docstring Apodictic.urgency_principle}

The law is stated using Rothbard's own definition of the marginal
utility of a supply: the ends you would give up on losing one unit. It
comes in two forms. Follow a chain of named units, and no
interchangeability is needed. State it Rothbard's way, by the size of
the supply, and it is.

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
`Classical.choice` is absent: no proof here fills a gap by assuming
that every question has a yes-or-no answer. The proofs do split into
cases, but only on whether two ends are the same end — and that is why
being able to tell two ends apart is declared in the statement instead
of slipping in unnoticed.

This output says one thing: the library adds nothing to Lean's logic.
It is not the list of praxeological assumptions.

Those are in the statement. The law carries one premise,
`SwapDominant plan`; three conditions on the situation —
`IndependentUses`, `plan.Homogeneous` (for the size-based form only),
and the two piles being on hand; and one condition on the frame,
`[DecidableEq frame.End]`, which just says two wants can be told
apart. The urgency principle and the chain form carry the same list
without `Homogeneous`.

# The horses in Lean

The case from the opening, built. It does a second job at the same
time. If Rothbard's own six horses satisfy the premise and every
condition at once, then those assumptions can all hold together, and
the theorems are not empty.

Wants are ranks on the man's value scale, and the lower rank is the
more urgent want:

{docstring Apodictic.Model.rankPrefers}

The man's plan is the obvious one — with any `n` horses he serves the
`n` most urgent wants — and it satisfies the premise. Wants can be told
apart, uses are independent, one-horse steps exist inside the stable,
each step has a marginal end, and preference is asymmetric. That last
one matters: it means the premise holds somewhere preference is
strict, which is how it was meant all along and what
`no_rival_swap_dominant` needs.

Two of the theorems here are conclusions Rothbard reached himself, not
bookkeeping. The first is his result at p. 25:

{docstring Apodictic.Model.loss_of_a_horse_ends_pleasure_riding}

The second is the point he names two horses in order to make, and it
is the reason the plan is encoded the way it is:

{docstring Apodictic.Model.which_horse_does_not_matter}

And the last step is the point:

{docstring Apodictic.Model.horses_law_applies}

That is the law itself, applied to the horses, with every assumption
met. Nothing was copied across by hand: `horses_swapDominant` proves
exactly the statement the theorem asks for.

Two places where this departs from Rothbard, both said out loud rather
than papered over. His ten ends are "for simplicity", to fit a
diagram; putting a ceiling on the scale would drag an extra condition
through every theorem and buy nothing, so here the horses can serve
any rank. And which of the earlier horses is Man o' War is arbitrary —
Rothbard says only that he arrived before Seabiscuit, and nothing
about a horse except its identity enters any claim.

# The other findings


What else the audit turned up, beyond the one premise.

- Rothbard's derivation is one step from an asserted premise (p. 24).
  The one-step proof is faithful to him; the audit point is that
  "derived from the fundamental axiom of human action" (p. 27) rests
  on an assertion.
- The law is strict, as Rothbard's is. Non-increasing marginal utility
  is the neoclassical form, not his.
- Nothing assumes that exactly one want is given up. Rothbard's phrase
  "the marginal unit" takes that for granted; the law here holds for
  every want that goes.
- The proof never uses the fact that the end at the smaller supply is
  the marginal one. The law holds for every end served there against
  every end the next unit would add — and stronger still, a served end
  beats *any* unserved end that could be served, not only the one the
  next unit reaches. Rothbard's statement claims less than his premise
  delivers.

What the law does not need, which is most of what it usually gets.

- No property of preference is forced: not transitivity, not
  completeness. Rothbard assumes a single ranked value scale (Figure 3,
  pp. 25–26). None of it is needed, because the plan already carries
  the ordering.
- Interchangeability of units is not needed for the ordering. With the
  plan indexed by which units, both the urgency principle and the law
  along a chain of named units go through without it. It is needed
  exactly once, to state the law by size of supply: the phrase "the
  plan at `n` units" only picks out one thing if two piles of the same
  size serve the same ends. So it bears on the wording, not on the
  derivation —
  which is why it is a hypothesis and not a commitment. Rothbard makes
  it part of what a supply *is* (p. 23), and where it fails the units
  are not one good.
- Indifference between units is needed nowhere. Rothbard defines a
  supply with the words "valued equally" and "regards ...
  indifferently" (p. 23), then takes them back on the next page:
  interchangeability "does not mean that the concrete units are
  actually valued equally" (p. 24). The formalization follows p. 24.
- Independence of uses is a condition on the situation, and it can only
  be stated at all once preference ranges over bundles of ends rather
  than single ends. Where uses are complementary the law says nothing,
  and the statement admits as much.

Findings about the formalizing rather than the doctrine.

- Being able to tell two ends apart is a suppressed premise of the
  phrase "this bundle, minus this end". It only came to light because
  the proofs refuse classical logic.
- The claim that people act splits into three: a definition, a bridge,
  and an existence claim. Only the bridge could do deductive work, and
  nothing has needed it.
- Never assert a claim about *every* structure of a given shape — say,
  every plan the man might have. Given one plan, a rival can always be
  built that breaks such a claim, so the claim is refutable by
  construction. Assert it of the single plan a theorem is handed
  instead, and that same construction becomes harmless. Better: it
  turns into a result. `no_rival_swap_dominant` proves that two plans
  satisfying the premise cannot differ by a single swap — so "the"
  value scale is something proved here, not something assumed.

# The vocabulary

Reference. These are the definitions the statements above are written
in; nothing earlier depends on having read them.

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
theorem above takes a plan `plan : AllocationPlan stock`, so the claim
is still on the page — you read it off the type of an argument instead
of the list of assumptions. That is the one place an audit has to look
past the statement itself.

Interchangeability of units is *not* hidden down there. The plan is
indexed by which exact units the man holds; that it depends only on how
many of them there are is a separate named condition, below.

{docstring Apodictic.AllocationPlan.Homogeneous}

{docstring Apodictic.Stock.OneMore}

# Claims no theorem uses


Two claims at the centre of the doctrine are used by no theorem here,
and so are not commitments. The first is the bridge from what a man
actually does to what he prefers — demonstrated preference, in
Rothbard's sense. It is written out below in the form it would take,
and then set aside:

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

