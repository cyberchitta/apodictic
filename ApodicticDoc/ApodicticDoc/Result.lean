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
everything the result depends on. Two conditions sit one level down,
inside the structures the theorem takes as arguments — and they are on
the manifest too, because the command that derives it reads one level
in. There is no longer anywhere for an assumption to sit unlisted.

The list is not padded, either. `#lint only unusedArguments` breaks
the build if an assumption is listed but the proof never uses it. That
is the whole reason to do this on a machine: it will not let the list
grow, and it will not let it shrink. Its three limits are stated where
the manifest is, and one of them turns up a finding.

Every docstring below is pulled out of the library when this page is
built. What you read is what was checked.

# The horses

The law of marginal utility is derived over three pages of *Man,
Economy, and State*, and Rothbard derives it on a worked case: a man
who owns six horses. This page follows that case throughout, and the
Lean returns to the same six horses once the theorems are stated. The point of working
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
full definitions are under *The vocabulary*; nothing before it
depends on reading them.

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

The law of marginal utility needs exactly one praxeological claim,
and that claim is not about action.

It is about what the man *would* do. For each string of horses he
might have, which wants would he serve? That is a plan, not a choice
he makes.

Rothbard's own premise packs two claims into one sentence: that a man
acts with the means he has, and that the wants he serves are "the most
urgent of the not yet satisfied wants" (*MES* p. 24). Only the second
does any work here. And it does that work in the subjunctive — exactly
as his own argument does, when it sets six horses beside five and asks
which want "the larger stock would have satisfied" (p. 25). No single
real act can answer that.

The subjunctive by itself is not the trouble, and it is worth saying
why, because it is the obvious complaint and it fails. Reasoning about
stocks the man does not hold is Rothbard's own practice. He builds the
law upward from one horse to two to three, he takes it downward from
six to five, and he says outright that holding none of a good "does
not affect the principle" (p. 32). What he refuses on p. 33 is
something else — a scale for a wholly different endowment, (3X, 4Y,
2Z) against (6X, 8Y, 5Z) — while inside the stock the man actually has
he allows "adding and subtracting from stock". That line is drawn
around the stock in hand, not at some distance from it, and stepping
one unit at a time, as he does, reaches every smaller string of horses
there is. The formal claim reaches no further than he does.

The trouble is the *tense*. His restriction is that "value scales do
not exist in a void apart from the concrete choices of action", and
that "there is no need for him to formulate hypothetical value scales"
(p. 33). His man needs no scale in advance: it shows up choice by
concrete choice, as each one is made. The plan is a single standing
object — every string of horses answered at once, before any of the
choosing. That is precisely the scale in advance that Rothbard says is
not needed. The complaint is not that we asked what he would do with
five horses; it is that we gave him a settled answer for all of them
at once, and no act of his settles it.

He saw a difficulty here, and exempted this law from the restriction
by name. On that same page, in a subordinate clause with no argument
attached: no one can predict the course of a man's choices "except
that they will follow the law of marginal utility, which was deduced
from the axiom of action". So the one thing that may be said about the
choices in advance is that they conform to the law — and that is what
licenses attributing the standing plan. The plan is the premise the
law is derived from. The warrant for the premise is the conclusion.

The circle is in the warrant, not in the proof. The Lean derives the
law from the claim; the claim is asserted, never proved, and nothing
in the derivation reaches back. What runs in a circle is Rothbard's
licence for asserting it.

This is not an objection from outside. The rule is Rothbard's, the
claim is Rothbard's, and so is the exemption.

There is a second thing the same plan has to carry, in a place usually
discussed on its own. The law is expected to founder on units: to
state it by the size of a supply you seem to need units the agent
values equally, and Rothbard denies that anyone ever demonstrates
indifference by acting. Here it does not founder. Indifference is
assumed nowhere, and the law survives without it. What the size-based
wording needs is weaker — only that the plan not care *which* units,
just how many. But that is one more thing the standing plan must
already have settled, and Rothbard does not deduce it from the axiom
of action. He grounds it in his definition of a supply: units
"equally capable of rendering the same service to the actor" (p. 23).

That definition does not reach it, and this is checked rather than
argued. Equal serviceability is a fact about the horses; what the
wording needs is a fact about the man's plan for them. One stable of
two horses, each able to serve any want, carries both a plan that
treats them alike and a plan that does not. The stock cannot settle
it, because the plan is a separate thing. Rothbard's other half —
that the man "must have valued each horse or each cow identically"
(p. 23) — would settle it, but he withdraws that on the next page,
where interchangeability "does not mean that the concrete units are
actually valued equally" (p. 24). Taking it back is what keeps
indifference out of the law; the cost is that the definition no
longer carries the condition the law's wording needs.

Two demands, then, and the encoding keeps them apart:

- The one the law is derived from is a *praxeological claim*. It rides
  on the signature of every theorem that uses it. If it is false, the
  law is false.
- The one its wording needs is a *hypothesis* of one theorem. Where it
  fails the law says nothing — it is silent, not wrong.

Telling which of the two gave way in a particular case is exactly what
an audit like this is for.

None of this makes the law wrong. The machine checked the reasoning:
the conclusion follows, and the proof uses only what the statement
lists. One question is left, and it is a narrow one — may praxeology
help itself to that standing plan?

# The other findings


What else the audit turned up, beyond the one claim.

- Rothbard's derivation is one step from an asserted premise (p. 24).
  The one-step proof is faithful to him; the audit point is that
  "derived from the fundamental axiom of human action" (p. 27) rests
  on an assertion.
- The law is strict, as Rothbard's is. Non-increasing marginal utility
  is the neoclassical form, not his.
- Nothing assumes that exactly one want is given up. Rothbard's phrase
  "the marginal unit" takes that for granted; the law here holds for
  every want that goes.
- One unit to one end is not needed at all. Rothbard assumes it and
  says he is assuming it — "each unit of means is capable of serving
  one of the ends", introduced with "We assume for simplicity"
  (p. 26) — and it reads like a premise of the derivation. It is not a
  premise of anything here. It was built into what a plan *is*, where
  no statement showed it; taken out, no theorem asked for it back.
  Where an extra unit adds no new end the law is simply silent, and
  the six horses supply a case where it is not silent, so nothing is
  lost. A simplification its own author flagged, and the ordering does
  not want it.
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
  which is why it is a hypothesis and not a praxeological claim. Rothbard makes
  it part of what a supply *is* (p. 23), and where it fails the units
  are not one good. But his definition does not deliver it. It speaks
  of units "equally capable of rendering the same service" — a fact
  about the units, where the wording needs a fact about the man's plan
  over them. One stock carries plans of both kinds
  (`unitsAlike_not_entail_homogeneous`), so no condition on the units
  can decide it.
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
  turns into a result. One of the theorems below proves that two plans
  satisfying the claim cannot differ by a single swap — so "the"
  value scale is something proved here, not something assumed.

# The one claim


The library contains no `axiom`. Every praxeological claim is written
as a structure, and a theorem that needs one takes it as a named
assumption. So to see what a theorem rests on, you read its statement.

A linter keeps that list honest. `#lint only unusedArguments` breaks
the build if an assumption is listed but the proof never uses it, so
little can be listed for show. Little, and not nothing: the linter can
be switched off, which makes keeping it on a promise rather than
something the machine guarantees, and it has two further limits that
let an idle hypothesis through. All three are set out with the
manifest below, and one of them turns up a finding. It is never
switched off here.

Each claim records three things. *Source* is a citation, or
"tacit". *Status* is one of three verdicts: explicit-in-tradition
(Rothbard or Mises say it), suppressed-premise (they use it without
saying it), or our-reconstruction (a decision the tradition never
faced). *Does not say* lists the stronger nearby claims it
deliberately avoids.

Two rules govern the list. A claim is added only when some theorem
first needs it, so every claim here is one that some theorem actually
uses. And only claims meant to hold always belong here; a
condition that says when a law applies is a hypothesis instead, and
those have a part of their own below.

There is exactly one.

{docstring Apodictic.SwapDominant}

# The conditions


The theorems take three assumptions besides the claim. Each says
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

All three are given in full here, in the order they are listed above,
because these are the assumptions a reader has to judge.

{docstring Apodictic.Stock.OneMore}

{docstring Apodictic.ActionFrame.IndependentUses}

{docstring Apodictic.AllocationPlan.Homogeneous}

# The theorems


The derivation is three steps, and only the first does any work.

Start with the six horses. The man serves ends 1–6; ends 7–10 remain
unsatisfied. The claim says: take that bundle, swap any served end for
any unserved end a horse could have served, and he prefers what he
would have had to what the swap leaves him. So `{1,2,3,4,5,6}` beats
`{1,2,3,4,5,7}`. It also beats `{1,2,3,4,5,8}`, and it beats
`{2,3,4,5,6,7}` if end 1 is the one swapped out. Any single swap
loses.

That is a claim about bundles. The law is a claim about single ends:
that pleasure riding is less urgent than leading a wagon. To pass from
one to the other you need that a preference between two bundles
differing in exactly one place is a preference between those two ends.
That step is independence of uses, and it is ours rather than
Rothbard's: he ranks ends against each other directly, off a scale
already ranked (Figure 3, pp. 25–26), and the passages quoted above
never compare bundles at all. We need the step because we make a claim
about bundles where he makes one fused claim — and where uses are
complementary the step fails, and the law is silent.

Take it, and every end he would serve with a given string of horses is
preferred to every end he would leave unserved. That is already more
than Rothbard claims. It does not care whether the unserved end is the
one the next horse would have reached: end 6 beats end 7, and it beats
end 10 just as squarely.

{docstring Apodictic.served_over_unserved}

Urgency is that ranking, restricted to the end he loses. Take a horse
away, and the end he gives up is one he would have served with six and
does not serve with five — an unserved end at the smaller stock.
Served-over-unserved has already ranked it below everything still
served. Rothbard's horse sentence, quoted at the start, says exactly
that and nothing more. That the larger stock is exactly one horse
larger does no work beyond naming which end is the lost one.

{docstring Apodictic.urgency_principle}

The law is urgency again, said of the ends a unit adds — the ends
served with the larger stock and not with the smaller, which is
Rothbard's own definition of the marginal utility of a supply.

{docstring Apodictic.marginalEnds}

Along a chain of named horses, apply it at the second step: what the
sixth horse adds is less urgent than what the fifth added, because
what the fifth added is still being served when he has five, and what
the sixth adds is not. That the first step is a one-horse step is not
used. Interchangeability is not used either, because the chain names
which horses.

{docstring Apodictic.marginal_utility_chain}

Said by the size of the supply, the two steps need not share a horse.
"The plan at five" and "the plan at six" are one thing each only if
any five horses get the same ends. Interchangeability is used exactly
once, to say that. After it the argument is urgency over again.

{docstring Apodictic.marginal_utility}

One result here is not a step in the derivation. The claim is asserted
of one plan, not of every plan of its shape. What that gives up — that
the man's scale is the only one of its kind — comes back as a theorem,
and it is shown here because the rest of the document leans on it.

{docstring Apodictic.no_rival_swap_dominant}

# The manifest


Everything the law carries, in one place. Nothing outside this list is
assumed. It is not compiled by reading the source, and it is not
transcribed from a command either: the command runs here, and what
follows is what it printed.

```lean (name := manifestMU)
#manifest marginal_utility
```
```leanOutput manifestMU
manifest of Apodictic.marginal_utility

  praxeological claims:
    dominance : SwapDominant plan

  situational conditions:
    independent : praxis.IndependentUses agent time
    interchangeable : plan.Homogeneous
    stepToSmaller : stock.OneMore belowSmaller smaller
    stepToLarger : stock.OneMore belowLarger larger
    smallerSize : smaller.card = n
    largerSize : larger.card = n + 1

  conditions on the data:
    [DecidableEq praxis.End]

  vocabulary (what the claims are about):
    praxis : ActionFrame
    agent : praxis.Agent
    time : praxis.Time
    stock : Stock praxis agent time
    plan : AllocationPlan stock
    belowSmaller : Finset praxis.Means
    smaller : Finset praxis.Means
    belowLarger : Finset praxis.Means
    larger : Finset praxis.Means
    n : ℕ
    atSmaller : praxis.End

  conditions carried by the vocabulary (not binders: discharged by
  whoever supplies the argument):
    stock.unitsAlike : ∀ unit ∈ stock.units, ∀ (want : praxis.End), praxis.Believes agent time unit want ↔ want ∈ stock.serves
    plan.servesOnlyWhatItCan : ∀ (subStock : Finset praxis.Means), ∀ want ∈ plan.wouldServe subStock, want ∈ stock.serves

  logical background: [propext, Quot.sound]

  (3 trailing binders belong to the conclusion, not the signature)
```

Read it by kind, because the sort is what the audit turns on. The one
*praxeological claim* is the thing that would have to be true of all
action for the law to follow. The *situational conditions* are what an
Austrian points at to say the law did not apply here — they are the
three set out above, plus the bookkeeping that fixes which two supplies
are being compared. The *condition on the data* says only that two
wants can be told apart. The *conditions carried by the vocabulary* are
not binders at all: they are fields of the structures the theorem takes
as arguments, so whoever supplies a stock and a plan has already
discharged them. They are preconditions of using the law in every sense
that matters, and they are the assumptions an encoding can hide. They
are set out again at the end of the vocabulary.

The last line is Lean's own logical background. `propext` and
`Quot.sound` arrive with ordinary mathematics: mathlib's finite sets
bring both, and so does extensionality for sets. `Classical.choice` is
absent — no proof here fills a gap by assuming that every question has
a yes-or-no answer. The proofs do split into cases, but only on whether
two ends are the same end, and that is why being able to tell two ends
apart is declared in the statement instead of slipping in unnoticed.

The chain form carries the same manifest without `Homogeneous`, and
the urgency principle the same again. It is worth printing the chain
form too, because of one line in it:

```lean (name := manifestChain)
#manifest marginal_utility_chain
```
```leanOutput manifestChain
manifest of Apodictic.marginal_utility_chain

  praxeological claims:
    dominance : SwapDominant plan

  situational conditions:
    independent : praxis.IndependentUses agent time
    _firstStep : stock.OneMore small medium   -- listed, does no work
    secondStep : stock.OneMore medium large

  conditions on the data:
    [DecidableEq praxis.End]

  vocabulary (what the claims are about):
    praxis : ActionFrame
    agent : praxis.Agent
    time : praxis.Time
    stock : Stock praxis agent time
    plan : AllocationPlan stock
    small : Finset praxis.Means
    medium : Finset praxis.Means
    large : Finset praxis.Means
    addedFirst : praxis.End

  conditions carried by the vocabulary (not binders: discharged by
  whoever supplies the argument):
    stock.unitsAlike : ∀ unit ∈ stock.units, ∀ (want : praxis.End), praxis.Believes agent time unit want ↔ want ∈ stock.serves
    plan.servesOnlyWhatItCan : ∀ (subStock : Finset praxis.Means), ∀ want ∈ plan.wouldServe subStock, want ∈ stock.serves

  logical background: [propext, Quot.sound]

  (3 trailing binders belong to the conclusion, not the signature)
```

`#manifest` derives both from the theorem itself: it walks the
signature and sorts every binder by kind, then reads one level into
the vocabulary and reports the `Prop` fields of the structures the
signature names, deciding that a binder is a praxeological claim when
the head of its type is declared in `Praxeology.lean` — the project's
own rule, asked of the compiler rather than of a maintainer. A claim
declared in the wrong place therefore shows up as a situational
condition, which is the mistake worth catching. What it will not do is
sort what it finds one level down: whether a carried condition could
fail of a real situation is a judgement about the world, not about the
term, and the two are sorted by hand in the prose above. That sorting
is the only thing here a reader is asked to take on anyone's word. The
lists themselves are printed by the compiler when this page is built,
and a page that showed anything else would not build.

Three things limit how much that settles, and each is load-bearing.
`#lint only unusedArguments` fails the build on any hypothesis that
did no work, and it is never switched off here — but switching it off
is possible, so keeping it on is a promise rather than something the
machine guarantees. It can also be silenced one binder at a time, by
prefixing a hypothesis with `_`, and doing that is how we record that
the hypothesis does nothing: `marginal_utility_chain` carries one such
binder, `_firstStep`, and that it does nothing is itself a finding.
And it works a whole binder at a time, so it cannot see a hypothesis
half of which is used — which happens in both marginal-utility
theorems.

`#manifest` closes the second of those, and the output above is the
proof of it: `_firstStep` is listed, and marked *listed, does no work*,
exactly where the linter has gone quiet. That is the line the chain
form was printed for. It does not close the third: a half-used
hypothesis looks whole to both. And it brings a limit of its own — Lean draws no line between a
signature and a conclusion, so the command cuts at the first anonymous
binder and reports how many it dropped.

So the guarantee is narrower than "nothing here is idle": nothing here
is idle except where the statement says so, in the only way Lean has
for saying it.

# The horses in Lean

The case from the opening, built. It does a second job at the same
time. If Rothbard's own six horses satisfy the claim and every
condition at once, then those assumptions can all hold together, and
the theorems are not empty.

Wants are ranks on the man's value scale, and the lower rank is the
more urgent want:

{docstring Apodictic.Model.rankPrefers}

The man's plan is the obvious one — with any `n` horses he serves the
`n` most urgent wants — and it satisfies the claim. Wants can be told
apart, uses are independent, one-horse steps exist inside the stable,
each step has a marginal end, and preference is asymmetric. That last
one matters: it means the claim holds somewhere preference is
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
met — every assumption, that is, of the chain form. The size-based
form asks for one thing more, interchangeability, and the horses meet
that too:

{docstring Apodictic.Model.horses_homogeneous}

Nothing was copied across by hand: `horses_swapDominant` proves
exactly the statement the theorem asks for.

{docstring Apodictic.Model.horses_swapDominant}

Two places where this departs from Rothbard, both said out loud rather
than papered over. His ten ends are "for simplicity", to fit a
diagram; putting a ceiling on the scale would drag an extra condition
through every theorem and buy nothing, so here the horses can serve
any rank. And which of the earlier horses is Man o' War is arbitrary —
Rothbard says only that he arrived before Seabiscuit, and nothing
about a horse except its identity enters any claim.

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

Two conditions sit a level down, as fields of the two structures every
theorem above takes as arguments. `servesOnlyWhatItCan` says a unit is
only ever put to an end the good is believed able to serve.
`unitsAlike`, a field of the stock, says every unit is believed to
serve exactly the same ends — and that is what fixes the range of
`stock.serves`, which is in turn what the one claim quantifies over.
Neither is a binder in any statement, and both are on the manifest
regardless: `#manifest` reads one level in and reports them, because
whoever supplies the argument has already discharged them.

The two are not alike, and the manifest does not pretend otherwise. A
plan that puts a horse to a job the man does not believe a horse can
do is not a situation that might obtain — it is an incoherent plan, so
`servesOnlyWhatItCan` assumes nothing about the world. A lame horse is
a situation that might obtain, so `unitsAlike` does. Which of the two
a carried condition is cannot be read off the term; it is ruled by
hand, and this is the ruling.

A third used to sit here, and now sits nowhere. One unit to one end
can fail of a real stable — two horses to one wagon, or a horse
standing idle — so it could not stay a field. Taking it out showed
that no theorem wants it, so it was not made a hypothesis either. See
the findings.

Interchangeability of units is *not* hidden down there. The plan is
indexed by which exact units the man holds; that it depends only on how
many of them there are is a separate named condition,
`AllocationPlan.Homogeneous`, given in full under *The conditions*
along with the other two.

# Claims no theorem uses


Two claims at the centre of the doctrine are used by no theorem here,
and so are not on the list. The first is the bridge from what a man
actually does to what he prefers — demonstrated preference, in
Rothbard's sense. It is written out below in the form it would take,
and then set aside:

```lean
/-- PARKED: the bridge from actual action to preference. Carried by
no theorem; lives in the document, not the library. -/
structure DemonstratedPreference (praxis : ActionFrame) : Prop where
  bridge : ∀ act : Action praxis, ∀ givenUp ∈ act.forgone,
    praxis.Prefers act.agent act.time {act.chosen} {givenUp}
```

The second is the claim that there is any action at all. Action itself
is a definition here, and no theorem uses it yet.

{docstring Apodictic.Action}

