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

The list is not padded, either. A linter refuses to let a hypothesis
stand unless the proof actually spends it, so nothing can be carried
for appearance. That is the whole reason to do this on a machine: it
will not let the list grow, and it will not let it shrink. The limits
of that guarantee are set out where the manifest is, and one of them
is itself a finding.

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
as his own argument does, when it holds six horses up against five to
ask which want "the larger stock would have satisfied" (p. 25). No
single real act can answer that.

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
from the axiom of action".

Read the clause slowly, because everything turns on it. The only thing
Rothbard will say about a man's choices before he makes them is that
they will obey the law of marginal utility. And saying it is exactly
what lets him hand the man a plan that already answers for every
smaller string of horses as well as the one in hand. But the law gets
proved from that very plan. The warrant for the premise is the
conclusion.

Notice where that leaves the machine. Nothing in the Lean runs
backwards: the derivation goes one way, from the claim to the law, and
the claim is never proved anywhere — it is handed in. The build passes,
and would pass however the claim had been arrived at. What a proof
assistant enforces is narrower and stranger than it first looks: that
the assumption be stated, stated in full, and spent in the open where a
reader can see what it cost. It cannot ask whether Rothbard was
entitled to assume it. Nothing can. That question took a reader holding
the stated claim in one hand and his own rule about value scales in the
other — and it could be asked at all only because the encoding refused
to let the claim stay unsaid.

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
  does not hold, the law simply does not speak. It makes no false
  claim; it makes none at all.

Telling which of the two gave way in a particular case is exactly what
an audit like this is for.

None of this makes the law wrong. The machine checked the reasoning:
the conclusion follows, and the proof uses only what the statement
lists. One question is left, and it is a narrow one — may praxeology
help itself to that standing plan?

Rothbard's is not the only derivation. Mises reaches the same law by
a different argument, and that argument, rebuilt the same way, turns
out to rest on a claim of the same kind, which he does not warrant
either. It is set out under *Mises's route*.

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
  flags the assumption — "each unit of means is capable of serving one
  of the ends", which he prefaces "We assume for simplicity" (p. 26) —
  and it reads like a premise of the derivation. It is not a premise of
  anything here. It was built into what a plan *is*, where no statement
  showed it; taken out, no theorem asked for it back. A stock whose
  next unit opens no further want is a case the law passes over in
  silence, and the six horses are a case where it does not, so nothing
  is lost. A simplification its own author flagged, and the ordering does
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
  it part of what a supply *is* (p. 23), and a stock where it fails is
  not one good but several. But his definition does not deliver it. It speaks
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
- Rothbard does say which unit goes, three times, and each time he
  gets the answer from interchangeability instead of stating a
  condition on the plan. With six horses, "As a result of the
  interchangeability of units, it does not matter to him which of the
  six units he must lose" (pp. 26–27). In the recapitulation of
  fundamentals: "The definition of a good is that it consists of an
  interchangeable supply of one or more units. Therefore, every unit
  will always be valued equally with every other" (p. 320). And a
  lost unit costs the lowest-ranked use "regardless of which end the
  unit is supplying at present" (p. 458). That "Therefore" is the
  step the counter-model refutes: units alike in what they can do
  does not make a plan blind to which of them it has. The charge
  does not need him to have shifted the word's meaning, either. Grant
  the usual reconciliation — p. 24 about units taken on one after
  another, p. 320 about units in a stock each valued at the margin —
  and both readings are still facts about the units or their
  valuation, where the size-based wording needs a fact about the plan
  over sub-stocks. It is a distinction prose has no way to mark, and
  one the machine would not leave unmarked.
- Independence of uses is a condition on the situation, and it can only
  be stated at all once preference ranges over bundles of ends rather
  than single ends. Where uses are complementary the law says nothing,
  and the statement admits as much.

Findings about the formalizing rather than the doctrine.

- The phrase "this bundle, minus this end" hides a premise: that the
  two can be told apart in the first place. It only came to light
  because the proofs refuse classical logic.
- The claim that people act splits into three: a definition, a bridge,
  and an existence claim. Only the bridge could do deductive work, and
  nothing has needed it.
- Never assert a claim about *every* structure of a given shape — say,
  every plan the man might have. Hand someone one plan and they can
  cook up a neighbour of it that breaks the claim, so a claim of that
  form is refutable by construction. Make it about the one plan the
  theorem actually receives, and the same construction is harmless. Better: it
  turns into a result. One of the theorems below proves that two plans
  satisfying the claim cannot differ by a single swap — so "the"
  value scale is something proved here, not something assumed.

# The claims


The library contains no `axiom`. Every praxeological claim is written
as a structure, and a theorem that needs one takes it as a named
assumption. So to see what a theorem rests on, you read its statement.

A linter keeps that list honest. `#lint only unusedArguments` refuses
the build when a listed assumption turns out to be idle, so little
survives that is there for show. Little, and not nothing: the linter
is something we choose to leave running rather than something imposed
on us, and two further gaps let an unused hypothesis slip past even
while it runs. All three are set out with the manifest below, where
one of them becomes a finding in its own right. It is never switched
off here.

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

There are three. The first is the premise of Rothbard's derivation,
and on his route it is the only claim the law needs. The second is the
premise of Mises's, reconstructed in the same vocabulary; the third is
asymmetry of preference, which neither derivation spends and one
comparison between them does. Each docstring names the theorems that
carry it.

{docstring Apodictic.SwapDominant}

{docstring Apodictic.ServedInOrder}

{docstring Apodictic.AsymmetricPreference}

# The conditions


The theorems take four assumptions besides the claims. Each says
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
- `stock.ComparableServiceable`: any two wants the good can serve are
  ranked one way or the other. Only Mises's route needs it; Rothbard's
  never does.

Nothing here has to say which plan is the man's. A theorem is handed a
plan and makes its claim about that one, so there is no rival plan
anyone could build to refute it.

All four are given in full here, in the order they are listed above,
because these are the assumptions a reader has to judge.

{docstring Apodictic.Stock.OneMore}

{docstring Apodictic.ActionFrame.IndependentUses}

{docstring Apodictic.AllocationPlan.Homogeneous}

{docstring Apodictic.Stock.ComparableServiceable}

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

One result here is not a step in the derivation. The claim is made
about a single plan rather than about every plan shaped like it. What
that gives up — that
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
And it judges each binder whole, so it cannot see a hypothesis half of
which is used — which happens in both marginal-utility
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

# Mises's route
%%%
file := "Mises-route"
%%%

Rothbard's is not the only derivation the tradition offers. Mises
reaches the same law in *Human Action* (ch. VII, §1) by an argument of
a wholly different shape, and the library carries his route as a
second target. It is built in a module that cannot see Rothbard's
theorems at all, so that whatever his argument spends has to be stated
there, and shows on the signature. A proof that could reach for
Rothbard's lemmas would have assumed the answer to the question this
part exists to ask.

His statement of the law:

> If the supply available increases from n–1 units to n units, the
> increment can be employed only for the removal of a want which is
> less urgent or less painful than the least urgent or least painful
> among all those wants which could be removed by means of the supply
> n–1.

Two things differ from Rothbard's wording. The ladder runs upward, from
n–1 to n, where Rothbard takes a horse away; and it singles out a least
urgent want, where Rothbard compares two named steps. It is read here
as Rothbard's is read — two supplies held up against each other at one
time — because Mises's own definition has that shape: the marginal
employment is the one a man makes at n units "but would not make if,
other things being equal, his supply were only n–1 units". A reading
on which the ladder is a history of acquisitions is a separate target,
and untouched.

{docstring Apodictic.Mises.marginalEmployment}

{docstring Apodictic.Mises.LeastUrgentServed}

{docstring Apodictic.Mises.LadderHolds}

**His conclusion is Rothbard's.** Before asking what Mises's argument
spends, ask whether it has to spend anything. Does the ladder follow
from Rothbard's premise outright? It does, and the proof is a few
lines. Two things fall out of it. The upward direction is narration.
And the least-urgent qualifier does no work at all: the proof consumes
only that the want was served at the smaller supply, and the machine
can show as much, because the same conclusion goes through for every
want served there, not only the least urgent.

{docstring Apodictic.Mises.ladder_for_every_served}

{docstring Apodictic.Mises.ladder_holds}

The marginal employment, meanwhile, is Rothbard's marginal ends under
another name — the same set, by definition. So there is one law on the
table, not two, and what differs between the authors is only the
argument for it.

{docstring Apodictic.Contrast.marginalEmployment_eq_marginalEnds}

**His argument is a dilemma.** Mises does not assert an ordering
premise the way Rothbard does. He holds that the law "is already
implied in the category of action", and argues it so:

> There are only two alternatives. Either there are or there are not
> intermediate stages between the felt uneasiness which impels a man
> to act and the state in which there can no longer be any action …
> In the second case there could be only one action; as soon as this
> action is consummated, a state would be reached in which no further
> action is possible. This is manifestly incompatible with our
> assumption that there is action; this case no longer implies the
> general conditions presupposed in the category of action. Only the
> first case remains.

The dilemma is encoded as it stands, with the second horn read through
its stated consequence — there could be only one action — rather than
through an invented measure of how much uneasiness remains. That keeps
the vocabulary as it was. Two small frames then check the two steps of
the argument, one each.

First, the refutation of the second horn. Mises says one action
followed by a terminal state is incompatible with "our assumption that
there is action". It is not. A frame admitting exactly one action
satisfies both halves he calls incompatible. What his step needs is
that action is plural — that two distinct actions occur — and the bare
claim that there is action does not deliver it. This is the first time
the library has put that claim to any work, and it was too weak for
the job.

{docstring Apodictic.Model.existence_does_not_refute_second_horn}

Second, grant him the horn. Let action be plural, so the dilemma is
won. The ladder still does not follow. A frame with two actions, a
preference that is asymmetric and not empty, and a plan that serves
the less urgent want first meets everything the dilemma establishes
and breaks the law.

{docstring Apodictic.Model.recurs_does_not_deliver_ladder}

So the dilemma is not the premise. What carries Mises from it to the
law is a single sentence, offered as though it added nothing: "It is
nothing else than the reverse of the statement that what satisfies
more is preferred to what gives smaller satisfaction." That sentence
is where his premise lives, and it is unargued.

**His premise, reconstructed.** The tempting reading of that sentence
adds a scale of satisfaction to the vocabulary — a second ordering, on
states, by how much uneasiness each removes. That was refused. It
would enlarge the ontology on one sentence's authority, it invites
cardinal degrees through the back door, and a satisfaction scale would
still have to be connected to which want a unit serves, which is the
premise all over again. The reading used instead is the most generous
one the existing vocabulary allows: the agent serves in order of
urgency. If the good can serve a want, and that want is more urgent
than one on his plan, the plan has it too. That is a
praxeological claim, subjunctive throughout like Rothbard's, and it is
the second of the three under *The claims*.

One thing more is needed, and it is a condition, not a claim: that
every pair of wants the good can serve is ranked, one way or the
other. Where a pair is not, the theorem is silent. It is the fourth under *The
conditions*, and the one Rothbard's route never asks for.

{docstring Apodictic.Mises.ladder_from_order}

Its manifest, printed by the same command as Rothbard's:

```lean (name := manifestLadder)
#manifest Mises.ladder_from_order
```
```leanOutput manifestLadder
manifest of Apodictic.Mises.ladder_from_order

  praxeological claims:
    order : ServedInOrder plan

  situational conditions:
    comparable : stock.ComparableServiceable

  vocabulary (what the claims are about):
    praxis : ActionFrame
    agent : praxis.Agent
    time : praxis.Time
    stock : Stock praxis agent time
    plan : AllocationPlan stock
    fewer : Finset praxis.Means
    more : Finset praxis.Means

  conditions carried by the vocabulary (not binders: discharged by
  whoever supplies the argument):
    stock.unitsAlike : ∀ unit ∈ stock.units, ∀ (want : praxis.End), praxis.Believes agent time unit want ↔ want ∈ stock.serves
    plan.servesOnlyWhatItCan : ∀ (subStock : Finset praxis.Means), ∀ want ∈ plan.wouldServe subStock, want ∈ stock.serves

  logical background: [propext, Quot.sound]

  (5 trailing binders belong to the conclusion, not the signature)
```

Hold it against the manifest of `marginal_utility`. Swap dominance is
gone, and so is independence of uses; in their place, one claim and
one condition, neither of which the Rothbard route carries. The two
carried conditions and the logical background are the same. This is
what the second target was for: not a verdict on one reconstruction
but a trade between two, computed from the signatures rather than
argued.

**The two premise sets, related.** Are the routes independent, then?
Not quite, and the relation runs one way. Given Rothbard's premise,
independence of uses, and asymmetry of preference, the agent serves
in order of urgency. Rothbard's premises entail Mises's bridge. The
asymmetry is the third claim under *The claims*, and this is the
theorem that spends it — the first in the library to force any
property on preference at all; it is recorded as ours, because no
sentence of either author states it.

{docstring Apodictic.Contrast.rothbard_entails_servedInOrder}

The converse fails. A frame can rank wants and serve them in order and
still be too coarse to rank bundles, and then serving in order holds
where swap dominance does not.

{docstring Apodictic.Model.servedInOrder_not_entail_swapDominant}

So on the allocation Mises's premise is strictly the weaker. The
premise sets are still incomparable, because his route pays for the
weaker premise with comparability of wants, which Rothbard's never
needs. Mises asks less of the agent's plan and more of his value
scale. And the price is paid in situations: there are agents to whom
Rothbard's law applies and Mises's does not. The gap is narrow, and
the reason it is narrow is itself a small finding — swap dominance
already ranks each served want against each unserved one the good
could reach, so the only pairs left unranked are those that never sit
on opposite sides of a margin.

{docstring Apodictic.Model.rothbard_applies_where_mises_is_silent}

**Where this leaves the question.** *The finding* ended on whether
praxeology may help itself to a standing plan. Mises's route does not
escape that question; it meets it in another form. His premise is as
counterfactual as Rothbard's — it says what the agent would serve at
every smaller supply — and he restricts value scales exactly as
Rothbard does, three chapters earlier: "These scales have no
independent existence apart from the actual behavior of individuals"
(ch. IV, §2). Where Rothbard exempts the law by name, Mises simply
announces that the counterfactual costs nothing: "We do not
transcend the sphere of praxeological reasoning in establishing the
following definition". Neither warrants the premise. That is as far as
this part goes.

# The circle
%%%
file := "The-circle"
%%%

Two derivations of one law have now been rebuilt, and they give way
at the same place. The pieces are under *The finding* and *Mises's
route*; this part sets them side by side and says plainly what the
audit does and does not establish about them. It is short because
most of the work is already done.

**Both deny needing what both use.** Rothbard's man has "no need for
him to formulate hypothetical value scales" (p. 33); Mises's scales
have "no independent existence apart from the actual behavior of
individuals" (ch. IV, §2). Two sentences, three chapters apart in one
book and a hundred pages into the other, and they are the same rule:
a man's ranking shows up in what he does, and nowhere else.

Then each derives the law from a premise that rule forbids. Rothbard's
premise ranks the wants the man would serve with every stable he could
cut from his own. Mises's asks less of that plan and more of the
ranking, and it is written over exactly the same stables — the two
claims quantify over the same region, every subset of the stock in
hand, and neither reaches an inch past it. Reach was never the
trouble, on either route. What both premises are is a settled answer,
held in advance, for every one of those stables at once — and that is
the scale in advance both authors say a man does not need.

**What each then helps himself to.** Rothbard sees the difficulty and
exempts the law from the rule by name, in a subordinate clause, with
the derivation as the exemption's only warrant. Mises does not see it,
or does not say so: he sets down his counterfactual definition and
announces that in doing so "We do not transcend the sphere of
praxeological reasoning" (ch. VII, §1). One reasons in a circle; the
other declares. Neither gives the premise a warrant that stands apart
from the law it is used to prove.

**The weaker premise does not help.** Mises's premise is strictly the
weaker on the allocation, and a reader might hope that weakening
further reaches something about actual choices alone. Here is the
reason to expect not. The law compares two supplies, and the man
holds one of them. Whatever premise delivers the law has to say
something about the supply he does not hold, and the only thing that
can be said about it is what he would do with it. Weakening the
premise changes how much it says in that tense; it cannot change the
tense. That is a reason, not a result: nothing here proves that no
premise about actual choices can reach the law, and no one has tried
to prove it. What the audit has is two routes, each resting on a
standing counterfactual its author disowns, and no third found.

**One shape, if you like.** This last is a reading and not a
finding, and it is offered as one. The two defects the audit turned
up in Rothbard — the circle here, and the inference about units set
out under *The other findings* — have a common form. Each time, what
is offered as a warrant does not reach what it is offered for. The
exemption is offered for the plan and reaches only the law; the
definition of a supply is offered for the plan's indifference to
which units and reaches only the units. Mises's declaration fits the
same form trivially, since it reaches nothing. Whether that is one
habit or two coincidences is not something a proof assistant can
say.

**What is and is not established.** Established: that each derivation
follows from its stated premise, that each premise is a claim about
what the man would do, that each author restricts value scales to
what he does do, and that neither warrants the exception. Not
established: that the law is false, that praxeology cannot have it,
or that no route from actual action exists. The question the audit
began with — whether the certainty Mises claimed for this law is the
certainty of a theorem — has an answer of the same width. The
derivation is as certain as its premise. The premise is the part
nobody has derived.

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
is a definition here, and no derivation of the law uses it. It has
been tried once. Mises appeals to it to close his dilemma, and a frame
with exactly one action shows the appeal falls short of what he needs;
the details are under *Mises's route*.

{docstring Apodictic.Action}

