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

*What this is.* This document rebuilds arguments of Mises and
Rothbard in Lean 4. Lean is a proof assistant: a program that checks
every step of a proof. The main case is the law of marginal utility.
Later parts do the same for exchange, time preference, the regression
theorem and interest. The aim is to find the premises the verbal
arguments leave unstated.

*Terms.* These words are used in every part.

- The library is the Lean code in which every step is checked.
- A docstring is the text attached to a name in the library.
- A theorem's signature lists everything it takes: its claims, its
  conditions, and the things they speak of, such as a man and his
  stock of goods.
- A praxeological claim, or claim, is a premise meant to hold of all
  action, not only in some situations. In the library each claim is a
  structure: a named bundle of statements, kept in the file
  `Praxeology.lean`. See {ref "claims"}[The claims].
- A condition says something about the situation, not about action as
  such. Where one fails, the theorem says nothing. See
  {ref "conditions"}[The conditions].
- The linter (`#lint only unusedArguments`) runs on every build, in
  every file whose theorems carry a claim or a condition. It fails the
  build when one of those theorems lists anything it never uses. An
  exception is a name marked with `_`. That mark records that the hypothesis does no work,
  and each such case is a finding (see {ref "manifest"}[The manifest]).
- A frame (`ActionFrame`) is a world of agents, goods, ends and times,
  with what each agent believes and prefers. The library builds some
  small frames. Some show that the claims and conditions can hold
  together. Others show that one premise does not give another.
- The vocabulary is the library's terms, such as a man's stock of
  goods and his plan for it. See {ref "vocabulary"}[The vocabulary].

*The result.* Rothbard says the law of marginal utility was "deduced
from the axiom of action" (*MES* p. 33). So one would expect it to need
only claims about what people do. Each author gives one verbal
argument for the law. Here these are called routes: Rothbard's in
*Man, Economy, and State* (pp. 24–27), and Mises's in *Human Action*
(ch. VII, §1; see {ref "mises-route"}[Mises's route]). On each route
the proof of the law checks. On each it needs exactly one claim. That
claim is not about action:

- On Rothbard's route it is swap dominance (`SwapDominant`).
- On Mises's route it is that the agent serves in order of urgency
  (`ServedInOrder`).

Each is about a plan: what the man would do with every part of his
stock, settled in advance. Neither is about anything he does.
A third reading of the law trades the plan for a claim about what he
does (`ActsInOrder`). It proves less in return: the law only on the
scale he ranked by before his stock grew. The case is made under {ref "finding"}[The finding].

*How to read it.* Lean will not let a proof skip a step. A premise the
argument needs must be written down, or the proof does not check. It
goes into the theorem's own statement, or into a definition the
statement names. So there is one fixed place to look. Read the
statement, the definitions it names, and the definitions those name in
turn. Every assumption the theorem rests on is there, or in Lean's
logical background. The small frames, and every theorem about them,
are in one file (`Consistency.lean`). For every theorem outside it,
that background is two axioms of ordinary mathematics (`propext`,
`Quot.sound`). It holds no claim about economics. Theorems in that file
may also use a third (`Classical.choice`). No theorem outside that file
depends on it.

The statement is also printed as a manifest. The project's command
`#manifest` derives it from the theorem. It sorts what the statement
lists into kinds: the claims, the conditions, and the things they
speak of. Some conditions do not appear in the statement itself. They
are fields of the structures the theorem takes as arguments, such as a
man's stock of goods. Those structures are definitions the statement
names. `#manifest` looks inside each of them that the library defines,
and prints their conditions too. It looks one level deep. Anything
deeper is in a definition that one of those names, and so on down. The
law of marginal utility carries two such conditions:

- Every unit of the stock is believed to serve exactly the ends the
  good can serve, by his lights (`stock.unitsAlike`).
- Whatever units the man's plan is asked about, it would serve no end
  the good is not believed able to serve (`plan.servesOnlyWhatItCan`).

The line headed _logical background_ is Lean's own. See
{ref "manifest"}[The manifest].

Each docstring here is taken from the library each time this document
is built. It is shown with the Lean signature it is attached to. Lean
checks that signature. It does not check the docstring's words. Each
manifest is printed by Lean during the same build. The prose around
them is not checked by Lean.

# The horses
%%%
tag := "horses"
%%%

Terms such as library, claim and condition are explained under
{ref "result"}[The Result].

Rothbard derives the law of marginal utility over pp. 24–27 of *Man,
Economy, and State*. He states it on p. 27:

> The greater the supply of a good, the lower the marginal utility;
  the smaller the supply, the higher the marginal utility.

He says what the marginal utility is: "This least important end
fulfilled by the stock is known as … marginal utility" (p. 27). Utility, he adds,
is "expressible only in terms of higher or lower order in the
preferences of men" (p. 28).

He works one case through: a man who owns six horses. This document
follows that case throughout. The library comes back to the same six
horses once the theorems are stated. The point is that you can hold
his paragraph beside the formal statement. Then you can judge for
yourself whether they say the same thing.

He sets the case up twice and takes a horse away. The first set-up
adds horses one at a time (*MES* p. 24). This builds the law upward,
as the stock grows:

> The first horse will fulfill the most urgent wants that a horse can
  serve; this follows from the universal fact that action uses scarce
  means to satisfy the most urgent of the not yet satisfied wants.

He then writes that "for all human actions, as the quantity of the
supply (stock) of a good increases, the utility (value) of each
additional unit decreases" (p. 25).

Between the two set-ups he takes a horse away (p. 25). This takes the law downward, from
six horses to five:

> Assume that a man has a supply of six (interchangeable) horses. …
  Suppose that he is now faced with the necessity of giving up one
  horse. … Obviously, he gives up the least urgent of the wants which
  the larger stock would have satisfied. Thus, if the individual was
  using one horse for pleasure riding, and he considers this the least
  important of his wants that were fulfilled by the six horses, the
  loss of a horse will cause him to give up pleasure riding.

The second set-up numbers the ends, for a diagram of the value
scale (his Figure 3, not shown here). The numbers are used later: "end
6" is the sixth-ranked end (pp. 25–26):

> We assume for simplicity that there are 10 ends which the means
  could fulfill, and that each unit of means is capable of serving one
  of the ends. If the supply of the good is 6 units, then the first
  six ends, ranked in order of importance by the valuing individual,
  are the ones that are being satisfied. Ends ranked 7–10 remain
  unsatisfied.

These passages carry the derivation. One more comes below.
Everything below tries to say them in a form a machine will check.

Three pieces of vocabulary carry the argument. They are worth naming
now, because the argument's shape turns on the second.

- The *stock* (`Stock`): the six horses, and the ends a horse can
  serve at all.
- The *plan* (`AllocationPlan`): for any set of horses he might
  have, which wants he would serve with them.
- The *preference* (`Prefers`): his ranking of one bundle of wants
  above another. Here a want and an end are the same thing (`End`). A
  bundle is a set of them. Nothing more is assumed of the ranking. It is not assumed transitive: A over B and B over C
  need not put A over C. It is not assumed complete: two bundles need
  not be ranked either way. No numbers are attached.

Rothbard's argument is one of two routes to the law (see
{ref "result"}[The Result]). On it the law needs one claim: swap
dominance (`SwapDominant`). It ties the plan to the ranking. Take any
set of his horses. Swap any want the plan would serve for any want a
horse could serve but the plan would leave unserved. Then he prefers what
the plan would serve to what the swap leaves him.

Ranking bundles, not single wants, is what lets the step from bundles
to single wants be a named condition (`IndependentUses`).

A property of the ranking is added only when some theorem forces it.
On this route the law forces neither transitivity nor completeness. The order among
single wants comes from swap dominance (`SwapDominant`), with
independence of uses (`IndependentUses`). See
{ref "theorems"}[The theorems] and
{ref "other-findings"}[The other findings].

The full definitions are under {ref "vocabulary"}[The vocabulary]. The
parts between here and that one can be read without them.

The plan is where the trouble starts. It is worth seeing why now,
before the formal statement makes it look inevitable.

Rothbard's argument compares six horses with five. But the man has
six. What he would do with five is not anything he does. It is a plan,
and it covers stocks he does not own. His own words give it away:
"which the larger stock *would have* satisfied".

The trouble is not that the plan covers such stocks. Rothbard reasons
about them himself. The trouble is that the plan is settled in
advance. It answers for every set of horses at once. It is not a
choice he makes, and no act of his settles it. That matters because
Rothbard holds that "value scales do not exist in a void apart from
the concrete choices of action" (p. 33). On the same page he exempts
this law from that rule, with no argument. The case is made under
{ref "finding"}[The finding].

His first passage is about acquiring horses one after another. It can
be read with no plan at all, as a history of what he did with each.
That reading returns under *The ladder as a history*.

A later passage (p. 27) decides how the plan has to be written down:

> suppose that the sixth horse that he had previously acquired (named
  "Seabiscuit") he had placed in the service of pleasure riding.
  Suppose that he now must lose another horse ("Man o' War") which had
  arrived earlier, and which was engaged in the more important duty
  (to him) of leading a wagon. He will still give up end 6 by simply
  transferring Seabiscuit from this function to the wagon-leading end.

End 6 here is pleasure riding, the sixth of his ranked ends.
Seabiscuit is the sixth horse in order of arrival.

Rothbard names two horses to insist that *which* horse goes makes no
difference. That is only worth saying if the plan could have depended
on which. So in the library the plan says what he would serve with
each particular set of horses. It is not indexed by a number of
horses (`AllocationPlan`). That only the number matters is a separate
{ref "conditions"}[condition] (`plan.Homogeneous`). It says any two
sets of his horses of the same size would serve the same wants. It is assumed only
where a theorem needs it.

The library builds a model of the six horses. Both of his conclusions
are proved as theorems about it, under
{ref "horses-lean"}[The horses in Lean]:

- The loss of a horse ends pleasure riding
  (`Model.loss_of_a_horse_ends_pleasure_riding`).
- Which horse goes makes no difference
  (`Model.which_horse_does_not_matter`).

Neither takes a condition. The second rests on a theorem that the
model's plan is interchangeable (`horses_homogeneous`). There the
condition is proved, not assumed.

# The finding
%%%
tag := "finding"
%%%

Terms such as library, claim and condition are explained under
{ref "result"}[The Result].

*In brief.* Rothbard states the law of marginal utility on p. 27 of
*Man, Economy, and State*:

> The greater the supply of a good, the lower the marginal utility;
  the smaller the supply, the higher the marginal utility.

The marginal utility is the least important end the stock serves:
"This least important end fulfilled by the stock is known as …
marginal utility" (p. 27). Rothbard says the law was "deduced from the
axiom of action" (p. 33). So one would expect it to need only claims
about what people do. On both routes the authors wrote, it needs
exactly one praxeological claim. That claim is not about action. It is
about a plan: what the man would do with every part of his stock,
settled in advance. It is not about anything he does. Each route has
its own such claim:

- On Rothbard's route the claim is `SwapDominant`.
- On Mises's route it is `ServedInOrder`.

A third reading trades it for a claim about action (`ActsInOrder`).
That reading is taken up at the end of this part.

Go back to Rothbard's man with six horses (see
{ref "horses"}[The horses]). On Rothbard's route the claim
(`SwapDominant`) is about what the man *would* do. For each set of
horses he might have, which wants would he serve? The answer is a
plan. It is not a choice he makes.

The claim ties the plan to his ranking. A bundle is a set of wants.
Take any set of his horses and the bundle the plan would serve with
it. Make any single swap: trade any want served for any want a horse
could serve, by his lights, that the plan leaves out. The claim says he prefers the bundle
the plan would serve to the bundle after the swap.

Rothbard's own premise packs two claims into one sentence (*MES*
p. 24):

- A man acts with the means he has.
- The wants he serves are "the most urgent of the not yet satisfied
  wants".

Only the second does any work here. The claim (`SwapDominant`) keeps
it and drops the first. It states it in the subjunctive: over the wants
he *would* serve. So does Rothbard's own argument. It holds six horses
up against five. It asks which want "the larger stock would have
satisfied" (p. 25). No single real act can answer that.

*The subjunctive alone is not the trouble.* The plan has a trouble,
and the next paragraphs locate it. One might complain that
the claim speaks of stocks the man does not hold. That is the obvious
complaint, and it fails. Reasoning about stocks the man does not hold
is Rothbard's own practice:

- He builds the law upward, from one horse to two to three.
- He takes it downward, from six horses to five.
- He says outright that holding none of a good "does not affect the
  principle" (p. 32).

What he refuses on p. 33 is something else. It is a hypothetical value
scale for a wholly different endowment. His example has several goods,
X, Y and Z. The man holds three units of X, four of Y and two of Z:
(3X, 4Y, 2Z). The refused scale is for (6X, 8Y, 5Z). What he allows is different: his choices "for
adding and subtracting from stock take place in this region". The
region is that of the stock he has. So the line between what he allows
and what he refuses is drawn around the stock in hand. It is not drawn
at some distance from it. Each of his own steps adds or takes away one
unit of the stock held at that point. His upward build is made of
such steps: the man "successively finds one horse, then a second, then
a third" (p. 24). Stepping down one unit at a time from six horses
reaches
every set of horses cut from those six. The formal claim
(`SwapDominant`) speaks only of those sets. It reaches no further than
he does.

*The trouble is timing.* What matters is when the answer is settled.
Rothbard restricts value scales in two phrases (p. 33):

- "value scales do not exist in a void apart from the concrete choices
  of action"
- "there is no need for him to formulate hypothetical value scales"

His man needs no scale in advance. The scale shows up choice by
concrete choice, as each choice is made. The plan is different. It is
a single standing object. It answers for every set of horses at once,
before any of the choosing. That is precisely the scale in advance
that Rothbard says is not needed. More than that, he says scales "do
not exist in a void apart from the concrete choices of action". The
plan is a scale of the kind he denies. It stands apart from the
choices. So the complaint is not that we
asked what he would do with five horses. It is that we gave him a
settled answer for every set at once. No act of his settles it.

*The exemption.* The law itself says something about the man's
choices before they are made. Rothbard saw a difficulty here. He
exempted this law by name. He did it on that same page, in a subordinate
clause, with no argument attached. No one can predict with certainty the
course of a man's choices, he says, "except that they will follow the law of
marginal utility, which was deduced from the axiom of action".

Read the clause slowly, because everything turns on it. Before a man
makes his choices, Rothbard will say only one thing about them with
certainty: they
will obey the law of marginal utility. The plan, too, says in advance
what the man would choose. So saying this is what lets him hand the
man a standing plan, one that answers for every smaller set of horses
as well as for the stock in hand. But the law gets proved from that
very plan.
The warrant for the premise is the conclusion.

*What the machine enforces.* The circle is in the warrant, not in the
proof. Nothing in the Lean is circular. The derivation goes one way,
from the claim to the law. The claim is never
proved anywhere. It is handed in. The build passes. It would pass
however the claim had been arrived at.

What a proof assistant enforces is narrower and stranger than it first
looks. It enforces three things about the assumption:

- It is stated.
- It is stated in full.
- It is spent in the open, where a reader can see what it cost.

It cannot ask whether Rothbard was entitled to assume it. No machine
check can. That question took a reader. The reader held the stated claim in one
hand and Rothbard's own rule about value scales in the other. And the
question could be asked at all only because the encoding refused to
let the claim stay unsaid.

This is not an objection from outside. The rule is Rothbard's. So is
the exemption. The claim is Rothbard's in doctrine. Its one-swap form
is this document's encoding, not Rothbard's.

*The second demand: units.* The same plan has to carry a second thing.
That thing belongs to a question usually discussed apart from this
one: the question of units. The law is expected to founder on them:

- To state the law by the size of a supply, you seem to need units the
  agent values equally.
- Rothbard denies that anyone ever demonstrates indifference by
  acting.

Here the law does not founder. Indifference is assumed nowhere, and
the law survives without it. The library states the law in two forms
(see {ref "theorems"}[The theorems]):

- By the size of a supply, as Rothbard words it (`marginal_utility`).
- Along a chain of named units, one added at a time
  (`marginal_utility_chain`).

The chain form needs no interchangeability of units, because it names
which units are involved. What the size-based wording needs is weaker
than indifference. The plan must not care *which* units the man has,
only how many (`plan.Homogeneous`). With the six horses, any five would be put to
the same uses. But that is one more thing the standing plan must
already have settled. Rothbard does not deduce from the axiom of
action that the plan cares only how many. He grounds it in his
definition of a supply: units "equally capable of rendering the same
service to the actor" (p. 23).

That definition does not deliver it. Equal serviceability of the
units does not give a plan that cares only how many
(`plan.Homogeneous`). This is checked, not argued: a
theorem in the library proves it
(`unitsAlike_not_entail_homogeneous`). Equal serviceability is a fact
about the horses (`unitsAlike`, a condition carried by the stock). The wording
needs a fact about the man's plan for them. Take one stable of two
horses, each able to serve any want. It carries a plan that treats the
two alike. It also carries a plan that does not. The stock cannot
settle it, because the plan is a separate thing.

His definition of a supply has a second half, about valuation. That
half would settle it: the man "must have valued each horse or each cow
identically" (p. 23). But he withdraws that on the next page. There,
interchangeability "does not mean that the concrete units are actually
valued equally" (p. 24). Valuing each horse identically would be
indifference among them. So taking it back is what keeps indifference
out of the law. The cost is that the definition no longer carries the
condition the law's wording needs.

*Two demands.* The encoding keeps them apart:

- The one the law is derived from is a *praxeological claim*
  (`SwapDominant`, on Rothbard's route). It rides on the signature of
  every theorem that uses it. If it is false, praxeology has asserted
  something false, and the law loses its proof on this route.
- The one its wording needs is a *condition* of the size form of the
  law (`plan.Homogeneous`). Where it does not hold, the law simply does
  not speak. It says nothing false. It says nothing at all.

Telling which of the two gave way in a particular case is exactly what
an audit like this is for.

None of this makes the law wrong. The machine checked the reasoning.
The conclusion follows. The proof uses only what the statement lists.
One question is left, and it is a narrow one. May praxeology help
itself to that standing plan? Rothbard's own warrant for it is
circular, as shown above. Whether praxeology has another warrant,
this page does not settle.

*The other routes.* Rothbard's is not the only derivation.

- Mises reaches the same law by a different argument. Rebuilt the same
  way, it turns out to rest on a claim of the same kind
  (`ServedInOrder`). Mises does not warrant it either. It is set out
  under {ref "mises-route"}[Mises's route].
- A third way reads the ladder as a history. The ladder is the law
  built upward: one horse, then a second, then a third. As a history it
  is about what the man served as his stock grew. It spends a claim
  about what he actually does (`ActsInOrder`), and no plan at all. It
  proves the ladder only on the scale he ranked by before the stock
  grew. On that scale it is a short theorem. It restates acting in
  order about a want the next horse happens to serve. It also needs
  two conditions. Any two wants the good can serve were ranked at the
  earlier moment, one way or the other
  (`earlier.ComparableServiceable`). He learned no new use for the
  good between the two moments (`earlier.NoNewUses later`). On the
  later scale the ladder does not follow from acting in order, even
  granted at both moments (`Model.later_judged_ladder_fails`). It pays
  for doing without a plan in a different coin. The first two routes
  rest on a plan their authors refuse. This one needs a man who learned
  no new use for the good between the two acts. Neither author
  addresses that condition. Nothing in the texts grants it, and nothing
  refuses it. The part called {ref "ladder-history"}[The ladder as a history] sets it out.

# The other findings
%%%
tag := "other-findings"
%%%

Terms such as library, claim and condition are explained under
{ref "result"}[The Result].

The audit turned up more than the one claim. This part lists the rest.
Most of it is about the law of marginal utility. Rothbard states it on
p. 27 of *Man, Economy, and State*:

> The greater the supply of a good, the lower the marginal utility;
  the smaller the supply, the higher the marginal utility.

The marginal utility is the least important end the stock serves:
"This least important end fulfilled by the stock is known as …
marginal utility" (p. 27). Here a want and an end are the same thing
(`End`). A bundle is a set of ends.

Two pieces of the library recur below. They are set out under
{ref "horses"}[The horses] and {ref "finding"}[The finding].

- The plan (`AllocationPlan`): for any set of units the man might
  have, which ends he would serve with them.
- Swap dominance (`SwapDominant`), the one claim the law needs on
  Rothbard's route. Take any set of his units, and the ends the plan
  would serve with it. Make any single swap: take out any end the plan
  would serve, and put in any end it leaves out that he believes the
  good could serve. The claim says he prefers what the plan would
  serve to what the swap leaves him.

The findings fall into three groups.

*What the derivation is, and what it delivers.*

- Rothbard's derivation takes one step. It starts from what he calls
  the "universal fact that action uses scarce means to satisfy the
  most urgent of the not yet satisfied wants" (p. 24). He asserts that
  premise. The library's proof has three steps, and only the first
  does any work (see {ref "theorems"}[The theorems]). So it too has one
  working step, and is faithful to him. So the audit's point is not
  the proof. It is the premise. He calls the law "derived from the
  fundamental axiom of human action" (p. 27). That derivation rests on
  an assertion.
- The law is strict, as Rothbard's is. The theorem
  (`marginal_utility`) says that every end marginal at the smaller
  supply is preferred to every end marginal at the larger. It is not
  the weaker claim that the one is ranked no lower. That weaker form,
  non-increasing marginal utility, is the neoclassical one. It is not
  his.
- Nothing assumes that exactly one end is given up. Rothbard's phrase
  "the marginal unit" takes that for granted. Here, when the supply
  shrinks by one unit, the law holds for every end given up.
- One unit to one end is not needed at all. Rothbard assumes it. He
  flags the assumption: "each unit of means is capable of serving one
  of the ends". He prefaces it "We assume for simplicity"
  (pp. 25–26). It reads like a premise of the derivation. It is not a
  premise of any theorem here. At first the library built it into the
  definition of a plan (`AllocationPlan`). There it sat in a field of
  the plan, not in any theorem's statement. It has since been taken
  out. No theorem asked for it back. Without it, adding one unit may
  add no new end. The law speaks of every end a one-unit step adds.
  Where the step adds none, the law says nothing about it. Every plan
  that met the assumption is still a plan, and the law still holds of
  it. So dropping the assumption loses nothing. The six horses meet it:
  each horse added serves one more end, so there the law speaks (see
  {ref "horses"}[The horses]). It is a simplification its own
  author flagged. The ordering the law states does not need it.
- The proof never uses the fact that the end at the smaller supply is
  the marginal one. The law holds for every end served there. It holds
  against every end the next unit would add. Something stronger holds
  still. A theorem (`served_over_unserved`) shows that a served end
  beats *any* unserved end that could be served, not only the one the
  next unit reaches. Rothbard's statement claims less than his premise
  delivers.

*What the law does not need.* Rothbard's text supplies most of it.

- On Rothbard's route the law needs neither transitivity of preference
  nor completeness. Transitive would mean that A over B and B over C
  puts A over C. Complete would mean that any two bundles are ranked
  one way or the other. Rothbard assumes a single ranked value scale
  (Figure 3, pp. 25–26). The law does not need one. The ordering comes
  from the plan instead, through swap dominance (`SwapDominant`) and
  independence of uses (`IndependentUses`, explained below).
- Interchangeability of units (`plan.Homogeneous`) is not needed for
  the ordering. It is the condition that any two sets of his units of
  the same size would serve the same ends. Here the plan is indexed by
  which units, not by how many. With that, two theorems go
  through without interchangeability:
  the urgency principle (`urgency_principle`), and the law along a
  chain of named units (`marginal_utility_chain`). The chain is three
  named sets of units, each one unit more than the last. Among the
  law's theorems, interchangeability is needed exactly once: to state
  the law by size of supply (`marginal_utility`). The phrase "the plan
  at `n` units" picks out one thing only if two piles of the same size
  serve the same ends. So interchangeability bears on the wording, not
  on the derivation. Where it fails, the law stated by size says
  nothing, and the chain form still holds. That is why it is a
  condition and not a praxeological claim.
- Rothbard makes interchangeability part of what a supply *is*
  (p. 23). On his definition, a stock where it fails is not one good
  but several. But what his definition fixes is a fact about the
  units. It speaks of units "equally capable of rendering the same
  service". The wording needs a fact about the man's plan for them. So
  his definition does not deliver the condition. One stock can carry a
  plan that cares only how many units it has, and a plan that cares
  which. The library's counter-model is two horses, each able to serve
  any want, with one plan of each kind
  (`unitsAlike_not_entail_homogeneous`, a theorem). So no condition on
  the units can decide it.
- Indifference between units is needed nowhere. No claim or condition
  in the library says the man is indifferent between units, and the
  law is proved without one. Rothbard defines a supply with the words
  "valued equally" and "regards ... indifferently" (p. 23). He takes
  them back on the next page: interchangeability "does not mean that
  the concrete units are actually valued equally" (p. 24). The
  formalization follows p. 24.
- Three times Rothbard treats which unit goes as making no difference.
  Twice he gets the answer from interchangeability (pp. 26–27,
  p. 320). On p. 458 he refers back to "the basic law of utility". In
  none of the three does he state a condition on the plan (`plan.Homogeneous`).
  With six horses: "As a result of the interchangeability of units, it
  does not matter to him which of the six units he must lose"
  (pp. 26–27). In the recapitulation of fundamentals: "The definition
  of a good is that it consists of an interchangeable supply of one or
  more units. Therefore, every unit will always be valued equally with
  every other" (p. 320). And a lost unit costs the lowest-ranked use
  "regardless of which end the unit is supplying at present" (p. 458).
- That "Therefore" is the step the counter-model refutes
  (`unitsAlike_not_entail_homogeneous`). Units can be alike in what
  they can do. That does not make a plan blind to which of them it
  has. Pages 24 and 320 can look opposed. On p. 24 interchangeability
  "does not mean that the concrete units are actually valued equally".
  On p. 320 "every unit will always be valued equally with every other"
  follows a "Therefore". The objection to that "Therefore" holds even
  if the two pages are consistent. Grant the usual reconciliation.
  On it, p. 24 is about units taken on one after another. Page 320 is
  about units in a stock, each valued at the margin. Both readings are
  still facts about the units or their valuation. The size-based
  wording needs a fact about the plan over sets of units. In these
  three passages Rothbard's prose never marks that distinction. The
  machine would not leave it
  unmarked.
- Independence of uses is a condition on the situation
  (`IndependentUses agent time`). Take two bundles that are the same
  except that one has one end where the other has another. It says
  that preferring the first bundle to the second carries down to
  preferring its end to the other's. So it can be stated at all only
  once preference ranges over bundles of ends, not just single ends.
  It fails where uses are complementary: where one end is worth having
  only alongside another. There the law says nothing. The law's
  statement carries the condition. So the statement itself shows where
  the law is silent.

*About the formalizing, not the doctrine.*

- The swap takes one end out of a bundle and puts another in. Forming
  "this bundle, minus this end" hides a premise: that two ends can be
  told apart in the first place (`DecidableEq praxis.End`). Classical
  logic would grant that for free, by assuming every question has a
  yes-or-no answer. The proofs refuse classical logic. So the premise
  had to be stated, and that is how it came to light (see
  {ref "manifest"}[The manifest]).
- The claim that people act splits into three. There is a definition
  (`Action`). It asserts nothing. There is an existence statement, from
  Mises's argument (`Mises.ActionOccurs`; see
  {ref "mises-route"}[Mises's route]). It says only that some action
  occurs. It says nothing about what anyone prefers. And there is a
  bridge from an act to a preference (`DemonstratedPreference`). It
  says that, at a trade, the man prefers the holding he chose to what
  refusing would have left him with. Of the three, only the bridge could do deductive
  work. The law of marginal utility never needs it. Three parts need
  it: *Exchange*, *The regression theorem* and *Interest*. Rothbard
  states it of any action. Each time it enters here, it is stated of
  one trade (see {ref "claims"}[The claims]). *Time preference* needs
  a second bridge, for acts across dates (`DemonstratedTimePreference`).
- The ladder is the law built upward: one horse, then a second, then
  a third. Read as a history, it is about what the man served as his
  stock grew (see {ref "ladder-history"}[The ladder as a history]).
  That reading uses a claim about what a man actually does
  (`ActsInOrder`). That claim is neither of the two bridges just named
  (`DemonstratedPreference`, `DemonstratedTimePreference`). Each of
  those runs from an act to his ranking. This one runs from his
  ranking to his act. It says nothing about what an act shows he
  prefers. So tying the ranking to what he does here takes a
  separate claim in each direction.
- One finding became a rule of method. Take a claim about *every*
  structure of a given shape: say, every plan the man might have. A
  plan is only a rule saying which ends each set of units would serve.
  So from any one plan you can define a neighbour: the same plan,
  changed by one swap at one set of units. Such a neighbour can break
  the claim. So a claim of that form is refutable by construction. The
  rule: never assert one. Make the claim about the one plan the
  theorem actually receives. Then the construction of a neighbour is
  harmless. Better: it turns into a result. The theorem
  `no_rival_swap_dominant`, shown under {ref "theorems"}[The theorems],
  says that, if preference is asymmetric, the neighbour cannot also
  satisfy swap dominance (`SwapDominant`). Two plans satisfying it cannot differ by a single
  swap at some set of units. The theorem takes one more claim:
  preference is asymmetric (`AsymmetricPreference`, one of
  {ref "claims"}[The claims]). If he prefers one bundle to another, he
  does not prefer the second to the first. Rothbard writes as though
  the man's value scale were simply given: "the" marginal unit, "the"
  least urgent want (*MES* pp. 24–27). He never argues that there is
  only one. Here that scale is the plan. What is proved is narrower:
  no rival plan that, at some set of units, is one swap from his also
  satisfies swap dominance. The theorem says nothing of a rival plan
  that is never a single swap from his, at any set of units.

# The claims
%%%
tag := "claims"
%%%


Terms such as library, docstring, claim, condition, linter, frame and
vocabulary are explained under {ref "result"}[The Result].

The library contains no `axiom`. In Lean, an `axiom` can be used by
any proof without appearing in the statement of the theorem it
proves. Only a separate report shows it: the last line of each
manifest. So instead, every praxeological claim is written as a
structure. A theorem that needs a claim takes it as a named
assumption. So to see what a theorem rests on, you read its statement.

A theorem's statement thus lists the claims it rests on. That list
cannot be padded either. Take, say, a claim about action that the
proof never touches. A theorem could list it only to look better
grounded. `#lint only unusedArguments` runs on every build. It fails
the build when a listed assumption does no work. So the list is held
from both sides:

- Lean rejects a theorem that leaves a premise off. Without the
  premise, the proof does not check.
- The linter rejects a theorem that lists a premise it never uses.

That is the reason to do this on a machine. The hold is not perfect.
Where it gives is set out under {ref "manifest"}[The manifest].

Below, a theorem is said to *spend* a claim when its proof uses it.

Each claim records three things:

- *Source*: a citation, or "tacit". *MES* is Rothbard's *Man, Economy,
  and State*. Citations of Mises and Rothbard are to the Mises Institute
  editions.
- *Status*: a verdict, or two, from the three listed next.
- *Does not say*: the stronger nearby claims it deliberately avoids.

The three verdicts are these:

- explicit-in-tradition: Rothbard or Mises say it.
- suppressed-premise: they use it without saying it.
- our-reconstruction: a decision the tradition never faced.

A Status may give two verdicts. The first is for the doctrine: what
the tradition holds. The second is for the claim as written here, or
for a named part of it, such as its form. So "explicit-in-tradition
as doctrine; our-reconstruction as a claim" says this: the tradition
states the doctrine, and the claim as it stands here is ours. Where
there are two, the Status says which part is ours.

Two rules govern the list:

- A claim is added only when some theorem first needs it. So every
  claim here is one that some theorem actually uses.
- Only claims meant to hold always belong here. A condition says when
  a theorem applies. Where it fails, the theorem says nothing. It is
  not a claim. A theorem takes it as a hypothesis of its own, or finds
  it in a field of the vocabulary (see {ref "result"}[The Result]). The
  docstrings below call such a condition either a hypothesis or a
  condition. The two words mean the same there. The conditions have a
  part of their own, {ref "conditions"}[The conditions].

The claims speak of a few things from the vocabulary:

- The stock (`Stock`): the units of one good that a man holds at one
  time, and the ends the good can serve, by his lights.
- The plan (`AllocationPlan`), for a stock: for any set of its units he
  might have, which ends he would serve with exactly those units. It
  is settled in advance.
- The preference (`Prefers`): his ranking, at a given time, of one
  bundle of ends above another. A bundle is a set of ends. Nothing
  more is built into the ranking. A theorem that needs more takes it as
  a claim, such as the third below, or as a condition. The same ranking of single ends is
  `PrefersEnd`.
- Times have names. `now` is the present time of a claim. It is a
  variable: any time can play that part.

Take a claim about every plan the man might have. From any one plan
a neighbour can be defined: the same plan, changed by one swap at one
set of units. Such a neighbour can break the claim. So a claim of that
form is refutable by construction. Hence a rule of method: each claim
about a plan is made of the one plan a theorem is handed, never of
every plan. The rule is set out under
{ref "other-findings"}[The other findings].

A dotted name, such as `Apodictic.Model.Impulse`, is a name in the
library. Names under `Apodictic.Model` are in `Consistency.lean`: the
small frames and the theorems about them.

There are ten. The first three are these:

- The first is the premise of Rothbard's derivation (`SwapDominant`).
  On his route it is the only claim the law of marginal utility needs.
  The theorem that derives the law there is `marginal_utility`.
- The second is the premise of Mises's derivation, reconstructed in
  the same vocabulary (`ServedInOrder`). Mises argues for the law by a
  dilemma. The dilemma does not deliver this premise. A small frame
  meets everything the dilemma establishes, and breaks the law
  (`Model.recurs_does_not_deliver_ladder`). Both are set out under
  {ref "mises-route"}[Mises's route].
- The third is asymmetry of preference (`AsymmetricPreference`). If he
  prefers one bundle to another, he does not prefer the second to the
  first. Neither derivation spends it. The theorem relating the two
  routes does (`Contrast.rothbard_entails_servedInOrder`, under
  *Mises's route*). Four theorems under {ref "interest"}[Interest]
  also spend it. So does the rival-plan theorem
  (`no_rival_swap_dominant`, under {ref "theorems"}[The theorems]).
  Take a plan that satisfies swap dominance, and a rival plan for the
  same stock. At one set of units on hand, the rival would serve what
  the first would serve there, with one change. One end the first
  would serve is swapped out. In its place is an end the good can
  serve that the first would leave out there. Given asymmetry, the
  theorem says the rival does not also satisfy swap dominance.

The next two are about what a man actually does, not what he would do:

- The fourth is the premise of the ladder read as a history
  (`ActsInOrder`). The ladder is the law built upward: one horse, then
  a second, then a third, in Rothbard's example of a man's horses (see
  {ref "horses"}[The horses]). Read as a history, it is about what the man
  served as his stock grew. The docstring calls this the temporal
  reading. The claim runs from his ranking to his act. The theorem
  under {ref "ladder-history"}[The ladder as a history] carries it
  (`Temporal.ladder_judged_earlier`).
- The fifth runs the other way, from an act to his ranking. It is
  demonstrated preference (`DemonstratedPreference`). Rothbard states
  it of any action. Here it is stated of one trade. *Exchange*, *The
  regression theorem* and *Interest* carry it.

The next two are about time:

- The sixth is time preference (`TimePreference`). A satisfaction is
  preferred sooner rather than later. One theorem under
  {ref "time-preference"}[Time preference] carries it
  (`TimePreference.less_durable_preferred`). So do the interest
  theorems that conclude a preference or a rate
  (`PureInterest.present_sum_preferred`,
  `PureInterest.present_sum_preferred_to_less` and the three loan
  theorems under {ref "interest"}[Interest]).
- The seventh is its demonstration (`DemonstratedTimePreference`). It
  is stated of one act. Taking a satisfaction and forgoing the same
  satisfaction later shows a preference for the sooner. Like the fifth,
  it runs from an act to his ranking. It is set out under *Time
  preference*. Two theorems there carry this claim
  (`TimePreference.consumption_reveals`, `TimePreference.regress`).

The next two are about a medium of exchange. Both are premises of the
regression theorem, under {ref "regression"}[The regression theorem].
Its argument runs back through a record of exchanges. The docstrings
call that argument a regress. The seventh claim's docstring uses the
word for a different argument, Mises's on time preference (see *Time
preference*).

- The eighth is appraisal from the past (`AppraisalFromPast`). Nobody
  appraises a good as a medium unless it changed hands on some earlier
  day.
- The ninth is Mises's division of the demand for a medium into two
  (`TwoPartialDemands`). Sort the ends into those reached by passing
  a good on, and the rest. The sort leaves none over. Classical logic
  would grant that sort for free, by assuming every statement is true
  or false. That assumption is called excluded middle. The library's
  theorems outside `Consistency.lean` do without it: they are
  constructive. So the sort has to be stated, and this claim states
  it.

Where the sort is needed comes from the theorem's two forms. Mises
states the theorem in the negative. Say nobody acquired the good,
before a given day, for an end other than passing it on. Then on that
day nobody appraises it as a medium. The positive form turns it round.
Say the good is a medium on some day. Then on an earlier day, someone
acquired it for an end other than passing it on. At each step back,
the proof meets an acquirer and the end he wanted the good for. The
positive form has to decide whether that end is onward or not. The
negative form never has to decide. So the positive forms carry the
ninth claim (`Regression.direct_acquisition_before`,
`Regression.narrow_acquisition_before`, `Regression.barter_origin`,
`Regression.prior_money_relates_back`). The negative forms do not.
Two other theorems carry it too
(`Regression.partial_demands_exhaust`,
`Regression.only_onward_without_direct`).

The tenth is the interest theorems' own claim. It is about sums of
money (`MoreMoneyPreferredWhenSpent`). Take two sums of money, one
part of the other. Take the date he would spend them (`spend`). The
claim says this. Say both sums are free to hold now: holding them
costs him nothing. And say the two would buy different ends. Then, at
that date, he prefers what the larger would buy to what the smaller
would buy. The claim applies only where the two would buy different
ends. It does not say that they do. A theorem that needs that takes a
condition (`BuysMoreThanItsParts`): every strict part of a given sum
would buy other ends than the whole does. The theorems that carry the
claim also carry time preference (`TimePreference`). They are under
*Interest*.

The manifests in each part list exactly which claims each theorem
carries.

{docstring Apodictic.SwapDominant}

{docstring Apodictic.ServedInOrder}

{docstring Apodictic.AsymmetricPreference}

{docstring Apodictic.ActsInOrder}

{docstring Apodictic.DemonstratedPreference}

{docstring Apodictic.TimePreference}

{docstring Apodictic.DemonstratedTimePreference}

{docstring Apodictic.AppraisalFromPast}

{docstring Apodictic.TwoPartialDemands}

{docstring Apodictic.MoreMoneyPreferredWhenSpent}

# The conditions
%%%
tag := "conditions"
%%%


Terms such as library, claim, condition and frame are explained under
{ref "result"}[The Result].

The law of marginal utility is read three ways here. Two are the
routes: Rothbard's and Mises's. The third is the ladder read as a
history. All three are introduced under {ref "result"}[The Result].
The third has a part of its own,
{ref "ladder-history"}[The ladder as a history]. Across the three, the law takes five conditions besides the claims
(see {ref "claims"}[The claims]). Each says something about the
situation, not about action as such. Each is written into the
statement of every theorem that needs it. So a reader can point at
one and say: that is the one that did not hold. Where one fails, the
law says nothing. It is silent, not wrong.

The list speaks of the man's plan (`AllocationPlan`). For each set of
his units, the plan says which wants he would serve with exactly those
units. Such a set is a sub-stock. The plan is under
{ref "vocabulary"}[The vocabulary].

- One more unit (`stock.OneMore fewer more`). The two piles compared
  are both sub-stocks: both are cut from the units on hand. They
  differ by exactly one unit. So the theorems that carry it compare
  only parts of the man's own stock. Rothbard's route and Mises's
  route carry it. The ladder read as a history does not.
- Independence of uses (`IndependentUses agent time`). A bundle is a
  set of wants. Take two bundles that differ in one want only: the
  first has want X where the second has want Y. If he prefers the
  first bundle to the second, he prefers X to Y. Put loosely: what one
  want is worth does not depend on which other wants are being served.
  Of the three readings, only Rothbard's route carries it.
- Interchangeability of units (`plan.Homogeneous`). The plan depends
  only on how many units there are, not on which ones. On Rothbard's
  route the law has two forms (see {ref "theorems"}[The theorems]).
  The chain form (`marginal_utility_chain`) names which units. The
  size-based form (`marginal_utility`) compares supplies by size. Only
  the size-based form carries this condition. No theorem on Mises's
  route carries it.
- Comparability (`stock.ComparableServiceable`). Any two wants the
  good can serve are ranked one way or the other. Mises's route needs
  it (`Mises.ladder_from_order`). So does the ladder read as a history
  (`Temporal.ladder_judged_earlier`). No theorem on
  Rothbard's route carries it. That route's claim is swap dominance
  (`SwapDominant`, under {ref "claims"}[The claims]). At any sub-stock,
  swap one want the plan serves for one the good can serve but the plan
  leaves unserved. He prefers the wants the plan would serve there to
  the wants left after the swap. With independence of uses, this ranks
  some pairs of wants. At any sub-stock, he prefers every want the plan
  would serve to every want the good can serve that the plan would
  leave unserved (`served_over_unserved`, under
  {ref "theorems"}[The theorems]). Every pair of wants that route's
  theorems compare is of that kind: one served at a sub-stock, one left
  unserved there. That is so for `urgency_principle` directly, and for
  the chain form through it. For the size-based form it holds once
  interchangeability of units (`plan.Homogeneous`) makes the plan the
  same at its two sub-stocks of one size. So those pairs are ranked without
  comparability. What stays unranked is under
  {ref "mises-route"}[Mises's route].
- No new uses (`earlier.NoNewUses later`). At the later moment, the
  good is believed to serve no use it was not believed to serve at the
  earlier one. Only the ladder read as a history needs it. There it is
  the one condition that spans two moments. It is about what he
  believes the good can do, not about how he ranks his wants. And it
  runs one way: whatever is believed later was believed earlier, not
  the reverse. The man learns no new use, though he may drop an old
  one.

No theorem here has to pick out which plan is the man's. Each is
handed a plan, and its statement is about that plan. The other way
would be a claim about every plan the man might have. Such a claim can
be refuted by construction. From any one plan a neighbour can be
built: the same plan, changed by one swap at one set of units. Take
the claim that every such plan satisfies swap dominance. If preference
is asymmetric, the neighbour of a plan that satisfies it does not
(`no_rival_swap_dominant`, under {ref "theorems"}[The theorems]). So
nothing here is said of every plan. The one condition here that
speaks of a plan (`plan.Homogeneous`) ranges over every sub-stock.
But it is a condition on the one plan the theorem is handed. So
there is no rival plan anyone could build to refute the theorem. This
is the rule of method under
{ref "other-findings"}[The other findings].

Each of the five is shown below: first its Lean definition, then its
docstring. They come in the order of the list above. They are shown
whole because these are the conditions a reader has to judge.

Other parts take conditions of their own:

- Exchange takes conditions about trades rather than stocks. They are
  given in full under *Exchange*.
- Time preference takes its own too, about dated ends. They are given
  in full under *Time preference*.
- The regression theorem's are about a record of exchanges. They are
  given in full under *The regression theorem*.
- The interest theorems' are about sums of money and a loan. They are
  given in full under *Interest*. Some of the interest theorems take
  interchangeability of units too. They take it of his plan for a
  stock of future money (`futurePlan.Homogeneous`).

{docstring Apodictic.Stock.OneMore}

{docstring Apodictic.ActionFrame.IndependentUses}

{docstring Apodictic.AllocationPlan.Homogeneous}

{docstring Apodictic.Stock.ComparableServiceable}

{docstring Apodictic.Stock.NoNewUses}

# The theorems
%%%
tag := "theorems"
%%%


Rothbard's route is one of the two routes to the law (see
{ref "result"}[The Result]). On it the derivation has three steps:

- Served over unserved (`served_over_unserved`). Every end the man
  would serve with a set of his horses is preferred to every end a
  horse could serve that he would leave unserved with that set.
- Urgency (`urgency_principle`). Take a horse away. Every end he
  would still serve is preferred to every end he would give up.
- The law of marginal utility. It comes in two forms: along a chain
  of named horses (`marginal_utility_chain`), and by the size of the
  supply (`marginal_utility`).

Only the first step does real work. Its proof is the only one that
applies swap dominance (`SwapDominant`) and independence of uses,
for one man at one time (`IndependentUses agent time`). Both are
explained below. The later steps take both as hypotheses, only to
hand them to the step before.
Urgency is one application of the first step. The chain form is one
application of urgency. The size form adds one thing first:
interchangeability of units (`plan.Homogeneous`). It says any two
sets of his horses of the same size would serve the same ends. After
that, the size form too is urgency again.

Start with Rothbard's six horses, set out under
{ref "horses"}[The horses]. There his ten ends are numbered by rank,
in order of importance (pp. 25–26). With six horses the man serves ends
1–6. Ends 7–10 remain unsatisfied. A bundle is a set of ends. Take
the bundle he serves, `{1,2,3,4,5,6}`. The claim (`SwapDominant`) says
the following. Swap any served end for any unserved end a horse could have
served. Then he prefers what he would have had to what the swap leaves
him. So `{1,2,3,4,5,6}` beats `{1,2,3,4,5,7}`. It also beats
`{1,2,3,4,5,8}`. And it beats `{2,3,4,5,6,7}` if end 1 is the one
swapped out. Any single swap loses.

That claim is about bundles. The law is about single ends. Rothbard's
case ranks pleasure riding below leading a wagon, "the more important
duty (to him)" (p. 27). Pleasure riding is end 6. Rothbard gives
leading a wagon no number. The point is that the law ranks one end
against another, not one bundle against another. To pass from bundles
to ends takes one more condition. Take two bundles that differ in
exactly one place. A preference between them is then a preference
between the two ends where they differ. That condition is independence
of uses (`IndependentUses agent time`). It is ours rather than
Rothbard's. He ranks ends against each other directly. He reads their
ranking off his value scale (Figure 3, pp. 25–26). He takes that
ranking as given. The passages quoted under
{ref "horses"}[The horses] never compare bundles at all. We need the
condition because we make a claim about bundles where he makes one
fused claim. The condition fails where uses are complementary: where
one end is worth having only alongside another. Each step of the
derivation below carries the condition as a hypothesis. So where it fails, the law is
silent. It says nothing there, rather than something false.

Add that condition, and the conclusion is served over unserved
(`served_over_unserved`). Take any set of his horses (a sub-stock).
Every end he would serve with it is preferred to every end a horse
could serve that he would leave unserved with it. That is already
more than Rothbard says. The conclusion does
not care whether the unserved end is the one the next horse would have
reached. End 6 beats end 7. It beats end 10 just as squarely.

{docstring Apodictic.served_over_unserved}

Urgency is that ranking, restricted to the end he loses. Take a horse
away. The end he gives up is one he would have served with six and
does not serve with five. So it is an unserved end at the smaller
stock. Served-over-unserved has already ranked it below everything
still served. Rothbard's sentence on losing a horse (p. 25, quoted
under {ref "horses"}[The horses]) says exactly that and nothing more.
The larger stock is exactly one horse larger
(`stock.OneMore fewer more`). The proof uses only part of that: the
smaller stock lies inside the larger, which lies inside the stock. So
the smaller stock is on hand. That the larger has exactly one horse
more is not used. The linter cannot flag that, because it judges each
hypothesis whole (see {ref "manifest"}[The manifest]).

{docstring Apodictic.urgency_principle}

The law is urgency again, said of the ends a unit adds. These are the
ends served with the larger stock and not with the smaller. That is
Rothbard's own definition of the marginal utility of a supply.

{docstring Apodictic.marginalEnds}

Along a chain of named horses, take three sets of them: `small`
inside `medium` inside `large`, each one horse more than the last. So
there are two one-horse steps: `small` to `medium`, then `medium` to
`large`. Apply urgency at the second of them. What the sixth horse
adds is less urgent than what the fifth added. That is because what
the fifth added is still being served when he has five, and what the
sixth adds is not. That the first of the two is a one-horse step
(`stock.OneMore small medium`) is not used. Interchangeability
of units (`plan.Homogeneous`) is not needed either, because the chain names
which horses.

{docstring Apodictic.marginal_utility_chain}

Said by the size of the supply, the law compares what a fifth horse
adds with what a sixth adds. The two one-horse steps need not share a
horse. The fifth runs from `belowSmaller` to `smaller`, a set of five.
The sixth runs from `belowLarger`, a set of five that need not be
the same one, to `larger`.
Interchangeability of units (`plan.Homogeneous`) is used exactly once:
to say that `smaller` and `belowLarger` would serve the same ends.
After that, the argument is urgency over again.

{docstring Apodictic.marginal_utility}

One result here is not a step in the derivation. The claim
(`SwapDominant`) is made about one plan: the man's rule for which ends
he would serve with each set of his horses. It is not made about every
plan shaped like it. That rule of method is under
{ref "other-findings"}[The other findings]. A claim made of one plan
says nothing about other plans. So it does not say that his plan is
the only one that satisfies swap dominance.
A narrow piece of that is proved instead (`no_rival_swap_dominant`).
It is not uniqueness. It takes asymmetry of preference
(`AsymmetricPreference`): if he prefers one bundle to another, he does
not prefer the second to the first. Then no rival plan that is one
swap from his, at some set of horses, also satisfies swap dominance.
Three earlier parts cite this theorem, so it is shown here:
{ref "other-findings"}[The other findings], {ref "claims"}[The claims]
and {ref "conditions"}[The conditions]. The last uses it to show that,
given asymmetry, a claim about every plan the man might have can be
refuted.

{docstring Apodictic.no_rival_swap_dominant}

# The manifest
%%%
tag := "manifest"
%%%


Terms such as library, signature, claim, condition, linter and
vocabulary are explained under {ref "result"}[The Result].

This part prints the manifest of the law of marginal utility, in its
size-based form (`marginal_utility`, under
{ref "theorems"}[The theorems]). Everything that theorem carries is
here, in one place. Nothing outside this list is assumed. The list is
not compiled by reading the source. Nor does it rest on a copy of a
command's output. The command (`#manifest`) itself runs each time this
page is built. The page's source also holds a copy of what it prints.
The build checks that the two match. So what follows is what the
command printed.

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

Read it by kind. The sort is what the audit turns on. If the claim is
false, praxeology has asserted something false, and the law loses its
proof on this route. Where a condition does not hold, the law says
nothing there. It is silent, not wrong. Telling which of the two gave
way in a particular case is what the audit is for (see
{ref "finding"}[The finding]).

The printed manifest has five headed lists, then the logical
background. Each line in the first four lists is a binder: one thing the statement takes as an argument. The four
are the praxeological claims, the situational conditions, the
conditions on the data, and the vocabulary (what the claims are
about). The fifth lists fields, not binders. The bullets below take the
lists in turn.

- The one *praxeological claim* is swap dominance (`SwapDominant`,
  under {ref "claims"}[The claims]). It is a premise meant to hold of
  all action, not only in some situations. On this route the law is
  derived from it.
- The *situational conditions* are what an Austrian points at to say
  the law did not apply here. The size form compares two one-unit
  steps (see {ref "theorems"}[The theorems]). The first runs from a
  set of units `belowSmaller` to a set `smaller`, of `n` units. The
  second runs from `belowLarger` to `larger`, of `n + 1`. Three of the
  conditions listed are among the five set out under
  {ref "conditions"}[The conditions]: independence of uses
  (`IndependentUses agent time`), interchangeability of units
  (`plan.Homogeneous`) and one more unit (`stock.OneMore`). One more
  unit appears twice, once for each step (`stepToSmaller`,
  `stepToLarger`). The other two lines (`smallerSize`, `largerSize`)
  are not among the five. They are bookkeeping. They fix which two
  supplies are being compared: one of `n` units, one of `n + 1`. They
  are printed under this heading because the command puts there every
  hypothesis that is neither a claim nor a condition on the data.
- The *condition on the data* (`[DecidableEq praxis.End]`) says only
  that two ends can be told apart: for any two ends, whether they are
  the same end can be decided.
- The *conditions carried by the vocabulary* are not binders at all.
  They are fields of the structures the theorem takes as arguments:
  the stock (`stock.unitsAlike`) and the plan
  (`plan.servesOnlyWhatItCan`). So whoever supplies a stock and a plan
  has already discharged them. They are preconditions of using the law
  in every sense that matters. But they do not show in the signature.
  So they are where an encoding could hide an assumption. `#manifest`
  prints them, so these two are not hidden. They are set out again
  under {ref "vocabulary"}[The vocabulary].

The line headed _logical background_ is Lean's own: the axioms the
theorem depends on. `propext` and `Quot.sound` arrive with ordinary
mathematics. A proof that uses mathlib's finite sets brings both. So
does one that uses extensionality for sets. Neither axiom says
anything about economics (see {ref "result"}[The Result]).
`Classical.choice` is different, and it is absent. It is the axiom
behind classical logic. With it, every question counts as having a
yes-or-no answer, whether or not anything settles it. No proof here
fills a gap that way.

The proofs do split into cases. But they split only on whether two
ends are the same end. A case split needs a yes-or-no answer. Without
`Classical.choice`, the logic does not supply one in general. So this
one answer is asked for in the statement, as the condition on the data
(`[DecidableEq praxis.End]`). Had a proof used `Classical.choice`
instead, the statement would not show it. The axiom would appear only
on the logical background line, with nothing to say what it decided.

The size form needs interchangeability of units (`plan.Homogeneous`)
for one thing. It says that `smaller` and `belowLarger`, two sets of
`n` units, would serve the same ends. The law has a second form, the
chain form (`marginal_utility_chain`, under
{ref "theorems"}[The theorems]). It names which units are compared:
`small` inside `medium` inside `large`. Its two steps share a set,
`medium`. So it needs no interchangeability of units, and no sizes.
Its manifest has the same claim and the same condition on the data.
Its situational conditions are independence of uses and two
one-more-unit steps (`_firstStep`, `secondStep`). The `_` mark is
explained below. The urgency principle (`urgency_principle`, under
{ref "theorems"}[The theorems]) says this. Take a unit away. Every end
he would still serve is preferred to every end he would give up. Its
one step runs from a set `fewer` to a set `more`
(`stock.OneMore fewer more`): `more` holds `fewer` and one unit
besides, and lies inside the stock. It carries the same claim and the same
kinds of condition as the chain form, with that one step in place of
two. The chain form is worth printing too, because of one line in it:

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

`#manifest` derives both manifests from the theorem itself. It walks
the signature and sorts every binder by kind. Then it reads one level
into the vocabulary. There it reports the fields of the library's
structures that are statements (in Lean, fields of type `Prop`), as
against data such as a set of units. It decides that a binder is a
praxeological claim by the name its type is built on: `SwapDominant`
in `SwapDominant plan`. If that name is declared in the file
`Praxeology.lean`, the binder is a claim. That is the project's own
rule: every claim is a structure in `Praxeology.lean`. The command asks
it of the compiler rather than of a maintainer. So a claim declared in
the wrong place shows up as a situational condition. That is the
mistake worth catching.

What `#manifest` will not do is sort what it finds one level down.
Whether a carried condition could fail in a real situation is a
judgement about the world. The command reads only the condition's
statement in Lean. So it cannot make that judgement. The two carried
conditions (`stock.unitsAlike`, `plan.servesOnlyWhatItCan`) are sorted
by hand instead, under {ref "vocabulary"}[The vocabulary]. That
sorting is not checked by the machine. Nor is the list of part-used
hypotheses below, which comes from reading the proofs. The lists
themselves are checked. The compiler prints them when this document is
built. The build compares each printed list with the copy in this
page's source. If the two differ, the build fails. So this page cannot
show a list the theorem does not have.

The lists show what each theorem takes. The linter checks that each
binder does work (see {ref "claims"}[The claims]). Three things limit
how much that settles. Each is real.

- The linter is never switched off here. But switching it off is
  possible. So keeping it on is our practice, not something the
  machine guarantees.
- The linter can also be silenced one binder at a time, by prefixing a
  hypothesis with `_`. Doing that is how we record that the hypothesis
  does nothing. `marginal_utility_chain` carries one such binder,
  `_firstStep` (`stock.OneMore small medium`). That it does nothing is
  itself a finding. Each hypothesis that does no work is recorded as
  one: the statement asks for more than the proof needs. This one
  shows that the chain form needs nothing of how `small` stands
  to `medium`: not that the first step adds one unit, nor even that
  `small` lies inside `medium` (see {ref "theorems"}[The theorems]).
- The linter judges each binder whole. So it cannot see a hypothesis
  only part of which is used. Both marginal-utility theorems have such
  hypotheses. They are listed below.

`#manifest` does nothing about the first limit: it does not run the
linter. It closes the second limit. In the chain form's manifest
above, the line for `_firstStep` ends with the mark
`-- listed, does no work`. So the binder is listed, and marked, exactly
where the linter has gone quiet. That is the line the chain form was
printed for.

`#manifest` does not close the third limit. A part-used hypothesis
looks whole to both. Reading the two proofs finds three:

- Each form's conclusion begins "for every end marginal at the first
  step, …". So the conclusion carries a hypothesis of its own: that
  the end is marginal there (`marginalEnds`). (The paragraph after
  this list says more on binders in a conclusion.) Marginal means
  served at the step's larger set, and not served at its smaller one.
  Only the first half is used. In the chain form the first step is
  from `small` to `medium`. The conclusion still speaks of the ends
  that step adds, though `_firstStep`, the hypothesis that it is a
  one-unit step, does no work. The proof names the unused half
  `_notNeeded`. That name is inside the proof, not in the statement.
  So neither the linter nor `#manifest` shows it.
- The chain form's second step (`secondStep`) is handed to the urgency
  principle. That proof uses only that the smaller supply is on hand:
  it lies inside the larger, which lies inside the stock. That the
  larger has exactly one unit more is not used.
- The size form's first step (`stepToSmaller`), from `belowSmaller`
  to `smaller`, is used only for this: `smaller` lies inside the stock. That `belowSmaller` lies inside
  `smaller` is not used. Nor is it used that the step adds one unit.

And `#manifest` brings a limit of its own. Lean draws no line between
a signature and a conclusion. A conclusion of the form "for every end
in this set, …" (`∀ x ∈ s, …`) binds things too. It binds the end, and
a hypothesis that the end is in the set. Lean gives that hypothesis no
name of its own: it is an anonymous binder. The command takes the
first anonymous binder, other than a condition on the data, to begin
the conclusion. It cuts there, and reports how many binders it
dropped. But a conclusion binder the author named, before that cut, is
still listed under vocabulary. In the two manifests above, `atSmaller`
and `addedFirst` are such binders: each is the first end the
conclusion speaks of. So is `least`, in the manifest under
{ref "ladder-history"}[The ladder as a history]. They are binders, so
they are printed under the vocabulary heading, "what the claims are
about". But no claim is about them. When the command drops any
binders, the manifest ends with a line in parentheses saying how many.
When it drops none, there is no such line. Both manifests above end
with one. The count does not say where the conclusion begins: a named
binder of the conclusion can sit before the cut, as here. So where
that line appears, read the statement too.

So the guarantee is narrower than "nothing here is idle", that is,
"every hypothesis does work in the proof". With the linter on, it is
this: no hypothesis the signature lists is wholly idle, unless its
name starts with `_`. A hypothesis can still be partly idle, as the
three above are. The statement does not say so. Neither the linter nor
`#manifest` finds such a case. Reading the proofs does.

# Mises's route
%%%
file := "Mises-route"
tag := "mises-route"
%%%

Terms such as library, docstring, signature, claim, condition, linter
and frame are explained under {ref "result"}[The Result].

Rothbard's is not the only derivation the tradition offers. Mises
reaches the same law in *Human Action* (ch. VII, §1). His argument has
a wholly different shape. The library carries his route as a second
target. It is built in a module that cannot see Rothbard's theorems at
all. So whatever his argument spends has to be stated there, and it
shows on the signature. This part asks what his argument spends. A
proof that could reach for Rothbard's lemmas would have assumed the
answer to that question.

His statement of the law:

> If the supply available increases from n–1 units to n units, the
  increment can be employed only for the removal of a want which is
  less urgent or less painful than the least urgent or least painful
  among all those wants which could be removed by means of the supply
  n–1.

This statement is called his ladder here (`Mises.LadderHolds`). His
wording differs from Rothbard's in two ways:

- His ladder runs upward, from n–1 to n. Rothbard's example runs
  downward: he takes a horse away, six horses to five (see
  {ref "horses"}[The horses]).
- His ladder singles out a least urgent want
  (`Mises.LeastUrgentServed`). Rothbard's law names no least want. It
  compares what a fifth horse adds with what a sixth adds (see
  {ref "theorems"}[The theorems]).

Mises's statement is read here as Rothbard's is read. Two supplies are
held up against each other at one time. The reason is that Mises's
own definition has that shape. The marginal employment
(`Mises.marginalEmployment`) is the one a man makes at n units "but
would not make if, other things being equal, his supply were only n–1
units". Mises prefaces that definition with a remark: establishing it
does not transcend praxeological reasoning. The remark returns at the
end of this part. On another reading, the ladder is a history of
acquisitions. That reading is a separate target, set out under *The
ladder as a history*.

The docstrings below speak of a few things from the vocabulary (see
{ref "vocabulary"}[The vocabulary]):

- A sub-stock is a set of units cut from the man's stock (see
  {ref "conditions"}[The conditions]). Each supply compared here is
  one.
- The plan (`AllocationPlan`): for any sub-stock, which wants he would
  serve with exactly those units. It is settled in advance.
- The preference (`Prefers`): his ranking of one bundle of wants above
  another. A bundle is a set of wants. Nothing more is built into the
  ranking. The same ranking of single wants is `PrefersEnd`. One want
  is more urgent than another when he prefers it in that ranking.

{docstring Apodictic.Mises.marginalEmployment}

{docstring Apodictic.Mises.LeastUrgentServed}

{docstring Apodictic.Mises.LadderHolds}

*His conclusion is Rothbard's.* Before asking what Mises's argument
spends, ask whether it has to spend anything. Rothbard's premise is
swap dominance (`SwapDominant`, under {ref "claims"}[The claims]).
Take any sub-stock. Take one want the plan would serve with that
sub-stock, and one the good can serve that the plan would leave
unserved. Swap the second in for the first. Then the man prefers what
the plan would serve to what the swap leaves him. Whether
Rothbard may assume this at all is the warrant problem, set out under {ref "finding"}[The finding]. Add
independence of uses (`IndependentUses`, under
{ref "conditions"}[The conditions]). Does the ladder
(`Mises.LadderHolds`) follow outright from these two? It does. So his
conclusion needs nothing beyond Rothbard's premise and independence of
uses. The docstrings below call this check the control. It comes back
positive: the ladder follows. The proof is a few lines. Two things
fall out of it:

- The upward direction is narration. The ladder's statement holds two
  supplies, `fewer` and `more`, at one time. Nothing in it runs upward
  or downward.
- The least-urgent qualifier does no work at all. The proof consumes
  only that the want was served at the smaller supply. The machine can
  show as much, because the same conclusion goes through for every
  want served there, not only the least urgent.

{docstring Apodictic.Mises.ladder_for_every_served}

{docstring Apodictic.Mises.ladder_holds}

The marginal employment (`Mises.marginalEmployment`), meanwhile, is
Rothbard's marginal ends (`marginalEnds`) under another name. It is
the same set, by definition. So there is one law on the table, not
two. What differs between the authors is only the argument for it.

{docstring Apodictic.Contrast.marginalEmployment_eq_marginalEnds}

*His argument is a dilemma.* Mises does not assert an ordering
premise the way Rothbard does. He holds that the law "is already
implied in the category of action". He argues it so:

> There are only two alternatives. Either there are or there are not
  intermediate stages between the felt uneasiness which impels a man
  to act and the state in which there can no longer be any action …
  In the second case there could be only one action; as soon as this
  action is consummated, a state would be reached in which no further
  action is possible. This is manifestly incompatible with our
  assumption that there is action; this case no longer implies the
  general conditions presupposed in the category of action. Only the
  first case remains.

The dilemma is encoded as it stands. The second horn is read through
its stated consequence: there could be only one action
(`Mises.AtMostOneAction`). It is not read through an invented measure
of how much uneasiness remains. That keeps the vocabulary as it was.
Two small frames then check the argument's two steps, one frame for
each step.

First, the refutation of the second horn. Mises says one action
followed by a terminal state is incompatible with "our assumption that
there is action". It is not. Take a frame that admits exactly one
action (`Model.Solitary`). Both of these hold in it:

- There is action (`Mises.ActionOccurs`).
- There is at most one action (`Mises.AtMostOneAction`). That is the
  second horn.

So the two are not incompatible. What his step needs is that action is
plural: that two distinct actions occur (`Mises.ActionRecurs`). The
bare statement that there is action (`Mises.ActionOccurs`) does not
deliver plurality. That statement is what the tradition calls the
axiom of action, in the only form the tradition states it: there is
action. The library names it as a definition and asserts it nowhere.
This is the first time the library has put it to any work. It was too
weak for the job.

{docstring Apodictic.Model.existence_does_not_refute_second_horn}

Second, grant him the horn. Let action be plural, so the dilemma is
won. The ladder still does not follow. Take a frame with three
features:

- It has two actions. So action is plural, and that is everything the
  dilemma establishes.
- Its preference is asymmetric and not empty. Asymmetric means: if he
  prefers one bundle of wants to another, he does not prefer the second
  to the first (`AsymmetricPreference`, under
  {ref "claims"}[The claims]). The frame satisfies that claim too.
  Not empty means some want really is preferred to another. With
  nothing preferred, every ranking the ladder asks for would fail at
  once, and the failure would show nothing.
- With no units, its plan would serve the less urgent want. Only with
  one unit would it serve the more urgent one too. That is what breaks
  the law.

That frame meets everything the dilemma establishes. And it breaks the
law.

{docstring Apodictic.Model.recurs_does_not_deliver_ladder}

So the dilemma does not supply the premise the law needs. What carries
Mises from it to the law is a single sentence. In his text it comes
straight after this one: "Thus the law of marginal utility is already
implied in the category of action." He offers it as though it added
nothing: "It is nothing else than the reverse of the statement that
what satisfies more is preferred to what gives smaller satisfaction."
That second sentence is where his premise for the law lives. It is
reconstructed below as `ServedInOrder`. The sentence is unargued.

*His premise, reconstructed.* There is a tempting reading of that
sentence. It adds a scale of satisfaction to the vocabulary. The scale
would be a second ordering, on states, by how much uneasiness each
removes. That reading was refused, for three reasons:

- It would enlarge the ontology on one sentence's authority.
- It invites cardinal degrees through the back door: how much one
  state satisfies, as an amount. The ranking here attaches no numbers
  (see {ref "horses"}[The horses]).
- A satisfaction scale would still have to be connected to which want
  a unit serves. That connection is the premise all over again.

The reading used instead is the most generous one the existing
vocabulary allows. The agent serves in order of urgency
(`ServedInOrder`). Take any sub-stock on hand. Suppose the good can
serve a want, and that want is more urgent than one the plan would
serve with that sub-stock. Then the plan would serve it too, with the
same sub-stock. That is a praxeological claim. Like Rothbard's, it is
subjunctive throughout. It is the second under
{ref "claims"}[The claims].

One thing more is needed. Serving in order shows only this: the want
a unit adds is not more urgent than any want already served at the
smaller supply. The law says it is less urgent. To pass from the one
to the other, the two wants must be ranked one way or the other. The
route takes this as a condition, not a claim. The condition says that
every pair of wants the good can serve is ranked, one way or the other
(`stock.ComparableServiceable`). Where a pair is not, the theorem is
silent. This condition is the fourth under
{ref "conditions"}[The conditions]. It is the one Rothbard's route
never asks for.

{docstring Apodictic.Mises.ladder_from_order}

The theorem's manifest is printed by the same command as Rothbard's:

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

Hold it against the manifest of `marginal_utility`, printed under
{ref "manifest"}[The manifest]. These are gone:

- Swap dominance (`SwapDominant`).
- Independence of uses (`IndependentUses agent time`).
- The condition on the data (`DecidableEq praxis.End`).
- The one-unit steps (`stock.OneMore`), as hypotheses. They sit inside
  the ladder's statement (`Mises.LadderHolds`) instead. It speaks of
  every pair of sub-stocks one unit apart.
- Interchangeability of units (`plan.Homogeneous`), and the two sizes
  (`smallerSize`, `largerSize`). Mises's ladder compares within one
  step: the added want against a want served at the same smaller
  supply. So it never needs two sub-stocks of one size to serve the
  same ends. Rothbard's chain form (`marginal_utility_chain`, under
  {ref "theorems"}[The theorems]) states the law along a chain of named
  units. It lacks interchangeability and the sizes too.

In their place are one claim (`ServedInOrder`) and one condition
(`stock.ComparableServiceable`). The Rothbard route carries neither.
Two things are the same in both manifests. The conditions carried by
the vocabulary are the same two (`stock.unitsAlike`,
`plan.servesOnlyWhatItCan`). The logical background is the same,
`[propext, Quot.sound]` (see {ref "manifest"}[The manifest]). The
comparison of the two manifests is what the second target was for. It
is not a verdict on one reconstruction. It is a trade between
two, computed from the signatures rather than argued.

*The two premise sets, related.* Are the routes independent, then?
Not quite. The relation runs one way. Grant three things:

- Rothbard's premise (`SwapDominant`).
- Independence of uses (`IndependentUses agent time`).
- Asymmetry of preference (`AsymmetricPreference`).

Then the agent serves in order of urgency (`ServedInOrder`).
These three entail Mises's bridge. Asymmetry is the third
claim under *The claims*. The theorem below spends it, as do the
rival-plan theorem (`no_rival_swap_dominant`) and four theorems under
*Interest*.
Mises states asymmetry, as a law of thought (*Human Action*, ch. II,
§2), so its status is explicit-in-tradition.

The docstring below says the proof's case split needs no classical
logic. Why the library avoids classical logic is under
{ref "manifest"}[The manifest].

{docstring Apodictic.Contrast.rothbard_entails_servedInOrder}

The converse fails. Serving in order (`ServedInOrder`) compares single
wants. Swap dominance (`SwapDominant`) compares bundles: what the plan
would serve, against the same bundle with one swap made. A frame can
rank wants and serve them in order. It can still be too coarse to rank
those bundles. Then serving in order holds where swap dominance does
not.

{docstring Apodictic.Model.servedInOrder_not_entail_swapDominant}

So on the allocation, Mises's premise is strictly weaker than swap
dominance taken with independence of uses and asymmetry. Still,
neither premise set contains the other. The reason is that his route pays
for the weaker premise with comparability of wants
(`stock.ComparableServiceable`). Rothbard's route never needs it. Mises
asks less of the agent's plan and more of the agent's value scale.
Comparability is a condition, not a claim. So the price is paid in
situations: where comparability fails, Mises's route is silent. There
are agents for whom Rothbard's premise holds and Mises's route does
not apply. The gap is narrow. Why it is narrow is itself a small
finding. Swap dominance, with independence of uses (`IndependentUses`),
already ranks each served want against each unserved one the good
could reach (`served_over_unserved`, under
{ref "theorems"}[The theorems]). So every pair that some sub-stock
splits, one want served there and the other not, is already ranked.
Comparability can then fail only for a pair that no sub-stock splits:
at every sub-stock, the plan serves both or neither. That is why the
gap is narrow.

{docstring Apodictic.Model.rothbard_premise_holds_where_mises_is_silent}

*Where this leaves the question.* {ref "finding"}[The finding] left
one question. May praxeology help itself to a standing plan? A
standing plan is settled in advance. It answers for every set of the
man's units at once, and no act of his settles it. Rothbard's rule is
that "value scales do not exist in a void apart from the concrete
choices of action" (p. 33). The plan is a scale of the kind that rule
denies. That is the case made under *The finding*.

Mises's route does not escape that question. It meets it in another
form. His premise is as counterfactual as Rothbard's. It says what the
agent would serve at every smaller supply. And Mises restricts value
scales exactly as Rothbard does, three chapters earlier: "These scales
have no independent existence apart from the actual behavior of
individuals" (ch. IV, §2). So the warrant problem is Mises's too.

The two authors meet it differently:

- Rothbard exempts the law by name, on the page that states his rule.
  No one can predict with certainty the course of a man's choices, he
  says, "except that they will follow the law of marginal utility,
  which was deduced from the axiom of action". That clause is what
  lets him hand the man a standing plan. The law is then proved from
  that plan. So his warrant is circular (see *The finding*).
- Mises instead simply announces that the counterfactual costs
  nothing: "We do not transcend the sphere of praxeological reasoning
  in establishing the following definition". The definition is the
  marginal employment, quoted near the top of this part. It is
  counterfactual: the employment he makes at n units but would not
  make if, other things being equal, his supply were only n–1 units.

Neither warrants the premise. That is as far as this part goes.

# The circle
%%%
file := "The-circle"
tag := "circle"
%%%

Terms such as library, claim and condition are explained under
{ref "result"}[The Result].

Two derivations of one law, the law of marginal utility, have now
been rebuilt. Both give way at the same place. The pieces are under
{ref "finding"}[The finding] and {ref "mises-route"}[Mises's route].
This part sets them side by side. It says plainly what the audit
establishes about them, and what it does not. It is short, because
most of the work is already done.

Two words recur below. A sub-stock is a set of units cut from the
man's stock (see {ref "conditions"}[The conditions]). The plan
(`AllocationPlan`) says, for each sub-stock, which wants he would
serve with exactly those units (see {ref "vocabulary"}[The vocabulary]).

*Both deny needing what both use.* Here are the two authors' rules
about value scales:

- Rothbard: value scales "do not exist in a void apart from the
  concrete choices of action", and "there is no need for him to
  formulate hypothetical value scales" (p. 33).
- Mises: the scales have "no independent existence apart from the
  actual behavior of individuals" (ch. IV, §2).

They state the same rule. A man's ranking shows up in what he does,
and nowhere else.

Then each author derives the law from a premise that rule forbids.
The premises come first. Why the rule forbids them comes after.


- Rothbard's premise (`SwapDominant`) ranks the wants the man's plan
  would serve. It does so for every sub-stock.
- Mises's premise (`ServedInOrder`) is written over exactly the same
  sub-stocks. His route asks less of the man's plan and more of his
  ranking. The more is a condition: every pair of wants the good can
  serve is ranked, one way or the other (`stock.ComparableServiceable`;
  see {ref "mises-route"}[Mises's route]).

So the two premises (`SwapDominant`, `ServedInOrder`) range over the
same region: every subset of the stock in hand. Neither reaches past
it. They do speak of supplies he does not hold: the sub-stocks smaller
than his stock. The obvious complaint is that this is the trouble.
{ref "finding"}[The finding] shows the complaint fails:

- Reasoning about such supplies is Rothbard's own practice.
- One-unit steps down, of the kind he takes, reach every sub-stock
  from the stock in hand.
- On p. 33, the line between what he allows and what he refuses is
  drawn around the stock in hand.

So how far the premises reach is not the trouble, on either route.

The trouble is what both premises are. Each is a claim about the plan.
The plan is a settled answer, held in advance, for every one of those
sub-stocks at once. It answers before any of the choosing. On the rule
above, a scale shows up choice by concrete choice, as each choice is
made (see *The finding*). So no act of his settles the plan. It is a scale that
stands apart from the concrete choices. Both rules deny such a scale.
The case is made for Rothbard under *The finding*, and for Mises under
*Mises's route*.

*What each then helps himself to.* Rothbard sees the difficulty. The
law says something about the man's choices before they are made. So
does the plan. On p. 33, the page that states his rule, he says no one
can predict with certainty the course of a man's choices, "except that
they will follow the law of marginal utility, which was deduced from
the axiom of action". That subordinate clause exempts the law from the
rule, by name. He attaches no argument. The circle runs like this:

- The clause says in advance what his choices will obey. The plan, too,
  says in advance what he would choose. So the clause is what lets him
  hand the man a standing plan: one settled in advance, for every
  sub-stock at once.
- The law is then proved from that plan.
- So the warrant for the premise is the law it is used to prove.

Mises does not see the difficulty, or does not say so. He sets down
his definition of the marginal employment (`Mises.marginalEmployment`).
It is the employment a man makes at n units "but would not make if,
other things being equal, his supply were only n–1 units". So it is
counterfactual: it turns on what he would do if his supply were
smaller. He prefaces the definition with a remark: "We do not
transcend the sphere of praxeological reasoning in establishing the
following definition" (ch. VII, §1). Rothbard reasons in a circle. Mises
declares. Neither gives the premise a warrant that stands apart from
the law it is used to prove.

*The weaker premise does not help.* Mises's premise
(`ServedInOrder`) is strictly weaker than two claims and a condition
taken together:

- Rothbard's premise (`SwapDominant`).
- Independence of uses (`IndependentUses`).
- Asymmetry of preference (`AsymmetricPreference`).

The three entail it (`Contrast.rothbard_entails_servedInOrder`). It
does not entail Rothbard's premise
(`Model.servedInOrder_not_entail_swapDominant`). Both theorems are
under *Mises's route*. A reader might hope that weakening it further reaches
something about actual choices alone. Here is the reason to expect
not. On both routes the law compares two supplies at one moment. The
man holds one of them. So whatever premise delivers the law at one
moment has to say something about the supply he does not hold. The
only thing that can be said about that supply is what he would do with
it. That is the counterfactual tense: what he would do, not what he
did. Weakening the premise changes how much it says in that tense. It
cannot change the tense.

That is a reason, not a result. Nothing here proves that no premise
about actual choices can reach the law. No one has tried to prove it.
What the audit has is two routes. Each rests on a standing
counterfactual that its author disowns.

A third reading drops the one moment. It speaks only of what the man
did. On it, he held the smaller supply at an earlier moment. It needs
no plan. It pays instead with conditions. One is that he learned no
new use for the good between the two moments (`earlier.NoNewUses
later`). The part called
{ref "ladder-history"}[The ladder as a history] sets it out.

*One shape, if you like.* What follows is a reading, not a finding.
These are the two defects the audit turned up in Rothbard:

- The circle, here.
- The inference about units: from his definition of a supply (p. 23)
  to a plan that cares only how many units the man has. It is set out
  under {ref "other-findings"}[The other findings].

The two have a common form. Each time, what is offered as a warrant
does not reach what it is offered for:

- The exemption is offered as the warrant for the standing plan. What
  it names is only the law.
- Rothbard's definition of a supply is offered as the warrant for a
  plan that does not care which units the man has, only how many
  (`plan.Homogeneous`). What it reaches is a fact about the units
  only: each is equally able to serve (`stock.unitsAlike`). A fact
  about the plan does not follow (`Model.unitsAlike_not_entail_homogeneous`;
  see *The finding*).

Is that common form one habit, or two coincidences? A proof assistant
cannot say. Mises's declaration fits the same form trivially, since it
reaches nothing.

*What is and is not established.* Established:

- Each derivation follows from its stated premise and conditions.
- Each premise is a claim about what the man would do.
- Each author restricts value scales to what the man does do.
- Neither author gives his premise a warrant that stands apart from
  the law.

Not established:

- That the law is false.
- That praxeology cannot have it.

One more fact sits beside the second. The third reading above has a
theorem (`Temporal.ladder_judged_earlier`). It proves the ladder read
as a history: each want the later allocation serves, and the earlier
did not, ranks below the least urgent want the earlier one served (see
{ref "ladder-history"}[The ladder as a history]). It rests on
acting in order (`ActsInOrder`), a claim about what the man actually
does, and on no plan. It also takes two conditions. So a ladder does
follow from a claim about action without a plan, but only on the
scale he ranked by before the stock grew. On
the later scale the ladder does not follow from acting in order
(`Model.later_judged_ladder_fails`). What it reaches, and what
it costs, is under *The ladder as a history*.

The audit began with a question. Is the certainty Mises claimed for
this law the certainty of a theorem? The answer is as narrow as the
two lists under *What is and is not established*. Each derivation is
as certain as its premise. The premises are the part nobody has
derived.

# The ladder as a history
%%%
file := "The-ladder-as-a-history"
tag := "ladder-history"
%%%

Terms such as library, claim and condition are explained under
{ref "result"}[The Result].

The library derives the law of marginal utility by two routes:
Rothbard's (see {ref "theorems"}[The theorems]) and Mises's (see
{ref "mises-route"}[Mises's route]). Mises states the law as a ladder,
from a supply of n–1 units to n. His sentence is quoted below. Both
routes read the ladder at one moment. Take Rothbard's man with six
horses. The law compares the six he holds with five he might have held
instead. He does not hold those five. So the comparison is with a
supply he does not hold.

Both routes get that comparison from a plan (`AllocationPlan`). A
sub-stock is a set of units cut from the man's stock. The plan says,
for each sub-stock, which wants he would serve with exactly those
units (see {ref "vocabulary"}[The vocabulary]).

There is another way to read the ladder. Rothbard tells it that way himself:
"suppose that the isolated individual successively finds one
horse, then a second, then a third" (p. 24). Mises's ladder runs in
the same direction, from n–1 units to n.

Read like that, the ladder is not about a plan at all. It is about two
things the man actually did:

- What he served when he held n–1 units.
- What he serves once he holds n.

No stock he does not hold comes into it. Unlike the plan, nothing here
says in advance what he would serve with each sub-stock of his stock.

The library carries this reading in a module of its own. The module
imports the claims. It imports neither route's theorems. So it cannot
borrow a result from either route. Whatever it spends shows on its
theorem's signature. Its objects are these:

- Two actual allocations (`Allocation`). Each records the wants he
  served with the stock he held at one moment.
- A supply that grew by one unit from one moment to the other
  (`Stock.Grows`).

Both definitions are under {ref "vocabulary"}[The vocabulary]. In the
Lean, the two stocks are named `earlier` and `later`. The two
allocations are named `before` (of `earlier`) and `after` (of
`later`).

In place of a plan, the reading spends acting in order
(`ActsInOrder`). It is the fourth claim under {ref "claims"}[The claims].
It is the only claim in the library that runs from what a man ranks to
what he actually does. Here is what it says. With the stock he holds
at one moment, he never serves a want while passing over one he
prefers to it and believes the good can serve.

*The question the reading forces.* Rothbard goes on: "When the second
horse is found, he will be put to work satisfying the most urgent of
the wants remaining. These wants, however, must be ranked lower than
the wants that the previous horse has satisfied." Ranked lower on
which scale? The man ranks at every moment he acts. He ranked when he
held one horse. He ranks again when he holds two. Rothbard's sentence
does not say which ranking it means. Neither does Mises's. A proof
assistant will not let that go unsaid. So the ladder
(`Temporal.Ladder`) takes as an argument the moment whose scale does
the ranking:

{docstring Apodictic.Temporal.Ladder}

The two answers come apart.

*Judged on the earlier scale, the ladder is a theorem*
(`Temporal.ladder_judged_earlier`). It is a short one. Read it as
acting in order restated about a want the next horse happens to serve.
Do not read it as a route to the law. The manifest below, and what is
missing from it, shows why.

Take Rothbard's horses. The man holds one horse at the earlier moment
and two at the later. The theorem's conclusion is about the earlier
scale, the one he ranked by when he held one horse. On that scale, the
least urgent want he served then ranks above any want he serves with
two horses and did not serve with one.

The theorem spends one claim and two conditions. Each can fail:

- He acted in order with one horse (`ActsInOrder before`). Rothbard says so:
  action "uses scarce means to satisfy the most urgent of the not yet
  satisfied wants" (p. 24). This fails if he served a want while
  passing over one he preferred to it and believed a horse could
  serve.
- At the earlier moment, any two wants a horse can serve were ranked
  one way or the other (`earlier.ComparableServiceable`). This fails if
  two of them were not ranked against each other at the earlier
  moment. Rothbard's story ranks the wants it names, but does not say
  every pair was ranked. The theorem adds it as a condition.
- He learned no new use for a horse between the two moments
  (`earlier.NoNewUses later`). This fails if, by the second horse, he
  believes a horse can serve a want he did not believe it could serve
  before. Rothbard's story does not say either way. The theorem adds it
  as a condition.

{docstring Apodictic.Temporal.ladder_judged_earlier}

```lean (name := manifestTemporal)
#manifest Temporal.ladder_judged_earlier
```
```leanOutput manifestTemporal
manifest of Apodictic.Temporal.ladder_judged_earlier

  praxeological claims:
    order : ActsInOrder before

  situational conditions:
    comparable : earlier.ComparableServiceable
    noNewUses : earlier.NoNewUses later

  vocabulary (what the claims are about):
    praxis : ActionFrame
    agent : praxis.Agent
    earlierTime : praxis.Time
    laterTime : praxis.Time
    earlier : Stock praxis agent earlierTime
    later : Stock praxis agent laterTime
    before : Allocation earlier
    after : Allocation later
    least : praxis.End

  conditions carried by the vocabulary (not binders: discharged by
  whoever supplies the argument):
    earlier.unitsAlike : ∀ unit ∈ earlier.units, ∀ (want : praxis.End), praxis.Believes agent earlierTime unit want ↔ want ∈ earlier.serves
    later.unitsAlike : ∀ unit ∈ later.units, ∀ (want : praxis.End), praxis.Believes agent laterTime unit want ↔ want ∈ later.serves
    before.servesOnlyWhatItCan : ∀ want ∈ before.served, want ∈ earlier.serves
    after.servesOnlyWhatItCan : ∀ want ∈ after.served, want ∈ later.serves

  logical background: [propext, Quot.sound]

  (4 trailing binders belong to the conclusion, not the signature)
```

Read what is not on it:

- The supply growing is not a hypothesis. Added as one, the linter
  refuses it as unused.
- Nothing about the later scale appears.
- Nothing about how the later allocation was chosen appears.
- Nothing about which moment came first appears. In the Lean,
  "earlier" and "later" are names only, of the two stocks and their
  times. The frame these theorems use (`ActionFrame`) puts no order on
  its times.

The first absence is why it is not a route to the law. Mises's law
speaks of an increment. This theorem never uses the supply's growth.
So nothing in it depends on a unit having been added.

One condition does span the two moments: no new uses
(`earlier.NoNewUses later`). Whatever the good is believed to serve
later, it was believed to serve earlier. He may stop believing in a
use. He may not start. The routes with a plan read at one moment, so
one scale ranks everything. Here what spans the moments is a one-way
condition on belief about the good, not the scale. Without the
condition, the new horse's want need not be among the wants a horse
was believed able to serve at the earlier moment. The theorem's other
two hypotheses speak only of those wants: acting in order
(`ActsInOrder before`) and comparability
(`earlier.ComparableServiceable`). The condition is under
{ref "conditions"}[The conditions] with the rest.

It is a short theorem, and it should be read as one. What it
says is about the earlier act. Whatever he passed over then ranked
below whatever he served then. The want the second horse later goes to
is simply one of the wants he passed over. The added unit is
narration.
On this reading, the ladder is acting in order, restated about a want
the next horse happens to serve.

*Judged on the later scale, it does not follow.* Grant, at both
moments, the one-moment claim and condition the earlier-scale theorem
used, and one claim more:

- He acts in order (`ActsInOrder before`, `ActsInOrder after`). This
  is a claim.
- The good's wants are comparable (`earlier.ComparableServiceable`,
  `later.ComparableServiceable`). This is a condition.
- Preference is asymmetric: he never prefers one bundle to another and
  the second to the first at the same moment (`AsymmetricPreference`).
  This is a claim, the third under {ref "claims"}[The claims]. The
  earlier-scale theorem does not need it.

Grant two things across the moments:

- The supply grew by one (`earlier.Grows later`).
- The good is believed able to serve the same wants at both moments
  (`later.serves = earlier.serves`). This is more than no new uses,
  which asks only that the wants the good is believed able to serve
  later be among those it was believed able to serve earlier.

Then ask for the ladder on the later scale
(`Temporal.LadderJudgedLaterFromOrder`):

{docstring Apodictic.Temporal.LadderJudgedLaterFromOrder}

{docstring Apodictic.Model.later_judged_ladder_fails}

The frame that refutes it is small. There are two moments and two
wants. He holds one horse, and then two. With one horse, he serves the
want most urgent then. With two, he serves both. By then the other
want has become the more urgent. Each act is in order on its own
scale. On the later scale, the want newly served with two horses
outranks the want served with one. Judged there, the ladder fails.

*What would close the gap, and why it is not assumed.* It would take a
relation between the man's scales at the two moments. The later scale
would rank what the earlier ranked, the same way. Call that constancy.
Both authors deny it. Mises: "value judgments are not immutable" (*Human Action*, ch. V,
§4). Rothbard's own actor changes his mind between moments, a few
pages before the horses: "the ranking on his preference scale shifts
to this order" (p. 18). So the history reading does not assume
constancy. It assumes it neither as a claim nor as a condition. Where
the reading would need it, the frame above shows what goes missing.

Rothbard, for his part, would not judge on the earlier scale at all.
When his man must give up one of six horses, "he deals only with his
presently available stock", in "disregard of past events" (p. 27).
Judged that way, the ladder is the one-moment law at the later time:
the supply he holds against one unit fewer. Both routes derive that
law from a premise about a plan (`SwapDominant`, `ServedInOrder`; see
{ref "circle"}[The circle]). So judging that way brings back the plan,
and the circle with it.

Constancy is not all they deny. They also deny something that bears
on the claim this reading does spend, acting in order (`ActsInOrder`).
Both hold that a scale of value exists only as it is read off what a
man does. So a scale and the act it was read from cannot disagree. The
passages are quoted in `ActsInOrder`'s docstring under
{ref "claims"}[The claims]. The library keeps the ranking apart from
the act. That way the claim can say something an act could
contradict. That is why the claim's status is our reconstruction and
not theirs.

*The trade.* The counterfactual routes need a plan that no act
exhibits. Both authors deny a scale that stands apart from the
concrete choices, and the plan is one (see {ref "circle"}[The circle]).
Judged on the later scale, the history needs a scale that no act can
show to have stayed put. Judged on the earlier scale, where it is a
theorem, it needs a man who learned no new use for the good between
the two acts (`earlier.NoNewUses later`). Neither author addresses that condition.
Nothing in the texts grants it, and nothing refuses it. So the two
routes pay in different coin:

- The counterfactual routes rest on something their authors refuse.
- The history route rests on something they never examined.

Reading the ladder as a history moves the cost. It does not remove it.

*What a failure would point at.* Suppose the ladder, read as a
history, fails of a real case. Its manifest says where to look.
Some conditions are built into its vocabulary: fields of the stocks
and allocations it takes, such as each allocation serving only wants
the good is believed able to serve. Whoever supplies a stock or an
allocation has already met them (see {ref "manifest"}[The manifest]).
Besides those, it names three places:

- The man did not act in order (`ActsInOrder before`).
- He learned a new use for the good between the moments
  (`earlier.NoNewUses later`).
- Two of the good's wants were never ranked against each other at the
  earlier moment (`earlier.ComparableServiceable`).

A scale that moved is not on the list. That is because no theorem on
this reading assumes it stayed put. Those three are where to look.

# Exchange
%%%
file := "Exchange"
%%%

Terms such as library, docstring, claim, condition, linter and frame
are explained under {ref "result"}[The Result].

The law of marginal utility is one target. Exchange is the second. It
was chosen for what it can diagnose. The tradition leans on few
conclusions more than this one: both parties to a voluntary exchange
benefit. Read as a statement about what each party expects when he
trades, it is hard to fault. Read as a statement about how the trade
turns out, it plainly misses some real trades. The buyer may have been
mistaken about what he bought. Or he may regret it. So there are two
questions. Which reading do Rothbard's words commit him to? And where
the second reading misses, which assumption fails?

Rothbard states the doctrine in one paragraph (*MES*, p. 85). The
paragraph says four things:

- Why people trade: "both people make it because they expect that it
  will benefit them; otherwise they would not have agreed to the
  exchange."
- When they can. The two goods must "have reverse valuations on the
  respective value scales of the two parties". That is, each ranks the
  other's good above his own. This must hold "before making the
  exchange".
- What they must know: "each of the parties knows of the existence of
  the other and the goods that he possesses."
- The result: "After the exchange is made, both A and B have shifted to
  a higher position on their respective value scales."

The paragraph also confines itself to "actions that are purely
voluntary".

*The bridge.* "Otherwise they would not have agreed" infers what a man
prefers from what he does. That is demonstrated preference
(`DemonstratedPreference`). Its docstring is given in full under *The
claims*. The law of marginal utility never needed it. Exchange cannot do
without it. Every exchange theorem below runs back from what was done to
what was preferred, and each one carries the bridge. Three things mark
how it is stated:

- It is stated of one trade, not of action in general.
- It ranks whole holdings. One is everything the man owns with one good.
  The other is everything he owns with the other good. That is what a
  trade chooses between.
- It counts each holding by what the man believes its goods can do. It
  takes his beliefs at the moment of trading.

*How goods count.* The third point above is how goods enter at all. Rothbard
sets the value scales out as a table. It has two columns, one per party.
The columns rank goods: A's column puts "(Good Y)" first and "Good X"
second. "Parentheses around the good indicate that the party does not
have it in his stock" (p. 85). The library ranks ends, not goods. So a good counts here for the
ends the man believes it can serve (`ActionFrame.ServedBy`). "A values
the typewriter above the vase" is read as "A prefers what he believes
the typewriter can do to what he believes the vase can do". No doctrine
of how goods take their value from ends is assumed.

But counting a good this way is a choice. It has two consequences:

- A good counts for every end he believes it could serve. It does not
  count only for the one it would be put to. The definition
  (`ActionFrame.ServedBy`) asks only what he believes a good can serve.
- Two goods that serve the same end count for it once.

Rothbard's case is single goods with separate uses. For those, counting
by goods and counting by ends agree. The substitutes condition below
(`Trade.KeptServesOtherEnds`) says that nothing he keeps is believed to
serve an end either traded good serves. Where the two counts part, it
is the one that fails. `Trade` and
`Exchange` leave out any condition no proof uses. Five such conditions
are listed after the theorems. The definitions:

{docstring Apodictic.ActionFrame.ServedBy}

{docstring Apodictic.Trade}

{docstring Apodictic.Exchange}

*Reverse valuations follow, given a claim and three conditions per party.* Take Rothbard's own case: "If
A has a vase and B a typewriter, if each knows of the other's asset, and
if A values the typewriter more highly, and B values the vase more
highly, there will be an exchange" (p. 86). Rothbard runs from the
valuations to the exchange. The theorem runs back, from the exchange to
the valuations. Say the exchange is made, and the claim and conditions
below hold.
The theorem (`MutualBenefit.reverse_valuations`) concludes the
following. A ranks the typewriter above the vase. B ranks the vase above
the typewriter. Each ranks on his own scale, by his own beliefs, at the
time of his trade. Put generally, each party ranks the good he got
above the good he gave:

{docstring Apodictic.MutualBenefit.reverse_valuations}

```lean (name := manifestExchange)
#manifest MutualBenefit.reverse_valuations
```
```leanOutput manifestExchange
manifest of Apodictic.MutualBenefit.reverse_valuations

  praxeological claims:
    demonstratedA : DemonstratedPreference exchange.first
    demonstratedB : DemonstratedPreference exchange.second

  situational conditions:
    voluntaryA : exchange.first.Voluntary
    voluntaryB : exchange.second.Voluntary
    separableA : exchange.first.SeparableFromRest
    separableB : exchange.second.SeparableFromRest
    uniqueA : exchange.first.KeptServesOtherEnds
    uniqueB : exchange.second.KeptServesOtherEnds

  vocabulary (what the claims are about):
    praxis : ActionFrame
    exchange : Exchange praxis

  conditions carried by the vocabulary (not binders: discharged by
  whoever supplies the argument):
    exchange.swap_gives : exchange.second.gets = exchange.first.gives
    exchange.swap_gets : exchange.second.gives = exchange.first.gets

  logical background: [propext, Quot.sound]
```

The manifest lists what the theorem takes, sorted by kind (see
{ref "manifest"}[The manifest]). Its last group is the conditions
carried by the vocabulary. It is taken up below. The rest is one claim and three
conditions per party. Rothbard's table shows none of the conditions.
Here they are for A. B's are the same, with the goods swapped. Each can
fail.

The claim is the bridge (`DemonstratedPreference`). It fails if A traded
against his own ranking at the time.

The first condition is that the trade was voluntary (`Trade.Voluntary`).
It fails if A handed over the vase under a threat. The bridge holds of a
robbery too. The victim prefers handing over his wallet to what refusing
would cost him. What it then shows is a ranking of his wallet against
the threat. It does not rank his wallet against anything he got. So a
trade records what refusing would have left the man with, alongside the
goods. A trade is voluntary when refusing would have left him with
exactly what he held before the trade. Rothbard
rests the inference on exactly this: "The only reason we know that A and
B benefit from an exchange is that they voluntarily make the exchange"
(p. 1239).

{docstring Apodictic.Trade.Voluntary}

The other two conditions are what it costs to talk about two goods at
all. The trade ranks whole holdings. The table ranks two goods. To get
from one to the other, the rest of what the man owns must stay out of
it. Rothbard's table says nothing of what else A owns. The theorem adds
two conditions for that. They fail in two opposite ways:

- A preference between the two holdings carries down to the two goods
  (`Trade.SeparableFromRest`). It fails for complements, goods that are
  worth more together. A left shoe is worth little without the right
  one.
- Nothing he keeps is believed to serve an end either traded good serves
  (`Trade.KeptServesOtherEnds`). It fails for substitutes. Take a man
  with two umbrellas who trades one away. He gives up nothing the other
  cannot do. So the trade shows no ranking of the umbrella at all.

Rothbard's case is "unique goods with a supply of one unit" (p. 86).
That phrase assumes the substitutes condition
(`Trade.KeptServesOtherEnds`). It does not touch complements. A unique
left shoe is still half a pair.

The first docstring below compares separability with independence of
uses (`IndependentUses`). That is a condition the law of marginal
utility carries, explained under {ref "conditions"}[The conditions].

{docstring Apodictic.Trade.SeparableFromRest}

{docstring Apodictic.Trade.KeptServesOtherEnds}

*What does no work.* Knowledge of the other party is a condition for a
trade to happen. Every theorem here starts from a trade that did happen.
So knowledge does no work. It is not among the theorems'
hypotheses, the claims and conditions a theorem takes. The
unused-argument linter reports any hypothesis no proof uses, and a
report fails the build. If knowledge were added as a hypothesis, the
linter would report it.

*"Shifted to a higher position" — on which scale?* The same question
came up under {ref "ladder-history"}[The ladder as a history]. Is the
position judged on the scale of the moment he acted, or on a later one?
Here too there are those two readings. The question is settled
differently here. The reading under *The ladder as a history* did not
assume a constant scale,
either as a claim or as a condition. Here constancy enters as a
condition, for one pair of holdings only. It enters because the
later-judged result needs it. Without it that result fails, as a model
below shows.

Judged on the scale and the beliefs of the moment of trading, Rothbard's
result is a theorem (`MutualBenefit.better_off_judged_at_trade`). It is
a short one: the bridge plus voluntariness. On that reading, "benefit"
is demonstrated preference in a voluntary trade, and nothing more.

{docstring Apodictic.MutualBenefit.better_off_judged_at_trade}

Judged afterwards, it is a second theorem
(`MutualBenefit.better_off_judged_later`). Take the vase and the
typewriter again. The conclusion is about A at some later moment. On his
later scale, he prefers his holding with the typewriter to his holding
with the vase. Both holdings are counted by what he then believes. The
theorem takes one claim and three conditions. Each can fail:

- The bridge (`DemonstratedPreference`). It fails if A traded against
  his own ranking at the time.
- The trade was voluntary (`Trade.Voluntary`). It fails if A handed over
  the vase under a threat.
- His beliefs about the goods hold (`Trade.BeliefsHold`). Later, every
  good in the trade is believed to serve exactly what it was believed to
  serve when the trade was made. It fails if A comes to believe the
  typewriter does nothing. Rothbard's paragraph does not say either way. The theorem
  adds it as a condition.
- His ranking of the two holdings holds (`Trade.RankingHolds`). It fails
  if A comes to want the vase back. Rothbard's paragraph does not say
  either way. The theorem adds it as a condition.

Judging afterwards needs the last two. Judging at the trade does without
them. Each answers to one way the later result fails. The beliefs
condition fails on a change of belief. The ranking condition fails on
regret. The theorem and its manifest come first, then the two
conditions:

{docstring Apodictic.MutualBenefit.better_off_judged_later}

```lean (name := manifestBenefit)
#manifest MutualBenefit.better_off_judged_later
```
```leanOutput manifestBenefit
manifest of Apodictic.MutualBenefit.better_off_judged_later

  praxeological claims:
    demonstrated : DemonstratedPreference trade

  situational conditions:
    voluntary : trade.Voluntary
    beliefsHold : trade.BeliefsHold later
    rankingHolds : trade.RankingHolds later

  vocabulary (what the claims are about):
    praxis : ActionFrame
    trade : Trade praxis
    later : praxis.Time

  logical background: [propext, Quot.sound]
```

{docstring Apodictic.Trade.BeliefsHold}

{docstring Apodictic.Trade.RankingHolds}

Both are needed. A small made-up model shows that each is. The model is
a frame, in the library's word. It is Rothbard's vase and typewriter, in two
variants:

- In one, A comes to believe the typewriter does nothing. His beliefs
  about it change. His ranking does not.
- In the other, A comes to want the vase back. His beliefs stay. His
  ranking turns.

In each, A's trade is voluntary. It demonstrates what the bridge says.
In neither is A better off by his later lights.

{docstring Apodictic.Model.later_without_beliefs_fails}

{docstring Apodictic.Model.later_without_ranking_fails}

There is a third variant, where nothing changes. In it, every claim and
condition of `reverse_valuations` and of `better_off_judged_later`
holds of both parties' trades. So both trades can be handed to both of
those theorems. That shows their conditions can all hold at once, so
neither theorem is vacuous. The docstrings call this non-vacuity:

{docstring Apodictic.Model.barter_reverse_valuations_applies}

{docstring Apodictic.Model.barter_better_off_later_applies}

*Fraud.* Rothbard would not count the defrauded buyer against him. For
him a deceived party has not traded voluntarily: "Since the exchange has
been made falsely, the actual form of which might not have been
contracted had the other party not been deceived, this is not an example
of voluntary exchange, but of one-sided theft" (p. 184). So his
"voluntary" does part of the work the beliefs condition
(`Trade.BeliefsHold`) does here. It is the part where someone else
changed what the buyer believed. Voluntariness here (`Trade.Voluntary`)
asks only what refusing would have cost. It cannot see deception. The
cut here is finer. Take a buyer who was deceived, and a buyer who was
simply mistaken. Both fail the beliefs condition (`Trade.BeliefsHold`).
Only the first is outside Rothbard's "voluntary". So only the second is
a case his paragraph covers. He is the mistaken buyer of the opening.
The opening's second reading, of how the trade turns out, misses him. Here the condition that fails for him has
a name: the beliefs condition (`Trade.BeliefsHold`).

*The carried conditions.* The first manifest lists two fields of the
exchange:

- What A gives, B gets.
- What B gives, A gets.

Neither says anything about the world. Suppose the good A hands over
were not the good B receives. Then there would be no exchange to speak
of. Whether a field says nothing about the world in this way is a
judgement. The Lean cannot make it. It is made here as it is for the fields of a stock and a plan, under
*The vocabulary* later in the document. The second manifest has no such
group. Nothing is built into a trade as defined. The conditions its
theorem needs are the named ones it lists.

Five conditions a reader might expect are in neither manifest:

- A and B are two people.
- The two trades are made at one moment.
- The good given is not also kept.
- The good received is not among the kept.
- Two different goods change hands.

None is a field of `Trade` or of `Exchange`, because no proof uses it.

Two people and one moment do no work. The reason is that
`reverse_valuations` applies a one-trade result
(`ranks_received_above_given`) to each side. (Each party ranks what he
got above what he gave.) All that ties the sides
together is the two fields of an exchange: what A gives, B gets, and
what B gives, A gets.

The next two are what makes `kept` the rest of a man's holding: neither
the good given nor the good received is among the kept. A good both
traded and kept is no trade in the ordinary sense. But a `Trade` does
not exclude it. The substitutes condition (`Trade.KeptServesOtherEnds`)
forbids a kept good to share any end with a traded good. So it excludes
the case, unless the good counted twice is believed to serve no end at
all. `reverse_valuations` carries that condition. The two `better_off`
theorems do not, and nothing in them excludes the case. So in them it
can arise two ways:

- The good given is also kept. Then they say only that he prefers his
  holding with the received good to his holding without it. The given
  good is in both holdings, so they show no ranking of it.
- The good received was already kept. Then they say only that he prefers
  his holding without the given good to his holding with it. The
  received good is in both holdings, so they show no ranking of it.

The fifth condition, two different goods, takes the next paragraph.

Rothbard states the two-different-goods condition himself: "In
describing the conditions that must obtain for interpersonal exchange to
take place (such as reverse valuations), we implicitly assumed that it
must be two different goods that are being exchanged" (p. 95). For him
it is a condition for an exchange to take place. So it is like knowledge
of the other party, above. Every theorem here starts from a trade that
did happen. So, like knowledge, it does no work in any proof. But
leaving it out is not idle. It lets in the man who trades a good for
itself. Of him the bridge, with voluntariness, says that he
prefers his holding to itself. `Prefers` is meant as strict. But the
library nowhere assumes that nothing is preferred to itself. That
follows only from a claim of its own, asymmetry of preference
(`AsymmetricPreference`, under *The claims*). The exchange theorems do
not carry it. So as encoded nothing keeps him out. Assume the bridge
of his trade, and the theorems still apply to him. They say only that he ranks a good,
or a holding, above itself. Add asymmetry (`AsymmetricPreference`), and
the bridge is false of his voluntary trade. Every theorem here about
what a trader prefers asks for the bridge and for voluntariness. So with
asymmetry added, none of them applies to him.

*Where the tradition stands.* For Rothbard the bridge cannot fail. The
scale is read off the act: "We deduce the existence of a specific value
scale on the basis of the real act" (p. 260). On that reading, an act
against one's own ranking is not a possibility. Here the ranking exists
apart from the act. So the bridge constrains it. Its status as a claim
is our reconstruction and not his. Nor does the library assume,
anywhere, that a man's scale stays put. The reasons are under *The
ladder as a history*. What the later-judged benefit carries is narrower.
It is a condition that his ranking of these two holdings did not turn
(`Trade.RankingHolds`). Where it fails, the theorem is silent.

*What a failure would point at.* Two of the conclusions name different
places to look: reverse valuations (`MutualBenefit.reverse_valuations`)
and the later-judged benefit (`MutualBenefit.better_off_judged_later`).
The at-trade result (`MutualBenefit.better_off_judged_at_trade`) takes
only the bridge and voluntariness. Say a man did not rank the good he got above the good he
gave. Then look for one of these:

- The trade was not voluntary (`Trade.Voluntary`).
- The goods were complements of something he kept
  (`Trade.SeparableFromRest`).
- The goods were substitutes for something he kept
  (`Trade.KeptServesOtherEnds`).
- He traded against his own ranking at the time. Then the bridge itself
  failed (`DemonstratedPreference`).

Say instead he is not better off afterwards. Then look for one of these:

- The trade was not voluntary (`Trade.Voluntary`).
- His beliefs about a good changed (`Trade.BeliefsHold`). That is error,
  or deception. Rothbard already counts deception as not voluntary.
- His ranking of the two holdings turned (`Trade.RankingHolds`). That is
  regret.
- The bridge failed (`DemonstratedPreference`).

On each list only the bridge is a claim. The rest are conditions. Where
they fail, the theorems are silent, not wrong. The defence "the
conditions did not hold" now has a list to check against.

# Time preference
%%%
file := "Time-preference"
tag := "time-preference"
%%%

Time preference is the third target. Like exchange, it was chosen for
what it can diagnose. The claim (`TimePreference`) is this: a man
prefers a satisfaction sooner to the same satisfaction later, if the
sooner is not already past. Rothbard builds interest on it. Both
authors state it as universal. Rothbard:
"A fundamental and constant truth about human action is that man
prefers his end to be achieved in the shortest possible time. Given
the specific satisfaction, the sooner it arrives, the better" (*MES*,
p. 15). Mises: "Satisfaction of a want in the nearer future is, other
things being equal, preferred to that in the farther distant future",
and "Time preference is a categorial requisite of human action"
(*Human Action*, ch. XVIII, §2). Each of them attaches a qualifier.
Rothbard's is "given the specific satisfaction". Mises's is "other
things being equal". Everything turns on these qualifiers, and on who
decides when they are met.

*Dates.* Until now the vocabulary had no "sooner". Time was not
ordered, and an end had no date. That was because no theorem asked for
either. Time
preference cannot be stated without them. So the vocabulary grows
here. It grows by extending the frame (`DatedFrame`), not by editing
it. The earlier theorems are stated over the unextended frame
(`ActionFrame`). So none of them gets vocabulary it does not use.
Three things are added:

- Times get a bare relation, "before" (`Before`). It has no
  properties at all.
- Each end gets the time it is attained at (`attained`).
- A relation says which pairs of ends are the same satisfaction
  at two dates, for a given man (`SameSatisfaction`).

{docstring Apodictic.DatedFrame}

*Who decides "the same satisfaction".* Rothbard's footnote defines
time preference as "the preference for present satisfaction over
future satisfaction or present good over future good, provided it is
remembered that it is the same satisfaction (or “good”) that is being
compared". It then meets the obvious objection: "Since
ice-in-the-summer provides different (and greater) satisfactions than
ice-in-the-winter, they are not the same, but different goods"
(pp. 15–16, n. 15). On that reading, how the man values two dated
ends settles whether they are the same satisfaction. Then whenever he
prefers the later one, it was a different good. So the claim is never
tested.

Mises sets the same case aside on another ground. He calls it "the
case of perishable goods". Winter ice is "a good that loses its
specific usefulness even if not consumed". Summer ice is "another good
which requires a different process of production". So the two are
"for all practical purposes different commodities" (*Human Action*,
ch. XVIII, §2). Neither description is a valuation. Each says how the
ice is kept or produced:

- Winter ice serves in summer only through a special process of
  conservation.
- Summer ice needs a different process of production.

So each can be checked without asking what the man prefers. Rothbard's
ground cannot be checked that way. His ground is how the man values
the two.

Lean shows exactly what Rothbard's reading buys. Two statements about
a pair of dated ends are in play here. They are called the two halves
of time preference:

- The negative half: the later is not preferred to the sooner.
- The strict half: the sooner is preferred to the later. This is what
  the claim (`TimePreference`) states.

Now define "the same satisfaction" as "the later is not preferred to
the sooner" (`SameByValuation`). Then the negative half holds in every
frame, of every pair that is the same satisfaction on this reading. It
carries no claim at all:

{docstring Apodictic.TimePreference.SameByValuation}

{docstring Apodictic.TimePreference.valuation_reading_is_free}

The strict half is not free. The docstring above gives the reason:
two ends with neither preferred count as the same satisfaction on this
reading. The next theorem checks that reason in one frame. Nothing is
ranked in it. So every pair counts as the same satisfaction on this
reading. And there the sooner is not preferred:

{docstring Apodictic.Model.valuation_reading_strict_half_fails}

So, on Rothbard's reading, time preference asserts one
thing. Take two ends, one before the other, the sooner not yet past.
One is ranked above the other. Neither author argues for that. And it
sits badly with a doctrine of Rothbard's own: indifference cannot
be demonstrated in action. On this reading the claim rules out one
case: two dated ends, neither preferred to the other. That is exactly
the case no act of the man's could ever show. So, on this reading, no
act of his could show the claim false.

The library therefore takes the other road. Sameness is supplied
separately from the ranking. It is the man's, since satisfactions are
his. But it is not read off his preferences. So the claim can fail.
Say a man ranks the same satisfaction higher later. He is then a
counterexample to the claim, not a case of a different good.

In Lean, sameness is a relation given with the frame
(`SameSatisfaction`), never defined from the ranking. The library does
not say how it is fixed in a given case. The ways it can fail are
listed below, under *What a failure would point at*.

The claim's docstring, below, names three things explained elsewhere:

- The lifting condition (`DatedFrame.LiftsOverRest`), under
  *Durability* below.
- The bridge from an act (`DemonstratedTimePreference`), under
  *Mises's regress* below.
- The interest theorems, under {ref "interest"}[Interest].

The docstring's point on anticipation is taken up in the last
paragraph of this page.

{docstring Apodictic.TimePreference}

*Durability.* Rothbard draws one consequence at once: "if the actor
values the total service rendered by two consumers' goods equally, he
will, because of time preference, choose the less durable good"
(pp. 16–17, n. 16). Its smallest case is two goods whose services
differ only in the date of one service. There it follows, at a price:

{docstring Apodictic.TimePreference.less_durable_preferred}

```lean (name := manifestDurable)
#manifest TimePreference.less_durable_preferred
```
```leanOutput manifestDurable
manifest of Apodictic.TimePreference.less_durable_preferred

  praxeological claims:
    timePreference : TimePreference praxis agent now

  situational conditions:
    same : praxis.SameSatisfaction agent soon late
    sooner : praxis.Before (praxis.attained soon) (praxis.attained late)
    notPast : ¬praxis.Before (praxis.attained soon) now
    lifts : praxis.LiftsOverRest agent now rest soon late

  vocabulary (what the claims are about):
    praxis : DatedFrame
    agent : praxis.Agent
    now : praxis.Time
    rest : Set praxis.End
    soon : praxis.End
    late : praxis.End

  logical background: []
```

Rothbard gives no example of this consequence. Here is one, and it is ours. Two
season tickets cover the same nine concerts (`rest`). The first also
covers a tenth concert on Friday (`soon`). The second covers the same
concert, repeated on Sunday (`late`). The conclusion: the man now
prefers the first ticket to the second. It costs one claim and four
conditions:

- Time preference (`TimePreference`), the claim. It fails if he does
  not prefer the Friday concert to the Sunday one, though the next
  three conditions hold.
- The two concerts are the same satisfaction for him
  (`SameSatisfaction`). It fails if Sunday's has another soloist, say.
- Friday comes before Sunday (`sooner`). It fails if the repeat is on
  Thursday.
- Friday is not already past (`notPast`). It fails if it is Saturday
  now.
- Preferring Friday's concert carries up to preferring the whole first
  ticket (`LiftsOverRest`). It can fail if Friday's concert clashes
  with one of the nine. Say one of the nine is also on Friday evening.
  Then the second ticket may be better, though Friday's concert alone
  is preferred.

The price is the last condition. Time preference ranks single
satisfactions. The goods deliver streams of them. Preferring the
sooner service is one thing. Preferring the stream it belongs to is
another. To get from the one to the other, the rest of the stream must
stay out of it. That fails where the sooner delivery clashes with
something else in the stream. Rothbard's sentence does not show this
condition. Independence of uses (`IndependentUses agent time`, under
*The conditions*) carries a preference down, from bundles to ends.
This condition carries one up, from ends to bundles:

{docstring Apodictic.DatedFrame.LiftsOverRest}

Two things are not reached:

- More than one service at a different date. The preferences would
  then have to be chained. That needs transitivity of preference, which
  nothing here asserts.
- Rothbard's "will choose". The conclusion is a preference. No claim
  here runs from what a man ranks to which of two goods he picks. Only
  one claim in the library runs from ranking to act (`ActsInOrder`,
  under {ref "claims"}[The claims]). It is about how a stock is
  allocated, not about this.

*Mises's regress.* Mises does not only assert time preference. He
argues that action is impossible without it: "If he were not to prefer
satisfaction in a nearer period of the future to that in a remoter
period, he would never consume and so satisfy wants. ... He would not
consume today, but he would not consume tomorrow either, as the morrow
would confront him with the same alternative." The argument runs from
what a man prefers to what he does. So it cannot be stated without a
bridge between the two. Mises supplies one, in the same section. It
runs the other way round, from the act to the preference. That is the
same link read backwards:

- The bridge: if he consumes, that shows he prefers the sooner.
- Read backwards: if he does not prefer the sooner, he does not
  consume. That is the step the regress needs.

Mises states the bridge: "He who consumes a nonperishable good instead of
postponing consumption for an indefinite later moment thereby reveals
a higher valuation of present satisfaction". That sentence is the
second new claim (`DemonstratedTimePreference`). It is stated of one
act:

{docstring Apodictic.DemonstratedTimePreference}

The regress runs along a sequence (`Morrows`). Each day a satisfaction
is on offer, and another on the next day. The regress spends one claim,
the bridge above. It also spends three conditions:

- That the act in question consumes (`ConsumesAt`). This only says
  that the act takes the day's offer and forgoes the next day's.
- That each day's offer is the same satisfaction as the next
  (`SameAlternative`), shown below, after the sequence.
- That the absence of a preference carries from day to day
  (`NoPreferenceCarries`), shown below too.

The sequence's docstring keeps sameness (`SameAlternative`) out of
its fields, because it can fail. The same was done with one unit to
one end. It can fail of a real stable, so it could not stay a field
(see {ref "vocabulary"}[The vocabulary]). The fields that stay, and why
each assumes nothing about the world, are under *The carried
conditions* below.

{docstring Apodictic.Morrows}

{docstring Apodictic.Morrows.SameAlternative}

{docstring Apodictic.Morrows.NoPreferenceCarries}

With the bridge in place, one step goes from "he consumed" to "he
preferred the sooner". It is one application of the bridge, plus the
sameness condition (`SameAlternative`):

{docstring Apodictic.TimePreference.consumption_reveals}

The regress adds only one thing to it. It carries the conclusion back
from the day he consumes to the first day. Only a weaker thing arrives
there: not the preference, but a refutation of having had none.

{docstring Apodictic.TimePreference.regress}

```lean (name := manifestRegress)
#manifest TimePreference.regress
```
```leanOutput manifestRegress
manifest of Apodictic.TimePreference.regress

  praxeological claims:
    demonstrated : DemonstratedTimePreference act

  situational conditions:
    consumes : morrows.ConsumesAt n act
    sameAlternative : morrows.SameAlternative
    carries : morrows.NoPreferenceCarries

  vocabulary (what the claims are about):
    praxis : DatedFrame
    agent : praxis.Agent
    morrows : Morrows praxis agent
    n : ℕ
    act : Action praxis.toActionFrame

  conditions carried by the vocabulary (not binders: discharged by
  whoever supplies the argument):
    morrows.dated : ∀ (n : ℕ), praxis.attained (morrows.offer n) = morrows.date n
    morrows.successive : ∀ (n : ℕ), praxis.Before (morrows.date n) (morrows.date (n + 1))
    act.forgone_nonempty : act.forgone.Nonempty
    act.chosen_not_forgone : act.chosen ∉ act.forgone
    act.belief : praxis.Believes act.agent act.time act.means act.chosen

  logical background: []

  (1 trailing binders belong to the conclusion, not the signature)
```

Mises's own case runs through the theorem. A man holds a nonperishable
good. Today he can consume it, or keep it for tomorrow. Tomorrow
offers him the same choice. Say that on some day he consumes it. The
conclusion: it is not the case that, on the first day, he had no
preference for the sooner. It costs one claim and three conditions:

- Consuming reveals a preference for the sooner
  (`DemonstratedTimePreference`), the claim. It fails if he consumes
  without preferring the sooner.
- On that day he consumes: he takes the day's offer and forgoes the
  next day's (`ConsumesAt`). It fails if he keeps the good that day.
- Each day's offer is the same satisfaction as the next
  (`SameAlternative`). This is Mises's "the same alternative", and his
  "nonperishable". It fails if the good perishes. Mises's winter ice
  fails it. That ice serves in summer only after a process of
  conservation.
- Having no preference for the sooner carries from each day to the
  next (`NoPreferenceCarries`). It fails if, after a day on which he
  does not prefer the sooner, he comes to prefer it the next day.

Three findings are in this:

- The regress and the "reveals" sentence are one premise, used twice.
  The premise is that consuming the sooner shows a preference for it.
  The regress passage leaves it unstated. The "reveals" sentence
  states it. Once it is stated, it does all the work. The regress
  contributes only the carrying from day to day.
- What comes out is far short of the universal. It is a preference at
  one date, for one sequence of offers. It is not "the sooner is
  better" for every end at every date.
- It comes out only as a double negation. Mises carries the *absence*
  of a preference forward. So the argument refutes his having no
  preference on the first day. This argument yields the preference
  itself only with excluded middle. The library's theorems outside
  `Consistency.lean` do without excluded middle. With excluded
  middle, every question would count as having a yes-or-no answer, whether or not
  anything settles it (see {ref "manifest"}[The manifest], on
  `Classical.choice`).

`Waiting` is a frame where a man prefers each satisfaction sooner. Its
name is only a label. In it, both claims and every condition of both
theorems hold together. So both theorems can be handed this frame.
That shows their conditions can all hold at once, so neither theorem is vacuous. The docstrings below
call this non-vacuity. As a test of it, `Waiting` is weak in two
places, and they are worth saying:

- The durability case is handed an empty rest of the stream. So the
  lifting condition (`LiftsOverRest`) is never tried on a real one.
- There is no absence of preference for the regress's carrying
  condition (`NoPreferenceCarries`) to carry. So it holds with nothing
  to do.

{docstring Apodictic.Model.waiting_less_durable_applies}

{docstring Apodictic.Model.waiting_regress_applies}

*The carried conditions.* The regress's manifest lists two fields of
the sequence:

- Each day's offer is attained on that day (`dated`).
- Each day comes before the next (`successive`).

It also lists three fields of the act:

- The act gives something up (`forgone_nonempty`).
- What it takes is not among what it gives up (`chosen_not_forgone`).
- He believes the means bring about what he takes (`belief`).

Each of the five is of a kind that assumes nothing about the world. Take a
sequence whose "offer on the third day" arrives on some other day. Or take an
act that gives nothing up. Neither is a situation that might obtain.
Nor is an act whose means he does not believe bring about what he
takes. The docstring of an action (`Action`) says why: its fields hold
together as a package, and nothing with fewer parts counts as an
action.
That each day's offer is the same satisfaction as the next is not of
that kind. The good may perish. So it is not a field. It is the named
condition above (`SameAlternative`).

*What "before" was asked for.* Nothing. No proof here uses any
property of "before". None uses that it is transitive. None uses even
that no time comes before itself. "Sooner" enters every statement as a
label on a pair of dates. It is never a step in an argument. Lean was
expected to force an order on time here. It did not.

*What a failure would point at.* Say a man prefers a satisfaction
later. Then one of these failed:

- The two dated ends were the same satisfaction for him
  (`SameSatisfaction`). It fails where the good perishes, or the
  enjoyments cannot be had together. It fails where the later is
  surer, or the wait itself is worth something to him.
- The sooner one was not already past (`notPast`).
- The claim itself (`TimePreference`).

Say he prefers the less durable good less. Then one of the same
failed. Or the sooner service clashed with the rest of the stream
(`LiftsOverRest`). Say the regress does not bite. Then one of these
failed:

- The offer was the same from day to day (`SameAlternative`).
- His lack of preference carried (`NoPreferenceCarries`).
- Consuming revealed what Mises says it does
  (`DemonstratedTimePreference`).

The textbook case against the claim is on that list. It is the case
where the wait itself is worth something to the man
(`SameSatisfaction`). People will pay more for a pleasure a few
days off than for the same pleasure now. And they will pay more to avoid a pain that is put off: "Subjects on
average were willing to pay more to experience a kiss delayed by 3
days than an immediate kiss or one delayed by three hours or one day"
(Loewenstein, *Economic Journal* 1987, p. 668). Waiting for a pleasure
is itself a pleasure. Waiting for a pain is itself a pain. So the
later option carries a satisfaction that begins now. The pair falls
outside the claim, which says nothing about it. Setting the pair
outside the claim has the shape of Rothbard's ice. One test separates
a diagnosis from an escape. A diagnosis points at a condition that
failed, and the failure can be shown apart from the choice, as under
*What a failure would point at* above. An escape reads the failure off
the choice itself. Then no choice can count against the claim, as on
Rothbard's reading of the ice. Can
the difference be shown without looking at the choice? For the ice,
it can on Mises's ground: the processes of conservation and of
production above. On Rothbard's "greater satisfactions", read off the
preference, it cannot. For dread it has been shown. People waiting
for an electric shock were scanned. The scans told them apart: "Even when no decision was
required, these extreme dreaders were distinguishable from those who
dreaded mildly". And the extreme dreaders were the ones who, given the
choice, "preferred to receive more voltage rather than wait" (Berns et
al., *Science* 2006). This page cites no such showing for savouring,
as in the kiss. Anticipation that is only inferred from the waiting
brings back the reading on which the claim cannot fail.

# The regression theorem
%%%
file := "Regression-theorem"
tag := "regression"
%%%

The regression theorem is the fourth target. It is Mises's account of
where a medium of exchange can come from: "no good can be employed for
the function of a medium of exchange which at the very beginning of its
use for this purpose did not have exchange value on account of other
employments" (*Human Action*, ch. XVII, §4). It was chosen because a
case is pressed against it. Some media came into use inside a monetary
economy. Bitcoin is one of them. Their first buyers paid money for
them. What the theorem requires of such a medium depends on how its
terms are read. Here each reading is written separately in Lean. So a
move from one reading to another is a change of hypothesis, and the
change shows in a signature. The end of the page says what each
reading asks of a medium whose first buyers paid money.

The theorem has two halves, and only one is here. It is the genetic
half, about a medium's origin. The other half says that today's
purchasing power is formed from yesterday's. That half is about
quantities, and nothing below has any. And the theorem is about any
medium of exchange, not only money: "For all that is to be predicated
of money is valid for every medium of exchange" (ch. XVII, §1).

*A medium, by belief.* Mises's medium of exchange is a good wanted "to
keep it as a medium of exchange and to give it away at need in a later
act of exchange" (ch. XVII, §4). To say so, the vocabulary grows by one
bare relation (`Onward`). An end is *onward* for a good when the man
would reach it by giving that good itself away in a later trade.

{docstring Apodictic.MediumFrame}

A man appraises a good as a medium when he believes it serves some
onward end (`MediumFrame.AppraisesAsMedium`). Two other definitions
were available. Neither is used:

- One calls a good a medium when its price is being appraised. Then a
  medium would have a price behind it by the meaning of the word. The
  regress would be true by definition.
- The other waits for an actual later trade. But take a man who holds
  a good meaning to pass it on. He already demands it as a medium,
  whether or not the trade comes.

So demand in anticipation counts.

{docstring Apodictic.MediumFrame.AppraisesAsMedium}

A good, here, is a kind, such as gold or salt. It is not a unit of a
kind. The regress is about the kind. A coin minted today was never
traded before, and the theorem is not about that coin.

The regress runs back through what happened. So there is a record of
it (`History`). The record holds the exchanges made on each day. Days
are counted from a first one.

{docstring Apodictic.History}

Three things are read off the record. The theorem comes in two forms,
a negative and a positive, stated in these terms under *The regress*
below:

- A man acquired the good on a day, giving another good for it
  (`History.AcquiredAgainst`). Most of the conditions below are about
  these acquisitions.
- Someone acquired the good on a day for an end other than passing it
  on (`History.DirectAcquisitionAt`). Any end other than passing it on
  counts. That is the broad reading of Mises's "other employments". A
  narrower one comes under *Two readings of "other employments"*
  below. The positive form concludes that such an acquisition
  happened. A condition of the negative form (`noDirect`) says that
  none did.
- On a day, someone appraises the good as a medium
  (`History.MediumAt`). The negative form concludes that this does not
  happen. The positive form starts from it.

{docstring Apodictic.History.AcquiredAgainst}

{docstring Apodictic.History.DirectAcquisitionAt}

{docstring Apodictic.History.MediumAt}

*Indirect exchange needs no new claim.* Take a man who trades for a
good only to pass it on. He ranks what he expects to reach by passing
it on above what the good he gave could do. That is the exchange
theorem again, with onward ends counted like any others
(`Regression.indirect_ranks_onward_ends`). It carries the same claim
and conditions as the exchange theorem. It adds one condition: that he
wants the good for nothing else (`Trade.PurelyIndirect`). No theorem
of the regress below uses it. It shows that a trade for a medium is
already covered by the exchange theorem.

{docstring Apodictic.Trade.PurelyIndirect}

{docstring Apodictic.Regression.indirect_ranks_onward_ends}

*The claim.* The hinge of the theorem is a sentence about judgment.
The man considering money "cannot form a judgment about the future
purchasing power of money otherwise than by looking at its
configuration in the immediate past". And so "A medium of exchange
without a past is unthinkable" (ch. XVII, §§4, 8). Mises's premise
shuts out every other ground of judgment. The library does not follow
him that far. The claim is appraisal from the past
(`AppraisalFromPast`). Its docstring says what the claim asserts.
Under *Does not say*, it says what the claim leaves out.

{docstring Apodictic.AppraisalFromPast}

*Rothbard's gold.* Rothbard tells the regress with gold (*MES*,
pp. 272–74). It is the example used below. In his figure, "a system of
barter prevails on days 1, 2, and 3, and gold is used as a medium of
exchange on day 4 and thereafter" (p. 274). In the days of barter,
"gold is used only for direct consumption or production purposes and
not as a medium of exchange" (p. 274). His instance of a direct use is
"the use of gold for ornaments" (p. 272). We read his story through
the definitions above. On that reading, nobody appraises gold as a
medium on days 1 to 3. Someone does on day 4.

*The regress.* Mises states his conclusion in the negative. The
negative form needs the fewest claims: one. Say nobody
acquired the good, before a given day, for an end other than passing
it on. Then on that day nobody appraises it as a medium. In the
example, say nobody acquired gold before day 4 for an end other than
passing it on. Then on day 4 nobody appraises gold as a medium:

{docstring Apodictic.Regression.no_medium_without_direct_acquisition}

```lean (name := manifestRegression)
#manifest Regression.no_medium_without_direct_acquisition
```
```leanOutput manifestRegression
manifest of Apodictic.Regression.no_medium_without_direct_acquisition

  praxeological claims:
    appraisal : AppraisalFromPast history m

  situational conditions:
    begins : history.BeginsBeforeMedium m
    purposive : history.AcquisitionsPurposive m n
    noDirect : ∀ k < n, ¬history.DirectAcquisitionAt k m

  vocabulary (what the claims are about):
    praxis : MediumFrame
    history : History praxis
    m : praxis.Means
    n : ℕ

  logical background: []

  (1 trailing binders belong to the conclusion, not the signature)
```

The manifest holds one claim and three conditions. The third
(`noDirect`) is the hypothesis Mises's sentence itself states. The
other two conditions are not in his sentence.

The proof steps back one acquisition at a time. Each step rests on the
claim and the conditions:

- Someone appraises the good as a medium on a day after the first.
  The claim (`AppraisalFromPast`) gives an exchange of the good on an
  earlier day. So someone acquired it on that day.
- The second condition (`History.AcquisitionsPurposive`, below) gives
  an end he acquired it for.
- Say that end is onward. Then he believed the good served an onward
  end. So he appraised it as a medium on that earlier day, and the
  same step applies to him.
- Say that end is not onward. Then his was an acquisition for an end
  other than passing the good on. The third condition (`noDirect`)
  says there was none.
- The steps cannot go on for ever. Days are counted from a first one.
  The first condition (`History.BeginsBeforeMedium`, below) says
  nobody appraises the good as a medium on that first day.

The claim (`AppraisalFromPast`) fails if someone appraises the good as
a medium on a day after the first, and the good changed hands on no
earlier day of the record. In the example it holds, on our reading.
Gold changed hands in barter on days 1 to 3.

The first condition is that the regress ends
(`History.BeginsBeforeMedium`). Counting days from a first one
supplies half of that. From any day there are finitely many days back.
The other half is assumed: on the first day of the record, the good is
not yet a medium. Both authors assert it. Neither argues it. In the
example, the first day is Rothbard's day 1, a day of barter. The
condition fails if someone appraises the good as a medium on the
record's first day. A record of gold that began on day 4 would fail
it.

{docstring Apodictic.History.BeginsBeforeMedium}

The second condition is that whoever acquired the good wanted it for
something (`History.AcquisitionsPurposive`). The proof needs it at
every step back. Take an acquirer who believed the good served no end
at all, not even resale. He neither holds a medium nor uses the good
directly. So the regress stops at him with nothing to show. We found
no passage in either author that states the condition. It fails if
someone acquired the good before the day in question, believing it
served no end at all. In the example, that is someone who took gold
before day 4 believing it good for nothing. Rothbard's story leaves no
room for him if "used only for direct consumption or production
purposes" (p. 274) covers every acquisition. That reading is ours.

{docstring Apodictic.History.AcquisitionsPurposive}

*The positive form, and what it adds.* Turned round, the theorem says
this. Say the good is a medium on some day. Then on an earlier day,
someone acquired it for an end other than passing it on. And the proof
finds that acquisition. In the example, gold is a medium on day 4. So
someone acquired gold on day 1, 2 or 3 for an end other than passing
it on. On our reading of Rothbard's story, that could be gold taken in
barter for ornaments, say. The positive form needs one claim more
(`TwoPartialDemands`).

{docstring Apodictic.Regression.direct_acquisition_before}

```lean (name := manifestRegressionPositive)
#manifest Regression.direct_acquisition_before
```
```leanOutput manifestRegressionPositive
manifest of Apodictic.Regression.direct_acquisition_before

  praxeological claims:
    twoDemands : TwoPartialDemands praxis m
    appraisal : AppraisalFromPast history m

  situational conditions:
    begins : history.BeginsBeforeMedium m
    purposive : history.AcquisitionsPurposive m n
    medium : history.MediumAt n m

  vocabulary (what the claims are about):
    praxis : MediumFrame
    history : History praxis
    m : praxis.Means
    n : ℕ

  logical background: []
```

At each step back, the proof meets an acquirer and the end he wanted
the good for. If the end is onward, the regress goes on. If it is not,
the regress has arrived. The negative form never has to decide which.
It concludes a denial: nobody appraises the good as a medium. So it is
enough that each case leads to a contradiction. A non-onward end
contradicts its third condition (`noDirect`). An onward end makes the
acquirer an appraiser on an earlier day, and the same argument rules
that out. Ruling out both cases needs no decision between them. The
positive form must hand over the acquisition. So at each step it must
know which case it is in. Nothing in the vocabulary decides that. A sentence of
Mises's own decides it: "Thus the demand for a medium of exchange is
the composite of two partial demands: the demand displayed by the
intention to use it in consumption and production and that displayed
by the intention to use it as a medium of exchange". Read the two
parts as leaving nothing over. Then the composite is the statement
that each end is onward or is not. That statement is a case of the law
of excluded middle. With excluded middle, every question would count
as having a yes-or-no answer, whether or not anything settles it (see
{ref "manifest"}[The manifest], on `Classical.choice`). The library's
theorems do without it. The one exception is the file of small frames
(`Consistency.lean`; see {ref "result"}[The Result]). Proofs that do
without excluded middle are called constructive. So the statement enters as a named claim
(`TwoPartialDemands`), not as logic.
The sentence is Mises's. Reading "composite" as leaving nothing over
is ours.

{docstring Apodictic.TwoPartialDemands}

Without the claim, what is shown is weaker
(`Regression.partial_demands_not_not_exhaust`). No end the good serves
is outside both parts. That is a double negation: it is not the case
that the end is in neither part. Without excluded middle, it does not
say which part the end is in. With the claim, every end the good
serves is shown to be in one part or the other
(`Regression.partial_demands_exhaust`):

{docstring Apodictic.Regression.partial_demands_not_not_exhaust}

{docstring Apodictic.Regression.partial_demands_exhaust}

One thing is not proved in either form: that there was a *last* day of
barter. That is a day before which the good was no medium, and after
which it was. Rothbard's story has one. It is day 3 of his figure
(p. 274): "the last day of barter, the day before gold began to be used
as a medium of exchange" (p. 273). Proving a last day needs one thing
decided for each day: whether the good is a medium on that day. The
claim (`TwoPartialDemands`) decides less. It decides, for each end,
whether that end is onward. Whether the good is a medium on a day asks
something else: whether some agent, that day, believes it serves some
onward end (`History.MediumAt`). That is a question about every agent
and every end at once. No claim here settles it. It would take
excluded middle for that question too. The claim grants excluded
middle for no other question (its *Does not say*, item 4).

*Two readings of "other employments".* In the theorems above, an end
other than passing the good on is any such end. The direct part of the
demand is whatever is not onward. Mises names something narrower: "the
services it can render directly to consumption or production". He does
not say which ends those are. And the library sorts no ends. So the
narrow reading is a condition (`History.OtherEmploymentsNarrow`).
Whoever applies the theorem supplies the ends he counts as consumption
or production. The condition says that every other employment the
good was acquired for was one of them. It fails if someone acquired
the good before the day in question for an end that is not onward and
is outside them. In the example, that is someone who took gold before
day 4 for a game, say. For day 4, in Rothbard's story it holds: in
the days of barter gold is used "only for direct consumption or production
purposes" (p. 274). Reading his "purposes" as the acquirers' ends is
ours.

{docstring Apodictic.History.OtherEmploymentsNarrow}

{docstring Apodictic.Regression.narrow_acquisition_before}

The narrow theorem adds nothing but the condition. It is the broad
positive form, with the condition applied to the acquisition that form
finds. The library also states the narrow negative form
(`Regression.no_medium_without_narrow_acquisition`). Say nobody
acquired the good before a given day for an end, other than passing
it on, among those supplied.
Then, given the condition, nobody appraises it as a medium that day.
It too is the broad form with the condition applied.

*Rothbard's two versions.* Rothbard states the origin twice, and
differently:

- In *MES*, a medium "can arise only out of a commodity previously
  used directly in a barter situation, and therefore having had an
  array of prices in terms of other goods" (p. 275).
- In *Power and Market*, "no money can be established on the market
  except as it can be exchanged for a previously existing money (which
  in turn must have ultimately related back to a commodity in barter)"
  (*MES* ed., p. 1021).

The first version adds a clause to the conclusion. The clause is that
the earlier acquisition, for an end other than passing the good on, was
made against a good not then a medium. The library does not derive
that clause from its claims. It takes it as a condition on every
earlier acquisition of the good (`History.FormedInBarter`). The conclusion's clause is that condition,
applied to the one acquisition the regress finds. In the example, we
read Rothbard's days 1 to 3 as having no medium at all. Then nothing
given for gold before day 4 was a medium, and the condition holds. It
fails if, on some day before the day in question, the good was
acquired against a good that someone then appraised as a medium. A
good bought with money is one case:

{docstring Apodictic.History.FormedInBarter}

{docstring Apodictic.Regression.barter_origin}

```lean (name := manifestBarterOrigin)
#manifest Regression.barter_origin
```
```leanOutput manifestBarterOrigin
manifest of Apodictic.Regression.barter_origin

  praxeological claims:
    twoDemands : TwoPartialDemands praxis m
    appraisal : AppraisalFromPast history m

  situational conditions:
    begins : history.BeginsBeforeMedium m
    purposive : history.AcquisitionsPurposive m n
    barter : history.FormedInBarter m n
    medium : history.MediumAt n m

  vocabulary (what the claims are about):
    praxis : MediumFrame
    history : History praxis
    m : praxis.Means
    n : ℕ

  logical background: []
```

The second version is a theorem about the prior money
(`Regression.prior_money_relates_back`). Rothbard's case is Germany
after its inflation of 1923. It could found "a new currency based on
exchanges with other pre-existing moneys (gold or foreign paper)"
(p. 1021). The theorem runs as follows. Say the new medium is a
medium on some day. Then it was acquired, on an earlier day, against
some good. Say that good was then a medium itself. Then, before that
day, someone acquired that good for an end other than passing it on.
This delivers less than the parenthesis says. It gives an earlier
acquisition of that good for an end of its own. It does not give that
the acquisition was in barter. And the theorem carries both claims, and the two
conditions on the record's start and on purposive acquisitions
(`History.BeginsBeforeMedium`, `History.AcquisitionsPurposive`), for
every good. Its docstring says why.

{docstring Apodictic.Regression.prior_money_relates_back}

The detour through the prior money is not needed for the new medium.
Take the broad reading. The positive form already concludes, for the
new medium itself, an earlier acquisition for an end other than
passing it on. It concludes this whatever was paid for the new medium.
The regress follows the acquirers' ends, never what they gave. The
prior money's history adds a conclusion about the prior money.

*"Its own past price."* Mises's exclusive premise is that the
appraisal rests on the good's own past price. That premise would best
be a condition separate from the claim. Then a failure could be laid
to one or the other. Here it cannot be kept separate. The vocabulary
has no quantities: no prices, no purchasing power. An appraisal is a
belief that the good serves an onward end
(`MediumFrame.AppraisesAsMedium`). It has no size. Nothing in the
vocabulary links it to an exchange it was formed from. So "rests on"
has no statement here. What can be stated is that an
exchange of the good came earlier (`History.OwnPastPrice`). And that
is the claim again (`Regression.ownPastPrice_of_claim`).

{docstring Apodictic.History.OwnPastPrice}

{docstring Apodictic.Regression.ownPastPrice_of_claim}

*The case.* The library builds one frame to test this on. In it, a
good is first believed fit only for eating. From the next day, it is
also believed fit for passing on. In this frame both claims hold. So
does every condition of the positive barter and narrow theorems. The
negative forms are not tried on this frame. And on the
second day someone appraises the good as a medium. So the theorems do
not hold merely because nothing meets their hypotheses. The test is
thin, and it is worth saying where:

- There is one agent. So the acquirer the regress finds is the same
  man who appraises the good as a medium.
- The good is exchanged against itself, once a day. So nothing but
  the good itself is ever given for it. The barter theorem is tried
  for the second day. So its condition (`History.FormedInBarter`)
  looks only at the first day's exchange. It holds only because the
  good is no medium on that day. The
  prior-money theorem (`Regression.prior_money_relates_back`) is not
  tried on this frame.
- Nothing in the frame is ranked. So no theorem that concludes a
  ranking is tried here, the indirect-exchange theorem
  (`Regression.indirect_ranks_onward_ends`) among them.

*What a failure would point at.* Suppose a good is a medium. And no
earlier acquisition of it, for an end other than passing it on, is to
be found. Then one of these happened:

- The record began inside a monetary economy, with the good already a
  medium on its first day (`History.BeginsBeforeMedium`).
- Someone took the good believing it good for nothing
  (`History.AcquisitionsPurposive`).
- The record is missing an exchange that happened. A missing exchange
  can make only the claim fail: the claim is the one hypothesis that
  asks the record for an exchange. Then the claim fails of the record.
  It may still hold of the complete record.
- The first claim failed (`AppraisalFromPast`). Someone appraised the
  good as a medium when it had never changed hands. He might have done
  so on an issuer's pledge, say, or an edict.

The second claim (`TwoPartialDemands`) is not on that list. No case
can be brought against it. In the regress, a case would be an end the
good serves that is in neither part. The double negation above shows,
with no claim at all, that there is no such end
(`Regression.partial_demands_not_not_exhaust`). The regress looks only
at ends the good is believed to serve. What the claim adds is the
right to say which part. Without it, the negative form still stands.

Buying a good to resell it is not on that list as an escape. A man who
holds a good in order to sell it believes it serves an onward end. So
he already appraises it as a medium. And the regress asks for an
acquisition earlier than his.

For a medium whose first buyers paid money, the versions come apart:

- Rothbard's barter version is silent. Its condition fails wherever
  the good was bought with money before the day in question.
- The broad theorem is not silent on that account, since it never
  asks what was paid. Say the record begins before the good is a
  medium (`History.BeginsBeforeMedium`), and every acquisition was for
  some end (`History.AcquisitionsPurposive`). Then it asks a question
  about the early acquirers. Did some early acquirer want the good for
  an end other than passing it on? Say the record shows none before a
  day on which the good is a medium. Then, by the negative form, the
  claim (`AppraisalFromPast`) failed. It failed of the record. If the
  record is complete, it failed of the complete record too. If the
  record misses an exchange, the failure may be the record's alone.
- The narrow theorem asks more: that what they wanted it for was
  consumption or production. It is silent where the good was first
  wanted for a game, a cause, or a test.

This page does not answer these questions for Bitcoin. Nor does it say
whether the claim fails for it.

# Interest
%%%
file := "Interest"
tag := "interest"
%%%

*In brief.* Rothbard concludes that a pure rate of interest can never
be zero or negative. From 2014, banks in the euro area lent to one
another overnight at a negative rate. This part rebuilds his argument.
It asks which premise such a lender fails.

Terms such as library, docstring, signature, linter, frame and
vocabulary are explained under {ref "result"}[The Result].

The argument has four steps, numbered S2 to S5. Rothbard's argument
starts one step earlier, with goods: a present good is preferred to
the same good later (*MES*, pp. 349–50). That first step would be S1. No step here uses
it, so the library does not build it. Rothbard gives an example that
fits the four steps. John Smith holds money in units of ten ounces. He weighs
each unit against money ten years from now (*MES*, p. 380). On his
scale, ten ounces in ten years rank below every unit he holds now.

Rothbard never says what Smith would buy. Some conditions depend on
it. So we give him something to buy today: a coat. The coat is ours,
not Rothbard's.

Take one unit of ten ounces. Three sums in ten years matter:

- *The promise.* It would buy then what ten ounces buy now. If prices
  stay the same, it is ten ounces. It is fixed by what it would buy,
  not by its count, because S2 compares satisfactions, not ounces.
- *A smaller sum*, say nine ounces.
- *The repayment.* This is what a loan actually pays back.

The lists below leave out bookkeeping, such as which of three stocks
a sum is drawn from. The stocks are set out under *Money*, below.

*S2: present money beats the same amount of future money.* Smith
prefers ten ounces today to the promise. This uses a first claim, time
preference (`TimePreference`): he prefers a satisfaction sooner to the
same satisfaction later. Three conditions make it the same satisfaction, and sooner:

- The promised money would buy a coat as good as today's.
  (`SamePurchasingPower`. Rising prices are one way to break it.)
- He counts the promise as the money it promises. (`PromisePays`.
  Doubt about the borrower breaks it.)
- He would spend today's ounces first. (`SpentSooner`. It breaks if he
  would keep them unspent until the promise pays.)

*S3: …and beats any smaller amount.* Smith also prefers ten ounces
today to nine in ten years. He gets there through the promise. Ten
today beats the promise, by S2. The promise beats nine. This uses a second claim: more money is
preferred to less (`MoreMoneyPreferredWhenSpent`). The claim ranks a
sum against a part of it. It ranks them as he will rank them when he
spends. And it covers only sums of money, free to hold, that would buy
different things. Six conditions go with it.

The first three let the claim rank the promise above a nine-ounce part
of it:

- Any smaller part of the promise would buy something different from
  the whole. (`BuysMoreThanItsParts`.)
- The promise is of money, not of other goods. (`MoneyFrame.Money`.)
- Holding the promise, or any part of it, costs him nothing.
  (`FreeToHoldWithin`.)

The next two carry that ranking over to any nine ounces, and to today.
The claim ranks at the spending. S3 needs a ranking today, when he
weighs the loan:

- Any nine future ounces would buy what any other nine would buy.
  (`Homogeneous`.)
- If he will rank the promise above nine when he spends them, he
  already ranks it so today. (`RankedAlikeNowOf`. The impulse man
  breaks it. Tomorrow he will rank his ounce of cash above no cash.
  Today he ranks it below, because he would rather not have the
  impulse it will buy.)

The last joins the two preferences:

- His preferences are transitive across the three sums
  (`TransitiveOn`). Ten today beats the promise, by S2. The promise
  beats nine, by the claim. So ten today beats nine.

*S4: so a loan at zero or below shows no preference.* Suppose he lent ten ounces
and got back ten, or nine. By S3, he prefers keeping his ten ounces to
that repayment. A loan shows a preference when he prefers what lending
leaves him to what refusing would have left him. Here that would be the repayment over keeping his ten ounces:
the reverse of S3's preference. A third claim, asymmetry
(`AsymmetricPreference`), says he cannot prefer each of two things to
the other. So the loan could not show a preference. S5 adds the claim
that a loan he makes does show one. Together the two say he does not
make this loan. Three conditions.
The first two make the loan a choice between exactly those two things.
The third lets S3 apply:

- Had he said no, he would have kept his ten ounces at full value.
  (`RefusalKeepsSum`.)
- After the loan, what he holds is worth what the repayment would buy,
  and no more. (`Trade.AfterCountsAsPlanned`.)
- The promise is as many ounces as he lent. (`SameCount`. The loan's
  terms count the repayment against the sum lent. S3 counts it against
  the promise. This condition joins the two counts.)

*S5: so every rate struck is positive.* This uses a fourth claim,
demonstrated preference (`DemonstratedPreference`). It is asserted of
this one loan. Lending showed a preference. Smith preferred his holding
after the loan to what refusing would have left him. Together with S4, this means a loan he
makes repays more than ten.

Rothbard's scale says more than that. His "1st unit" is the first ten
ounces Smith would give up. It ranks above eleven future ounces and
below twelve. So he would lend it for twelve, but not for eleven. The
theorem gives no rate. It says only that the repayment is more than
ten.

S5 does not assume that saying no keeps his ten ounces at full value.
It gets this from two conditions:

- The loan was voluntary. Saying no would not have cost him anything.
  (`Trade.Voluntary`.)
- Before the loan, what he held was worth what ten ounces would buy:
  the coat. (`Trade.BeforeCountsAsPlanned`.)

The second of these (`Trade.BeforeCountsAsPlanned`), and S4's second
condition (`Trade.AfterCountsAsPlanned`), join two ways of weighing. A trade is weighed as a whole holding:
everything Smith owns before or after it. That count credits a holding
with every end any of its goods is believed able to serve
(*Exchange*). S2 to S4
weigh only sums: what ten ounces, or the repayment, would buy. The two
conditions say the two weighings agree. So nothing in the holding, not
even the lent ounces or the repaid ones, may serve an end beyond what the sum, or the
repayment, would buy. And the holding must serve every end the sum, or
the repayment, would buy. If either failed, the loan
would be a choice between two holdings, not between the two sums S3
ranks.

Some apparent premises do no work, in some steps or in all:

- *At a zero rate, the second claim.* Only a negative rate needs "more
  money is preferred" (`MoreMoneyPreferredWhenSpent`). A separate
  theorem covers a loan that repays exactly the sum lent (below). It
  drops that claim. Of S3's six conditions it keeps only
  interchangeable units (`Homogeneous`). The reason: at zero, the
  repayment is as many ounces as the sum lent, and so as the promise
  (`SameCount`). Interchangeable units
  make it buy what the promise would buy. So S2 is enough, and S3 is
  not needed.
- *"The same amount", in S2 and S3.* Neither step ties the promise's
  ounces to the present sum. S2 counts nothing. S3 does conclude that
  ten today beats nine. But the one count it makes is nine against the
  promise: nine is no more ounces than the promise. Today's ten enters
  only through S2's preference, which counts nothing. Only
  the loan theorems tie the promise's ounces to the sum lent, with a
  condition of its own (`SameCount`).
- *That holding the present sum costs nothing.* No step assumes it. A
  cost of holding it reaches the loan only through refusal. (That the
  promise is free to hold is one of S3's conditions.)
- *The borrower, and the market.* Every step is about one lender.
- *Any property of the order of time, and any classical step.* No
  step uses a property of "before" (`Before`). None uses a step of
  classical logic, such as excluded middle. `#print axioms` lists only
  `propext` and `Quot.sound` on these theorems, never `Classical.choice`.

What each case breaks:

- *The bank that lent overnight at a negative rate.* It breaks one of
  two conditions. If it had no use for the money that day, it breaks
  `SpentSooner`. Or it breaks `RefusalKeepsSum`: a bank that refused
  kept the sum at a cost. It held reserves the central bank charged
  for, or banknotes that had to be guarded. S5 does not assume
  `RefusalKeepsSum`. It derives it from two other conditions: the loan
  was voluntary (`Trade.Voluntary`), and the holding before it counts
  as planned (`Trade.BeforeCountsAsPlanned`). So against S5, the same
  cost breaks at least one of those two instead. Say the bank's holding
  before the loan counted for what the sum would buy. Then refusing left
  it something other than that holding, and `Trade.Voluntary` fails.
  Say instead refusing left it just that holding. Then the holding
  counted for something other than what the sum would buy, and
  `Trade.BeforeCountsAsPlanned` fails. Splitting the cases this way is a
  classical step, and no theorem takes it. This is a reading of the
  case. No frame is built for it.
- *The Christmas club saver.* He lends at zero. The zero-rate theorem
  never covered him, because he breaks `SamePurchasingPower`. No price
  need rise for that. The condition asks that the two sums buy the
  same satisfaction. His cash would buy an impulse. The club pays for
  what he saves for. Built in the library.
- *The impulse man.* Today he would rather not hold the cash he knows
  he will spend on an impulse tomorrow. He breaks `RankedAlikeNowOf`
  (S3), comparing his cash with no cash. He is never put in a loan.
  Built in the library.
- *Rising prices, and doubt about the borrower.* Rising prices break
  `SamePurchasingPower`. Doubt breaks `PromisePays`. Both are S2's
  conditions. Each can break while the other holds. Built in the library.

The detail follows.

Interest is the fifth target: the fifth conclusion put to the test.
Rothbard builds it on time preference, so the claim tested under *Time
preference* is used here. Rothbard's conclusion is categorical: "every man’s time
preference is positive, i.e., one ounce of present money will always
be preferred to one ounce or less of future money. Therefore, there
will never be any question of a zero or negative pure interest rate"
(*MES*, p. 382). It was chosen because the world seems to have
refuted that conclusion. From 2014, banks in the euro area lent to one another
overnight at a negative rate. An overnight loan is repaid the next
day. It cannot be sold on for a gain before then. So the lender knows,
when he lends, that he will be repaid less. The question is which step
of the argument such a lender falls outside.

Rothbard's argument has four steps, rebuilt here in order:

- Present money is preferred to the same amount of future money.
- So it is preferred to that amount or less.
- So a man does not lend at a rate of zero or below.
- So every rate actually struck is positive.

The docstrings below label them S2 to S5. The rate as a market number
is not reached. Nothing here adds up lenders or finds an equilibrium.

*Money.* The vocabulary gets two more relations. One says which
units are money. The other says whether holding a sum costs anything.
Nothing else is added.

{docstring Apodictic.MoneyFrame}

The man has a plan for his money. A sum counts for what the plan buys
with exactly those units. Goods in a trade are counted differently, under
*Exchange*. There a holding counts for every end any of its goods could
serve. For money the two counts differ at once. An ounce can be spent
now or kept for later, but not both. The trade's count credits it with
both uses. The plan credits it with the one it would buy.

Three stocks are weighed at the date of the loan:

- the present money;
- the promises of future money, counted as he counts them today (a
  promise he doubts counts for something other than the money it
  promises);
- the money promised, as he would spend it if he had it in hand.

A theorem takes a sum from each: the present sum (the sum lent, in the
loans), the promise, and the money it promises. (The three future sums at the top of this part, the
promise, the smaller sum and the repayment, all come from the second
stock.) S2's first two conditions compare them.
`SamePurchasingPower` compares the present sum with the money
promised. `PromisePays` compares the promise with the money promised.

*Present money over future money.* Rothbard: "It follows from the
law of time preference that present money is worth more than present
expectations of the same amount of future money" (*MES*, p. 376). It
does follow, but not from the amount.

{docstring Apodictic.PureInterest.present_sum_preferred}

The three conditions:

{docstring Apodictic.SamePurchasingPower}

{docstring Apodictic.PromisePays}

{docstring Apodictic.SpentSooner}

This step has three findings.

*The number of ounces does no work.* Equal counts are the same good at
two dates only if they buy the same thing. That is what the proof
uses. So none of the conditions above says the sums are the same
amount. The count enters later. There "repaid no more than lent" has
to be compared with a promise. The count is a condition of its own
(`SameCount`). (`SamePurchasingPower` and `PromisePays` once each held
an equality of counts that this step never used. The linter checks
whole assumptions, not their parts. So it could not see that. The
counts were moved out by hand.)

*Two things a reader might merge are kept apart.* One is that the
money will buy as much later. Rising prices break it. The other is
that the promise will pay. A risk of default breaks it. Each has its
own name, so a failure points at one of them. A frame shows this. It
has one agent, with an ounce and a promise of one. Each condition
fails while the other holds. The two could be merged into one
condition. It would use the same definition, `SamePurchasingPower`,
but compare the cash with the promise itself, not with the money
promised. Call it the merged condition. It fails the same way in both
cases. So it cannot say
which happened:

{docstring Apodictic.Model.CertaintySplit.doubt_power_but_not_pays}

{docstring Apodictic.Model.CertaintySplit.inflation_pays_but_not_power}

{docstring Apodictic.Model.CertaintySplit.merged_fails_in_both}

*Holding.* What the step needs is that the present sum would be
*spent* sooner. That holding it costs nothing is in no signature. No
step uses it. A theorem that listed it would fail the linter. (A
cost of holding cash does reach the loan theorems, by another road. It
enters through the condition that refusing a loan leaves the sum at
full value, below.)

Rothbard's footnote dismisses the man who would keep the money for
later, as "not the issue here, which is one of availability for use"
(*MES*, p. 386 n. 11). Suppose that man would spend the present sum on
the same thing, at the same date, as the promise. Then the two sums
buy the same bundle. Preferring one to the other would be preferring a
bundle to itself. Asymmetry forbids that. So neither sum is strictly
preferred, and S2's conclusion fails for him. The footnote does not
give him the strict preference back. He is the man for whom
`SpentSooner` fails.

*A rate of exactly zero.* The order of the steps hides one thing. A
loan that repays exactly the sum lent demonstrates no preference. Of
the claims, it needs only time preference and asymmetry. It does not
need "more money is preferred":

{docstring Apodictic.PureInterest.no_loan_at_zero_rate}

Three conditions tie the trade to the sums. The first says what
refusing would have left the lender. The second says what lending left
him. The third compares the promise's count with the sum lent:

{docstring Apodictic.Trade.RefusalKeepsSum}

{docstring Apodictic.Trade.AfterCountsAsPlanned}

{docstring Apodictic.SameCount}

"More money is preferred" is the claim the next step needs. It is
spent on one thing only: ruling out a *negative* rate.

*One ounce or less.* "Or less" needs a second claim. Rothbard:
"\[T\]o both present money and future money there applies the general rule that
more of a good will have greater utility than less of it" (*MES*,
p. 379). It is the tenth claim under *The claims*. Its docstring there
gives the reasons it is narrower than Rothbard's rule. Two of them are
findings of the build.

*The first is satiation.* Read as Rothbard states it, the rule ranks
the larger sum above the smaller, whatever each would buy. It still
ranks them so even when it is cut to money free to hold, and to sums one part
of the other:

{docstring Apodictic.PureInterest.MoreMoneyPreferredUnrestricted}

Suppose the larger sum would buy exactly what the smaller buys. Then
the rule has the man prefer a bundle to itself. Asymmetry forbids
that, and the loan theorems carry asymmetry. So the rule, with
asymmetry, says that every extra unit of free money changes what the
sum would buy. Money never satiates.

{docstring Apodictic.PureInterest.buysMore_of_unrestricted}

Mises denies that money never satiates, for the cash a man holds: "He who says that his thirst for more money can never be
quenched, does not mean to say that his cash holding can never be too
large. What he really means is that he can never be rich enough"
(*Human Action*, ch. XVII, §3). Rothbard agrees that "effective demand
for money is not and cannot be unlimited" (*MES*, p. 773). So the
claim here ranks only sums that buy different things. A condition says
that every part of the larger sum buys something other than the whole
(`BuysMoreThanItsParts`):

{docstring Apodictic.BuysMoreThanItsParts}

*The second is time.* The plan says what the man would buy with a sum.
He would buy it when he spends it, by his valuations then. A man may
know what he would do with money in hand. Then today he may prefer to
get less later, because of what he would buy with more. Rothbard's
rule, ranked today, says he cannot:

{docstring Apodictic.PureInterest.MoreMoneyPreferredNow}

The library builds this man. He has one ounce, which he would spend on
an impulse tomorrow. Today he would rather not have the impulse.
Tomorrow he will want it. Asymmetry holds at both dates. Tomorrow
he prefers the ounce to nothing. So the claim ranked at the spending
holds of him. The claim ranked now does not:

{docstring Apodictic.Model.Impulse.now_reading_fails}

So the claim here is dated at the spending. The step from then to now
is a condition. The theorems ask it of the one comparison the proof
makes: the promise against the sum repaid. The impulse man is never
put in a loan. But he fails the same condition, asked of his ounce
against no cash:

{docstring Apodictic.RankedAlikeNowOf}

{docstring Apodictic.Model.Impulse.not_rankedAlikeNow}

The frame's preferences are written by hand for the case. The frame is
built only to separate the two readings. Asymmetry and the dated claim
hold in it, and the undated reading fails. Not every claim holds in
it: time preference, for one, does not. Whether a given saver is such
a man is a question about him. A saver who locks his money in a
Christmas club looks like one. The club holds his money until just
before the holidays. But the club case below needs only a failure of
`SamePurchasingPower`.

Mises's own account of action has room for this man. A valuation that
changes is not a lapse from action: "If the valuations change, acting
must change also" (*Human Action*, ch. V, §4). His change of valuation
breaks this condition (`RankedAlikeNowOf`).

The rest of what "or less" takes:

- the promise's parts are free to hold;
- his preferences are transitive across the three sums compared;
- the promise is a promise of money;
- the future units are interchangeable (`plan.Homogeneous`, under *The
  conditions*).

{docstring Apodictic.FreeToHoldWithin}

{docstring Apodictic.ActionFrame.TransitiveOn}

{docstring Apodictic.PureInterest.present_sum_preferred_to_less}

*No loan at zero or below, and every rate struck positive.* The last
theorem does not assume that refusing leaves the lender the sum. It
derives this. In place of the refusal condition it takes two others:

- The trade was voluntary (`Trade.Voluntary`).
- His holding before the trade counts as planned
  (`Trade.BeforeCountsAsPlanned`).

{docstring Apodictic.PureInterest.no_loan_at_nonpositive_rate}

{docstring Apodictic.Trade.BeforeCountsAsPlanned}

{docstring Apodictic.PureInterest.struck_rate_positive}

```lean (name := manifestStruck)
#manifest PureInterest.struck_rate_positive
```
```leanOutput manifestStruck
manifest of Apodictic.PureInterest.struck_rate_positive

  praxeological claims:
    timePreference : TimePreference praxis.toDatedFrame exchange.first.agent exchange.first.time
    moreMoney : MoreMoneyPreferredWhenSpent futurePlan spend
    asymmetric : AsymmetricPreference praxis.toActionFrame exchange.first.agent exchange.first.time
    demonstrated : DemonstratedPreference exchange.first

  situational conditions:
    power : SamePurchasingPower presentPlan promisedPlan sum money soon late
    pays : PromisePays futurePlan promisedPlan promise money
    sooner : SpentSooner soon late
    count : SameCount sum promise
    promiseIn : promise ⊆ future.units
    repaidIn : repaid ⊆ future.units
    homogeneous : futurePlan.Homogeneous
    alike : RankedAlikeNowOf futurePlan spend promise repaid
    buysMore : BuysMoreThanItsParts futurePlan promise
    isMoney : ∀ unit ∈ promise, praxis.Money unit
    free : FreeToHoldWithin promise
    chain : praxis.TransitiveOn exchange.first.agent exchange.first.time ↑(presentPlan.wouldServe sum)
  ↑(futurePlan.wouldServe promise) ↑(futurePlan.wouldServe repaid)
    voluntary : exchange.first.Voluntary
    before : exchange.first.BeforeCountsAsPlanned presentPlan sum
    after : exchange.first.AfterCountsAsPlanned futurePlan repaid

  vocabulary (what the claims are about):
    praxis : MoneyFrame
    exchange : Exchange praxis.toActionFrame
    present : Stock praxis.toActionFrame exchange.first.agent exchange.first.time
    future : Stock praxis.toActionFrame exchange.first.agent exchange.first.time
    promised : Stock praxis.toActionFrame exchange.first.agent exchange.first.time
    presentPlan : AllocationPlan present
    futurePlan : AllocationPlan future
    promisedPlan : AllocationPlan promised
    sum : Finset praxis.Means
    promise : Finset praxis.Means
    money : Finset praxis.Means
    repaid : Finset praxis.Means
    soon : praxis.End
    late : praxis.End
    spend : praxis.Time

  conditions carried by the vocabulary (not binders: discharged by
  whoever supplies the argument):
    exchange.swap_gives : exchange.second.gets = exchange.first.gives
    exchange.swap_gets : exchange.second.gives = exchange.first.gets
    present.unitsAlike : ∀ unit ∈ present.units,
  ∀ (want : praxis.End), praxis.Believes exchange.first.agent exchange.first.time unit want ↔ want ∈ present.serves
    future.unitsAlike : ∀ unit ∈ future.units,
  ∀ (want : praxis.End), praxis.Believes exchange.first.agent exchange.first.time unit want ↔ want ∈ future.serves
    promised.unitsAlike : ∀ unit ∈ promised.units,
  ∀ (want : praxis.End), praxis.Believes exchange.first.agent exchange.first.time unit want ↔ want ∈ promised.serves
    presentPlan.servesOnlyWhatItCan : ∀ (subStock : Finset praxis.Means), ∀ want ∈ presentPlan.wouldServe subStock, want ∈ present.serves
    futurePlan.servesOnlyWhatItCan : ∀ (subStock : Finset praxis.Means), ∀ want ∈ futurePlan.wouldServe subStock, want ∈ future.serves
    promisedPlan.servesOnlyWhatItCan : ∀ (subStock : Finset praxis.Means), ∀ want ∈ promisedPlan.wouldServe subStock, want ∈ promised.serves

  logical background: [propext, Quot.sound]
```

Four claims carry it: time preference, "more money is preferred",
asymmetry, and demonstrated preference. The last is stated of the
lender's trade. The borrower contributes nothing. The result about
rates *struck* is about each lender. It says nothing about a market.
No borrower who would pay a positive rate is shown to exist.

*What the order of time was asked for.* Nothing, as under *Time
preference*. No proof here uses a property of the relation "before".
None needs a classical step. The one case split is on the size of a
sum.

*The case.* The library builds one frame to show that the theorem is
not empty: all its claims and conditions can hold at once. A lender
has a use for an ounce now. He lends it to be repaid two at the next
date. Every claim and condition of the last theorem holds.

{docstring Apodictic.Model.Loan.struck_rate_positive_applies}

The test is thin, and here is where:

- The lender's ranking does not change with the date. So `RankedAlikeNowOf`
  holds trivially.
- The money promised is the promises' own stock. So `PromisePays` is
  never tried on a promise that might not pay.
- Every unit counts as money, and every sum is free to hold. So
  neither of those conditions is tried (`MoneyFrame.Money`,
  `FreeToHoldWithin`).
- Preference is transitive throughout the frame, not only across the
  three sums.
- The promise is one unit. So `BuysMoreThanItsParts` compares it only
  with no units.
- There is one agent, lender and borrower both.

*What a failure would point at.* Suppose a man lends and is repaid
less. The theorem for a rate not above zero then says one of two
things. Either his trade did not demonstrate a preference for being
repaid over keeping the sum, or one of the theorem's assumptions
failed. These
are the ones a case is likely to land on:

- The money would buy less at repayment (`SamePurchasingPower`).
- He doubted the promise would pay (`PromisePays`).
- He had no use for the sum before the promise paid (`SpentSooner`).
- Refusing would not have left him the sum at full value, because
  keeping cash cost him something (`RefusalKeepsSum`). (In the last theorem this condition
  is derived, not assumed. It comes from the trade being voluntary and
  his holding counting as planned. So there the failure lands on one of
  those.)
- An extra unit of the promise bought nothing more
  (`BuysMoreThanItsParts`).
- He ranked the promise against the repayment differently now than at
  the spending (`RankedAlikeNowOf`).
- The promise was not of money, or not free to hold (`MoneyFrame.Money`,
  `FreeToHoldWithin`).
- His preferences were not transitive across the three sums
  (`TransitiveOn`).
- One of the claims failed.

That theorem's manifest has a few more that a case is less likely to
land on. The
promise and the repayment come from the stock of promises. The promise
is as many units as the sum lent (`SameCount`). The future units are
interchangeable (`Homogeneous`). What he holds after counts as planned
(`Trade.AfterCountsAsPlanned`).

The bank that lends overnight at a negative rate is likely to land on
two of these. One is `SpentSooner`. The bank may have had no use for the money
before repayment, a day later. Then the theorem says nothing more
about the bank. The other is `RefusalKeepsSum`. Refusing would not
have left the bank the sum at full value. A bank that refused kept
the sum as reserves at the central bank, which charged for them. Or it
kept banknotes, which have to be guarded. Either failure takes the
bank outside the theorem. Neither is shown here to be the only way
out.

Rothbard's own terms give an Austrian a reply to part of this. He
never applied it to negative rates. A deposit of present money is like
goods left in a warehouse. Redeeming it "is not the completion
of a transaction or equivalent to a creditor’s calling his loan; it is
a simple repossessing of a man’s own good" (*MES*, p. 800). The man who
deposits goods "pays the owner of the warehouse a certain sum for the
service of storage. He still retains ownership of the property; the
owner of the warehouse is simply guarding it" (*MES*, p. 801). On that
reading, a negative rate on a deposit is a fee for safekeeping. It is
not interest at all. The theorems never applied to it.

The reply does not reach the loan between two banks. That loan is a
promise of money tomorrow: a credit transaction, on Rothbard's own
terms. But the fee does reach the lender's refusal. It is what keeping
the sum would have cost. For banknotes the cost is plainly one of
keeping the sum safe. It is a price for guarding, not for time.

For reserves, it turns on what the central bank's overnight deposit
is. If it is a warehouse, its charge is a fee for safekeeping. If it
is a loan, its charge is a negative rate in its own right. That is
left open here. Nothing rests on it, because the charge did not stop
at that deposit. From June 2014 the same charge also fell on a bank's
excess reserves. These are the reserves it held above the required
minimum, in its ordinary account at the central bank. Those reserves
do not stand for money stored elsewhere. They are the money itself, as
banknotes are. So for them the question of what the deposit is does
not arise. Wherever a bank that refused the overnight loan kept the
sum, keeping it cost something. So `RefusalKeepsSum` fails. All of this
is a reading of the case, not a frame built for it.

Where a man lends at exactly zero, the list is shorter. It drops the
claim that more money is preferred, and the five conditions that come
with it.

The Christmas club saver lends at zero. The zero-rate theorem does not
reach him, because one of S2's conditions fails at once. A sum counts
for what he would buy with it. The cash in his hand would buy an
impulse. The club pays for what he saves for. Those are not the same
satisfaction. So `SamePurchasingPower` fails. It fails between his
cash and any money the club's promise pays in. The library builds him
too, with every claim holding:

{docstring Apodictic.Model.ChristmasClub.zero_rate_with_every_claim}

{docstring Apodictic.Model.ChristmasClub.outside_zero_rate}

In this frame a sum of cash would buy one end, however large. So the
frame cannot show him preferring less cash to more. That case is the
impulse man's, above, who breaks `RankedAlikeNowOf`.

# The horses in Lean
%%%
tag := "horses-lean"
%%%

Terms such as library, claim, condition and frame are explained under
{ref "result"}[The Result].

This is the case set out under {ref "horses"}[The horses], built in
Lean. It does a second job at the same time. It shows that the law, in
its chain form, is not empty. A theorem is not empty when all its
claims and conditions can hold at once. If they could not, the theorem would be
true only because nothing ever meets them. Rothbard's own six horses
meet them all. The man's plan satisfies swap dominance
(`SwapDominant`, explained under {ref "finding"}[The finding]). And
the horses meet every condition of the law's chain form, the form
along a chain of named horses (`marginal_utility_chain`, under
{ref "theorems"}[The theorems]).

Wants are ranks on the man's value scale. The smaller rank number is
the more urgent want:

{docstring Apodictic.Model.rankPrefers}

The man's plan is the obvious one. With any `n` horses he would serve
the `n` most urgent wants. This plan satisfies swap dominance
(`SwapDominant`). The proof is the last theorem on this page. Five
more things hold here. The first three are the chain form's
conditions:

- Wants can be told apart (`DecidableEq praxis.End`). For any two
  wants, whether they are the same want can be decided.
- Uses are independent (`IndependentUses agent time`, under
  {ref "conditions"}[The conditions]). Here the horses' jobs do not
  complement one another.
- One-horse steps exist inside the stable (`stock.OneMore`). A set of
  `n` of his horses lies inside a set of `n + 1`, and both lie inside
  the stable. The chain form takes two such steps, one after the
  other: from `n` horses to `n + 1`, then from `n + 1` to `n + 2`. Its
  conclusion compares them. Every want the first step adds is
  preferred to every want the second step adds.

The other two are not conditions of the chain form:

- Each step has a marginal end (`horses_marginal_nonempty`). Going
  from `n` horses to `n + 1`, the plan serves one more want, rank
  `n + 1`. That want is the step's marginal end: served with the larger
  set, not with the smaller. The law's conclusion speaks of every want
  a step adds. So this shows it speaks of actual wants here, not of
  none.
- Preference is asymmetric (`AsymmetricPreference`).

Asymmetry is a claim, one of {ref "claims"}[The claims]. If he
prefers one bundle to another, he does not prefer the second to the
first. It is the strict reading of preference, and preference is
meant as strict throughout. The chain form does not take it. It is
proved of this frame (`horses_asymmetric`) for another reason. It
shows that the two claims can hold together here: swap dominance
(`SwapDominant`) and asymmetry. The rival-plan theorem
(`no_rival_swap_dominant`, under {ref "theorems"}[The theorems]) takes
both. It says this. Take a rival plan for the same stable. At one set
of horses, it differs from his by a single swap. Then the rival does
not also satisfy swap dominance. The rival is constrained at that one
set of horses only. No theorem here applies the rival-plan theorem to
the horses.

Most theorems here only check that the horses meet one hypothesis or
another. Two do more. They are conclusions Rothbard reached himself.
The first is his result at p. 25:

{docstring Apodictic.Model.loss_of_a_horse_ends_pleasure_riding}

The second is the point he names two horses to make. It is also the
reason the plan is encoded the way it is:

{docstring Apodictic.Model.which_horse_does_not_matter}

And the last step is the point:

{docstring Apodictic.Model.horses_law_applies}

That settles the chain form. The size-based form, by the size of the
supply (`marginal_utility`, under {ref "theorems"}[The theorems]),
asks for one thing more: interchangeability (`plan.Homogeneous`). The
horses meet that too:

{docstring Apodictic.Model.horses_homogeneous}

But no theorem here applies the size-based form to them. That would
take one more theorem, and it has not been built. So this page shows
only the chain form not empty.

One step above was taken on trust: that the man's plan satisfies swap
dominance. Here is its proof. `horses_swapDominant` proves
`SwapDominant (horsePlan k)`, where `horsePlan k` is the man's plan
for a stable of `k` horses. That is exactly the hypothesis
`marginal_utility_chain` takes (`dominance`), and
`horses_law_applies` hands it over as it stands. So nothing was
copied across by hand. A hand copy would be a second statement of swap
dominance, written out for the horses. It could differ from the
hypothesis the law takes. Then the horses would be shown to meet
something other than that hypothesis. Here there is no second
statement.

{docstring Apodictic.Model.horses_swapDominant}

The model departs from Rothbard in two places. Both are said out loud
rather than papered over.

- *No ceiling on the scale.* His ten ends are "for simplicity", to fit
  a diagram. A ceiling would drag an extra condition through every
  theorem, and it would gain nothing: without one, his six horses
  still serve the first six ends, as in his case. So here the horses
  can serve any rank.
- *Which earlier horse is Man o' War is arbitrary.* Rothbard calls
  Seabiscuit "the sixth horse that he had previously acquired". He
  says only that Man o' War "had arrived earlier" (*MES* p. 27). So
  any earlier horse will do. Here the horses are numbered 0 to 5.
  Seabiscuit is horse 5 and Man o' War is horse 1. What the plan
  serves depends only on how many horses there are
  (`horses_homogeneous`). A horse's
  number serves only to tell horses apart. Nothing else about a horse
  enters any theorem here.

# The vocabulary
%%%
tag := "vocabulary"
%%%

Reference. These are the definitions the statements above are written
in. Nothing earlier depends on having read them.

Terms such as library, claim, condition and frame are explained under
{ref "result"}[The Result]. What the audit turned up, its findings, is
under {ref "finding"}[The finding] and
{ref "other-findings"}[The other findings].

The basic vocabulary is deliberately bare. Preference is just a
relation. It is not assumed transitive. It is not assumed to rank
every pair. Time is not assumed ordered. Properties get added when a
theorem forces them. So far one has been added as a claim: asymmetry
(`AsymmetricPreference`, under {ref "claims"}[The claims]). It says
that if an agent prefers one bundle to another at a time, he does not
also prefer the second to the first. Others enter as conditions of
particular theorems. Six theorems in the library use asymmetry:

- The theorem relating the two routes uses it
  (`Contrast.rothbard_entails_servedInOrder`), under
  {ref "mises-route"}[Mises's route].
- The rival-plan theorem uses it (`no_rival_swap_dominant`), under
  {ref "theorems"}[The theorems].
- Four theorems under {ref "interest"}[Interest] use it: the three
  loan theorems, and the check on the unrestricted rule
  (`PureInterest.buysMore_of_unrestricted`).

{docstring Apodictic.ActionFrame}

{docstring Apodictic.ActionFrame.PrefersEnd}

The law of marginal utility is about a stock of units and what the
agent would do with more or fewer of them.

The plan below, and an allocation further down, are each set against
an action (`Action`). An action is one agent, at one time, using means
he believes will bring about one chosen end. By acting he gives up at
least one other end. Its definition is shown under *Claims no theorem
uses*.

{docstring Apodictic.Stock}

{docstring Apodictic.AllocationPlan}

Two conditions sit a level down, inside the structures the theorems
take as arguments. They are fields of the stock, of the plan, and, on
the history reading, of an allocation. That reading is under
{ref "ladder-history"}[The ladder as a history].

- `servesOnlyWhatItCan` is a field of the plan and of an allocation.
  It says no unit is put to a job the man does not believe the good
  can do.
- `unitsAlike` is a field of the stock. It says every unit is believed
  to serve exactly the ends the good can serve, by his lights
  (`stock.serves`). So once a stock holds at least one unit,
  `unitsAlike` fixes `stock.serves`: it is the set of ends each unit
  is believed to serve.

Three claims quantify over those ends (see {ref "claims"}[The claims]).
Two are the claims of the two routes: swap dominance (`SwapDominant`)
and serving in order of urgency (`ServedInOrder`). The third is acting
in order of urgency (`ActsInOrder`), the claim of the history reading.
So, in a stock with at least one unit, `unitsAlike` fixes the ends
these claims speak of. (With no units it says nothing, so it fixes
nothing.) That is the work it does, though no proof uses it (see
below).

Neither condition is a binder in any statement: a binder is one thing
a statement takes as an argument (see {ref "manifest"}[The manifest]).
Each is a field inside such an argument: `unitsAlike` inside the
stock, `servesOnlyWhatItCan` inside the plan or the allocation. So
neither condition appears in the signature. Lean builds no stock
without a proof of its `unitsAlike`, and no plan or allocation without
a proof of its `servesOnlyWhatItCan`. So whoever supplies one has
already discharged its condition, that is, proved it. Both conditions
are still assumptions the theorems rest on. So `#manifest` reads one level in
and reports them, and they are not hidden.

The two are not alike, and the manifest does not pretend otherwise:

- Take a plan that puts a horse to a job the man does not believe a
  horse can do. That is not a situation that might obtain. It is an
  incoherent plan. So `servesOnlyWhatItCan` assumes nothing about the
  world. The same field on an allocation is said of what he did. It
  assumes nothing either.
- A lame horse is a situation that might obtain. Say the man does not
  believe it can do a job he believes his other horses can do. Then
  his units are not believed to serve the same ends, and `unitsAlike`
  fails. So `unitsAlike` does assume something about the world.

Whether a carried condition assumes something about the world cannot
be read off its statement in Lean. It is a judgement about the world,
so `#manifest` cannot make it (see {ref "manifest"}[The manifest]). It
is made by hand, and the two bullets above are that judgement.

A third condition used to sit here, and now sits nowhere: one unit to
one end. That can fail of a real stable. Two horses can pull one
wagon, or a horse can stand idle. So it could not stay a field.
Taking it out showed that no theorem wants it. So it was not made a
hypothesis either. See *The other findings*.

`unitsAlike` can fail too, yet it stays a field. The library's reason
is that it cannot be made a hypothesis. No theorem's proof uses it, so
as a hypothesis it would fail the unused-argument linter. Marking it
with `_` would record that it does no work. But it does work: it fixes
the ends the three claims above speak of. So it stays a field, and
`#manifest` reports it.

Interchangeability of units is *not* hidden down there. The plan is
indexed by which exact units the man holds. That it depends only on
how many of them there are is a separate named condition
(`AllocationPlan.Homogeneous`). It is given in full under *The
conditions*, along with the other conditions.

The history reading is under
{ref "ladder-history"}[The ladder as a history]. It puts an actual
allocation (`Allocation`) where the plan was. It reads the supply
growing (`Stock.Grows`) as something that happened. Yet no theorem
carries `Stock.Grows`:

- The ladder judged on the earlier scale (`Temporal.ladder_judged_earlier`)
  does not need the growth. Added to that theorem as a hypothesis, the
  growth fails the unused-argument linter. The theorem's earlier scale
  is the ranking he held at the moment the theorem calls earlier
  (`earlierTime`). Nothing in the theorem orders its two times.
- The ladder judged on the later scale is written out as a statement
  (`Temporal.LadderJudgedLaterFromOrder`). That statement takes the
  growth as a hypothesis. It is the only one that does. A counter-model
  shows it false (`Model.later_judged_ladder_fails`).

{docstring Apodictic.Allocation}

{docstring Apodictic.Stock.Grows}

The words of exchange are defined under *Exchange*, where they are
used: a trade, an exchange, and what a holding counts for. The dates
time preference needs are defined under *Time preference*: a bare
"before", the time an end is attained, and which ends are the same
satisfaction. The frame above has none of them.

# Claims no theorem uses


Terms such as library, claim and frame are explained under
{ref "result"}[The Result].

One statement at the centre of the doctrine is carried by no theorem
here. It is that there is any action at all. The library writes it
down as a definition (`Mises.ActionOccurs`). A definition only names
the statement. It does not assume it true. No claim in
`Praxeology.lean` asserts it, and no theorem takes it as a hypothesis.
So it is not one of the claims under {ref "claims"}[The claims]. A
claim is added there only when some theorem first needs it.

The doctrine that people act splits into three here (see
{ref "other-findings"}[The other findings]). The existence statement
above is one of the three. The other two, demonstrated preference and
the definition of action, follow in turn.

Demonstrated preference in Rothbard's sense (`DemonstratedPreference`)
is the bridge from what a man actually does to what he prefers. It is
one of the claims under {ref "claims"}[The claims]. Rothbard states it
of any action. Here it is asserted only of the one trade a theorem is
handed. So the claim does not say that every act demonstrates
preference. Theorems in three parts carry it:

- *Exchange* (`MutualBenefit.reverse_valuations` and the other exchange
  theorems).
- *The regression theorem* (`Regression.indirect_ranks_onward_ends`).
- *Interest* (`PureInterest.struck_rate_positive`).

Action itself is a definition here (`Action`). No derivation of the
law of marginal utility uses it. The law is quoted under
{ref "horses"}[The horses]. Each author's argument for the law is
here called a route (see {ref "result"}[The Result]). On each route,
the claim the law needs is about a plan: what the man would do with
every part of his stock, settled in advance. It is not about anything
he does. The case is made under {ref "finding"}[The finding].

Other theorems do take an action. Two theorems under
{ref "time-preference"}[Time preference] do
(`TimePreference.consumption_reveals`, `TimePreference.regress`). The
claim they carry, demonstrated time preference
(`DemonstratedTimePreference`), is stated of one action.

The existence statement appears in one test: of Mises's dilemma. The
dilemma is his argument for the law, set out under
{ref "mises-route"}[Mises's route]. Its second horn is that there
could be only one action. Mises rejects that horn by appeal to the
existence statement. A frame with exactly one action
(`Model.Solitary`) tests the appeal. In that frame there is action,
and there is at most one action. So the existence statement cannot
rule out that there is only one action. What his step needs is that
action is plural: that two distinct actions occur
(`Mises.ActionRecurs`). The library names that too as a definition
and asserts it nowhere. One theorem takes it as a hypothesis and
refutes the second horn with it (`Mises.recurs_refutes_second_horn`).

{docstring Apodictic.Action}

