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

Mises held that the theorems of praxeology carry apodictic certainty:
that they follow from the fact of human action as necessarily as a
theorem of mathematics follows from its axioms, and that no
experience could overturn them. This puts one such theorem to a proof
assistant — Rothbard's law of marginal utility, derived in Lean 4.

A proof assistant refuses an enthymeme. Whatever a verbal derivation
passes over in silence has to be written down before the proof will
close, and it has to be written down in the theorem's own statement —
as a hypothesis, or in the type of one. The audit surface is therefore
bounded and mechanical: read the statement, and read the definitions
its parameters name. Some claims sit one level down, as fields of a
structure the theorem takes, but none is off the page. Nor is the list
padded: `#lint only unusedArguments` fails the build on anything
standing there that the proof never uses. That is the whole reason for
doing this in a machine.

Every docstring here is pulled from the library at build time. What
you read is what was checked.

# The finding

The law of marginal utility needs exactly one praxeological premise,
and that premise is not about action.

It is about what the agent *would* serve with each sub-stock of the
units on hand: a disposition across supplies the agent does not have,
rather than a choice the agent makes. Rothbard's own premise fuses
two claims into one sentence — that action employs the means, and
that the wants served are "the most urgent of the not yet satisfied
wants" (*MES* p. 24). Only the second half does any work here, and it
does that work subjunctively, extended across supplies exactly as his
own derivation extends it: he sets a stock of six horses beside a
stock of five and asks which want "the larger stock would have
satisfied" (p. 25). No single actual allocation delivers that
comparison.

The collision this produces is internal to Rothbard. His own
restriction is that praxeology "may deal with utilities only as
deduced from the concrete actions of human beings" (*MES* p. 882
n. 8), and the premise his law requires is not one that restriction
admits.

It bites a second time, in a place usually discussed on its own. The
law is expected to founder on units: stating it by supply size seems
to need units the agent values equally, and Rothbard denies that
indifference is ever demonstrated in action. In this encoding it does
not founder there. Indifference between units is asserted nowhere,
and the law survives without it. What the supply-size form needs
instead is only that the plan ignore *which* units — and that
condition, too, ranges over sub-stocks the agent does not hold. So
the restriction excludes both the premise the law is derived from and
the condition that makes its usual statement well-formed.

Twice, though, and not once: the two are different claims, and the
encoding keeps them apart. The premise is a commitment, carried on
the signature of every theorem that uses it, and if it is false the
law is false. The condition is a hypothesis of one theorem, and where
it fails the law is silent rather than false. Which of the two has
given way in a particular case is exactly what an audit like this is
for.

None of this refutes the law. Lean certifies that the derivation is
valid and that it uses nothing beyond what its statement carries. What
is in question is the pedigree of the one thing it starts from.

# Vocabulary

The primitive vocabulary is a bare structure. Nothing in it has any
property — no transitivity, no totality, no order on time. Strength
is added when a theorem forces it, and so far none has.

{docstring Apodictic.ActionFrame}

{docstring Apodictic.ActionFrame.PrefersEnd}

The law is about a stock of units and what the agent would do with
more or fewer of them.

{docstring Apodictic.Stock}

{docstring Apodictic.AllocationDisposition}

One commitment travels a level down, as a field rather than a
hypothesis: `card_eq` is Rothbard's "we assume for simplicity"
(p. 26) — one unit, one end, no idle units. Every theorem below takes
`A : AllocationDisposition s`, so the claim is on the page; it is read
from the type of a parameter rather than from the hypothesis list, and
that is the one place an audit has to look past the signature.
Interchangeability of units is not down there. The plan is indexed by
*which* units, and that it depends only on how many is the named
condition below.

{docstring Apodictic.AllocationDisposition.Homogeneous}

{docstring Apodictic.Stock.OneMore}

# Commitments

The library declares no `axiom`. Every praxeological claim is a
structure, and a theorem that needs one takes it as a named
hypothesis; what a theorem rests on is read off its signature. That
every claim listed there does real work is enforced by `#lint only
unusedArguments`, which fails the build on a hypothesis the proof
never uses. The linter can be silenced, so leaving it on is a policy
and not a theorem. It is never silenced here.

Each commitment carries three fields. *Source* is a citation, or
"tacit". *Status* is one of three verdicts: explicit-in-tradition
(Rothbard or Mises say it), suppressed-premise (they use it without
saying it), or our-reconstruction (a decision the tradition never
faced). *Does not say* lists the nearby stronger claims it
deliberately omits.

Two rules govern the list. A commitment enters at the point of first
use, so nothing appears that no theorem carries. And only
claimed-universal facts about action are commitments; conditions
under which a law applies are hypotheses of the theorem, below.

There is exactly one.

{docstring Apodictic.SwapDominant}

# Hypotheses

The theorems take three hypotheses beyond the commitment. Each is a
situational condition rather than a universal claim, and each stands
in the statement so that it can be pointed at when it fails. Where
one fails the law is silent, not refuted.

- `s.OneMore U V`: the sub-stocks compared are on hand and differ by
  one unit. The disposition is data only there, and the law holds
  only there.
- `IndependentUses agent t`: the value of an end does not depend on
  which other ends are served.
- `A.Homogeneous`: the plan depends only on how many units, not
  which. Needed by the supply-size form of the law alone.

Which plan is the agent's needs no hypothesis of its own. The
theorems speak of the plan they are handed and the commitment is
asserted of that plan, so there is nothing quantified over rival
plans for a rival to refute.

{docstring Apodictic.ActionFrame.IndependentUses}

# Theorems

Rothbard's urgency principle — that the loss of a unit falls on the
least urgent want — is a theorem here rather than a premise. The
commitment delivers something stronger than the principle, so that
workhorse is stated first.

{docstring Apodictic.served_over_unserved}

{docstring Apodictic.urgency_principle}

The law is stated over Rothbard's own definition of the marginal
utility of a supply: the ends that would be given up on the loss of
one unit. It comes in two forms. Along a chain of named units it
needs no interchangeability; in Rothbard's wording, by supply size,
it does.

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

`propext` and `Quot.sound` are Lean's logical background. They arrive
with the ordinary mathematical vocabulary the statement is written in,
not with anything praxeological: mathlib's finite sets bring both, and
so does extensionality of sets. `Classical.choice` is absent — no
proof here closes a goal by helping itself to the principle that every
proposition is decided. The case splits the proofs do make run on
decidable equality of ends, which is why that travels as a declared
condition on the frame rather than as a silent convenience. That the
library adds nothing to Lean's logic is what this output is for, and
all it says.

The praxeological content is in the statement. The law carries one
commitment, `SwapDominant A`; three situational conditions,
`IndependentUses`, `A.Homogeneous` (the supply-size form only), and
the sub-stocks being on hand; and one data condition on the frame,
`[DecidableEq F.End]`. The urgency principle and the chain form carry
the same list less `Homogeneous`.

# Consistency

Consistency is not a side-question here: it is an instance. Build a
frame, a stock and a plan, prove the plan swap-dominant, and hand the
whole thing to the theorem. If that type-checks, the commitment and
the conditions are jointly satisfiable and the law is not vacuous.
The frame is `Apodictic.Model.Toy` — one agent, one instant, numbers
for ends — and this is its preference:

{docstring Apodictic.Model.swapPrefers}

In it, the plan that serves the most urgent ends, as many as there
are units, is swap-dominant and homogeneous; ends are decidable, uses
are independent, one-unit steps exist within the stock, each step has
a marginal end, and preference is asymmetric. So the commitment has a
model with strict preference — the reading intended throughout, and
what `no_rival_swap_dominant` needs.

The last step is the point:

{docstring Apodictic.Model.toy_law_applies}

That is the law itself, at the toy frame, with every hypothesis
discharged. Nothing is transcribed: `toy_swapDominant` proves the
same proposition the theorem consumes.

# Not in the base

Two doctrinally central claims are cited by no theorem and are
therefore not commitments. The bridge from actual action to
preference — demonstrated preference in Rothbard's sense — is stated
here in the form it would take, and parked:

```lean
/-- PARKED: the bridge from actual action to preference. Carried by
no theorem; lives in the document, not the library. -/
structure DemonstratedPreference (F : ActionFrame) : Prop where
  bridge : ∀ a : Action F, ∀ e ∈ a.forgone,
    F.Prefers a.agent a.time {a.chosen} {e}
```

So is the existence claim that there is action at all. The structure
of action itself is a definition, and no theorem uses it yet.

{docstring Apodictic.Action}

# Findings

What the derivation turned out to be, beyond the premise it rests on.

- Rothbard's derivation is one step from an asserted premise (p. 24).
  The one-step proof is faithful to him; the audit point is that
  "derived from the fundamental axiom of human action" (p. 27) rests
  on an assertion.
- The law is strict, as Rothbard's is. Non-increasing marginal
  utility is the neoclassical form, not his.
- Determinacy of the drop is not assumed. Rothbard's "the marginal
  unit" presupposes that exactly one end goes; the law here holds
  over all of them.
- The marginality of the end at the smaller supply is unused by the
  proof. The law holds for every end served there against every end
  the next unit adds — and stronger still, a served end beats *any*
  serviceable unserved end, not only the one the next unit reaches.
  Rothbard's statement is weaker than his premise delivers.

What the law does not need, which is most of what it is usually given.

- Nothing structural about preference is forced: no transitivity, no
  totality. Rothbard presupposes a linear value scale (Figure 3,
  pp. 25–26); the encoding needs none, because the disposition
  carries the order.
- Interchangeability of units is not needed for the ordering. With
  the plan indexed by which units, the urgency principle and the law
  along a chain of named units hold without it. It is needed once, to
  state the law by supply size: "the plan at `n` units" is a function
  of `n` only if two sub-stocks of the same size serve the same ends.
  It bears on the statement, not on the derivation — which is why it
  is a hypothesis and not a commitment. Rothbard makes it
  definitional of a supply (p. 23), and where it fails the units are
  not one good.
- Indifference between units is needed nowhere. Rothbard defines a
  supply with the words "valued equally" and "regards ...
  indifferently" (p. 23) and withdraws them on the next page:
  interchangeability "does not mean that the concrete units are
  actually valued equally" (p. 24). The encoding follows p. 24.
- Independence of uses is a situational hypothesis, statable only
  once preference ranges over bundles. Where uses are complementary
  the law is silent, and the statement says so.

Findings about the formalizing rather than the doctrine.

- Decidable identity of ends is a suppressed premise of "the bundle
  minus this end", surfaced by refusing classical logic.
- The claim that humans act decomposes into a definition, a bridge
  and an existence claim, and only the bridge could do deductive
  work. Nothing has needed it.
- A universal claim about "the agent's X" must not quantify over the
  type of X-shaped structures: given one, rivals are definable, and a
  claim about all of them is refutable by construction. Asserted of
  the plan a theorem is handed, the same construction is harmless and
  yields a uniqueness result instead — `no_rival_swap_dominant`, that
  two swap-dominant plans cannot differ by one swap. That there is
  "the" value scale is a theorem here, not a premise.
