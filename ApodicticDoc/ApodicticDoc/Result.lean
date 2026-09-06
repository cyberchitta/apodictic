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

What has been proved, from what. This part states the vocabulary,
the commitment, the hypotheses, and the two theorems, and reads the
receipt. Every docstring is pulled from the library at build time.

# Vocabulary

The primitive vocabulary is a bare structure. Nothing in it has any
property: no transitivity, no totality, no order on time. Strength
is added only when a theorem forces it, and so far none has.

{docstring Apodictic.ActionFrame}

{docstring Apodictic.ActionFrame.PrefersEnd}

The law of marginal utility is about a stock of interchangeable
units and what the agent would do with more or fewer of them.

{docstring Apodictic.Stock}

{docstring Apodictic.AllocationDisposition}

One commitment hides in a field shape here, where the receipt cannot
see it: `card_eq` is Rothbard's "we assume for simplicity" (p. 26),
one unit, one end, no idle units. Interchangeability of units does
not hide: the plan is indexed by *which* units, and that it depends
only on how many is the named condition below.

{docstring Apodictic.AllocationDisposition.Homogeneous}

{docstring Apodictic.Stock.OneMore}

# Commitments

The library declares no `axiom`. Every praxeological claim is a
structure, and a theorem that needs one takes it as a named
hypothesis; what a theorem rests on is therefore read off its
signature rather than off `#print axioms`. That every listed
commitment does real work is enforced by `#lint only
unusedArguments`, which fails the build on a hypothesis the proof
never uses.

Every commitment carries three fields. *Source* is a citation or "tacit".
*Status* is one of three verdicts: explicit-in-tradition (Rothbard or
Mises say it), suppressed-premise (they use it without saying it),
or our-reconstruction (a formalization decision the tradition never
faced). *Does not say* lists the nearby stronger claims it deliberately
omits.

Two rules govern the list. A commitment enters at the point of first
use, so nothing is here that no theorem carries. And only
claimed-universal facts about action are commitments; conditions
under which a law applies are hypotheses of the theorem, below.

There is exactly one.

{docstring Apodictic.SwapDominant}

# Hypotheses

The theorems take three hypotheses beyond the commitment. Each is a
situational condition, not a universal claim, and each is in the
statement so that it can be pointed at when it fails. Where one
fails the law is silent, not refuted.

- `s.OneMore U V`: the sub-stocks compared are on hand, and differ
  by one unit. The disposition is data only there, and the law holds
  only there.
- `IndependentUses agent t`: the value of an end does not depend on
  which other ends are served.
- `A.Homogeneous`: the plan depends only on how many units, not
  which. Needed only by the supply-size form of the law.

Which plan is the agent's needs no hypothesis of its own. The
theorems are about the plan they are handed, and the commitment is
asserted of that plan; there is nothing quantified over rival plans
for a rival to refute.

{docstring Apodictic.ActionFrame.IndependentUses}

# Theorems

Rothbard's urgency principle, that the loss of a unit falls on the
least urgent want, is a theorem here rather than a premise. What the
the commitment delivers is stronger than the principle, so the
workhorse is
stated first.

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

`propext` and `Quot.sound` are Lean's logical background; they ride
in with mathlib's finite sets. `Classical.choice` is absent: the
library is constructive by default, so that a case split a proof
needs is either named praxeological content or absent. Nothing else
appears, because the library adds nothing to Lean's logic — which is
what this output is for, and all it says.

The praxeological content is in the statement instead. The law
carries one commitment, `SwapDominant A`; three situational
conditions, `IndependentUses`, `A.Homogeneous` (the supply-size form
only) and the sub-stocks being on hand; and one data condition on the
frame, `[DecidableEq F.End]`. The urgency principle and the chain
form carry the same list less `Homogeneous`.

# Not in the base

Two doctrinally central claims are not cited by any theorem and are
therefore not commitments. The bridge from actual action to
preference,
demonstrated preference in Rothbard's sense, is stated here in the
form it would take, and it is parked:

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

# Consistency

Consistency is not a side-question here: it is an instance. Build a
frame, a stock and a plan, prove the plan swap-dominant, and hand the
whole thing to the theorem. If that type-checks, the commitment and
the conditions are jointly satisfiable and the law is not vacuous.
The frame is `Apodictic.Model.Toy`: one agent, one instant, numbers
for ends, and this preference:

{docstring Apodictic.Model.swapPrefers}

In it, the plan that serves the most urgent ends — as many as there
are units — is swap-dominant and homogeneous, ends are decidable,
uses are independent, one-unit steps exist within the stock, each
step has a marginal end, and preference is asymmetric. So the
commitment has a model with strict preference — the reading intended
throughout, and what `no_rival_swap_dominant` needs.

The last step is the point:

{docstring Apodictic.Model.toy_law_applies}

That is the law itself, at the toy frame, with every hypothesis
discharged. Nothing is transcribed: `toy_swapDominant` proves the
same proposition the theorem consumes.

# Findings

- The law of marginal utility rests on one praxeological premise,
  and that premise is subjunctive preference: what the agent *would*
  serve at each supply. Nothing about actual action is assumed.
  Rothbard's own premise (p. 24) fuses a claim about action with a
  claim about the ordering of wants; only the ordering half, extended
  subjunctively as his own derivation extends it (p. 25), does any
  work. So his law needs a premise his own restriction does not
  admit: praxeology "may deal with utilities only as deduced from the
  concrete actions of human beings" (p. 882 n. 8).
- Rothbard's own derivation is one step from an asserted premise
  (p. 24). The one-step proof is faithful to him; the audit point is
  that "derived from the fundamental axiom of human action" (p. 27)
  rests on an assertion.
- Nothing structural about preference is forced: no transitivity, no
  totality. Rothbard presupposes a linear value scale (Figure 3,
  pp. 25–26); the encoding needs none, because the disposition
  carries the order.
- The law is strict, as Rothbard's is. Non-increasing marginal
  utility is the neoclassical form, not his.
- Determinacy of the drop is not assumed. Rothbard's "the marginal
  unit" presupposes exactly one end goes; the law holds over all of
  them.
- The marginality of the end at the smaller supply is unused by the
  proof. The law holds for every end served there against every end
  the next unit adds; Rothbard's statement is weaker than his
  premise delivers. Stronger still: a served end beats *any*
  serviceable unserved end, not only the one the next unit reaches.
- Interchangeability of units is not needed for the ordering. With
  the plan indexed by which units, the urgency principle and the law
  along a chain of named units hold without it. It is needed once,
  to state the law by supply size: "the plan at `n` units" is a
  function of `n` only if two sub-stocks of the same size serve the
  same ends. It bears on the statement, not the derivation.
  Interchangeability is a hypothesis, not a commitment:
  Rothbard makes it definitional of a supply (p. 23), and where it
  fails the units are not one good.
- Rothbard defines a supply with the words "valued equally" and
  "regards ... indifferently" (p. 23), and withdraws them
  on the next page: interchangeability "does not mean that the
  concrete units are actually valued equally" (p. 24). The encoding
  follows p. 24. Indifference between units is asserted nowhere, and
  the law survives; what it needs instead, that the plan ignores
  which units, is subjunctive, the same kind of commitment as swap
  dominance. The units trap and the demonstrated-preference collision
  are one collision.
- Independence of uses is a situational hypothesis, statable only
  once preference ranges over bundles. Where uses are complementary
  the law is silent, and the statement says so.
- Decidable identity of ends is a suppressed premise of "the bundle
  minus this end", surfaced by refusing classical logic.
- The claim that humans act decomposes into a definition, a bridge,
  and an existence claim, and only the bridge could do deductive
  work. Nothing has needed it.
- A universal claim about "the agent's X" must not quantify over the
  type of X-shaped structures: given one, rivals are definable, and a
  claim about all of them is refutable by construction. Asserted of
  the plan a theorem is handed, the same construction is harmless and
  yields a uniqueness result instead — `no_rival_swap_dominant`: two
  swap-dominant plans cannot differ by one swap. That there is "the"
  value scale is thus a theorem here, not a premise.
