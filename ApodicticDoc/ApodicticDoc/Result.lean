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
the four axioms, the hypotheses, and the two theorems, and reads the
receipt. Every docstring is pulled from the library at build time.
How each piece came to be stated this way, and what was tried and
refuted before it, is the archaeology part.

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

# Axioms

Every axiom carries three fields. *Source* is a citation or "tacit".
*Status* is one of three verdicts: explicit-in-tradition (Rothbard or
Mises say it), suppressed-premise (they use it without saying it),
or our-reconstruction (a formalization decision the tradition never
faced). *Does not say* lists the nearby stronger claims the axiom
deliberately omits.

Two rules govern the list. An axiom enters at the point of first
use, so nothing is here that no theorem cites. And only
claimed-universal facts about action are axioms; conditions under
which a law applies are hypotheses of the theorem, below.

{docstring Apodictic.World}

{docstring Apodictic.ends_distinguishable}

{docstring Apodictic.actual_disposition}

{docstring Apodictic.swap_dominance}

# Hypotheses

The theorems take four hypotheses. Each is a situational condition,
not a universal claim, and each is in the statement so that it can
be pointed at when it fails. Where one fails the law is silent, not
refuted.

- `actual_disposition A`: the plan under discussion is the agent's.
- `s.OneMore U V`: the sub-stocks compared are on hand, and differ
  by one unit. The disposition is data only there, and the law holds
  only there.
- `IndependentUses agent t`: the value of an end does not depend on
  which other ends are served.
- `A.Homogeneous`: the plan depends only on how many units, not
  which. Needed only by the supply-size form of the law.

{docstring Apodictic.ActionFrame.IndependentUses}

# Theorems

Rothbard's urgency principle, that the loss of a unit falls on the
least urgent want, is a theorem here rather than a premise. What the
axiom delivers is stronger than the principle, so the workhorse is
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
'Apodictic.marginal_utility' depends on axioms: [propext,
 World,
 actual_disposition,
 ends_distinguishable,
 swap_dominance,
 Quot.sound]
```

`propext` and `Quot.sound` are Lean's logical background; they ride
in with mathlib's finite sets. `Classical.choice` is absent: the
library is constructive by default, so that a case split a proof
needs is either named praxeological content or absent. The remaining
four are the trusted base. The urgency principle and the chain form
of the law have the same receipt; the supply-size form differs from
the chain form only by the hypothesis `A.Homogeneous`, which is not
an axiom and so does not appear here.

# Not in the base

Two doctrinally central claims are not cited by any theorem and are
therefore not axioms. The bridge from actual action to preference,
demonstrated preference in Rothbard's sense, is stated here in the
form it would take, and it is parked:

```lean
/-- PARKED: the bridge from actual action to preference. Not cited by
any theorem; lives in the document, not the base. -/
axiom demonstrated_preference (a : Action World) :
    ∀ e ∈ a.forgone, World.Prefers a.agent a.time {a.chosen} {e}
```

So is the existence claim that there is action at all. The structure
of action itself is a definition, and no theorem uses it yet.

{docstring Apodictic.Action}

# Consistency

`World` cannot be built, so the axioms cannot be shown consistent by
building it. What can be built is a frame of the general vocabulary
in which every axiom's statement holds, together with the property
we intend to add and the theorems' hypotheses. That frame is
`Apodictic.Model.Toy`: one agent, one instant, numbers for ends, and
this preference:

{docstring Apodictic.Model.swapPrefers}

In it, swap dominance holds for the plan that serves the most
urgent ends, as many as there are units; that plan is actual and
homogeneous, ends are decidable, uses are independent, one-unit
steps exist within the stock, each step has a marginal end, and
preference is asymmetric. So the four axioms have a model with
strict preference, and the theorems are neither vacuous nor
trivial. That the model transfers to the `World`
axioms is the ordinary model-theoretic reading, which Lean cannot
check because `World` is opaque.

# Findings

- The law of marginal utility rests on one praxeological premise,
  and that premise is subjunctive preference: what the agent *would*
  serve at each supply. No axiom about actual action is cited.
  Rothbard's derivation therefore uses what his demonstrated-preference
  doctrine forbids. This is Nozick's cost argument (1977, §III)
  transposed to marginal utility and machine-checked.
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
  same ends. Nozick's remark that without a unit the law cannot be
  stated (1977, p. 371) lands here, on the statement and not the
  derivation. Interchangeability is a hypothesis, not an axiom:
  Rothbard makes it definitional of a supply (p. 23), and where it
  fails the units are not one good.
- Rothbard defines a supply with the words Nozick attacks, "valued
  equally", "regards ... indifferently" (p. 23), and withdraws them
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
- The action axiom decomposes into a definition, a bridge, and an
  existence claim, and only the bridge could do deductive work.
  Nothing has needed it.
- A universal claim about "the agent's X" must not quantify over the
  type of X-shaped structures: given one, rivals are definable and
  the axiom refutes itself. Two such crashes are in the archaeology.
