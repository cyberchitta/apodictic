import VersoManual
import Apodictic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Apodictic

set_option pp.rawOnError true
set_option verso.code.warnLineLength 0

#doc (Manual) "The Archaeology" =>
%%%
tag := "archaeology"
%%%

How the result came to be stated the way it is. This part goes
through the trusted base axiom by axiom, in the order the axioms were
forced, with the encodings we tried and rejected along the way. The
rejected code is type-checked here, so the reasons for rejection can
be inspected rather than trusted.

The part is written from the lab notes of 2026-08-02, 2026-09-04
and 2026-09-05, and from Nozick's 1977 paper, read 2026-09-04. Docstrings quoted here
are pulled live from the library and carry pedigree only; the
history is in this part and nowhere in the code.

# The receipt

Lean can list the axioms a proof depends on. For the law of marginal
utility the list is this:

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

Two of the six are Lean's logical background, not praxeology:
`propext` and `Quot.sound` ride in with mathlib's finite sets.
`Classical.choice` is absent, by decision (2026-09-04): the library
is constructive by default, so that when a proof needs a case split
we are forced to ask whether the split is praxeological content, and
if so to name it. The remaining four are the trusted base. The urgency
principle, which Rothbard offers as the premise, has the same receipt,
because it is derived rather than asserted.

Every axiom carries a docstring with two required fields. *Source* is
a citation or "tacit". *Status* is one of three verdicts:
explicit-in-tradition (Rothbard or Mises say it), suppressed-premise
(they use it without saying it), or our-reconstruction (a
formalization decision the tradition never faced). The docstrings
below are the axiom-by-axiom catalogue; there is no other.

One rule governs what appears in the base at all. An axiom enters at
the point of first use: it lives in the base only while some
theorem's receipt cites it. Two doctrinally central axioms are
therefore *not* here, and the last section says why that is the main
finding so far.

A second rule governs what is an axiom and what is not. The aim of
the audit is diagnostic: Austrian conclusions fail to match reality
in known cases, so some assumption is off, and we want to point at
which one. So claimed-universal facts about action are axioms, on the
receipt, and if one is false praxeology is wrong. Situational
conditions under which a law applies are named hypotheses in the
theorem statement, and where they fail the law is silent rather than
refuted. The Austrian reply "the conditions did not hold" then names
a checkable hypothesis instead of an escape hatch.

# `World`: the frame the axioms speak of

{docstring Apodictic.World}

The vocabulary that `World` instantiates is a bare structure. Nothing
in it has any property: no transitivity, no totality, no order on
time. Strength is added only when a theorem forces it, and each
forcing is a finding.

{docstring Apodictic.ActionFrame}

## Rejected: axioms over every frame

The first encoding (2026-08-02) had no `World`. Its bridge axiom,
demonstrated preference, quantified over every frame and every action
in it. Restated over today's bundle-valued `Prefers`, it reads:

```lean
/-- REJECTED (2026-08-02): the bridge over every frame. Lives in the
document only; the library never had this bundle form. -/
axiom forall_frame_bridge (F : ActionFrame) (a : Action F) :
    ∀ e ∈ a.forgone, F.Prefers a.agent a.time {a.chosen} {e}
```

A frame is an ordinary definable structure, so one can be built in
which preference is everywhere false, together with an action in it.
The axiom then yields `False` outright:

```lean (name := crash)
def badFrame : ActionFrame where
  Agent := Unit
  End := Bool
  Means := Unit
  Time := Unit
  Believes := fun _ _ _ _ => True
  Prefers := fun _ _ _ _ => False

def badAction : Action badFrame where
  agent := ()
  time := ()
  chosen := true
  means := ()
  forgone := {e | e = false}
  forgone_nonempty := ⟨false, rfl⟩
  chosen_not_forgone := fun h => Bool.noConfusion h
  belief := trivial

theorem forall_frame_inconsistent : False :=
  forall_frame_bridge badFrame badAction false rfl

#print axioms forall_frame_inconsistent
```
```leanOutput crash
'forall_frame_inconsistent' depends on axioms: [forall_frame_bridge]
```

The lesson is general and not about praxeology: a global axiom about
all inhabitants of a definable type is refutable by construction
unless the type's own fields secure the claim. The review that
approved the axiom had checked its fidelity to the doctrine, not its
quantifier range. Statement-fidelity review does not catch this;
building the pathological model does.

Four fixes were on the table. Fold the assertion into the structure
as a field: consistent, but it hides the bridge where the receipt
cannot see it, and the bridge is the one thing the brief says must be
its own flagged axiom. State it as a hypothesis on every theorem:
honest, but then the receipt shows nothing and the method is gone.
Define preference *as* demonstrated preference: consistent and
hardline Rothbardian, but it erases the distinction between the
latent ranking and choice, and the dispute with Nozick becomes
unstatable. The fourth is what we did: a distinguished opaque frame.
With the axiom restated over `World`, the same witness no longer
type-checks:

```lean +error (name := crashRed)
axiom world_bridge (a : Action World) :
    ∀ e ∈ a.forgone, World.Prefers a.agent a.time {a.chosen} {e}

theorem still_inconsistent : False :=
  world_bridge badAction false rfl
```
```leanOutput crashRed
Application type mismatch: The argument
  badAction
has type
  Action badFrame
but is expected to have type
  Action World
in the application
  world_bridge badAction
```

One thing should be said plainly. The distinguished frame was chosen
because it is the only option under which the receipt keeps printing
the commitments. The Misesian gloss in its docstring, that praxeology
is about action as such rather than about all conceivable structures,
is defensible, and it was attached afterwards. The switch to a
class-of-frames reading, should it ever be wanted, is mechanical:
each axiom becomes a field of a frame bundle and each theorem gains a
frame parameter. What does not transfer is consistency, which a class
of frames gets from any model and a fixed world must earn separately.
That is the price of the simpler formalism, and it is paid in the
section on consistency below.

# `ends_distinguishable`: ends can be told apart

{docstring Apodictic.ends_distinguishable}

This is the first axiom the constructive-by-default rule surfaced.
The derivation rewrites a served bundle as "this end together with
the rest", and that rewrite needs, for every end, that it either is
or is not the one withdrawn. Mathlib proves the rewrite classically.
We could have accepted `Classical.choice` on the receipt, or hidden
decidable identity as a field of the frame where the receipt cannot
see it. Naming it is the honest option: it sits beside `World` as a
second data axiom, and it says something a reader can dispute. One
more alternative was rejected: phrasing `swap_dominance` with the
served bundle already written as "`e` together with the rest" on
both sides, which needs no decidability in the proof only because it
hides the same identification inside the axiom's wording.

# `actual_disposition`: which plan is the agent's

{docstring Apodictic.actual_disposition}

The disposition it applies to is the counterfactual allocation plan,
a new primitive beyond action, adopted 2026-08-02 because a single
actual allocation cannot discriminate among the ends it serves: they
are all inside the chosen package.

{docstring Apodictic.Stock}

{docstring Apodictic.AllocationDisposition}

One commitment hides in a field shape here, where the receipt cannot
see it: `card_eq` is Rothbard's "we assume for simplicity" (p. 26),
one unit, one end, no idle units. A second used to. Until 2026-09-05
the plan was indexed by the *number* of units, which enforced
interchangeability silently; that encoding is restated here because
the crash below happened in it, and its replacement is the subject
of the units section.

```lean
/-- SUPERSEDED (2026-09-05): the disposition indexed by how many
units, not which. Interchangeability of units is a type shape here,
invisible to the receipt. -/
structure CountDisposition {agent : World.Agent} {t : World.Time}
    (s : Stock World agent t) where
  wouldServe : ℕ → Finset World.End
  serves_subset : ∀ n, ∀ e ∈ wouldServe n, e ∈ s.serves
  card_eq : ∀ n ≤ s.units.card, (wouldServe n).card = n
```

## Rejected: swap dominance over every plan

The evening of 2026-09-04 the human asked, of the then-new
`swap_dominance`, "is there something I might be missing?" There was.
The axiom was stated for every structure of the disposition type, and
given one plan, rivals are definable. Here is that axiom, restated in
the document:

```lean
/-- REJECTED (2026-09-04): swap dominance for EVERY disposition, not
the agent's. Identical to that day's library axiom minus `hA`, over
the count-indexed disposition of the time. -/
axiom swap_dominance_all
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : CountDisposition s)
    (n : ℕ) (hn : n ≤ s.units.card) :
    ∀ e ∈ A.wouldServe n, ∀ e' ∈ s.serves, e' ∉ A.wouldServe n →
      World.Prefers agent t (↑(A.wouldServe n))
        (insert e' ((↑(A.wouldServe n) : Set World.End) \ {e}))
```

Take any plan with a served end `e` and a serviceable unserved `e'`
at some supply. Build the rival plan identical except that at that
supply it serves the swap. The axiom applied to the plan says the
original bundle is preferred to the swap; applied to the rival it says
the swap is preferred to the original. With asymmetry of preference,
`False`. The classical lemmas in this proof do the bookkeeping for the
rival plan and are irrelevant to the point, which is model-theoretic:
no model with asymmetric preference satisfies the axiom once one
stock has a unit and two serviceable ends.

```lean (name := clash)
theorem swap_dominance_all_clash
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : CountDisposition s) (n : ℕ) (hn : n ≤ s.units.card)
    (e : World.End) (he : e ∈ A.wouldServe n)
    (e' : World.End) (he's : e' ∈ s.serves) (hne : e' ∉ A.wouldServe n)
    (hasym : ∀ X Y : Set World.End,
      World.Prefers agent t X Y → ¬ World.Prefers agent t Y X) :
    False := by
  classical
  let S := A.wouldServe n
  let S' : Finset World.End := insert e' (S.erase e)
  have hee' : e ≠ e' := fun h => hne (h ▸ he)
  have hcard' : S'.card = n := by
    have h1 : e' ∉ S.erase e := fun h => hne (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_notMem h1, Finset.card_erase_of_mem he,
      A.card_eq n hn]
    have hpos : 0 < n := by
      have := Finset.card_pos.mpr ⟨e, he⟩
      rw [A.card_eq n hn] at this
      exact this
    omega
  let A' : CountDisposition s :=
    { wouldServe := fun m => if m = n then S' else A.wouldServe m
      serves_subset := by
        intro m x hx
        by_cases hm : m = n
        · simp only [hm, if_true] at hx
          rcases Finset.mem_insert.mp hx with h | h
          · exact h ▸ he's
          · exact A.serves_subset n x (Finset.mem_of_mem_erase h)
        · simp only [hm, if_false] at hx
          exact A.serves_subset m x hx
      card_eq := by
        intro m hm
        by_cases h : m = n
        · simp only [h, if_true]; exact hcard'
        · simp only [h, if_false]; exact A.card_eq m hm }
  have hA'n : A'.wouldServe n = S' := by simp [A']
  have h1 := swap_dominance_all A n hn e he e' he's hne
  have he'S' : e' ∈ A'.wouldServe n := by
    rw [hA'n]; exact Finset.mem_insert_self e' _
  have hes : e ∈ s.serves := A.serves_subset n e he
  have heS' : e ∉ A'.wouldServe n := by
    rw [hA'n]; intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hee' h
    · exact (Finset.mem_erase.mp h).1 rfl
  have h2 := swap_dominance_all A' n hn e' he'S' e hes heS'
  rw [hA'n] at h2
  have hX : (↑S' : Set World.End) =
      insert e' ((↑S : Set World.End) \ {e}) := by
    simp [S']
  have hY : insert e ((↑S' : Set World.End) \ {e'}) =
      (↑S : Set World.End) := by
    ext x
    simp only [S', Finset.coe_insert, Finset.coe_erase, Set.mem_insert_iff,
      Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · rintro (rfl | ⟨(rfl | ⟨hxS, _⟩), hxe'⟩)
      · exact he
      · exact absurd rfl hxe'
      · exact hxS
    · intro hxS
      by_cases hxe : x = e
      · exact Or.inl hxe
      · refine Or.inr ⟨Or.inr ⟨hxS, hxe⟩, ?_⟩
        intro h; exact hne (h ▸ hxS)
  rw [hY, hX] at h2
  rw [show (↑S : Set World.End) = ↑(A.wouldServe n) from rfl] at h1 h2
  exact hasym _ _ h1 h2
```

The base was still consistent that day, because `Prefers` has no
properties yet and the everything-true model satisfies anything
positive. But strict preference has been the intended reading since
the first day, and the day asymmetry entered, the base would have
gone inconsistent. The failure has the same shape as the frame crash
above, one level down: a universal claim over a definable type,
refuted by a rival instance. `World` is opaque, but a disposition
over `World` is an ordinary structure.

Two fixes were possible. A data axiom handing over *the* disposition
for every stock would assert that every agent has a complete
counterfactual table for every good, which is more than anyone has
argued. The opaque predicate asserts only that there is a fact about
which plan is the agent's, and the axiom is restricted to it. With
the restriction in place, the rival plan has no proof of
`actual_disposition` to hand the axiom, and the refutation no longer
elaborates. The consistency section shows the fixed axiom has a model
with asymmetric preference.

# `swap_dominance`: the one praxeological premise

{docstring Apodictic.swap_dominance}

Rothbard's argument on pp. 24–27 is one step from a premise he
asserts. The premise: "action uses scarce means to satisfy the most
urgent of the not yet satisfied wants" (p. 24), offered as a
"universal fact" that "follows from" action, with no derivation
shown. The step: on losing one unit, "he gives up the least urgent of
the wants which the larger stock would have satisfied" (p. 25),
introduced with "Obviously" and backed by the reallocation argument
on p. 27. Our first encoding asserted the conclusion of that step as
the axiom, and the human noticed that the famous law then followed in
one line. The one-line proof was in fact faithful to Rothbard; the
audit point was upstream, in what the premise had compressed. Cutting
it finer gave this axiom plus two hypotheses, and the urgency
principle became a theorem.

What it does not say is listed in its docstring. The first item
matters most and is taken up in the last section: it says nothing
about actual action. The second is that the general form, "preferred
to every same-size bundle", was tried and is not needed; the weaker
one-swap axiom is also the more faithful, since Rothbard's p. 27
argument is a one-unit reallocation. Independence of uses is a
hypothesis, below. And the supply bound: the axiom this one replaced
claimed every supply level, which is more than the tradition's
argument delivers.

## What Nozick actually says

Nozick's 1977 paper is this project's adversarial reader, and until
2026-09-04 the notes and docstrings called this axiom "Nozick's
target". Having read §III of the paper, that was inverted.

Nozick lists three Austrian theses about preference and action
(p. 370). First, doing A shows A was preferred to every alternative
believed available. Second, no evidence can establish a preference
against a choice. Third, "the notion of preference makes no sense
apart from an actual choice made". He argues the first fails because
of indifference: doing A shows willingness to do A, not unwillingness
to do B. And he argues the third fails by the Austrians' own lights,
because cost is the value of the *best rejected* alternative, which
requires ranking among alternatives none of which was chosen. His
positive account is subjunctive: "to say a person prefers A to B at a
time is to say he would choose A over B if he were given a choice
between (only) A and B at that time" (p. 373). "'Prefers A to B' is
like 'soluble'; 'chooses A over B' is like 'dissolves'" (p. 374).

`swap_dominance` is subjunctive preference in exactly Nozick's sense.
What the agent *would* serve at each supply, preferred to what he
would serve after a swap. So the axiom is Nozick-shaped, and what it
collides with is Rothbard's third thesis. The receipt above then says
something sharper than the notes had claimed: Rothbard's derivation
of marginal utility uses, at its only load-bearing step, the notion
his demonstrated-preference doctrine forbids. That is Nozick's cost
argument replayed on marginal utility, and machine-checked.

Two smaller alignments. Nozick allows subjunctives to be undetermined
(p. 373), which is the reason `actual_disposition` asserts no
existence. And he holds that irreflexivity and asymmetry "seem to be
part of the notion of preference" (p. 377), while transitivity is a
violable rationality condition. Asymmetry is the one property we
intend to add; transitivity has not been needed.

# The hypotheses

The theorems take four hypotheses. Each is a situational condition,
not a universal claim, and the diagnostic aim puts it in the statement
so that it can be pointed at when it fails.

The first is `actual_disposition A`: the plan under discussion is the
agent's. The second is that the sub-stocks compared are on hand and
differ by one unit, `s.OneMore U V`; it descends from the supply
bound `n ≤ s.units.card` of the count-indexed days. The former axiom
quantified over every supply level, which is more than the
tradition's argument delivers; the disposition is data only within
the stock on hand, and the derivation gives the law only there. The
third is independence of uses. The fourth, interchangeability of
units, has its own section below.

{docstring Apodictic.ActionFrame.IndependentUses}

Independence became statable only when preference moved to bundles
(2026-09-04). With preference over single ends there was no way even
to write the condition that fails under complementarity. The human's
objection that forced the move was "are not all ends composites?",
and the answer is yes: "atomic" can only mean "not further divided by
this action", the same relativity as the size of a unit (p. 28). So
there is one ranking over bundles, and an end in the ordinary sense
is a singleton bundle.

{docstring Apodictic.ActionFrame.PrefersEnd}

The law is then stated over Rothbard's own definition of the marginal
utility of a supply, the ends that would be given up on the loss of
one unit, and it is strict, as his is.

{docstring Apodictic.marginalEnds}

{docstring Apodictic.urgency_principle}

{docstring Apodictic.marginal_utility}

# The units: where interchangeability is used

The brief named this the known trap: the law needs homogeneous units,
and Rothbard denies that indifference is demonstrable in action. The
count-indexed disposition above had walked around it by putting
interchangeability into a type: a plan that is a function of a number
cannot depend on which units. The receipt could not see that.

On 2026-09-05 the index became the sub-stock, the set of units the
agent would have, and interchangeability became a named condition.

{docstring Apodictic.AllocationDisposition.Homogeneous}

The sub-stocks are hypothesized, never constructed: "one unit more"
is inclusion plus a count, so no decidable equality on units was
forced, though an `erase`-based statement would have forced one.

{docstring Apodictic.Stock.OneMore}

The prototype compiled at the first attempt, which by the project's
rule is a warning, and the examination is the finding. Served over
unserved, the urgency principle, and the law along a chain of named
units need no interchangeability: each is about one sub-stock, and
none compares two of the same size. Rothbard's wording, by supply
size, uses it exactly once, to identify the plan at one sub-stock of
size `n` with the plan at another. Without it "the marginal utility
of a supply of `n` units" is not a function of `n`, so the supply-size
form cannot be stated. That is Nozick's p. 371, "without the notion
of a unit ... we have no way to state the law", located: a condition
on stating the law by size, not a premise of the ordering.

{docstring Apodictic.marginal_utility_chain}

Three notions of homogeneity were in play, and the text has all
three. Equal serviceability, `Stock.homog`, is p. 22, "equally
capable of rendering the same service", a belief notion; it does no
formal work in either form of the law. Indifference in value between
units is p. 23, "Cow A and cow B were valued equally", "regards
horses B and C indifferently", and it is withdrawn on p. 24:
interchangeability "does not mean that the concrete units are
actually valued equally." It is needed nowhere. What the supply-size
form needs is the third, that the plan ignores which units, and that
is subjunctive, what the agent would serve with horses A and B
against B and C. It is the same kind of commitment the base already
carries in `swap_dominance`, so the trap is one collision, not two.

Where the condition lives was the human's decision. An axiom
bridging equal serviceability to a homogeneous plan would have put a
fifth line on the receipt and made `Stock.homog` do work; it would
also claim a universal fact about action where the text gives a
definition. Rothbard: "If a specific unit is differently evaluated
from all other units, then the supply of that good is only one unit"
(p. 23). Interchangeability is what makes units one supply, so where
it fails the law's supply-size form is silent about them as one good,
and a hypothesis says exactly that. The other premise Rothbard names
for the reallocation, "disregard of past events" (p. 27), has nothing
to bite on in a one-instant frame, and waits for time to do work.

# What the law does not rest on

The receipt does not cite an axiom about actual action. This is the
main finding to date, and it took two passes to state correctly.

The first pass (2026-08-02) announced that the demonstrated-preference
bridge "does no work" and Nozick was vindicated. That was partly an
artifact: the urgency principle had been compressed into an axiom
that bypassed the bridge. The second pass (2026-09-04) unwound the
compression and derived the principle, expecting the bridge to
re-enter. It did not. The derivation runs on the subjunctive
extension alone. The bridge is parked with its pedigree:

```lean
/-- PARKED (2026-09-04): the bridge from actual action to
preference, in the bundle form it would need today. Never cited by
any theorem; lives in the document, not the base. -/
axiom demonstrated_preference (a : Action World) :
    ∀ e ∈ a.forgone, World.Prefers a.agent a.time {a.chosen} {e}
```

So is the existence axiom, "humans act". Here the archaeology is
about the shape of the famous axiom rather than its use. In this
encoding it is not one axiom. It decomposes into the *definition* of
action, carried by the fields of `Action`; the *bridge* above; and an
*existence* claim that there is action at all. Only the bridge could
do deductive work, and nothing has needed it. The existence claim
would guard against vacuity under the distinguished frame, and no
theorem has an existential conclusion yet, so it too waits.

{docstring Apodictic.Action}

The structure is a definition, not an assertion. That split, between
the jointly constitutive package and the separable claims about it,
is nowhere in Mises. It was adopted (2026-08-02) because the
type-checker makes reshaping cheap while little is built on top, and
because the asymmetry favours starting split: collapsing separable
axioms into one is bundling; prying a monolith apart rewrites every
proof that used the conjunction.

## Rejected: the urgency principle as an axiom

For the record, the axiom that the theorem replaced. It claimed every
supply level and, restated over today's vocabulary, quantifies over
every disposition; it almost certainly had the same over-quantification
hole as the first `swap_dominance`, though that was never checked
because it was superseded the same day.

```lean
/-- SUPERSEDED (2026-09-04, evening): the urgency principle asserted,
over the count-indexed disposition of the time. Compare the theorem
`urgency_principle`, which has the same conclusion under two more
hypotheses. -/
axiom urgency_principle_asserted
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : CountDisposition s) (n : ℕ) :
    ∀ e ∈ A.wouldServe n, ∀ e', e' ∈ A.wouldServe (n + 1) →
      e' ∉ A.wouldServe n → World.PrefersEnd agent t e e'
```

# Consistency

The consistency model lives in the library, in
`Apodictic.Consistency`, by the human's decision that a ledger kept
in prose would defeat the purpose. It was built the evening the
over-quantified swap dominance was refuted, to show the fixed axiom
survives asymmetry. What it shows and does not show is stated in the
result part. The toy was extended on 2026-09-05 to the sub-stock
plan: it is homogeneous, one-unit steps exist, and each step has a
marginal end, so the law's conclusion is a non-trivial preference in
it. What remains open is the transfer from the frame vocabulary to
the `World` axioms, which is a reading, not a check.

# Methodological findings

The substantive findings are listed in the result part. Two are
about method rather than praxeology and belong here.

- Two universal claims over definable types were refuted by
  constructing rivals: the frame-general bridge (2026-08-02) and the
  disposition-general swap dominance (2026-09-04). Statement-fidelity
  review, which checks an axiom against the doctrine, caught neither;
  building the pathological model did. The rule that followed: name
  the actual one with an opaque predicate and restrict the axiom to
  it.
- An announced finding was partly an artifact of an encoding. "The
  bridge does no work" was first said of a base whose urgency axiom
  had compressed the derivation past the bridge. Unwinding the
  compression was what made the finding real: the bridge was given
  every chance to re-enter and did not.
