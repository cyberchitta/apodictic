import Apodictic.Praxeology

/-!
# Mises's derivation — the second theorem target

Mises derives the law of marginal utility a completely different way
from Rothbard, and this module encodes HIS route. *Human Action*,
ch. VII, §1.

## Deliberate isolation

This module imports `Apodictic.Praxeology` and NOTHING ELSE from the
library. In particular it does NOT import `Apodictic.Urgency` or
`Apodictic.MarginalUtility`, so `urgency_principle`,
`served_over_unserved`, `marginal_utility_chain` and `marginal_utility`
are not in scope and cannot be reached for.

The isolation is methodological, not stylistic. The question this
target exists to answer is whether Mises's derivation needs the
premise Rothbard's needs (`SwapDominant`) or something else. A proof
that reached for Rothbard's results would assume the answer. With
them out of scope, whatever this route spends has to be stated here,
and the signature reports it.

Two consequences worth stating:

- `SwapDominant` IS still nameable, since it lives in
  `Apodictic.Praxeology` with every other claim about action (the
  library's one-file invariant). If a theorem here ends up carrying
  it, that is a finding and the signature shows it loudly. What is
  prevented is using it through a Rothbard lemma without saying so.
- Definitions are duplicated rather than shared, for the same
  reason. `marginalEmployment` below restates what
  `MarginalUtility.marginalEnds` says. That the two agree is a
  THEOREM, and it belongs in a module that imports both, not in an
  `import` here.

## The counterfactual reading (the fork, taken)

Mises's ladder runs upward — "if the supply available increases from
n–1 units to n units" — and the question was whether that is a
temporal acquisition sequence or the same one-time counterfactual
comparison Rothbard makes, narrated forward. Taken here as
COUNTERFACTUAL: one agent, one time, two supply sizes. His own
definition is explicitly of that shape ("would not make if, OTHER
THINGS BEING EQUAL, his supply were only n–1 units"), and the whole
paragraph is offered as reasoning that does not "transcend the sphere
of praxeological reasoning" — not as a history.

The temporal reading is not abandoned; it is a separate target, and a
finding either way (`_notes/`). Nothing in this module presumes it
false.
-/

namespace Apodictic
namespace Mises

/-- **Mises's marginal employment** — the ends served at the larger
supply and not at the smaller.

"We call that employment of a unit of a homogeneous supply which a man
makes if his supply is n units, but would not make if, other things
being equal, his supply were only n–1 units, the least urgent
employment or the marginal employment, and the utility derived from it
marginal utility" (*Human Action*, ch. VII, §1).

Stated as the DIFFERENCE of two counterfactual allocations at one
time, which is what "other things being equal" asks for.

Restates `MarginalUtility.marginalEnds` deliberately: see the module
docstring on isolation. That the two coincide is a theorem for a
module importing both, not an `import` here.

A definition, not a claim — Mises introduces it as one ("We call
that employment ..."), and says in the next breath that establishing
it costs nothing praxeological. -/
def marginalEmployment {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} {stock : Stock praxis agent time}
    (plan : AllocationPlan stock)
    (fewer more : Finset praxis.Means) : Set praxis.End :=
  {want | want ∈ plan.wouldServe more ∧ want ∉ plan.wouldServe fewer}

/-- **Least urgent among those served** — Mises's "the least urgent
or least painful among all those wants which could be removed by
means of the supply n–1".

A situational condition, NOT a claim about action: it says of a given
end that nothing else served at that sub-stock ranks below it. It is
stated of an end handed to a theorem, never asserted to exist —
whether such an end exists at all is a separate question, and one
that cannot be answered without saying more about `Prefers` than the
library assumes.

That this is a hypothesis rather than a derived object is the first
place the two routes visibly differ. Rothbard's derivation never needs
a minimum: it compares two named steps. Mises's sentence names one. -/
def LeastUrgentServed {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} {stock : Stock praxis agent time}
    (plan : AllocationPlan stock)
    (subStock : Finset praxis.Means) (want : praxis.End) : Prop :=
  want ∈ plan.wouldServe subStock ∧
    ∀ other ∈ plan.wouldServe subStock, other ≠ want →
      praxis.PrefersEnd agent time other want

/-- **Mises's ladder, as a target** — the statement to be derived,
written out so that what is and is not yet proved is legible.

"If the supply available increases from n–1 units to n units, the
increment can be employed only for the removal of a want which is
less urgent or less painful than the least urgent or least painful
among all those wants which could be removed by means of the supply
n–1" (*Human Action*, ch. VII, §1).

This is a `def` of a Prop, not a theorem. NOTHING IN THIS MODULE
PROVES IT YET: the premise Mises's route spends has not been settled,
and choosing one is a decision about philosophical commitment, not
about proof convenience. -/
def LadderHolds {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) : Prop :=
  ∀ fewer more : Finset praxis.Means, stock.OneMore fewer more →
    ∀ least, LeastUrgentServed plan fewer least →
      ∀ added ∈ marginalEmployment plan fewer more,
        praxis.PrefersEnd agent time least added


/-! ## The control: does Rothbard's premise already carry Mises's ladder?

Before asking what Mises's derivation spends INSTEAD of swap
dominance, ask the null hypothesis: does his conclusion follow from
swap dominance outright? If it does, his dilemma supplies no premise
the law needs, and his route does not escape Rothbard's circle — it
simply never asks for a warrant.

Isolation forbids importing `Apodictic.Urgency`, so the one lemma the
argument needs is reproved here rather than borrowed. -/

/-- Taking a member out of a set and putting it straight back leaves
the set alone. Reproved here rather than imported from
`Apodictic.Urgency`: see the module docstring. Constructive, given
decidable equality; mathlib's `Set.insert_sdiff_singleton` is
classical. -/
theorem insert_sdiff_self_of_mem' {α : Type} [DecidableEq α]
    {bundle : Set α} {want : α} (h : want ∈ bundle) :
    bundle = insert want (bundle \ {want}) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    by_cases hxWant : x = want
    · exact Or.inl hxWant
    · exact Or.inr ⟨hx, hxWant⟩
  · intro hx
    cases hx with
    | inl hxWant => rw [hxWant]; exact h
    | inr hx' => exact hx'.1

/-- **The ladder holds for EVERY end served at the smaller supply** —
not only for the least urgent one.

This is the control, and it is deliberately stated in the strong form
Mises does not state. His sentence singles out "the least urgent or
least painful among all those wants which could be removed by means
of the supply n–1"; this theorem drops the qualifier and keeps the
conclusion. Whatever the extra unit adds is less urgent than
ANYTHING the smaller supply serves.

What it spends: `SwapDominant plan` — Rothbard's premise, and the
whole of the warrant problem — plus `IndependentUses` and decidable
equality of ends. Nothing Misesian at all. -/
theorem ladder_for_every_served
    {praxis : ActionFrame} [DecidableEq praxis.End]
    {agent : praxis.Agent} {time : praxis.Time}
    {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) (dominance : SwapDominant plan)
    (independent : praxis.IndependentUses agent time)
    (fewer more : Finset praxis.Means) (step : stock.OneMore fewer more) :
    ∀ kept ∈ plan.wouldServe fewer,
      ∀ added ∈ marginalEmployment plan fewer more,
        praxis.PrefersEnd agent time kept added := by
  intro kept hkept added hadded
  obtain ⟨haddedMore, haddedNotFewer⟩ := hadded
  have hfewerOnHand : fewer ⊆ stock.units := fun u hu => step.2.1 (step.1 hu)
  have haddedServes : added ∈ stock.serves :=
    plan.servesOnlyWhatItCan more added haddedMore
  have hswap := dominance.swap fewer hfewerOnHand kept hkept added
    haddedServes haddedNotFewer
  have hkeptCoe : kept ∈ (↑(plan.wouldServe fewer) : Set praxis.End) :=
    Finset.mem_coe.mpr hkept
  apply independent
    ((↑(plan.wouldServe fewer) : Set praxis.End) \ {kept}) kept added
  · exact fun hmem => hmem.2 rfl
  · exact fun hmem => haddedNotFewer (Finset.mem_coe.mp hmem.1)
  · rw [← insert_sdiff_self_of_mem' hkeptCoe]
    exact hswap

/-- **Mises's ladder, derived from Rothbard's premise** — the control
comes back positive.

`LadderHolds` follows outright from `SwapDominant` and
`IndependentUses`. Mises's own derivation — the dilemma about
intermediate stages, the appeal to the category of action — supplies
nothing the conclusion needs, once the conclusion is read
counterfactually.

**And his minimality qualifier does no work.** The hypothesis
`LeastUrgentServed plan fewer least` is a conjunction; only its first
half (that `least` is served at the smaller supply) is consumed. The
second half — that nothing served there ranks below it — is
destructured as `_minimality` and never used. The linter cannot see
this, because it works a whole binder at a time and both halves
arrive in one binder; `ladder_for_every_served` above is what makes
the idleness a machine fact instead of a comment.

So of the two things Mises's sentence adds to Rothbard's — the
upward direction and the "least urgent" restriction — the first is a
narration and the second is idle. -/
theorem ladder_holds
    {praxis : ActionFrame} [DecidableEq praxis.End]
    {agent : praxis.Agent} {time : praxis.Time}
    {stock : Stock praxis agent time}
    (plan : AllocationPlan stock) (dominance : SwapDominant plan)
    (independent : praxis.IndependentUses agent time) :
    LadderHolds plan := by
  intro fewer more step least hleast added hadded
  obtain ⟨hleastServed, _minimality⟩ := hleast
  exact ladder_for_every_served plan dominance independent fewer more step
    least hleastServed added hadded



/-! ## Route C: the dilemma about intermediate stages

Control A settled that Mises's CONCLUSION is Rothbard's. So the whole
difference between the routes is the warrant, and the warrant is this
paragraph:

> "There are only two alternatives. Either there are or there are not
> intermediate stages between the felt uneasiness which impels a man
> to act and the state in which there can no longer be any action (be
> it because the state of perfect satisfaction is reached or because
> man is incapable of any further improvement in his conditions). In
> the second case there could be only one action; as soon as this
> action is consummated, a state would be reached in which no further
> action is possible. This is manifestly incompatible with our
> assumption that there is action; this case no longer implies the
> general conditions presupposed in the category of action. Only the
> first case remains."

The definitions below are `Prop`-valued and assert NOTHING. What is
encoded is the SHAPE of Mises's argument, so that the steps can be
checked one at a time.

Note what is deliberately not attempted: "intermediate stages" is
read here through its stated CONSEQUENCE — "there could be only one
action" — rather than by inventing a primitive for degrees of
satisfaction. That keeps the vocabulary unchanged and makes the horn
statable in the frame we already have. Reading it the other way
(a second ordering on states by degree of uneasiness-removal) is a
real alternative and would enlarge the frame; it is the option kept
in reserve, and if the argument below cannot be completed without it,
that is the finding. -/

/-- **Mises's second horn**, by its stated consequence: there could
be only one action.

"In the second case there could be only one action; as soon as this
action is consummated, a state would be reached in which no further
action is possible."

Stated as at-most-one rather than with a terminal state and a
successor relation, because `Time` carries no order and Mises's own
consequence is a count, not a moment. -/
def AtMostOneAction (praxis : ActionFrame) : Prop :=
  ∀ first second : Action praxis, first = second

/-- **"Our assumption that there is action"** — bare existence.

This is the parked action axiom, in the only form the tradition
states it: there is action. See
`_notes/2026-09-04-parked-axioms.md`. -/
def ActionOccurs (praxis : ActionFrame) : Prop :=
  Nonempty (Action praxis)

/-- **What refuting the second horn actually requires** — that action
is plural.

Mises writes that one action followed by a terminal state is
"manifestly incompatible with our assumption that there is action".
It is not: see `ActionOccurs` above, and the counter-model in
`Apodictic.Consistency`. What IS incompatible with the second horn is
this — that two distinct actions occur.

Named here as a statement, NOT asserted. Whether the tradition
licenses it, and on what pedigree, is exactly the question route C
puts to Mises. His own hedge — "this case no longer implies the
general conditions presupposed in the category of action" — is
reaching for something past bare existence without saying what. -/
def ActionRecurs (praxis : ActionFrame) : Prop :=
  ∃ first second : Action praxis, first ≠ second

/-- **The refutation of the second horn, given plurality.** Trivial,
and that is the point: once the premise is `ActionRecurs` the step
Mises calls "manifestly incompatible" is immediate. All the weight
sits in whether that premise is his to use. -/
theorem recurs_refutes_second_horn {praxis : ActionFrame}
    (recurs : ActionRecurs praxis) : ¬ AtMostOneAction praxis := by
  intro atMostOne
  obtain ⟨first, second, hne⟩ := recurs
  exact hne (atMostOne first second)

/-- **Existence does not refute the second horn.** The converse of
what Mises needs, and it fails: `ActionOccurs` is compatible with
`AtMostOneAction` — exactly one action — so bare existence cannot do
the work his argument gives it.

Stated here as an implication about an arbitrary frame so that the
counter-model in `Apodictic.Consistency` refutes it by construction. -/
def ExistenceRefutesSecondHorn : Prop :=
  ∀ praxis : ActionFrame, ActionOccurs praxis → ¬ AtMostOneAction praxis

/-! ## Mises's bridge, stated in the vocabulary we already have

The dilemma does not deliver the law (`Apodictic.Consistency`). What
would? Mises's next sentence:

> "It is nothing else than the reverse of the statement that what
> satisfies more is preferred to what gives smaller satisfaction."

The tempting move is to add a scale of satisfaction to `ActionFrame`
— a second ordering on states by degree of uneasiness-removal. That
is REFUSED here, and deliberately. It would enlarge the ontology on
one sentence's authority, it invites cardinality through the back
door ("degrees", "asymptotic approach"), and there is reason to think
it would only relocate the problem: a satisfaction scale still has to
be connected to WHICH END A UNIT SERVES, and that connection is the
premise all over again.

So the reading below uses only what the frame already has. It is the
most generous reconstruction the existing vocabulary allows, and
whatever it costs lands on the signature where it can be read. -/

/-! Mises's bridge is now the praxeological claim
`Apodictic.ServedInOrder` (human ruling 2026-09-10), and comparability
of a good's serviceable ends is the situational condition
`Stock.ComparableServiceable` (same ruling). Both were drafted here and
have moved: claims live in `Praxeology.lean` and conditions beside the
vocabulary they constrain. -/

/-- **The ladder, derived the Misesian way.**

Neither `SwapDominant` nor `IndependentUses` appears. In their place:
the agent serves in order of urgency, and the ends the good can serve
are comparable. That is a genuinely different premise set for the same
conclusion — which is what the second theorem target was for.

The argument is Mises's own, made honest. The added end is
serviceable and unserved at the smaller supply. Were it MORE urgent
than something already served there, serving in order would have
admitted it — so it is not more urgent. Comparability turns "not more
urgent" into "less urgent", and that step is where the route pays.

Mises's minimality qualifier is idle here too: `least` need only be
served at the smaller supply, exactly as in `ladder_for_every_served`.
Two different premise sets, the same idle qualifier. -/
theorem ladder_from_order
    {praxis : ActionFrame}
    {agent : praxis.Agent} {time : praxis.Time}
    {stock : Stock praxis agent time}
    (plan : AllocationPlan stock)
    (order : ServedInOrder plan)
    (comparable : stock.ComparableServiceable) :
    LadderHolds plan := by
  intro fewer more step least hleast added hadded
  obtain ⟨hleastServed, _minimality⟩ := hleast
  obtain ⟨haddedMore, haddedNotFewer⟩ := hadded
  have hfewerOnHand : fewer ⊆ stock.units := fun u hu => step.2.1 (step.1 hu)
  have haddedServes : added ∈ stock.serves :=
    plan.servesOnlyWhatItCan more added haddedMore
  have hne : least ≠ added := by
    intro heq
    exact haddedNotFewer (heq ▸ hleastServed)
  rcases comparable least (plan.servesOnlyWhatItCan fewer least hleastServed)
      added haddedServes hne with hgood | hbad
  · exact hgood
  · exact absurd
      (order.inOrder fewer hfewerOnHand least hleastServed added haddedServes hbad)
      haddedNotFewer

#print axioms ladder_for_every_served
#print axioms ladder_holds
#print axioms recurs_refutes_second_horn
#print axioms ladder_from_order

end Mises
end Apodictic

#lint only unusedArguments
