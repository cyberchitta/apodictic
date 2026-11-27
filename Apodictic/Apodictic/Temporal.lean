import Apodictic.Praxeology

/-!
# The temporal reading of Mises's ladder

Mises's ladder runs upward — "if the supply available increases from
n–1 units to n units" — and `Apodictic.Mises` reads that as one
counterfactual comparison at one time. This module reads it the other
way, as a HISTORY: the agent held n–1 units at one time and served
what he served; at another time he holds n and serves what he serves.
Rothbard narrates the same history — the man who "successively finds
one horse, then a second, then a third" (*MES* p. 24).

## What the reading is for

Both routes in `Apodictic.Mises` rest on a standing plan over
sub-stocks the agent does not hold, and neither author warrants one.
The temporal reading has no plan. Its objects are two actual
allocations (`Allocation`), and its premise is a claim about actual
action (`ActsInOrder`). If it carried the law, the standing plan would
be an artifact of which passage was formalized. If it does not, the
law needs something no act exhibits on either reading.

## The one decision the reading forces

The ladder compares a want served at the earlier time with a want the
new unit serves at the later time. Preference is indexed by time, so
the comparison has to be made on SOME scale, and the reading does not
say which. `Ladder` therefore takes the judging time as a parameter,
and the two cases come apart:

- Judged on the earlier scale, the ladder is a theorem
  (`ladder_judged_earlier`).
- Judged on the later scale, it is refutable with acting in order,
  comparability and asymmetry granted at both times
  (`LadderJudgedLaterFromOrder`, refuted in `Apodictic.Model`).

What separates the two is constancy of the scale across the two times,
and the library does not assume it: Mises holds that scales
"have no independent existence apart from the actual behavior of
individuals" (ch. IV, §2), and Rothbard's own actor, a few pages
before the horses, changes his mind between moments: "the ranking on
his preference scale shifts to this order" (p. 18).

## Isolation

Imports `Apodictic.Praxeology` and nothing else, for the reason given
in `Apodictic.Mises`: whatever this route spends has to be stated here.
`Time` carries no order here either — "earlier" and "later" name the
two stocks, and no proof below asks which came first.
-/

namespace Apodictic
namespace Temporal

/-- **Least urgent among those served** — Mises's "the least urgent or
least painful among all those wants which could be removed by means of
the supply n–1", said of an actual allocation at its own time.

A situational condition on an end handed to a theorem, never asserted
to exist; as in `Apodictic.Mises.LeastUrgentServed`. -/
def LeastUrgentServed {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} {stock : Stock praxis agent time}
    (allocation : Allocation stock) (want : praxis.End) : Prop :=
  want ∈ allocation.served ∧
    ∀ other ∈ allocation.served, other ≠ want →
      praxis.PrefersEnd agent time other want

/-- **Mises's ladder as a history**, judged on the scale of a stated
time.

"If the supply available increases from n–1 units to n units, the
increment can be employed only for the removal of a want which is
less urgent or less painful than the least urgent or least painful
among all those wants which could be removed by means of the supply
n–1" (*Human Action*, ch. VII, §1).

Two phrases are read as history:

- "could be removed by means of the supply n–1" is read as WAS
  removed by it, at the earlier time.
- "the increment can be employed" is read as what the later
  allocation serves that the earlier did not.

Besides the two allocations, the definition takes a time, named
`judged`. It is the time whose scale ranks the two wants. Mises's
sentence does not say which. The choice matters. Judged on the earlier
scale, the ladder is a theorem (`ladder_judged_earlier`). Judged on
the later scale, it does not follow, even with acting in order,
comparability and asymmetry granted at both times
(`LadderJudgedLaterFromOrder`, shown false in
`Apodictic.Model.later_judged_ladder_fails`). -/
def Ladder {praxis : ActionFrame} {agent : praxis.Agent}
    {earlierTime laterTime : praxis.Time}
    {earlier : Stock praxis agent earlierTime}
    {later : Stock praxis agent laterTime}
    (before : Allocation earlier) (after : Allocation later)
    (judged : praxis.Time) : Prop :=
  ∀ least, LeastUrgentServed before least →
    ∀ added ∈ after.served, added ∉ before.served →
      praxis.PrefersEnd agent judged least added

/-- **The ladder, judged on the earlier scale** — a theorem, from a
claim about actual action and two situational conditions.

What it spends:

- The earlier allocation acts in order (`ActsInOrder before`).
- The good's serviceable ends are comparable at the earlier time
  (`earlier.ComparableServiceable`).
- Whatever the good is believed to serve at the later time, it was
  believed to serve at the earlier one (`earlier.NoNewUses later`).
  Acting in order and comparability speak only of the wants the good
  was believed able to serve at the earlier time. No new uses puts the
  newly served want among them.

What it does NOT spend, as the signature shows:

- Of the later allocation, nothing beyond which wants it serves.
- Nothing about the supply having grown. `Stock.Grows` is not a
  hypothesis. Added as one, it fails the unused-argument linter.
- Nothing about the order of the two times. "Earlier" and "later"
  are names only, not an order.
- Nothing about the later scale.

The argument is Mises's. The newly served want was serviceable and
unserved before. Comparability ranks it against a want served before,
one way or the other. Had it ranked above, acting in order would have
served it. So it ranks below.

Mises's sentence picks out "the least urgent or least painful among
all those wants which could be removed by means of the supply n–1",
read here as served before. The proof needs only that the compared
want was served, not that it was the least urgent one served. So that
qualifier is idle here. It is idle on the counterfactual readings
too: the ladder from Rothbard's premises (`Apodictic.Mises.ladder_holds`)
and from Mises's (`Apodictic.Mises.ladder_from_order`).

So this is the ladder as a statement about the EARLIER allocation.
What was passed over then ranked below what was served then. Of the
newly served want it says only that it was passed over then. -/
theorem ladder_judged_earlier
    {praxis : ActionFrame} {agent : praxis.Agent}
    {earlierTime laterTime : praxis.Time}
    {earlier : Stock praxis agent earlierTime}
    {later : Stock praxis agent laterTime}
    (before : Allocation earlier) (after : Allocation later)
    (order : ActsInOrder before)
    (comparable : earlier.ComparableServiceable)
    (noNewUses : earlier.NoNewUses later) :
    Ladder before after earlierTime := by
  intro least hleast added haddedAfter haddedNotBefore
  obtain ⟨hleastServed, _minimality⟩ := hleast
  have haddedServes : added ∈ earlier.serves :=
    noNewUses (after.servesOnlyWhatItCan added haddedAfter)
  have hne : least ≠ added := by
    intro heq
    exact haddedNotBefore (heq ▸ hleastServed)
  rcases comparable least (before.servesOnlyWhatItCan least hleastServed)
      added haddedServes hne with hgood | hbad
  · exact hgood
  · exact absurd
      (order.inOrder least hleastServed added haddedServes hbad)
      haddedNotBefore

/-- **The ladder, judged on the later scale, from acting in order,
comparability and asymmetry at both times** — written out as a statement in its own
right (in Lean, a `Prop`). That way it can be shown false: a small
frame is built in which every hypothesis holds and the conclusion
fails (`Apodictic.Model.later_judged_ladder_fails`).

Granted at BOTH times:

- Acting in order.
- Comparability of the good's ends.
- Asymmetry of preference.

Granted across the two times:

- The supply grew by one.
- The good is believed to serve the same ends.

Not granted: any relation between the two scales. The statement is
false in a frame where the scale reverses between the two times. Both
authors say that situation cannot be excluded. -/
def LadderJudgedLaterFromOrder : Prop :=
  ∀ (praxis : ActionFrame) (agent : praxis.Agent)
    (earlierTime laterTime : praxis.Time)
    (earlier : Stock praxis agent earlierTime)
    (later : Stock praxis agent laterTime)
    (before : Allocation earlier) (after : Allocation later),
    earlier.Grows later → later.serves = earlier.serves →
    ActsInOrder before → ActsInOrder after →
    earlier.ComparableServiceable → later.ComparableServiceable →
    AsymmetricPreference praxis agent earlierTime →
    AsymmetricPreference praxis agent laterTime →
    Ladder before after laterTime

#print axioms ladder_judged_earlier

end Temporal
end Apodictic

#lint only unusedArguments
