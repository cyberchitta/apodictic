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
- Judged on the later scale, it is refutable with every one-time
  premise granted at both times
  (`LadderJudgedLaterFromOrder`, refuted in `Apodictic.Model`).

What separates the two is constancy of the scale across the two times,
and that is refused (owner ruling 2026-09-11): Mises holds that scales
"have no independent existence apart from the actual behavior of
individuals" (ch. IV, §2), and Rothbard, in the sentence after his
horse-by-horse history, that units "may and will be valued differently
whenever their position in the supply is different" (p. 24).

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
n–1" (*Human Action*, ch. VII, §1) — with "could be removed by means
of the supply n–1" read as WAS removed by it, at the earlier time, and
"the increment can be employed" as what the later allocation serves
that the earlier did not.

`judged` is the time whose scale ranks the two wants. Mises's
sentence does not say which; the module docstring says why it
matters. -/
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

What it spends: that the earlier allocation acts in order
(`ActsInOrder before`); that the good's serviceable ends are
comparable at the earlier time; and that whatever the good is
believed to serve at the later time it was believed to serve at the
earlier one (`sameJobs`) — the increment's want has to be on the
earlier scale at all before that scale can rank it.

What it does NOT spend, and the signature shows: nothing about the
later allocation beyond membership, nothing about the supply having
grown (`Stock.Grows` is not a hypothesis — added as one, it fails the
unused-argument linter), nothing about the order of the two times,
and nothing about the later scale. The argument is Mises's: the added
want was serviceable and unserved before; had it been more urgent than
something served, acting in order would have served it. Mises's
minimality qualifier is idle here as on both counterfactual routes:
`least` need only have been served.

So this is the ladder as a statement about the EARLIER allocation:
what was passed over ranked below what was served, then. It says of
the increment only that it was passed over. -/
theorem ladder_judged_earlier
    {praxis : ActionFrame} {agent : praxis.Agent}
    {earlierTime laterTime : praxis.Time}
    {earlier : Stock praxis agent earlierTime}
    {later : Stock praxis agent laterTime}
    (before : Allocation earlier) (after : Allocation later)
    (order : ActsInOrder before)
    (comparable : earlier.ComparableServiceable)
    (sameJobs : later.serves ⊆ earlier.serves) :
    Ladder before after earlierTime := by
  intro least hleast added haddedAfter haddedNotBefore
  obtain ⟨hleastServed, _minimality⟩ := hleast
  have haddedServes : added ∈ earlier.serves :=
    sameJobs (after.servesOnlyWhatItCan added haddedAfter)
  have hne : least ≠ added := by
    intro heq
    exact haddedNotBefore (heq ▸ hleastServed)
  rcases comparable least (before.servesOnlyWhatItCan least hleastServed)
      added haddedServes hne with hgood | hbad
  · exact hgood
  · exact absurd
      (order.inOrder least hleastServed added haddedServes hbad)
      haddedNotBefore

/-- **The ladder, judged on the later scale, from everything a
one-time premise can give** — written out as a `Prop` so that it can
be refuted by construction (`Apodictic.Model.later_judged_ladder_fails`).

Granted at BOTH times: acting in order, comparability of the good's
ends, asymmetry of preference. Granted across them: that the supply
grew by one and that the good is believed to serve the same ends. Not
granted: any relation between the two scales. The statement is false
in a frame where the scale reverses between the two times, which is
the situation both authors say cannot be excluded. -/
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
