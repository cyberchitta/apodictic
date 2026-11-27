import Apodictic.Praxeology

/-!
# Time preference — Rothbard's universal, his durability corollary,
and Mises's regress

## What is proved, and what it costs

- `less_durable_preferred`: Rothbard's durability corollary (*MES*
  pp. 16–17, n. 16), for two goods whose services differ in one date.
  It costs `TimePreference` and one condition his sentence never shows
  — that preferring the sooner service carries up to the whole stream
  (`LiftsOverRest`). Only the one-slot case: more slots would chain
  preferences, and that needs transitivity of
  `Prefers`, which nothing here asserts.
- `consumption_reveals`: an act of consuming now what could have been
  had on the morrow shows a preference for now, at that date. It is
  `DemonstratedTimePreference`, applied.
- `regress`: Mises's regress. An act of consuming that demonstrates,
  with no preference carrying from each date to the next, refutes "no
  preference for the sooner at the first date". The regress adds
  exactly one thing to `consumption_reveals`: it carries the conclusion
  BACK to the first date — and only as a double negation. Neither
  delivers the universal — a preference at one date, for one sequence,
  is all either reaches.
- `valuation_reading_is_free`: the rejected encoding. Define "the same
  satisfaction" from the ranking, as n. 15 does, and the
  never-prefers-later half of time preference holds in every frame,
  with no claim at all.

## What `Before` is asked for

Nothing. No theorem here uses a property of `Before`: "sooner" enters
every statement as a label on a pair of dates, never as something an
argument turns on.
-/

namespace Apodictic
namespace TimePreference

/-- **The less durable good is preferred** (*MES* pp. 16–17, n. 16: "if the
actor values the total service rendered by two consumers' goods
equally, he will, because of time preference, choose the less durable
good"), in its smallest case.

Two goods render the same shared services, called `rest`, plus one
service more. The first renders that service at the earlier date.
That dated service is called `soon`. The second renders it at the
later date. That one is called `late`. The first is read as the less
durable good, since that one service of it comes sooner. "Values the
total service equally" is read as two things. The two services are the same satisfaction. And everything
else is the same `rest`.

The conclusion is a preference, not a choice. No claim in the library
runs from the ranking to which good the agent picks. -/
theorem less_durable_preferred
    {praxis : DatedFrame} {agent : praxis.Agent} {now : praxis.Time}
    (rest : Set praxis.End) (soon late : praxis.End)
    (timePreference : TimePreference praxis agent now)
    (same : praxis.SameSatisfaction agent soon late)
    (sooner : praxis.Before (praxis.attained soon) (praxis.attained late))
    (notPast : ¬ praxis.Before (praxis.attained soon) now)
    (lifts : praxis.LiftsOverRest agent now rest soon late) :
    praxis.Prefers agent now (insert soon rest) (insert late rest) :=
  lifts (timePreference.sooner soon late same sooner notPast)

/-- **Consuming reveals a preference for now, at that date.** -/
theorem consumption_reveals
    {praxis : DatedFrame} {agent : praxis.Agent}
    (morrows : Morrows praxis agent) (n : ℕ)
    (act : Action praxis.toActionFrame)
    (consumes : morrows.ConsumesAt n act)
    (sameAlternative : morrows.SameAlternative)
    (demonstrated : DemonstratedTimePreference act) :
    praxis.PrefersEnd agent (morrows.date n)
      (morrows.offer n) (morrows.offer (n + 1)) := by
  obtain ⟨hagent, htime, hchosen, hforgone⟩ := consumes
  subst hagent
  have hsame : praxis.SameSatisfaction act.agent act.chosen (morrows.offer (n + 1)) := by
    rw [hchosen]
    exact sameAlternative n
  have hbefore : praxis.Before (praxis.attained act.chosen)
      (praxis.attained (morrows.offer (n + 1))) := by
    rw [hchosen, morrows.dated n, morrows.dated (n + 1)]
    exact morrows.successive n
  have h := demonstrated.demonstrates _ hforgone hsame hbefore
  rw [htime, hchosen] at h
  exact h

/-- No preference for the sooner at the first date, carried forward,
is no preference at any date of the sequence. -/
theorem no_preference_at_every_date
    {praxis : DatedFrame} {agent : praxis.Agent}
    (morrows : Morrows praxis agent)
    (none : ¬ praxis.PrefersEnd agent (morrows.date 0)
      (morrows.offer 0) (morrows.offer 1))
    (carries : morrows.NoPreferenceCarries) :
    ∀ n, ¬ praxis.PrefersEnd agent (morrows.date n)
      (morrows.offer n) (morrows.offer (n + 1)) := by
  intro n
  induction n with
  | zero => exact none
  | succ k ih => exact carries k ih

/-- **Mises's regress** (*Human Action*, ch. XVIII, §2): "If he were
not to prefer satisfaction in a nearer period of the future to that in
a remoter period, he would never consume and so satisfy wants. ... He
would not consume today, but he would not consume tomorrow either, as
the morrow would confront him with the same alternative."

It is stated from the act. Take an act of consuming at any date of the
sequence (`Morrows.ConsumesAt`). Say the act shows a preference for
the sooner (`DemonstratedTimePreference`). Then it refutes "no
preference for the sooner at the first date". What the argument
spends is in the signature:

- the claim that the act shows that preference (Mises's "reveals", in
  the same section);
- that the act consumes at that date;
- that each day's offer is the same satisfaction as the next (his "the
  same alternative");
- that the absence of preference carries from date to date.

The conclusion is a double negation. The argument refutes the absence
of a preference at the first date. It does not produce the preference.
That follows from how Mises words the step. He carries the ABSENCE of a
preference forward ("he would not consume tomorrow either"). So does
`NoPreferenceCarries`. Getting the preference itself back from that
needs excluded middle: at the first date he either prefers the sooner
or does not. The library does not assume excluded middle. The condition
could be carried the other way instead, as a preference passed back
from each date to the one before. Then it would give the preference
directly. -/
theorem regress
    {praxis : DatedFrame} {agent : praxis.Agent}
    (morrows : Morrows praxis agent) (n : ℕ)
    (act : Action praxis.toActionFrame)
    (consumes : morrows.ConsumesAt n act)
    (sameAlternative : morrows.SameAlternative)
    (demonstrated : DemonstratedTimePreference act)
    (carries : morrows.NoPreferenceCarries) :
    ¬ ¬ praxis.PrefersEnd agent (morrows.date 0)
      (morrows.offer 0) (morrows.offer 1) :=
  fun none => no_preference_at_every_date morrows none carries n
    (consumption_reveals morrows n act consumes sameAlternative demonstrated)

/-- "The same satisfaction", fixed by the ranking: the later is not
preferred to the sooner. This is the reading of *MES* pp. 15–16, n. 15.
Ice in summer "provides different (and greater) satisfactions" than ice
in winter. So the two are different goods. REJECTED as the library's
encoding. It is stated so that the rejection is checked. -/
def SameByValuation (praxis : DatedFrame) (agent : praxis.Agent)
    (now : praxis.Time) (soon late : praxis.End) : Prop :=
  ¬ praxis.PrefersEnd agent now late soon

/-- **On the valuation reading, time preference's negative half is
free.** Take any frame, agent and date. Take two ends that are the
same satisfaction by valuation. Then the later is never preferred. No
claim is carried: the signature has none. That is because the sentence
was made true by what "same" was allowed to mean.

On this reading the strict half, that the sooner IS preferred, is
NOT free. Take two ends, neither preferred to the other. The valuation
reading counts them the same satisfaction. Time preference then asserts
a preference that is not there. So on this reading the claim says one
thing. Take two ends, one before the other, the sooner not yet past.
If the later is not preferred to the sooner, then the sooner is
preferred to the later. So the pair is never left unranked. That is a
form of comparability, and neither author argues for it. -/
theorem valuation_reading_is_free (praxis : DatedFrame)
    (agent : praxis.Agent) (now : praxis.Time) :
    ∀ soon late : praxis.End,
      SameByValuation praxis agent now soon late →
        ¬ praxis.PrefersEnd agent now late soon :=
  fun _ _ same => same

#print axioms less_durable_preferred
#print axioms consumption_reveals
#print axioms regress
#print axioms valuation_reading_is_free

end TimePreference
end Apodictic

#lint only unusedArguments
