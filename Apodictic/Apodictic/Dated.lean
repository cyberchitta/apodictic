import Apodictic.Action

/-!
# Dated — the vocabulary of time preference

Definitions ONLY: this file asserts nothing. The claims time preference
spends are in `Apodictic.Praxeology`; the situational conditions are
here, as definitions a theorem takes as named hypotheses.

## Why a second frame

`ActionFrame` gives `Time` no order and ends no date, and no theorem
before time preference asked for either. Time preference is the first
claim that cannot be stated without "sooner", so the vocabulary grows
here — by EXTENDING the frame rather than editing it, so that no
earlier theorem acquires vocabulary it does not use.

## What is added, and what is not

- `Before`: a bare relation on times. Not assumed transitive,
  irreflexive or total; a theorem that needs one of those says so.
- `attained`: each end carries the time at which it is attained.
  Shape claim (audit): a function, so an end has exactly one date, and
  "the same end a day later" is a different end.
- `SameSatisfaction`: which pairs of ends are the same satisfaction at
  two dates. A bare relation, per agent, with no properties and NO
  link to `Prefers`. Who fixes it is the question time preference turns
  on (MES pp. 15–16, n. 15; `Apodictic.TimePreference`), so it is
  supplied, never defined from the ranking.
-/

namespace Apodictic

/-- An action frame whose times can be compared and whose ends carry a
date. -/
structure DatedFrame extends ActionFrame where
  /-- `Before t t'`: `t` comes before `t'`. No properties. -/
  Before : Time → Time → Prop
  /-- When the end is attained. -/
  attained : End → Time
  /-- `SameSatisfaction agent e e'`: for that agent, `e` and `e'` are
  the same satisfaction, differing (at most) in date. Supplied
  independently of `Prefers`. -/
  SameSatisfaction : Agent → End → End → Prop

/-- **Lifts over the rest** — a condition on the situation, NOT a
universal claim. Preferring one end to another carries UP. It becomes
preferring the bundle `rest` with the one to `rest` with the other.

It is the converse direction of `IndependentUses`, fixed to one pair
and one rest. It fails for complements and clashes. Say a sooner
delivery collides with something else in `rest`: two services due at
one moment. Then the bundle with the later one can be better, though
the sooner one alone is preferred. -/
def DatedFrame.LiftsOverRest (praxis : DatedFrame) (agent : praxis.Agent)
    (now : praxis.Time) (rest : Set praxis.End) (soon late : praxis.End) :
    Prop :=
  praxis.PrefersEnd agent now soon late →
    praxis.Prefers agent now (insert soon rest) (insert late rest)

/-- **The morrow's alternative** — Mises's regress, as data. At each
date in a sequence the agent can have a satisfaction now. Or he can
have the same satisfaction at the next date: "the morrow would confront
him with the same alternative" (*Human Action*, ch. XVIII, §2).

It is a structure because the regress is about one such sequence.
Besides the dates and the offers, its fields state only two facts:
which offer belongs to which date, and that each date comes before
the next. That each offer is the same
satisfaction as the next is what makes it the SAME alternative. It can
fail: the good perishes. So it is not a field. It is the named
condition `Morrows.SameAlternative`. -/
structure Morrows (praxis : DatedFrame) (agent : praxis.Agent) where
  /-- The successive dates. -/
  date : ℕ → praxis.Time
  /-- The satisfaction on offer at each date. -/
  offer : ℕ → praxis.End
  /-- The offer at a date is attained at that date. -/
  dated : ∀ n, praxis.attained (offer n) = date n
  /-- Each date comes before the next. -/
  successive : ∀ n, praxis.Before (date n) (date (n + 1))

/-- **The same alternative each day** — a condition on the situation.
For this agent, each day's offer is the same satisfaction as the next
day's. It is Mises's "the morrow would confront him with the same
alternative". It fails where the good perishes. It fails for Mises's
own ice. Winter ice serves in summer only after a process of
conservation. -/
def Morrows.SameAlternative {praxis : DatedFrame} {agent : praxis.Agent}
    (morrows : Morrows praxis agent) : Prop :=
  ∀ n, praxis.SameSatisfaction agent (morrows.offer n) (morrows.offer (n + 1))

/-- The agent consumes at date `n`: the act, at that date, takes the
offer now and forgoes the offer on the morrow. -/
def Morrows.ConsumesAt {praxis : DatedFrame} {agent : praxis.Agent}
    (morrows : Morrows praxis agent) (n : ℕ)
    (act : Action praxis.toActionFrame) : Prop :=
  act.agent = agent ∧ act.time = morrows.date n ∧
    act.chosen = morrows.offer n ∧ morrows.offer (n + 1) ∈ act.forgone

/-- **No time preference carries to the morrow** — a condition on the
situation. Say on some date the agent does not prefer the offer now to
the offer on the morrow. Then he does not on the next date either.

This is constancy of the scale, cut to the one thing the regress
spends: the ABSENCE of a preference, for this sequence, from one date
to the next. Both authors deny constancy in general (Rothbard: scales
"differ for the same individual at different times", *MES* p. 17). -/
def Morrows.NoPreferenceCarries {praxis : DatedFrame} {agent : praxis.Agent}
    (morrows : Morrows praxis agent) : Prop :=
  ∀ n, ¬ praxis.PrefersEnd agent (morrows.date n)
        (morrows.offer n) (morrows.offer (n + 1)) →
    ¬ praxis.PrefersEnd agent (morrows.date (n + 1))
        (morrows.offer (n + 1)) (morrows.offer (n + 2))

end Apodictic
