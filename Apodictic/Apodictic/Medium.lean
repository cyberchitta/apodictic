import Apodictic.Exchange

/-!
# Medium — the vocabulary of indirect exchange

Definitions ONLY: this file asserts nothing. The claims about it,
`AppraisalFromPast` and `TwoPartialDemands`, are in
`Apodictic.Praxeology`. The situational
conditions are here, as definitions a theorem takes as named hypotheses.

## What is added

- `MediumFrame`: an action frame with one bare relation more,
  `Onward m e` — `e` is an end the agent would reach by giving `m`
  itself away in a later trade. Mises's medium of exchange is a good
  wanted "to keep it as a medium of exchange and to give it away at
  need in a later act of exchange" (*Human Action*, ch. XVII, §4).
  Supplied, like `SameSatisfaction`; no link to `Believes` or
  `Prefers`.
- `History`: the record of exchanges that happened, day by day, with
  days indexed by ℕ. No `Prop` field.

## What "a medium" is

Defined by BELIEF: someone appraises `m` as a medium at a time when he
believes `m` serves an onward end (`AppraisesAsMedium`). Not by the
presence of an appraisal of its price (which would make the regress true by
definition), and not by an actual later trade: anticipatory demand
counts as monetary demand.

## Shape claims (audit)

- An element of `Means` is read here as a KIND of good (gold, salt),
  not as a unit. The regress is about the kind: a coin minted today was
  never traded before, and the theorem is not about that coin. Nothing
  in `Trade` fixes either reading; `Stock` reads `Means` as units, and
  no `Stock` appears in the regression theorem.
- An end is onward FOR A GOOD: `Onward m e` ties the end to giving `m`
  itself away. A baker's flour serves the end of selling bread, but
  the bread is what is given away, so that end is not onward for flour.
- Days are ℕ: every day has a predecessor except day 0, and from any
  day there are finitely many days back to day 0. That half of the
  regress's termination is supplied by the type, not argued.
-/

namespace Apodictic


/-- An action frame with onward ends. -/
structure MediumFrame extends ActionFrame where
  /-- `Onward m e`: `e` is an end the agent would reach by giving `m`
  itself away in a later trade. No properties. -/
  Onward : Means → End → Prop

/-- The agent, at that time, believes `m` serves some onward end: he
appraises `m` as a medium of exchange. -/
def MediumFrame.AppraisesAsMedium (praxis : MediumFrame) (agent : praxis.Agent)
    (time : praxis.Time) (m : praxis.Means) : Prop :=
  ∃ e, praxis.Onward m e ∧ praxis.Believes agent time m e

/-- The agent, at that time, believes `m` serves some end other than an
onward one: he values `m` for an "other employment" in the broad
reading. -/
def MediumFrame.ValuesDirectly (praxis : MediumFrame) (agent : praxis.Agent)
    (time : praxis.Time) (m : praxis.Means) : Prop :=
  ∃ e, ¬ praxis.Onward m e ∧ praxis.Believes agent time m e

/-- The onward ends the agent believes `m` serves: the medium-of-exchange
part of his demand for it. -/
def MediumFrame.OnwardEnds (praxis : MediumFrame) (agent : praxis.Agent)
    (time : praxis.Time) (m : praxis.Means) : Set praxis.End :=
  {e | praxis.Onward m e ∧ praxis.Believes agent time m e}

/-- The other ends the agent believes `m` serves: the direct part of his
demand for it. -/
def MediumFrame.DirectEnds (praxis : MediumFrame) (agent : praxis.Agent)
    (time : praxis.Time) (m : praxis.Means) : Set praxis.End :=
  {e | ¬ praxis.Onward m e ∧ praxis.Believes agent time m e}

/-- **Indirect exchange** — a trade in which the agent, at the time of
trading, appraises the good he gets as a medium. -/
def Trade.Indirect {praxis : MediumFrame} (trade : Trade praxis.toActionFrame) :
    Prop :=
  praxis.AppraisesAsMedium trade.agent trade.time trade.gets

/-- **Purely indirect** — a condition on one trade. Every end the agent
believes the received good serves is an onward end: he wants it only to
pass it on. Fails where the good is also wanted for itself. -/
def Trade.PurelyIndirect {praxis : MediumFrame}
    (trade : Trade praxis.toActionFrame) : Prop :=
  ∀ e, praxis.Believes trade.agent trade.time trade.gets e →
    praxis.Onward trade.gets e

/-- The record of exchanges that happened: on day `k`, at time
`date k`, the exchanges in `exchanges k` were made.

Shape (audit): the day of an exchange is its index here, and each
party's beliefs about it are read at `date k`. The `time` fields of the
exchange's two trades are not consulted. Nothing says the record is
complete; a claim asserted of an incomplete record asserts more than
one asserted of the complete one. -/
structure History (praxis : MediumFrame) where
  /-- The time of each day. -/
  date : ℕ → praxis.Time
  /-- The exchanges made on each day. -/
  exchanges : ℕ → Set (Exchange praxis.toActionFrame)

/-- `m` changed hands on day `k`, against anything. -/
def History.ExchangedOn {praxis : MediumFrame} (history : History praxis)
    (k : ℕ) (m : praxis.Means) : Prop :=
  ∃ x ∈ history.exchanges k, x.first.gets = m ∨ x.first.gives = m

/-- On day `k`, `agent` acquired `m`, giving `g` for it. -/
def History.AcquiredAgainst {praxis : MediumFrame} (history : History praxis)
    (k : ℕ) (m : praxis.Means) (agent : praxis.Agent) (g : praxis.Means) :
    Prop :=
  ∃ x ∈ history.exchanges k,
    (x.first.agent = agent ∧ x.first.gets = m ∧ x.first.gives = g) ∨
      (x.second.agent = agent ∧ x.second.gets = m ∧ x.second.gives = g)

/-- On day `n`, someone appraises `m` as a medium. -/
def History.MediumAt {praxis : MediumFrame} (history : History praxis)
    (n : ℕ) (m : praxis.Means) : Prop :=
  ∃ agent, praxis.AppraisesAsMedium agent (history.date n) m

/-- On day `k`, someone acquired `m` for an end other than passing it
on: `m` had "exchange value on account of other employments", in the
broad reading. -/
def History.DirectAcquisitionAt {praxis : MediumFrame} (history : History praxis)
    (k : ℕ) (m : praxis.Means) : Prop :=
  ∃ agent g, history.AcquiredAgainst k m agent g ∧
    praxis.ValuesDirectly agent (history.date k) m

/-- On day `k`, someone acquired `m` for an end other than passing it
on that is in `narrow`. -/
def History.NarrowAcquisitionAt {praxis : MediumFrame} (history : History praxis)
    (narrow : praxis.End → Prop) (k : ℕ) (m : praxis.Means) : Prop :=
  ∃ agent g, history.AcquiredAgainst k m agent g ∧
    ∃ e, ¬ praxis.Onward m e ∧ praxis.Believes agent (history.date k) m e ∧
      narrow e

/-- **The record begins before the medium** — a condition on the
situation. On day 0 nobody appraises `m` as a medium. Mises: "the
regression does not go back endlessly" (*Human Action*, ch. XVII, §4);
Rothbard: "as we regress backwards in time, we must eventually arrive
at the original point when people first began to use gold as a medium
of exchange" (*MES* p. 272). Both assert it; neither argues it. Fails
of a record that starts inside a monetary economy. -/
def History.BeginsBeforeMedium {praxis : MediumFrame} (history : History praxis)
    (m : praxis.Means) : Prop :=
  ¬ history.MediumAt 0 m

/-- **Acquisitions are purposive** — a condition on the situation.
Whoever acquired `m` before day `n` believed, that day, that `m`
serves some end. Fails where a good is taken only to be rid of the
good given for it. -/
def History.AcquisitionsPurposive {praxis : MediumFrame} (history : History praxis)
    (m : praxis.Means) (n : ℕ) : Prop :=
  ∀ k < n, ∀ agent g, history.AcquiredAgainst k m agent g →
    ∃ e, praxis.Believes agent (history.date k) m e

/-- **Own past price** — a condition, in the only form the vocabulary
can state without quantities: whoever appraises `m` as a medium on a
day before `n` does so after an exchange of `m` on an earlier day.
"The appraisal RESTS ON that exchange" cannot be said here; what can
be said coincides with the claim `AppraisalFromPast`, restricted to the
days before `n` (`Apodictic.Regression.ownPastPrice_of_claim`). -/
def History.OwnPastPrice {praxis : MediumFrame} (history : History praxis)
    (m : praxis.Means) (n : ℕ) : Prop :=
  ∀ j, j + 1 < n → ∀ agent,
    praxis.AppraisesAsMedium agent (history.date (j + 1)) m →
      ∃ k ≤ j, history.ExchangedOn k m

/-- **Formed in barter** — a condition on the situation. Whatever was
given for `m` on a day before `n` was not, that day, appraised as a
medium by anyone. Rothbard: "it can arise only out of a commodity
previously used directly in a barter situation" (*MES* p. 275). Fails
for every good first bought with money. -/
def History.FormedInBarter {praxis : MediumFrame} (history : History praxis)
    (m : praxis.Means) (n : ℕ) : Prop :=
  ∀ k < n, ∀ agent g, history.AcquiredAgainst k m agent g →
    ¬ history.MediumAt k g

/-- **Other employments are consumption or production** — the narrow
reading, as a condition on ends. Every end other than an
onward one for which `m` was acquired before day `n` is in `narrow`.
`narrow` is supplied by whoever applies the theorem, the ends Mises
means by "the services it can render directly to consumption or
production" (*Human Action*, ch. XVII, §4); the library sorts no ends.
Fails where a good was first wanted for a game, a cause, or a test. -/
def History.OtherEmploymentsNarrow {praxis : MediumFrame}
    (history : History praxis) (narrow : praxis.End → Prop)
    (m : praxis.Means) (n : ℕ) : Prop :=
  ∀ k < n, ∀ agent g, history.AcquiredAgainst k m agent g →
    ∀ e, ¬ praxis.Onward m e → praxis.Believes agent (history.date k) m e →
      narrow e

end Apodictic
