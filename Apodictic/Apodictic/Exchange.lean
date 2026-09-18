import Apodictic.Action

/-!
# Exchange — the vocabulary of a two-party trade

Definitions ONLY: this file asserts nothing. The one claim about
action that exchange spends — demonstrated preference — is in
`Apodictic.Praxeology`; the situational conditions are here, as
definitions a theorem takes as named hypotheses.

## Goods count for the ends they are believed to serve

Rothbard's value scales at *MES* p. 85 list goods ("1—(Good Y)
2—Good X"). The library has no ranking of goods: `Prefers` ranks
bundles of ENDS. A good enters only through `Believes` — it counts for
the ends the agent believes it can serve (`ServedBy`). So "A values Y
above X" is read as "A prefers the ends he believes Y serves to the
ends he believes X serves". No imputation claim is made; the reading
is a translation, and it keeps the means–ends link inside the agent's
beliefs.

Shape claim (audit): a holding counts for the UNION of what its goods
are believed able to serve. Two goods serving the same end count
once, and a good counts for every end it could serve, not for one it
would be put to. For unique goods with separate uses — the scope here,
Rothbard's vase and typewriter (*MES* p. 86) — the two readings agree;
where they part, `KeptServesOtherEnds` is the condition that fails.

## Beliefs and rankings are read at a stated time

Every bundle below is computed from the agent's beliefs at a time
passed in (`judged`), not at the trade's own time. That is what lets
"better off after the exchange" be asked on a later scale and a later
set of beliefs, and come apart into the two ways it can fail.
-/

namespace Apodictic

/-- The ends the agent, at that time, believes some good in `goods`
can serve. The bundle a holding counts for. -/
def ActionFrame.ServedBy (praxis : ActionFrame) (agent : praxis.Agent)
    (time : praxis.Time) (goods : Set praxis.Means) : Set praxis.End :=
  {want | ∃ good ∈ goods, praxis.Believes agent time good want}

/-- **Separable from the rest of the holding** — a condition on the
situation, NOT a universal claim. Preferring one holding to another
that differs only in one part carries down to preferring the one part
to the other, provided neither part serves an end the rest already
serves.

The bundle-level cousin of `IndependentUses`. It fails for
complements: a left shoe is worth little without the right one kept
beside it, so preferring (right shoe + a hat) to (right shoe + a left
shoe) need not mean preferring a hat to a left shoe — or the reverse
need not carry. Rothbard's p. 85 scales list the two goods alone and
never mention the rest of what the traders own; this is what that
omission costs. -/
def ActionFrame.SeparableFromRest (praxis : ActionFrame)
    (agent : praxis.Agent) (time : praxis.Time) : Prop :=
  ∀ (rest X Y : Set praxis.End), Disjoint X rest → Disjoint Y rest →
    praxis.Prefers agent time (X ∪ rest) (Y ∪ rest) →
      praxis.Prefers agent time X Y

/-- One party's side of a trade: at `time`, `agent` gives up the good
`gives` and receives `gets`, keeping `kept`.

`refusal` is what the agent would have been left with had he refused,
as a bundle of ends. In a voluntary trade that is simply his holding
before the trade (`Trade.Voluntary`); under a threat it is worse. It is
a field because the act alone does not fix it: the same handing-over
is a trade or a robbery according to what refusing would have cost.

Shape: our-reconstruction. That the two goods differ is Rothbard's own
("we implicitly assumed that it must be two different goods that are
being exchanged", *MES* p. 95). -/
structure Trade (praxis : ActionFrame) where
  /-- The trading party. -/
  agent : praxis.Agent
  /-- When the trade is made. -/
  time : praxis.Time
  /-- The good given up. -/
  gives : praxis.Means
  /-- The good received. -/
  gets : praxis.Means
  /-- The rest of the agent's holding, untouched by the trade. -/
  kept : Set praxis.Means
  /-- What refusing would have left him with, as ends. -/
  refusal : Set praxis.End
  /-- Two different goods change hands. -/
  gives_ne_gets : gives ≠ gets
  /-- The good given up is not also kept. -/
  gives_not_kept : gives ∉ kept
  /-- The good received was not already held. -/
  gets_not_kept : gets ∉ kept

/-- The holding before the trade, counted by the agent's beliefs at
`judged`. -/
def Trade.before {praxis : ActionFrame} (trade : Trade praxis)
    (judged : praxis.Time) : Set praxis.End :=
  praxis.ServedBy trade.agent judged (insert trade.gives trade.kept)

/-- The holding after the trade, counted by the agent's beliefs at
`judged`. -/
def Trade.after {praxis : ActionFrame} (trade : Trade praxis)
    (judged : praxis.Time) : Set praxis.End :=
  praxis.ServedBy trade.agent judged (insert trade.gets trade.kept)

/-- **Voluntary** — a condition on the situation. Refusing would have
left the agent with exactly what he held: nobody made refusal cost
more. Rothbard confines the analysis of exchange to "actions that are
purely voluntary" (*MES* p. 85), and rests the inference to benefit on
it: "The only reason we know that A and B benefit from an exchange is
that they voluntarily make the exchange" (p. 1239). -/
def Trade.Voluntary {praxis : ActionFrame} (trade : Trade praxis) : Prop :=
  trade.refusal = trade.before trade.time

/-- **The kept goods serve other ends** — a condition on the
situation, at the trade's time. Nothing the agent keeps is believed to
serve an end either traded good serves. It fails for substitutes: an
agent with two umbrellas who trades one away gives up no end, on the
union count, and so demonstrates no ranking of the umbrella at all.
It is the scope of "unique goods" (*MES* p. 86) made explicit. -/
def Trade.KeptServesOtherEnds {praxis : ActionFrame} (trade : Trade praxis) :
    Prop :=
  Disjoint (praxis.ServedBy trade.agent trade.time {trade.gives})
      (praxis.ServedBy trade.agent trade.time trade.kept) ∧
    Disjoint (praxis.ServedBy trade.agent trade.time {trade.gets})
      (praxis.ServedBy trade.agent trade.time trade.kept)

/-- **Beliefs about the goods hold** at `later` — a condition on the
situation. Every good in the trade is believed at `later` to serve
exactly what it was believed to serve when the trade was made. It
fails when the agent learns the good he got does less than he thought
— error, or fraud. -/
def Trade.BeliefsHold {praxis : ActionFrame} (trade : Trade praxis)
    (later : praxis.Time) : Prop :=
  ∀ good, (good = trade.gives ∨ good = trade.gets ∨ good ∈ trade.kept) →
    ∀ want, praxis.Believes trade.agent later good want ↔
      praxis.Believes trade.agent trade.time good want

/-- **The ranking of the two holdings holds** at `later` — a
condition on the situation. If, when trading, the agent ranked the
holding he chose above the one he gave up, he still does. It fails
when he changes his mind — regret. Only this one pair is constrained;
nothing is said of the rest of his scale. -/
def Trade.RankingHolds {praxis : ActionFrame} (trade : Trade praxis)
    (later : praxis.Time) : Prop :=
  praxis.Prefers trade.agent trade.time
      (trade.after trade.time) (trade.before trade.time) →
    praxis.Prefers trade.agent later
      (trade.after trade.time) (trade.before trade.time)

/-- A two-party exchange: two trades at one time, each party giving
what the other gets. "A gives up a good to B in exchange for a good
that B gives up to A" (*MES* p. 85). -/
structure Exchange (praxis : ActionFrame) where
  /-- A's side. -/
  first : Trade praxis
  /-- B's side. -/
  second : Trade praxis
  /-- Two people. -/
  two_people : first.agent ≠ second.agent
  /-- One exchange, one time. -/
  same_time : first.time = second.time
  /-- What A gives, B gets. -/
  swap_gives : second.gets = first.gives
  /-- What B gives, A gets. -/
  swap_gets : second.gives = first.gets

end Apodictic
