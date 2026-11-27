import Apodictic.Action

/-!
# Exchange — the vocabulary of a two-party trade

Definitions ONLY: this file asserts nothing. The one claim about
action that exchange spends — demonstrated preference — is in
`Apodictic.Praxeology`; the situational conditions are here, as
definitions a theorem takes as named hypotheses.

## Goods count for the ends they are believed to serve

Rothbard's value scales at *MES* p. 85 rank goods: A's column puts
"(Good Y)" first and "Good X" second. The library has no ranking of goods: `Prefers` ranks
bundles of ENDS. A good enters only through `Believes` — it counts for
the ends the agent believes it can serve (`ServedBy`). So "A values Y
above X" is read as "A prefers the ends he believes Y serves to the
ends he believes X serves". No imputation claim is made, and the
means–ends link stays inside the agent's beliefs; but how a holding is
counted is a choice, recorded next.

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

/-- The ends the agent believes, at that time, that some good in
`goods` can serve. A holding counts for this bundle. -/
def ActionFrame.ServedBy (praxis : ActionFrame) (agent : praxis.Agent)
    (time : praxis.Time) (goods : Set praxis.Means) : Set praxis.End :=
  {want | ∃ good ∈ goods, praxis.Believes agent time good want}

/-- One party's side of a trade. At `time`, `agent` gives up the good
`gives`. He receives `gets`. He keeps `kept`.

`refusal` is what the agent would have been left with had he refused.
It is a bundle of ends. In a voluntary trade it is simply his holding
before the trade (`Trade.Voluntary`). Under a threat it is worse. It
is a field because the act alone does not fix it. The same
handing-over is a trade or a robbery. Which one it is depends on what
refusing would have cost.

Shape: our-reconstruction. That is, the choice of fields that set out
a trade is ours. `kept` is read as the rest of the holding.
A `Trade` whose given or received good is also among the kept
describes no trade. Nothing rules that out, because no theorem in the
library needs it ruled out. Rothbard assumes the two goods differ ("we
implicitly assumed that it must be two different goods that are being
exchanged", *MES* p. 95). For him it is a condition for an exchange to
take place. No theorem in the library uses that either. So a `Trade`
does not require it. -/
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
left the agent with exactly what he held. Nobody made refusal cost
more. Rothbard confines the analysis of exchange to "actions that are
purely voluntary" (*MES* p. 85). He rests the inference to benefit on
voluntariness: "The only reason we know that A and B benefit from an exchange is
that they voluntarily make the exchange" (p. 1239). -/
def Trade.Voluntary {praxis : ActionFrame} (trade : Trade praxis) : Prop :=
  trade.refusal = trade.before trade.time

/-- **The kept goods serve other ends than the traded goods** — a
condition on the situation, at the trade's time. Nothing the agent
keeps is believed to serve an end either traded good serves. It fails
for substitutes. Take an agent with two umbrellas who trades one away.
The umbrella he keeps serves every end the traded one serves. Two goods
that serve one end count for it once. So he gives up no end, and he
demonstrates no ranking of the umbrella at all.
It is the scope of "unique goods" (*MES* p. 86) made explicit. -/
def Trade.KeptServesOtherEnds {praxis : ActionFrame} (trade : Trade praxis) :
    Prop :=
  Disjoint (praxis.ServedBy trade.agent trade.time {trade.gives})
      (praxis.ServedBy trade.agent trade.time trade.kept) ∧
    Disjoint (praxis.ServedBy trade.agent trade.time {trade.gets})
      (praxis.ServedBy trade.agent trade.time trade.kept)

/-- **Separable from what is kept** — a condition on the situation, NOT
a universal claim. Take two holdings that differ in one part only.
If the agent prefers one holding to the other, he prefers its part to
the other's. It speaks only of holdings whose rest is what this agent
keeps in this trade. It speaks only of parts that share no end with
the kept goods. So it reaches the two traded goods only if their ends
share none with the kept goods' ends. The substitutes condition
(`Trade.KeptServesOtherEnds`) says exactly that.

It is like independence of uses (`IndependentUses`). That condition
says a preference between two bundles that differ in one end carries
down to those two ends. The rest is any set, and the two ends lie
outside it. This one says it of two parts that are sets of ends, with
the rest fixed to one trade's holding. Nothing is said about any other
holding the agent might rank. It fails for complements. A man who keeps a right shoe may
rank (right shoe + left shoe) above (right shoe + hat). He may still
rank a hat above a left shoe on its own. The left shoe's worth is in
the pair. Rothbard's p. 85 scales list the two goods alone. They never
mention the rest of what the traders own. This condition is what that
omission costs. -/
def Trade.SeparableFromRest {praxis : ActionFrame} (trade : Trade praxis) :
    Prop :=
  ∀ (X Y : Set praxis.End),
    Disjoint X (praxis.ServedBy trade.agent trade.time trade.kept) →
    Disjoint Y (praxis.ServedBy trade.agent trade.time trade.kept) →
    praxis.Prefers trade.agent trade.time
        (X ∪ praxis.ServedBy trade.agent trade.time trade.kept)
        (Y ∪ praxis.ServedBy trade.agent trade.time trade.kept) →
      praxis.Prefers trade.agent trade.time X Y

/-- **Beliefs about the goods hold** at `later` — a condition on the
situation. Every good in the trade is believed at `later` to serve
exactly what it was believed to serve when the trade was made. It
fails when the agent learns the good he got does less than he thought.
That may come through his own error, or through deception. Rothbard
counts a deceived party's trade as not voluntary at all ("this is not
an example of voluntary exchange, but of one-sided theft", *MES*
p. 184). The condition here does not ask who changed the belief. -/
def Trade.BeliefsHold {praxis : ActionFrame} (trade : Trade praxis)
    (later : praxis.Time) : Prop :=
  ∀ good, (good = trade.gives ∨ good = trade.gets ∨ good ∈ trade.kept) →
    ∀ want, praxis.Believes trade.agent later good want ↔
      praxis.Believes trade.agent trade.time good want

/-- **The ranking of the two holdings holds** at `later` — a
condition on the situation. Say that when trading, the agent ranked
the holding he chose above the one he gave up. Then he still does. It
fails when he changes his mind. That is regret. Only this one pair is
constrained. Nothing is said of the rest of his scale. -/
def Trade.RankingHolds {praxis : ActionFrame} (trade : Trade praxis)
    (later : praxis.Time) : Prop :=
  praxis.Prefers trade.agent trade.time
      (trade.after trade.time) (trade.before trade.time) →
    praxis.Prefers trade.agent later
      (trade.after trade.time) (trade.before trade.time)

/-- A two-party exchange. It is two trades, each party giving what
the other gets. "A gives up a good to B in exchange for a good that B
gives up to A" (*MES* p. 85). No theorem in the library uses that A
and B are two people. None uses that the two trades are made at one
moment. An `Exchange` does not require either. -/
structure Exchange (praxis : ActionFrame) where
  /-- A's side. -/
  first : Trade praxis
  /-- B's side. -/
  second : Trade praxis
  /-- What A gives, B gets. -/
  swap_gives : second.gets = first.gives
  /-- What B gives, A gets. -/
  swap_gets : second.gives = first.gets

end Apodictic
