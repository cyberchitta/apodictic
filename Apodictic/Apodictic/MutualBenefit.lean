import Apodictic.Praxeology

/-!
# Mutual benefit — Rothbard's exchange paragraph, *MES* p. 85

One paragraph, four claims: both parties trade "because they expect
that it will benefit them"; the goods must have "reverse valuations"
"before making the exchange"; each party must know of the other and
his goods; and "After the exchange is made, both A and B have shifted
to a higher position on their respective value scales."

## What is proved, and what it costs

- `ranks_received_above_given` / `reverse_valuations`: the second claim
  from the first. The trade demonstrates a ranking of HOLDINGS; getting
  down to the two goods costs two conditions Rothbard's table never
  shows — that the rest of the holding does not interact with them
  (complements) and does not duplicate them (substitutes).
- `better_off_judged_at_trade`: the fourth claim, judged on the scale
  and beliefs of the trade itself. It is the demonstrated preference,
  restated.
- `better_off_judged_later`: the fourth claim, judged afterwards. It
  needs two further conditions, one per way it fails: the beliefs about
  the goods held (no error, no fraud) and the ranking held (no regret).
  `BetterOffLaterWithoutBeliefs` and `BetterOffLaterWithoutRanking`
  are the claim with each condition dropped, stated so they can be
  refuted by construction.

## What is not used

The third claim, knowledge of the other party, is a condition for a
trade to HAPPEN. Every theorem here starts from a trade that happened,
so it has no work to do and is not a hypothesis.
-/

namespace Apodictic
namespace MutualBenefit

/-- A holding with one more good counts for that good's ends together
with the rest's. Bookkeeping, not a claim. -/
theorem servedBy_insert {praxis : ActionFrame} (agent : praxis.Agent)
    (time : praxis.Time) (good : praxis.Means) (rest : Set praxis.Means) :
    praxis.ServedBy agent time (insert good rest) =
      praxis.ServedBy agent time {good} ∪ praxis.ServedBy agent time rest := by
  ext want
  constructor
  · rintro ⟨other, hother, hbelief⟩
    rcases (Set.mem_insert_iff.mp hother) with heq | hrest
    · exact Or.inl ⟨other, Set.mem_singleton_iff.mpr heq, hbelief⟩
    · exact Or.inr ⟨other, hrest, hbelief⟩
  · rintro (⟨other, hother, hbelief⟩ | ⟨other, hrest, hbelief⟩)
    · exact ⟨other, Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hother)),
        hbelief⟩
    · exact ⟨other, Set.mem_insert_iff.mpr (Or.inr hrest), hbelief⟩

/-- If every good in a holding is believed at two times to serve the
same ends, the holding counts for the same bundle at both. Bookkeeping,
not a claim. -/
theorem servedBy_congr {praxis : ActionFrame} (agent : praxis.Agent)
    (time time' : praxis.Time) (goods : Set praxis.Means)
    (same : ∀ good ∈ goods, ∀ want,
      praxis.Believes agent time' good want ↔ praxis.Believes agent time good want) :
    praxis.ServedBy agent time' goods = praxis.ServedBy agent time goods := by
  ext want
  constructor
  · rintro ⟨good, hgood, hbelief⟩
    exact ⟨good, hgood, (same good hgood want).mp hbelief⟩
  · rintro ⟨good, hgood, hbelief⟩
    exact ⟨good, hgood, (same good hgood want).mpr hbelief⟩

/-- **The good received ranks above the good given**, on the trader's
scale at the time of trading — each good counted by the ends he then
believes it serves. -/
theorem ranks_received_above_given
    {praxis : ActionFrame} (trade : Trade praxis)
    (demonstrated : DemonstratedPreference trade)
    (voluntary : trade.Voluntary)
    (separable : praxis.SeparableFromRest trade.agent trade.time)
    (unique : trade.KeptServesOtherEnds) :
    praxis.Prefers trade.agent trade.time
      (praxis.ServedBy trade.agent trade.time {trade.gets})
      (praxis.ServedBy trade.agent trade.time {trade.gives}) := by
  have chosen := demonstrated.demonstrates
  rw [voluntary] at chosen
  unfold Trade.after Trade.before at chosen
  rw [servedBy_insert, servedBy_insert] at chosen
  exact separable _ _ _ unique.2 unique.1 chosen

/-- **Reverse valuations** (*MES* p. 85): in an exchange, A ranks B's
good above his own and B ranks A's good above his own, each on his own
scale and by his own beliefs at the time of the exchange. -/
theorem reverse_valuations
    {praxis : ActionFrame} (exchange : Exchange praxis)
    (demonstratedA : DemonstratedPreference exchange.first)
    (demonstratedB : DemonstratedPreference exchange.second)
    (voluntaryA : exchange.first.Voluntary)
    (voluntaryB : exchange.second.Voluntary)
    (separableA : praxis.SeparableFromRest exchange.first.agent exchange.first.time)
    (separableB : praxis.SeparableFromRest exchange.second.agent exchange.second.time)
    (uniqueA : exchange.first.KeptServesOtherEnds)
    (uniqueB : exchange.second.KeptServesOtherEnds) :
    praxis.Prefers exchange.first.agent exchange.first.time
        (praxis.ServedBy exchange.first.agent exchange.first.time {exchange.first.gets})
        (praxis.ServedBy exchange.first.agent exchange.first.time {exchange.first.gives}) ∧
      praxis.Prefers exchange.second.agent exchange.second.time
        (praxis.ServedBy exchange.second.agent exchange.second.time {exchange.first.gives})
        (praxis.ServedBy exchange.second.agent exchange.second.time {exchange.first.gets}) := by
  constructor
  · exact ranks_received_above_given exchange.first demonstratedA voluntaryA
      separableA uniqueA
  · have hB := ranks_received_above_given exchange.second demonstratedB voluntaryB
      separableB uniqueB
    rw [exchange.swap_gives, exchange.swap_gets] at hB
    exact hB

/-- **Better off, judged at the trade** — the holding after ranks
above the holding before, on the scale and beliefs of the moment of
trading. Rothbard's "shifted to a higher position", read on the scale
the traders had "before making the exchange". -/
theorem better_off_judged_at_trade
    {praxis : ActionFrame} (trade : Trade praxis)
    (demonstrated : DemonstratedPreference trade)
    (voluntary : trade.Voluntary) :
    praxis.Prefers trade.agent trade.time
      (trade.after trade.time) (trade.before trade.time) := by
  have chosen := demonstrated.demonstrates
  rw [voluntary] at chosen
  exact chosen

/-- **Better off, judged later** — the holding after ranks above the
holding before on the agent's scale at `later`, each counted by what
he believes at `later`. It needs the beliefs about the goods and the
ranking of the two holdings both to have held. -/
theorem better_off_judged_later
    {praxis : ActionFrame} (trade : Trade praxis) (later : praxis.Time)
    (demonstrated : DemonstratedPreference trade)
    (voluntary : trade.Voluntary)
    (beliefsHold : trade.BeliefsHold later)
    (rankingHolds : trade.RankingHolds later) :
    praxis.Prefers trade.agent later
      (trade.after later) (trade.before later) := by
  have hafter : trade.after later = trade.after trade.time := by
    apply servedBy_congr
    intro good hgood
    rcases (Set.mem_insert_iff.mp hgood) with heq | hkept
    · exact beliefsHold good (Or.inr (Or.inl heq))
    · exact beliefsHold good (Or.inr (Or.inr hkept))
  have hbefore : trade.before later = trade.before trade.time := by
    apply servedBy_congr
    intro good hgood
    rcases (Set.mem_insert_iff.mp hgood) with heq | hkept
    · exact beliefsHold good (Or.inl heq)
    · exact beliefsHold good (Or.inr (Or.inr hkept))
  rw [hafter, hbefore]
  exact rankingHolds (better_off_judged_at_trade trade demonstrated voluntary)

/-- The later-judged claim with the beliefs condition dropped. False
where the agent learns the good he got does less than he thought —
refuted by construction in `Apodictic.Model`. -/
def BetterOffLaterWithoutBeliefs : Prop :=
  ∀ (praxis : ActionFrame) (trade : Trade praxis) (later : praxis.Time),
    DemonstratedPreference trade → trade.Voluntary →
    trade.RankingHolds later →
    praxis.Prefers trade.agent later (trade.after later) (trade.before later)

/-- The later-judged claim with the ranking condition dropped. False
where the agent changes his mind — refuted by construction in
`Apodictic.Model`. -/
def BetterOffLaterWithoutRanking : Prop :=
  ∀ (praxis : ActionFrame) (trade : Trade praxis) (later : praxis.Time),
    DemonstratedPreference trade → trade.Voluntary →
    trade.BeliefsHold later →
    praxis.Prefers trade.agent later (trade.after later) (trade.before later)

#print axioms ranks_received_above_given
#print axioms reverse_valuations
#print axioms better_off_judged_at_trade
#print axioms better_off_judged_later

end MutualBenefit
end Apodictic

#lint only unusedArguments
