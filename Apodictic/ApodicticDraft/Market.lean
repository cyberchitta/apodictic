import Apodictic

/-!
# Market — the draft vocabulary of a market of many agents (price controls, link 1)

Definitions ONLY: this file asserts nothing. The situational conditions
are here, as definitions a theorem takes as named hypotheses.

## What is added

- `Market praxis now Price`: finitely many buyers and sellers, at one
  time, each seller offering one unit, each with limit prices given as
  data (I-10 (b)). A buyer's limit is per unit: `topPrice buyer seller`
  is the most the buyer would pay for that seller's unit. A seller's
  limit is `floorPrice seller`, the least he would take for his unit.
- The schedules: `demanded p` counts the buyers willing to buy at `p`,
  `supplied p` the sellers willing to sell at `p`.
- `Clears p`: the counts are equal at `p` (PC-4).
- `Homogeneous`: every buyer's limit is the same for every unit (SUP-1).
- `Between p clearing`: someone is willing at one of the two prices and
  not at the other (PC-7, GAP-2).

## Shape claims (audit)

- One unit per seller, one purchase per buyer (GAP-1b). Rothbard's own
  setup (*MES* pp. 112–113). Read of labor, it says one unit of service
  is one worker: the place where hours and heads come apart.
- Limit prices are data. They do not move with the price called
  (GAP-1a). Where they come from is what I-10 (c) would supply from
  `Prefers`, and this defers.
- The schedules are evaluated at one price for every unit. That is a
  hypothetical uniform price, not a claim that the market stands at one
  price. Whether it does is the decree's question (C5), not here.
- Prices are compared by a preorder, decidably. Nothing says any two
  prices are comparable. Decidability is what lets willingness be
  counted; for amounts of money it is the ordinary comparison of sizes.
- A buyer is willing at `p` if there is SOME unit he would pay `p` for.
  With per-unit limits that is one of several readings; under
  `Homogeneous` they coincide (`willingToBuy_iff_of_homogeneous`).
-/

namespace ApodicticDraft

open Apodictic

/-- A market for one good, at one time: buyers and sellers with limit
prices. Each seller offers one unit; each buyer wants one. The data are
the agents' as of `now`. -/
structure Market (praxis : ActionFrame) (now : praxis.Time) (Price : Type) where
  /-- The buyers in the market. -/
  buyers : Finset praxis.Agent
  /-- The sellers in the market, each offering one unit. -/
  sellers : Finset praxis.Agent
  /-- `topPrice buyer seller`: the most `buyer` would pay for the unit
  `seller` offers. Given as data. -/
  topPrice : praxis.Agent → praxis.Agent → Price
  /-- `floorPrice seller`: the least `seller` would take for his unit.
  Given as data. -/
  floorPrice : praxis.Agent → Price

namespace Market

variable {praxis : ActionFrame} {now : praxis.Time} {Price : Type}
  [Preorder Price] [DecidableRel (α := Price) (· ≤ ·)]
  (market : Market praxis now Price)

/-- At price `p`, the buyer would buy some unit on offer. -/
def WillingToBuy (p : Price) (buyer : praxis.Agent) : Prop :=
  ∃ seller ∈ market.sellers, p ≤ market.topPrice buyer seller

/-- At price `p`, the seller would sell his unit. -/
def WillingToSell (p : Price) (seller : praxis.Agent) : Prop :=
  market.floorPrice seller ≤ p

instance (p : Price) : DecidablePred (market.WillingToBuy p) := fun buyer =>
  inferInstanceAs (Decidable (∃ seller ∈ market.sellers, p ≤ market.topPrice buyer seller))

instance (p : Price) : DecidablePred (market.WillingToSell p) := fun seller =>
  inferInstanceAs (Decidable (market.floorPrice seller ≤ p))

/-- Quantity demanded at `p`: the number of buyers willing to buy at `p`. -/
def demanded (p : Price) : ℕ :=
  (market.buyers.filter (market.WillingToBuy p)).card

/-- Quantity supplied at `p`: the number of sellers willing to sell at `p`. -/
def supplied (p : Price) : ℕ :=
  (market.sellers.filter (market.WillingToSell p)).card

/-- **Clears** — a condition on the situation (PC-4). At `p`, the
quantity demanded equals the quantity supplied.

Rothbard: "the price of the good will find a resting point where the
quantity demanded is equal to the quantity supplied" (*MES* p. 116).
He joins two other characterisations to it by "i.e.": no incentive to
bid up or down, and no frustrated buyers or sellers (pp. 116–117).
They are not this, and are not shown to follow from it. -/
def Clears (p : Price) : Prop :=
  market.demanded p = market.supplied p

/-- **Homogeneous units** — a condition on the situation (SUP-1). Every
buyer would pay the same for any unit on offer.

Rothbard stipulates it: the horses are "considered by all parties as
homogeneous units of the same good" (*MES* p. 112). Stated here of
limit prices, as I-10 (b) supplies them; under I-10 (c) it would follow
from the library's `AllocationPlan.Homogeneous`, which speaks of the
ends units serve, not of prices. -/
def Homogeneous : Prop :=
  ∀ buyer ∈ market.buyers, ∀ seller ∈ market.sellers, ∀ other ∈ market.sellers,
    market.topPrice buyer seller = market.topPrice buyer other

/-- **Someone between** — a condition on the situation (PC-7, GAP-2).
Some buyer is willing at `p` and not at `clearing`, or some seller is
willing at `clearing` and not at `p`. -/
def Between (p clearing : Price) : Prop :=
  (∃ buyer ∈ market.buyers,
      market.WillingToBuy p buyer ∧ ¬ market.WillingToBuy clearing buyer) ∨
  (∃ seller ∈ market.sellers,
      market.WillingToSell clearing seller ∧ ¬ market.WillingToSell p seller)

end Market

end ApodicticDraft
