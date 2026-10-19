import ApodicticDraft.Market

/-!
# PriceControl — link 1: below a clearing price, demand is at least supply

The static inequality of price controls (C1–C4 of the 2026-10-13
scoping), Rothbard's way: the schedules are counts of willing buyers
and sellers over limit prices given as data (I-10 (b)).

Rothbard: "a price that is below the equilibrium price creates an
additional shortage of supply for demanders, while a price above
equilibrium creates a surplus of goods for sale as compared to demands
for purchase" (*MES* p. 118).

## What is proved

- The schedules slope the usual way (`demanded_antitone`,
  `supplied_monotone`). GAP-1, a theorem from the limit prices.
- Below a clearing price, supplied ≤ demanded (`supplied_le_demanded`);
  above it, the mirror (`demanded_le_supplied`). The minimum wage is the
  mirror read of a market whose sellers are workers.
- Strictly, under `Between` (`supplied_lt_demanded`,
  `demanded_lt_supplied`).
- Under `Homogeneous`, a buyer's willingness does not depend on which
  unit (`willingToBuy_iff_of_homogeneous`, `demanded_eq_of_homogeneous`):
  the count is a count of buyers of the good, whichever unit.

## What is not

No claim about action is carried: none of these theorems takes one. The
clearing price is a hypothesis (PC-5); that one exists is not shown, and
in a market of whole units it may not (the toy has a case, *MES* p. 116
n. 25). Nothing is said of a decree, of a market standing at a price,
or of a buyer who goes without (C5–C6).
-/

namespace ApodicticDraft

open Apodictic

namespace Market

variable {praxis : ActionFrame} {now : praxis.Time} {Price : Type}
  [Preorder Price] [DecidableRel (α := Price) (· ≤ ·)]
  (market : Market praxis now Price)

omit [DecidableRel (α := Price) (· ≤ ·)] in
/-- A buyer willing at a price is willing at any lower one. -/
theorem willingToBuy_of_le {p q : Price} (hpq : p ≤ q) {buyer : praxis.Agent}
    (h : market.WillingToBuy q buyer) : market.WillingToBuy p buyer := by
  obtain ⟨seller, hseller, hq⟩ := h
  exact ⟨seller, hseller, le_trans hpq hq⟩

omit [DecidableRel (α := Price) (· ≤ ·)] in
/-- A seller willing at a price is willing at any higher one. -/
theorem willingToSell_of_le {p q : Price} (hpq : p ≤ q) {seller : praxis.Agent}
    (h : market.WillingToSell p seller) : market.WillingToSell q seller :=
  le_trans h hpq

/-- The demand schedule: as the price rises, quantity demanded does not
rise. -/
theorem demanded_antitone {p q : Price} (hpq : p ≤ q) :
    market.demanded q ≤ market.demanded p := by
  apply Finset.card_le_card
  intro buyer hbuyer
  rw [Finset.mem_filter] at hbuyer ⊢
  exact ⟨hbuyer.1, market.willingToBuy_of_le hpq hbuyer.2⟩

/-- The supply schedule: as the price rises, quantity supplied does not
fall. -/
theorem supplied_monotone {p q : Price} (hpq : p ≤ q) :
    market.supplied p ≤ market.supplied q := by
  apply Finset.card_le_card
  intro seller hseller
  rw [Finset.mem_filter] at hseller ⊢
  exact ⟨hseller.1, market.willingToSell_of_le hpq hseller.2⟩

/-- **The static inequality** (C4). At a price at or below a clearing
price, quantity supplied is at most quantity demanded. -/
theorem supplied_le_demanded {p clearing : Price} (clears : market.Clears clearing)
    (below : p ≤ clearing) : market.supplied p ≤ market.demanded p := by
  calc market.supplied p ≤ market.supplied clearing := market.supplied_monotone below
    _ = market.demanded clearing := clears.symm
    _ ≤ market.demanded p := market.demanded_antitone below

/-- **The mirror** (C4, and read of labor, C8). At a price at or above a
clearing price, quantity demanded is at most quantity supplied. -/
theorem demanded_le_supplied {p clearing : Price} (clears : market.Clears clearing)
    (above : clearing ≤ p) : market.demanded p ≤ market.supplied p := by
  calc market.demanded p ≤ market.demanded clearing := market.demanded_antitone above
    _ = market.supplied clearing := clears
    _ ≤ market.supplied p := market.supplied_monotone above

/-- Strict demand side: a buyer willing at `p` and not at `clearing`
makes demand at `p` exceed demand at `clearing`. -/
theorem demanded_lt {p clearing : Price} (below : p ≤ clearing)
    {buyer : praxis.Agent} (hbuyer : buyer ∈ market.buyers)
    (hp : market.WillingToBuy p buyer) (hc : ¬ market.WillingToBuy clearing buyer) :
    market.demanded clearing < market.demanded p := by
  apply Finset.card_lt_card
  constructor
  · intro other hother
    rw [Finset.mem_filter] at hother ⊢
    exact ⟨hother.1, market.willingToBuy_of_le below hother.2⟩
  · intro hsub
    exact hc (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hbuyer, hp⟩))).2

/-- Strict supply side: a seller willing at `clearing` and not at `p`
makes supply at `p` fall short of supply at `clearing`. -/
theorem supplied_lt {p clearing : Price} (below : p ≤ clearing)
    {seller : praxis.Agent} (hseller : seller ∈ market.sellers)
    (hc : market.WillingToSell clearing seller) (hp : ¬ market.WillingToSell p seller) :
    market.supplied p < market.supplied clearing := by
  apply Finset.card_lt_card
  constructor
  · intro other hother
    rw [Finset.mem_filter] at hother ⊢
    exact ⟨hother.1, market.willingToSell_of_le below hother.2⟩
  · intro hsub
    exact hp (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hseller, hc⟩))).2

/-- **The static inequality, strict** (C4 under GAP-2). Below a clearing
price, with someone between the two prices, quantity supplied is
strictly less than quantity demanded. -/
theorem supplied_lt_demanded {p clearing : Price} (clears : market.Clears clearing)
    (below : p ≤ clearing) (between : market.Between p clearing) :
    market.supplied p < market.demanded p := by
  cases between with
  | inl hbuyer =>
    obtain ⟨buyer, hmem, hp, hc⟩ := hbuyer
    calc market.supplied p ≤ market.supplied clearing := market.supplied_monotone below
      _ = market.demanded clearing := clears.symm
      _ < market.demanded p := market.demanded_lt below hmem hp hc
  | inr hseller =>
    obtain ⟨seller, hmem, hc, hp⟩ := hseller
    calc market.supplied p < market.supplied clearing := market.supplied_lt below hmem hc hp
      _ = market.demanded clearing := clears.symm
      _ ≤ market.demanded p := market.demanded_antitone below

/-- **The mirror, strict.** Above a clearing price, with someone between
— a buyer willing at `clearing` and not at `p`, or a seller willing at
`p` and not at `clearing` — quantity demanded is strictly less than
quantity supplied. -/
theorem demanded_lt_supplied {p clearing : Price} (clears : market.Clears clearing)
    (above : clearing ≤ p) (between : market.Between clearing p) :
    market.demanded p < market.supplied p := by
  cases between with
  | inl hbuyer =>
    obtain ⟨buyer, hmem, hc, hp⟩ := hbuyer
    calc market.demanded p < market.demanded clearing := market.demanded_lt above hmem hc hp
      _ = market.supplied clearing := clears
      _ ≤ market.supplied p := market.supplied_monotone above
  | inr hseller =>
    obtain ⟨seller, hmem, hp, hc⟩ := hseller
    calc market.demanded p ≤ market.demanded clearing := market.demanded_antitone above
      _ = market.supplied clearing := clears
      _ < market.supplied p := market.supplied_lt above hmem hp hc

omit [DecidableRel (α := Price) (· ≤ ·)] in
/-- Under homogeneous units, a buyer is willing at `p` exactly when he
would pay `p` for any one given unit on offer. -/
theorem willingToBuy_iff_of_homogeneous (homogeneous : market.Homogeneous)
    {buyer seller : praxis.Agent} (hbuyer : buyer ∈ market.buyers)
    (hseller : seller ∈ market.sellers) (p : Price) :
    market.WillingToBuy p buyer ↔ p ≤ market.topPrice buyer seller := by
  constructor
  · intro h
    obtain ⟨other, hother, hp⟩ := h
    rw [homogeneous buyer hbuyer seller hseller other hother]
    exact hp
  · intro hp
    exact ⟨seller, hseller, hp⟩

/-- Under homogeneous units, quantity demanded counts the buyers who
would pay `p` for a unit, whichever unit is taken. -/
theorem demanded_eq_of_homogeneous (homogeneous : market.Homogeneous)
    {seller : praxis.Agent} (hseller : seller ∈ market.sellers) (p : Price) :
    market.demanded p =
      (market.buyers.filter (fun buyer => p ≤ market.topPrice buyer seller)).card := by
  unfold demanded
  congr 1
  apply Finset.filter_congr
  intro buyer hbuyer
  exact market.willingToBuy_iff_of_homogeneous homogeneous hbuyer hseller p

end Market

#print axioms Market.demanded_antitone
#print axioms Market.supplied_monotone
#print axioms Market.supplied_le_demanded
#print axioms Market.demanded_le_supplied
#print axioms Market.supplied_lt_demanded
#print axioms Market.demanded_lt_supplied
#print axioms Market.willingToBuy_iff_of_homogeneous
#print axioms Market.demanded_eq_of_homogeneous

end ApodicticDraft

#lint only unusedArguments
