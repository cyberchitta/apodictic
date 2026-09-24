import Mathlib.Data.Finset.Card
import Apodictic.Allocation

/-!
# Region — the sub-stocks single-unit steps reach

Pure combinatorics about stocks. It asserts nothing about action and
carries no praxeological claim; nothing here is imported by
`Apodictic.Praxeology`.

`SwapDominant` quantifies over every `subStock ⊆ stock.units`. The
defence of that reach is that Rothbard's permitted region is anchored
to the stock the agent has and closed under single-unit steps, and
that such steps, taken downward from a stock, reach every sub-stock of
it and nothing else. This module proves the second half: the smallest
family of sets of units that contains the stock and is closed under
removing one unit is exactly the family of sub-stocks
(`Stock.reachable_iff_subset`). The same holds when the family is
closed under adding a unit back as well
(`Stock.reachableBothWays_iff_subset`). Whether Rothbard's region IS
such a family is a reading of his text, and no theorem.

A single-unit step is `Stock.OneMore`, the library's own, stated with
an inclusion and a count rather than by naming the unit. So nothing
here decides when two units are the same unit: the statements carry no
`DecidableEq` on units, and neither do the proofs. Mathlib's lemma
for finding a unit of the stock outside a smaller sub-stock
(`Finset.exists_mem_notMem_of_card_lt_card`) is classical; it is
replaced by `exists_mem_not_mem_of_subset_of_card_lt`, proved by
peeling units off a list representation, which needs no decision.

What the reach DOES rest on is that a stock is finite: `Stock.units`
is a `Finset`. From an infinite stock, finitely many removals never
reach a finite sub-stock of it, and the region would not be all
sub-stocks.
-/

namespace Apodictic

/-- Constructive pigeonhole on lists: a duplicate-free list shorter than
a duplicate-free list it is contained in leaves out one of its
entries. -/
theorem list_exists_mem_not_mem_of_subset_of_length_lt {α : Type}
    (small : List α) : ∀ (big : List α), small.Nodup → big.Nodup →
      (∀ z ∈ small, z ∈ big) → small.length < big.length →
        ∃ e ∈ big, e ∉ small := by
  induction small with
  | nil =>
    intro big _ _ _ hlen
    cases big with
    | nil => exact absurd hlen (Nat.lt_irrefl 0)
    | cons a _ => exact ⟨a, List.mem_cons_self, List.not_mem_nil⟩
  | cons y rest ih =>
    intro big hsmall hbig hsub hlen
    obtain ⟨front, back, rfl⟩ := List.append_of_mem (hsub y List.mem_cons_self)
    have hbig' := List.nodup_cons.mp (List.nodup_middle.mp hbig)
    have hsmall' := List.nodup_cons.mp hsmall
    have hsub' : ∀ z ∈ rest, z ∈ front ++ back := by
      intro z hz
      have hzbig := hsub z (List.mem_cons_of_mem y hz)
      rcases List.mem_append.mp hzbig with hfront | hmid
      · exact List.mem_append.mpr (Or.inl hfront)
      · rcases List.mem_cons.mp hmid with heq | hback
        · exact absurd (heq ▸ hz) hsmall'.1
        · exact List.mem_append.mpr (Or.inr hback)
    have hlen' : rest.length < (front ++ back).length := by
      simp only [List.length_append, List.length_cons] at hlen ⊢
      omega
    obtain ⟨e, he, hnot⟩ := ih (front ++ back) hsmall'.2 hbig'.2 hsub' hlen'
    refine ⟨e, ?_, ?_⟩
    · rcases List.mem_append.mp he with hfront | hback
      · exact List.mem_append.mpr (Or.inl hfront)
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem y hback))
    · intro hmem
      rcases List.mem_cons.mp hmem with heq | hrest
      · exact hbig'.1 (heq ▸ he)
      · exact hnot hrest

/-- A sub-stock with fewer units than the stock it sits in leaves out
some unit of it — found without deciding when two units are equal. -/
theorem exists_mem_not_mem_of_subset_of_card_lt {α : Type}
    {small big : Finset α} (hsub : small ⊆ big)
    (hcard : small.card < big.card) : ∃ e ∈ big, e ∉ small := by
  rcases small with ⟨smallMulti, smallNodup⟩
  rcases big with ⟨bigMulti, bigNodup⟩
  induction smallMulti using Quot.ind with
  | mk smallList =>
  induction bigMulti using Quot.ind with
  | mk bigList =>
  obtain ⟨e, he, hnot⟩ :=
    list_exists_mem_not_mem_of_subset_of_length_lt smallList bigList
      smallNodup bigNodup (fun z hz => hsub hz) hcard
  exact ⟨e, he, hnot⟩

/-- **The region reached by removing units one at a time** from the
stock the agent has: the stock itself, and whatever is one unit short
of something already reached. As an inductive predicate it is the
SMALLEST such family (`Stock.Reachable.least`). -/
inductive Stock.Reachable {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} (stock : Stock praxis agent time) :
    Finset praxis.Means → Prop
  /-- The stock the agent has. -/
  | whole : stock.Reachable stock.units
  /-- One unit fewer than something reached. -/
  | remove {fewer more : Finset praxis.Means} :
      stock.Reachable more → stock.OneMore fewer more →
        stock.Reachable fewer

/-- `Stock.Reachable` is the least family containing the stock and
closed under removing one unit: every such family contains it. -/
theorem Stock.Reachable.least {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} {stock : Stock praxis agent time}
    (family : Finset praxis.Means → Prop) (hwhole : family stock.units)
    (hremove : ∀ fewer more, family more → stock.OneMore fewer more →
      family fewer)
    {subStock : Finset praxis.Means} (hreach : stock.Reachable subStock) :
    family subStock := by
  induction hreach with
  | whole => exact hwhole
  | remove _ hstep ih => exact hremove _ _ ih hstep

/-- Everything reached is a sub-stock. -/
theorem Stock.Reachable.subset {praxis : ActionFrame} {agent : praxis.Agent}
    {time : praxis.Time} {stock : Stock praxis agent time}
    {subStock : Finset praxis.Means} (hreach : stock.Reachable subStock) :
    subStock ⊆ stock.units := by
  induction hreach with
  | whole => exact Finset.Subset.refl _
  | remove _ hstep ih => exact Finset.Subset.trans hstep.1 ih

/-- Every sub-stock `missing` units short of the stock is reached. -/
theorem Stock.reachable_of_subset_of_card {praxis : ActionFrame}
    {agent : praxis.Agent} {time : praxis.Time}
    (stock : Stock praxis agent time) (missing : ℕ) :
    ∀ subStock : Finset praxis.Means, subStock ⊆ stock.units →
      stock.units.card = subStock.card + missing →
        stock.Reachable subStock := by
  induction missing with
  | zero =>
    intro subStock hsub hcard
    have heq : subStock = stock.units :=
      Finset.eq_of_subset_of_card_le hsub (Nat.le_of_eq hcard)
    rw [heq]
    exact Stock.Reachable.whole
  | succ missing ih =>
    intro subStock hsub hcard
    have hlt : subStock.card < stock.units.card := by omega
    obtain ⟨unit, hunit, hnot⟩ :=
      exists_mem_not_mem_of_subset_of_card_lt hsub hlt
    have hmoreSub : Finset.cons unit subStock hnot ⊆ stock.units :=
      Finset.cons_subset.mpr ⟨hunit, hsub⟩
    have hmoreCard :
        stock.units.card = (Finset.cons unit subStock hnot).card + missing := by
      rw [Finset.card_cons]
      omega
    exact Stock.Reachable.remove (ih _ hmoreSub hmoreCard)
      ⟨Finset.subset_cons hnot, hmoreSub, Finset.card_cons hnot⟩

/-- **Removing units one at a time from the stock reaches every
sub-stock, and nothing else.** The smallest family containing
`stock.units` and closed under removing one unit
(`Stock.OneMore`) is exactly the family of `subStock ⊆ stock.units`. -/
theorem Stock.reachable_iff_subset {praxis : ActionFrame}
    {agent : praxis.Agent} {time : praxis.Time}
    (stock : Stock praxis agent time) (subStock : Finset praxis.Means) :
    stock.Reachable subStock ↔ subStock ⊆ stock.units := by
  constructor
  · exact Stock.Reachable.subset
  · intro hsub
    have hle : subStock.card ≤ stock.units.card := Finset.card_le_card hsub
    exact stock.reachable_of_subset_of_card (stock.units.card - subStock.card)
      subStock hsub (by omega)

/-- **The region reached by single-unit steps in either direction**
from the stock the agent has: removing one unit, or adding one back.
`Stock.OneMore` keeps the larger set inside the stock, so a step up
never leaves it. -/
inductive Stock.ReachableBothWays {praxis : ActionFrame}
    {agent : praxis.Agent} {time : praxis.Time}
    (stock : Stock praxis agent time) : Finset praxis.Means → Prop
  /-- The stock the agent has. -/
  | whole : stock.ReachableBothWays stock.units
  /-- One unit fewer than something reached. -/
  | remove {fewer more : Finset praxis.Means} :
      stock.ReachableBothWays more → stock.OneMore fewer more →
        stock.ReachableBothWays fewer
  /-- One unit more than something reached. -/
  | add {fewer more : Finset praxis.Means} :
      stock.ReachableBothWays fewer → stock.OneMore fewer more →
        stock.ReachableBothWays more

/-- **Steps in both directions reach the same region.** Adding units
back, as well as removing them, reaches exactly the sub-stocks. -/
theorem Stock.reachableBothWays_iff_subset {praxis : ActionFrame}
    {agent : praxis.Agent} {time : praxis.Time}
    (stock : Stock praxis agent time) (subStock : Finset praxis.Means) :
    stock.ReachableBothWays subStock ↔ subStock ⊆ stock.units := by
  constructor
  · intro hreach
    induction hreach with
    | whole => exact Finset.Subset.refl _
    | remove _ hstep ih => exact Finset.Subset.trans hstep.1 ih
    | add _ hstep _ => exact hstep.2.1
  · intro hsub
    exact Stock.Reachable.least stock.ReachableBothWays
      Stock.ReachableBothWays.whole
      (fun _ _ hmore hstep => Stock.ReachableBothWays.remove hmore hstep)
      ((stock.reachable_iff_subset subStock).mpr hsub)

#print axioms Stock.reachable_iff_subset
#print axioms Stock.reachableBothWays_iff_subset
#print axioms Stock.Reachable.least

end Apodictic

#lint only unusedArguments
