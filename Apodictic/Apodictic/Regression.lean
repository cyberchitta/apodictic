import Apodictic.Praxeology
import Apodictic.MutualBenefit

/-!
# Regression — Mises's regression theorem, the genetic claim

No good becomes a medium of exchange without having been acquired, before,
for some end other than passing it on: Mises's regression theorem in its
genetic form (*Human Action*, ch. XVII, §4), with Rothbard's two versions
of where it ends (*MES* p. 275; *Power and Market*, *MES* ed. p. 1021).
The vocabulary is `Apodictic.Medium`; the two claims it spends,
`AppraisalFromPast` and `TwoPartialDemands`, are in
`Apodictic.Praxeology`. Without quantities: the explanatory claim, that
today's purchasing power is formed from yesterday's, is not here.
-/

namespace Apodictic
namespace Regression

/-!
## Indirect exchange

A medium of exchange is wanted "to keep it as a medium of exchange and
to give it away at need in a later act of exchange" (*Human Action*,
ch. XVII, §4). In the library's vocabulary that is a trade whose
received good the agent believes serves onward ends.

### What is proved, and what it costs

- `indirect_ranks_onward_ends`: in a purely indirect trade, the agent
  ranks the ends he expects to reach by passing the good on above the
  ends of the good he gave. No new claim: it is
  `Apodictic.MutualBenefit.ranks_received_above_given`, applied, with
  `ServedBy` counting onward ends like any other. What indirect exchange
  adds is the condition `Trade.PurelyIndirect`, which turns the
  received good's bundle into its onward ends.
-/

/-- A good counts, alone, for exactly the ends it is believed to serve.
Bookkeeping. -/
theorem servedBy_singleton {praxis : ActionFrame} (agent : praxis.Agent)
    (time : praxis.Time) (m : praxis.Means) :
    praxis.ServedBy agent time {m} = {e | praxis.Believes agent time m e} := by
  ext e
  constructor
  · rintro ⟨good, hgood, hbelief⟩
    rw [Set.mem_singleton_iff.mp hgood] at hbelief
    exact hbelief
  · intro hbelief
    exact ⟨m, Set.mem_singleton m, hbelief⟩

/-- **Indirect exchange ranks onward ends** — in a trade where the
agent wants the received good only to pass it on, he ranks the ends he
expects to reach by passing it on above the ends of the good he gave,
on his scale at the time of trading. -/
theorem indirect_ranks_onward_ends {praxis : MediumFrame}
    (trade : Trade praxis.toActionFrame)
    (demonstrated : DemonstratedPreference trade)
    (voluntary : trade.Voluntary)
    (separable : trade.SeparableFromRest)
    (unique : trade.KeptServesOtherEnds)
    (pure : Trade.PurelyIndirect trade) :
    praxis.Prefers trade.agent trade.time
      (praxis.OnwardEnds trade.agent trade.time trade.gets)
      (praxis.ServedBy trade.agent trade.time {trade.gives}) := by
  have hranks := MutualBenefit.ranks_received_above_given trade demonstrated
    voluntary separable unique
  have honward : praxis.ServedBy trade.agent trade.time {trade.gets} =
      praxis.OnwardEnds trade.agent trade.time trade.gets := by
    rw [servedBy_singleton]
    ext e
    constructor
    · intro hbelief
      exact ⟨pure e hbelief, hbelief⟩
    · rintro ⟨_, hbelief⟩
      exact hbelief
  rw [honward] at hranks
  exact hranks

/-!
## The two partial demands

"Thus the demand for a medium of exchange is the composite of two
partial demands: the demand displayed by the intention to use it in
consumption and production and that displayed by the intention to use
it as a medium of exchange" (*Human Action*, ch. XVII, §4).

Here the two parts are the direct ends and the onward ends the agent
believes a good serves (`MediumFrame.DirectEnds`,
`MediumFrame.OnwardEnds`). "Direct" is "not onward", so the direct part
is the BROAD reading of Mises's "consumption and production";
the narrow reading is a condition, `History.OtherEmploymentsNarrow`.

### What is proved, and what it costs

- `partial_demands_within`: both parts lie inside what the good serves.
  Free.
- `partial_demands_not_not_exhaust`: every end the good serves is,
  not-not, in one part or the other. Free, and that is all that is free.
- `partial_demands_exhaust`: every end the good serves IS in one part
  or the other. It costs the claim `TwoPartialDemands`: every end is
  onward for `m` or not. Mises's "composite" is exhaustive only by
  excluded middle on the sort of an end, so the composite IS that
  excluded middle, carried as his claim.
- `only_onward_without_direct`: a good with no direct ends counts
  only for its onward ends. Same cost.
-/

/-- **The two parts lie within what the good serves.** -/
theorem partial_demands_within {praxis : MediumFrame} (agent : praxis.Agent)
    (time : praxis.Time) (m : praxis.Means) :
    praxis.DirectEnds agent time m ∪ praxis.OnwardEnds agent time m ⊆
      praxis.ServedBy agent time {m} := by
  rw [servedBy_singleton]
  rintro e (⟨_, hbelief⟩ | ⟨_, hbelief⟩)
  · exact hbelief
  · exact hbelief

/-- **Not-not exhaustive** — without deciding the sort of an end, every
end the good serves is only not-not in one of the two parts. -/
theorem partial_demands_not_not_exhaust {praxis : MediumFrame}
    (agent : praxis.Agent) (time : praxis.Time) (m : praxis.Means) :
    ∀ e ∈ praxis.ServedBy agent time {m},
      ¬ ¬ (e ∈ praxis.DirectEnds agent time m ∪ praxis.OnwardEnds agent time m) := by
  rw [servedBy_singleton]
  intro e hbelief hout
  apply hout
  apply Or.inl
  refine ⟨?_, hbelief⟩
  intro honward
  exact hout (Or.inr ⟨honward, hbelief⟩)

/-- **The two partial demands exhaust what the good serves** — given
that every end is onward for `m` or not (`TwoPartialDemands`). -/
theorem partial_demands_exhaust {praxis : MediumFrame} (agent : praxis.Agent)
    (time : praxis.Time) (m : praxis.Means) (twoDemands : TwoPartialDemands praxis m) :
    praxis.ServedBy agent time {m} =
      praxis.DirectEnds agent time m ∪ praxis.OnwardEnds agent time m := by
  apply Set.Subset.antisymm
  · rw [servedBy_singleton]
    intro e hbelief
    rcases twoDemands.sorted e with honward | hdirect
    · exact Or.inr ⟨honward, hbelief⟩
    · exact Or.inl ⟨hdirect, hbelief⟩
  · exact partial_demands_within agent time m

/-- **Without direct ends, only onward ends** — a good the agent
believes serves no end other than passing it on counts, in his holding,
only for its onward ends. -/
theorem only_onward_without_direct {praxis : MediumFrame}
    (agent : praxis.Agent) (time : praxis.Time) (m : praxis.Means)
    (twoDemands : TwoPartialDemands praxis m)
    (noDirect : praxis.DirectEnds agent time m = ∅) :
    praxis.ServedBy agent time {m} = praxis.OnwardEnds agent time m := by
  rw [partial_demands_exhaust agent time m twoDemands, noDirect, Set.empty_union]

/-!
## Appraisal from the past

The hinge of the regression theorem: appraising a good as a medium
needs an exchange of it before. The claim is `AppraisalFromPast`, in
the weak form: some earlier exchange of the good, against anything.

### What is proved, and what it costs

- `acquired_of_exchanged`: an exchange of `m` has a party who acquired
  `m`. Bookkeeping; it spends the exchange's `swap_gives`.
- `exchanged_before`: whoever appraises `m` as a medium on day `n`,
  `m` was acquired by someone, against something, on an earlier day.
  It costs the claim and `BeginsBeforeMedium`, and nothing else.
- `ownPastPrice_of_claim`: the condition "own past price", stated
  without quantities, follows from the claim. Without
  quantities the two are one: see `History.OwnPastPrice`.
-/

/-- An exchange of `m` has an acquirer: whoever was on the receiving
side. Bookkeeping. -/
theorem acquired_of_exchanged {praxis : MediumFrame} {history : History praxis}
    {k : ℕ} {m : praxis.Means} (exchanged : history.ExchangedOn k m) :
    ∃ agent g, history.AcquiredAgainst k m agent g := by
  obtain ⟨x, hx, hgets | hgives⟩ := exchanged
  · exact ⟨x.first.agent, x.first.gives, x, hx, Or.inl ⟨rfl, hgets, rfl⟩⟩
  · refine ⟨x.second.agent, x.second.gives, x, hx, Or.inr ⟨rfl, ?_, rfl⟩⟩
    rw [x.swap_gives]
    exact hgives

/-- **Exchanged before** — if anyone appraises `m` as a medium on day
`n`, then on some earlier day someone acquired `m`, against something. -/
theorem exchanged_before {praxis : MediumFrame} (history : History praxis)
    (m : praxis.Means) (n : ℕ)
    (appraisal : AppraisalFromPast history m)
    (begins : history.BeginsBeforeMedium m)
    (medium : history.MediumAt n m) :
    ∃ k < n, ∃ agent g, history.AcquiredAgainst k m agent g := by
  cases n with
  | zero => exact absurd medium begins
  | succ j =>
    obtain ⟨agent, happraises⟩ := medium
    obtain ⟨k, hk, hexchanged⟩ := appraisal.fromPast j agent happraises
    exact ⟨k, Nat.lt_succ_of_le hk, acquired_of_exchanged hexchanged⟩

/-- **Own past price follows from the claim** — stated, as it must be
here, without quantities and without "rests on", the condition is the
claim restricted to the days before `n`. -/
theorem ownPastPrice_of_claim {praxis : MediumFrame} (history : History praxis)
    (m : praxis.Means) (n : ℕ)
    (appraisal : AppraisalFromPast history m) :
    history.OwnPastPrice m n := by
  intro j _ agent happraises
  exact appraisal.fromPast j agent happraises

/-!
## The genetic regress and the narrow reading

"no good can be employed for the function of a medium of exchange which
at the very beginning of its use for this purpose did not have exchange
value on account of other employments" (*Human Action*, ch. XVII, §4;
again in ch. XXI, §6).

### What is proved, and what it costs

- `no_medium_without_direct_acquisition`: Mises's negative form. If
  nobody acquired `m` before day `n` for an end other than passing it
  on, nobody appraises `m` as a medium on day `n`. By strong induction
  on the day. It costs the claim `AppraisalFromPast` and two
  conditions: that the record begins before the medium
  (`BeginsBeforeMedium`, the termination Mises asserts) and that every
  acquisition before `n` was for some end (`AcquisitionsPurposive`).
  No decidability: the negative form is exactly what is constructive.
- `direct_acquisition_before`: the positive form — some acquisition
  before `n` WAS for an end other than passing it on, and the proof
  finds it. It costs one thing more:
  the claim `TwoPartialDemands`, that every end is onward for `m` or
  not — Mises's "composite of two partial demands". Not
  classical: what is classical is the LAST day of barter, not proved here,
  which needs "medium on day `k`" decided, and that quantifies over
  agents.
- `no_medium_without_narrow_acquisition`,
  `narrow_acquisition_before`: the same two forms, for the narrow
  reading of "other employments" (consumption or production). They cost
  the broad theorems plus the condition `OtherEmploymentsNarrow`, which
  is the narrow reading itself. Nothing is derived beyond it.

### What `AppraisalFromPast` is NOT asked for

The barter condition, the own-past-price condition, and the
counter-good. Under the broad reading, the earliest direct acquisition
is reached through exchanges against anything, money included: the
regress follows the acquirers' ENDS, never what they paid.
-/

/-- **No medium without a direct acquisition before** — Mises's
negative form of the genetic claim, in the broad reading. -/
theorem no_medium_without_direct_acquisition {praxis : MediumFrame}
    (history : History praxis) (m : praxis.Means) (n : ℕ)
    (appraisal : AppraisalFromPast history m)
    (begins : history.BeginsBeforeMedium m)
    (purposive : history.AcquisitionsPurposive m n)
    (noDirect : ∀ k < n, ¬ history.DirectAcquisitionAt k m) :
    ¬ history.MediumAt n m := by
  have key : ∀ j, j ≤ n → ¬ history.MediumAt j m := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hmedium
      cases j with
      | zero => exact begins hmedium
      | succ i =>
        obtain ⟨agent, happraises⟩ := hmedium
        obtain ⟨k, hk, hexchanged⟩ := appraisal.fromPast i agent happraises
        obtain ⟨buyer, g, hacquired⟩ := acquired_of_exchanged hexchanged
        have hkj : k < i + 1 := Nat.lt_succ_of_le hk
        have hkn : k < n := Nat.lt_of_lt_of_le hkj hj
        obtain ⟨e, hbelief⟩ := purposive k hkn buyer g hacquired
        have hnotDirect : ¬ ¬ praxis.Onward m e := by
          intro hdirect
          exact noDirect k hkn ⟨buyer, g, hacquired, e, hdirect, hbelief⟩
        apply hnotDirect
        intro honward
        exact ih k hkj (Nat.le_of_lt hkn) ⟨buyer, e, honward, hbelief⟩
  exact key n (Nat.le_refl n)

/-- **A direct acquisition before** — the positive form: if anyone
appraises `m` as a medium on day `n`, someone acquired `m` on an earlier
day for an end other than passing it on. Given that every end is
onward for `m` or not (`TwoPartialDemands`). -/
theorem direct_acquisition_before {praxis : MediumFrame}
    (history : History praxis) (m : praxis.Means) (n : ℕ)
    (twoDemands : TwoPartialDemands praxis m)
    (appraisal : AppraisalFromPast history m)
    (begins : history.BeginsBeforeMedium m)
    (purposive : history.AcquisitionsPurposive m n)
    (medium : history.MediumAt n m) :
    ∃ k < n, history.DirectAcquisitionAt k m := by
  have key : ∀ j, j ≤ n → history.MediumAt j m →
      ∃ k < j, history.DirectAcquisitionAt k m := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hmedium
      cases j with
      | zero => exact absurd hmedium begins
      | succ i =>
        obtain ⟨agent, happraises⟩ := hmedium
        obtain ⟨k, hk, hexchanged⟩ := appraisal.fromPast i agent happraises
        obtain ⟨buyer, g, hacquired⟩ := acquired_of_exchanged hexchanged
        have hkj : k < i + 1 := Nat.lt_succ_of_le hk
        have hkn : k < n := Nat.lt_of_lt_of_le hkj hj
        obtain ⟨e, hbelief⟩ := purposive k hkn buyer g hacquired
        rcases twoDemands.sorted e with honward | hdirect
        · obtain ⟨k', hk', hfound⟩ :=
            ih k hkj (Nat.le_of_lt hkn) ⟨buyer, e, honward, hbelief⟩
          exact ⟨k', Nat.lt_trans hk' hkj, hfound⟩
        · exact ⟨k, hkj, buyer, g, hacquired, e, hdirect, hbelief⟩
  exact key n (Nat.le_refl n) medium

/-- **No medium without a narrow acquisition before** — the negative
form, for the narrow reading: if nobody acquired `m` before day `n` for
an end in `narrow` (consumption or production), nobody appraises `m` as
a medium on day `n` — provided every other employment `m` was acquired
for was in `narrow`. -/
theorem no_medium_without_narrow_acquisition {praxis : MediumFrame}
    (history : History praxis) (narrow : praxis.End → Prop)
    (m : praxis.Means) (n : ℕ)
    (appraisal : AppraisalFromPast history m)
    (begins : history.BeginsBeforeMedium m)
    (purposive : history.AcquisitionsPurposive m n)
    (narrowReading : history.OtherEmploymentsNarrow narrow m n)
    (noNarrow : ∀ k < n, ¬ history.NarrowAcquisitionAt narrow k m) :
    ¬ history.MediumAt n m := by
  apply no_medium_without_direct_acquisition history m n appraisal begins purposive
  rintro k hk ⟨agent, g, hacquired, e, hdirect, hbelief⟩
  exact noNarrow k hk
    ⟨agent, g, hacquired, e, hdirect, hbelief,
      narrowReading k hk agent g hacquired e hdirect hbelief⟩

/-- **A narrow acquisition before** — the positive form, for the narrow
reading. -/
theorem narrow_acquisition_before {praxis : MediumFrame}
    (history : History praxis) (narrow : praxis.End → Prop)
    (m : praxis.Means) (n : ℕ)
    (twoDemands : TwoPartialDemands praxis m)
    (appraisal : AppraisalFromPast history m)
    (begins : history.BeginsBeforeMedium m)
    (purposive : history.AcquisitionsPurposive m n)
    (narrowReading : history.OtherEmploymentsNarrow narrow m n)
    (medium : history.MediumAt n m) :
    ∃ k < n, history.NarrowAcquisitionAt narrow k m := by
  obtain ⟨k, hk, agent, g, hacquired, e, hdirect, hbelief⟩ :=
    direct_acquisition_before history m n twoDemands appraisal begins purposive medium
  exact ⟨k, hk, agent, g, hacquired, e, hdirect, hbelief,
    narrowReading k hk agent g hacquired e hdirect hbelief⟩

/-!
## The prior-money variant and the barter version

Rothbard states the genetic claim twice, differently. *MES* p. 275: a
medium "can arise only out of a commodity previously used directly in a
barter situation, and therefore having had an array of prices in terms
of other goods". *Power and Market* (*MES* ed. p. 1021): "no money can
be established on the market except as it can be exchanged for a
previously existing money (which in turn must have ultimately related
back to a commodity in barter)".

### What is proved, and what it costs

- The general version, concluding only that the good was exchanged
  before, against anything, is `exchanged_before`
  (above). It costs the claim and
  `BeginsBeforeMedium`.
- `barter_origin`, `no_medium_without_barter_acquisition`: p. 275's
  version, positive and negative — an earlier acquisition for an end
  other than passing it on, AND against a good that was not then a
  medium. "In barter" is not derived: it is the condition
  `FormedInBarter`, passed through to the conclusion.
- `prior_money_relates_back`: p. 1021's parenthesis — the good the
  medium was first acquired against, if it was then a medium itself,
  had a direct acquisition before that. It is `direct_acquisition_before`
  applied to the counter-good, and it costs the claim and the
  conditions for that good too.

### What the variant does NOT weaken

Under the broad reading, `direct_acquisition_before` already concludes,
for the new medium itself, an earlier acquisition for an end other than
passing it on, whatever was paid for it. The prior money's own history
adds a conclusion about the prior money; it is not needed to reach the
new medium's.
-/

/-- Purposive acquisitions before a later day are purposive before an
earlier one. Bookkeeping. -/
theorem purposive_mono {praxis : MediumFrame} {history : History praxis}
    {m : praxis.Means} {k n : ℕ} (hkn : k ≤ n)
    (purposive : history.AcquisitionsPurposive m n) :
    history.AcquisitionsPurposive m k :=
  fun j hj agent g hacquired =>
    purposive j (Nat.lt_of_lt_of_le hj hkn) agent g hacquired

/-- **Barter origin** — Rothbard's p. 275 version, positive: if anyone
appraises `m` as a medium on day `n`, someone acquired `m` on an earlier
day for an end other than passing it on, giving for it a good that was
not then a medium. -/
theorem barter_origin {praxis : MediumFrame}
    (history : History praxis) (m : praxis.Means) (n : ℕ)
    (twoDemands : TwoPartialDemands praxis m)
    (appraisal : AppraisalFromPast history m)
    (begins : history.BeginsBeforeMedium m)
    (purposive : history.AcquisitionsPurposive m n)
    (barter : history.FormedInBarter m n)
    (medium : history.MediumAt n m) :
    ∃ k < n, ∃ agent g, history.AcquiredAgainst k m agent g ∧
      praxis.ValuesDirectly agent (history.date k) m ∧ ¬ history.MediumAt k g := by
  obtain ⟨k, hk, agent, g, hacquired, hdirect⟩ :=
    direct_acquisition_before history m n twoDemands appraisal begins purposive medium
  exact ⟨k, hk, agent, g, hacquired, hdirect, barter k hk agent g hacquired⟩

/-- **No medium without a barter acquisition** — Rothbard's p. 275
version, negative: if nobody acquired `m` before day `n` both for an end
other than passing it on and against a good not then a medium, nobody
appraises `m` as a medium on day `n` — given that every acquisition of
`m` before `n` was against such a good. -/
theorem no_medium_without_barter_acquisition {praxis : MediumFrame}
    (history : History praxis) (m : praxis.Means) (n : ℕ)
    (appraisal : AppraisalFromPast history m)
    (begins : history.BeginsBeforeMedium m)
    (purposive : history.AcquisitionsPurposive m n)
    (barter : history.FormedInBarter m n)
    (noBarterDirect : ∀ k < n, ¬ ∃ agent g, history.AcquiredAgainst k m agent g ∧
      praxis.ValuesDirectly agent (history.date k) m ∧ ¬ history.MediumAt k g) :
    ¬ history.MediumAt n m := by
  apply no_medium_without_direct_acquisition history m n appraisal begins purposive
  rintro k hk ⟨agent, g, hacquired, hdirect⟩
  exact noBarterDirect k hk
    ⟨agent, g, hacquired, hdirect, barter k hk agent g hacquired⟩

/-- **The prior money relates back** — *Power and Market*'s
parenthesis: if anyone appraises `m` as a medium on day `n`, someone
acquired `m` on an earlier day `k` against some good `g`; and if `g`
was then a medium, someone acquired `g` before `k` for an end other
than passing it on.

The claim and the conditions are carried for every good, since which
good was paid is found, not given: the record must begin before any
medium at all. -/
theorem prior_money_relates_back {praxis : MediumFrame}
    (history : History praxis) (m : praxis.Means) (n : ℕ)
    (twoDemands : ∀ g, TwoPartialDemands praxis g)
    (appraisal : ∀ g, AppraisalFromPast history g)
    (begins : ∀ g, history.BeginsBeforeMedium g)
    (purposive : ∀ g, history.AcquisitionsPurposive g n)
    (medium : history.MediumAt n m) :
    ∃ k < n, ∃ agent g, history.AcquiredAgainst k m agent g ∧
      (history.MediumAt k g → ∃ k' < k, history.DirectAcquisitionAt k' g) := by
  obtain ⟨k, hk, agent, g, hacquired⟩ :=
    exchanged_before history m n (appraisal m) (begins m) medium
  refine ⟨k, hk, agent, g, hacquired, ?_⟩
  intro hmoney
  exact direct_acquisition_before history g k (twoDemands g) (appraisal g) (begins g)
    (purposive_mono (Nat.le_of_lt hk) (purposive g)) hmoney

#print axioms servedBy_singleton
#print axioms indirect_ranks_onward_ends
#print axioms partial_demands_within
#print axioms partial_demands_not_not_exhaust
#print axioms partial_demands_exhaust
#print axioms only_onward_without_direct
#print axioms acquired_of_exchanged
#print axioms exchanged_before
#print axioms ownPastPrice_of_claim
#print axioms no_medium_without_direct_acquisition
#print axioms direct_acquisition_before
#print axioms no_medium_without_narrow_acquisition
#print axioms narrow_acquisition_before
#print axioms purposive_mono
#print axioms barter_origin
#print axioms no_medium_without_barter_acquisition
#print axioms prior_money_relates_back

end Regression
end Apodictic

#lint only unusedArguments
