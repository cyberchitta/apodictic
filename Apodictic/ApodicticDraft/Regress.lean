import ApodicticDraft.Appraisal

/-!
# The genetic regress (T2, S4) and the narrow reading (M-2 (b))

"no good can be employed for the function of a medium of exchange which
at the very beginning of its use for this purpose did not have exchange
value on account of other employments" (*Human Action*, ch. XVII, §4;
again in ch. XXI, §6).

## What is proved, and what it costs

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
  `[DecidablePred (praxis.Onward m)]`, the sort of an end decided. Not
  classical: what is classical is the LAST day of barter (S5, parked),
  which needs "medium on day `k`" decided, and that quantifies over
  agents.
- `no_medium_without_narrow_acquisition`,
  `narrow_acquisition_before`: the same two forms, for the narrow
  reading of "other employments" (consumption or production). They cost
  the broad theorems plus the condition `OtherEmploymentsNarrow`, which
  is the narrow reading itself. Nothing is derived beyond it.

## What `AppraisalFromPast` is NOT asked for

The barter condition, the own-past-price condition, and the
counter-good. Under the broad reading, the earliest direct acquisition
is reached through exchanges against anything, money included: the
regress follows the acquirers' ENDS, never what they paid.
-/

namespace ApodicticDraft

open Apodictic

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
day for an end other than passing it on. Given that the sort of an end
can be decided. -/
theorem direct_acquisition_before {praxis : MediumFrame}
    (history : History praxis) (m : praxis.Means) (n : ℕ)
    [DecidablePred (praxis.Onward m)]
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
        rcases Decidable.em (praxis.Onward m e) with honward | hdirect
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
    [DecidablePred (praxis.Onward m)]
    (appraisal : AppraisalFromPast history m)
    (begins : history.BeginsBeforeMedium m)
    (purposive : history.AcquisitionsPurposive m n)
    (narrowReading : history.OtherEmploymentsNarrow narrow m n)
    (medium : history.MediumAt n m) :
    ∃ k < n, history.NarrowAcquisitionAt narrow k m := by
  obtain ⟨k, hk, agent, g, hacquired, e, hdirect, hbelief⟩ :=
    direct_acquisition_before history m n appraisal begins purposive medium
  exact ⟨k, hk, agent, g, hacquired, e, hdirect, hbelief,
    narrowReading k hk agent g hacquired e hdirect hbelief⟩

#print axioms no_medium_without_direct_acquisition
#print axioms direct_acquisition_before
#print axioms no_medium_without_narrow_acquisition
#print axioms narrow_acquisition_before

end ApodicticDraft

#lint only unusedArguments
