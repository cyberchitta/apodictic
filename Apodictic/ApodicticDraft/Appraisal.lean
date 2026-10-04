import ApodicticDraft.Claims

/-!
# Appraisal from the past (T2, S3)

The hinge of the regression theorem: appraising a good as a medium
needs an exchange of it before. The claim is `AppraisalFromPast`, in
the weak form ruled 2026-10-04 (M-3): "some earlier exchange of m,
against anything". Its Lean wording awaits the owner's approval.

## What is proved, and what it costs

- `acquired_of_exchanged`: an exchange of `m` has a party who acquired
  `m`. Bookkeeping; it spends the exchange's `swap_gives`.
- `exchanged_before`: whoever appraises `m` as a medium on day `n`,
  `m` was acquired by someone, against something, on an earlier day.
  It costs the claim and `BeginsBeforeMedium`, and nothing else.
- `ownPastPrice_of_claim`: the condition "own past price", stated
  without quantities, follows from the claim. Ruled as two things,
  in this vocabulary they are one: see the module `Medium` and the
  ledger.
-/

namespace ApodicticDraft

open Apodictic

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

#print axioms acquired_of_exchanged
#print axioms exchanged_before
#print axioms ownPastPrice_of_claim

end ApodicticDraft

#lint only unusedArguments
