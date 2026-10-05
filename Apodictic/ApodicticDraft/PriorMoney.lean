import ApodicticDraft.Regress

/-!
# The prior-money variant and the barter version (T2, S6; M-7 (a))

Rothbard states the genetic claim twice, differently. *MES* p. 275: a
medium "can arise only out of a commodity previously used directly in a
barter situation, and therefore having had an array of prices in terms
of other goods". *Power and Market* (*MES* ed. p. 1021): "no money can
be established on the market except as it can be exchanged for a
previously existing money (which in turn must have ultimately related
back to a commodity in barter)".

## What is proved, and what it costs

- The general version, concluding only that the good was exchanged
  before, against anything, is `exchanged_before`
  (`ApodicticDraft.Appraisal`). It costs the claim and
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

## What the variant does NOT weaken

Under the broad reading, `direct_acquisition_before` already concludes,
for the new medium itself, an earlier acquisition for an end other than
passing it on, whatever was paid for it. The prior money's own history
adds a conclusion about the prior money; it is not needed to reach the
new medium's.
-/

namespace ApodicticDraft

open Apodictic

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

#print axioms purposive_mono
#print axioms barter_origin
#print axioms no_medium_without_barter_acquisition
#print axioms prior_money_relates_back

end ApodicticDraft

#lint only unusedArguments
