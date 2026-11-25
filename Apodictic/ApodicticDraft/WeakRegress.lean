import Apodictic.TimePreference
import ApodicticDraft.Claims

/-!
# The regress from the weak first step

Mises and Rothbard both word the regress's first step weakly: without
a preference for the sooner, a man would not consume. The library's
`Apodictic.TimePreference.regress` spends the stronger claim
`DemonstratedTimePreference`: consuming shows the preference. This
module builds the regress from the weak wording
(`NoConsumingWithoutPreference`, in `ApodicticDraft.Claims`), as a
rival, so that what `regress` needs is checked and not argued.

## What is proved, and what it costs

- `consumption_refutes_no_preference`: the weak counterpart of
  `consumption_reveals`. An act of consuming at a date refutes "no
  preference for the sooner" at that date. It does not give the
  preference.
- `regress_from_weak`: `regress`'s conclusion, word for word, with the
  weak claim in place of `DemonstratedTimePreference` and every other
  hypothesis unchanged.
- `weak_of_demonstrated`: the strong claim gives the weak one. So
  `regress` follows from `regress_from_weak`, and the weak version
  asserts no more.
- `demonstrated_of_weak_of_decidable`: where each preference the claim
  speaks of either holds or does not, the weak claim gives the strong
  one back. The two differ by excluded middle on those preferences and
  by nothing else, so no frame satisfies one and fails the other.

The proofs are short: each is the library's proof with one step
changed. Nothing here is hard-won; the content is in which claim the
signature names.
-/

namespace ApodicticDraft
namespace WeakRegress

open Apodictic

/-- **Consuming refutes the absence of a preference, at that date.**
The weak counterpart of `Apodictic.TimePreference.consumption_reveals`:
the same hypotheses with the weak claim, and the conclusion a double
negation. -/
theorem consumption_refutes_no_preference
    {praxis : DatedFrame} {agent : praxis.Agent}
    (morrows : Morrows praxis agent) (n : ℕ)
    (act : Action praxis.toActionFrame)
    (consumes : morrows.ConsumesAt n act)
    (sameAlternative : morrows.SameAlternative)
    (weak : NoConsumingWithoutPreference act) :
    ¬ ¬ praxis.PrefersEnd agent (morrows.date n)
      (morrows.offer n) (morrows.offer (n + 1)) := by
  obtain ⟨hagent, htime, hchosen, hforgone⟩ := consumes
  subst hagent
  have hsame : praxis.SameSatisfaction act.agent act.chosen (morrows.offer (n + 1)) := by
    rw [hchosen]
    exact sameAlternative n
  have hbefore : praxis.Before (praxis.attained act.chosen)
      (praxis.attained (morrows.offer (n + 1))) := by
    rw [hchosen, morrows.dated n, morrows.dated (n + 1)]
    exact morrows.successive n
  have h := weak.refutes _ hforgone hsame hbefore
  rw [htime, hchosen] at h
  exact h

/-- **Mises's regress, from the weak first step.** The conclusion of
`Apodictic.TimePreference.regress`, unchanged, and its hypotheses
unchanged but one: `NoConsumingWithoutPreference` stands where
`DemonstratedTimePreference` stood.

The regress never needed the preference at the date of the act. It
needs only that its absence there is refuted, because what it carries
forward from the first date is the absence. -/
theorem regress_from_weak
    {praxis : DatedFrame} {agent : praxis.Agent}
    (morrows : Morrows praxis agent) (n : ℕ)
    (act : Action praxis.toActionFrame)
    (consumes : morrows.ConsumesAt n act)
    (sameAlternative : morrows.SameAlternative)
    (weak : NoConsumingWithoutPreference act)
    (carries : morrows.NoPreferenceCarries) :
    ¬ ¬ praxis.PrefersEnd agent (morrows.date 0)
      (morrows.offer 0) (morrows.offer 1) :=
  fun none =>
    consumption_refutes_no_preference morrows n act consumes sameAlternative weak
      (Apodictic.TimePreference.no_preference_at_every_date morrows none carries n)

/-- **The strong claim gives the weak one.** An act that demonstrates
the preference refutes its absence. -/
theorem weak_of_demonstrated
    {praxis : DatedFrame} {act : Action praxis.toActionFrame}
    (demonstrated : DemonstratedTimePreference act) :
    NoConsumingWithoutPreference act :=
  ⟨fun later hforgone hsame hbefore none =>
    none (demonstrated.demonstrates later hforgone hsame hbefore)⟩

/-- **The weak claim gives the strong one where the preference is
decided.** If each preference the claim speaks of either holds or does
not, refuting its absence produces it. The hypothesis `decided` is
excluded middle for those preferences, which the library does not
assume. -/
theorem demonstrated_of_weak_of_decidable
    {praxis : DatedFrame} {act : Action praxis.toActionFrame}
    (weak : NoConsumingWithoutPreference act)
    (decided : ∀ later ∈ act.forgone,
      praxis.PrefersEnd act.agent act.time act.chosen later ∨
        ¬ praxis.PrefersEnd act.agent act.time act.chosen later) :
    DemonstratedTimePreference act :=
  ⟨fun later hforgone hsame hbefore =>
    match decided later hforgone with
    | Or.inl prefers => prefers
    | Or.inr lacks => absurd lacks (weak.refutes later hforgone hsame hbefore)⟩

#print axioms consumption_refutes_no_preference
#print axioms regress_from_weak
#print axioms weak_of_demonstrated
#print axioms demonstrated_of_weak_of_decidable

end WeakRegress
end ApodicticDraft

#lint only unusedArguments
