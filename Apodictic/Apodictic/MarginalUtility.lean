import Apodictic.Urgency

/-!
# Marginal Utility — Rothbard's allocation version

The law is stated about the *marginal utility of a supply* in
Rothbard's own sense — the end(s) that would be given up on the
loss of one unit (*MES* p. 27) — via the definition `marginalEnds`
below, in two forms:

- `marginal_utility_chain`: along a chain of specific units, what the
  second unit adds is less urgent than what the first added. Needs
  no interchangeability of units.
- `marginal_utility`: Rothbard's wording, by supply SIZE — "the
  greater the supply, the lower the marginal utility". Needs
  `Homogeneous A` (interchangeability), used exactly once: to say
  what "the plan at `n` units" is. Without it the supply-size form
  cannot be stated: interchangeability is a condition on STATING the
  law by size, not a premise of the ordering.

`#print axioms marginal_utility` = `[propext, Quot.sound]` —
Lean's own background (both arrive with the quotient-based `Finset`,
and with set extensionality), and nothing else: the library declares
no axioms. The
praxeological content is read off the SIGNATURE instead, and it is
one commitment plus three situational conditions: `SwapDominant A`
(the commitment), `IndependentUses` and `Homogeneous A` (situational;
the latter for the supply-size form only), `[DecidableEq F.End]` (a
data condition on the frame), and the sub-stocks being on hand. That
every one of them does real work is enforced by
`#lint only unusedArguments`, not by the proof term — see
`Apodictic.Commitments`.

What the receipt shows is read in the Verso document (part I,
findings). In brief: no axiom about ACTUAL action is cited — the law
rests on the subjunctive disposition alone; independence of uses and
interchangeability of units are hypotheses, not axioms; no
structural property of `Prefers` is forced; the law is strict, as
Rothbard's is; determinacy of the drop is not assumed; and the
marginality of the end at the smaller supply is unused by the proof
— the law holds for every end served there.
-/

namespace Apodictic

/-- One more unit always serves some new end: there is an end served
with `V` that is not served with `U`. Pure counting, carrying no
philosophical weight — it just keeps the law from being about
nothing. -/
theorem exists_marginal {F : ActionFrame} {agent : F.Agent} {t : F.Time}
    {s : Stock F agent t} (A : AllocationDisposition s)
    (U V : Finset F.Means) (hUV : s.OneMore U V) :
    ∃ e ∈ A.wouldServe V, e ∉ A.wouldServe U := by
  by_contra h
  have hsub : A.wouldServe V ⊆ A.wouldServe U := by
    intro e he
    by_contra hne
    exact h ⟨e, he, hne⟩
  have hle := Finset.card_le_card hsub
  have hU : U ⊆ s.units := fun x hx => hUV.2.1 (hUV.1 hx)
  rw [A.card_eq V hUV.2.1, A.card_eq U hU, hUV.2.2] at hle
  exact Nat.not_succ_le_self U.card hle

/-- **Marginal utility of the step `U → V`** — of going up by one
unit — in Rothbard's own sense: the ends the extra unit adds, which
are the same as the ends that would be given up if it were lost.
"The marginal utility of the supply is the end that must be given up
as the result of a loss of the unit" (*MES* p. 27); "he gives up the
least urgent of the wants which the larger stock would have
satisfied" (p. 25).

A set of ends rather than a single end, because it is not assumed
that exactly one end drops (see the module docstring). A `Set` rather
than a `Finset` for a mechanical reason: subtracting one `Finset`
from another needs decidable equality on `F.End`, which an arbitrary
frame does not give us, and reaching for `Classical` would put
`Classical.choice` on the receipt for no praxeological reason at all.

A definition, not a claim — Rothbard introduces it as one ("is
called", "is known as"). What licenses calling this the utility of
the *unit* is imputation of value from ends back to means: "actors
value means strictly in accordance with their valuation of the ends
that they believe the means can serve" (p. 19).

Indexed by the step rather than by a size, because which ends a unit
adds can depend on which units are already on hand — unless the plan
is `Homogeneous`. -/
def marginalEnds {F : ActionFrame} {agent : F.Agent} {t : F.Time}
    {s : Stock F agent t} (A : AllocationDisposition s)
    (U V : Finset F.Means) : Set F.End :=
  {e | e ∈ A.wouldServe V ∧ e ∉ A.wouldServe U}

/-- **The law of marginal utility, along a chain of named units.**
Take `U ⊂ V ⊂ W`, each one unit more than the last. Every end the
first step adds is preferred to every end the second step adds.

No interchangeability of units is needed, because the chain says
which units are involved. One application of `urgency_principle`; the
fact that `e` is marginal at the first step goes unused
(`_h_marg`). -/
theorem marginal_utility_chain
    {F : ActionFrame} [DecidableEq F.End]
    {agent : F.Agent} {t : F.Time} {s : Stock F agent t}
    (A : AllocationDisposition s) (hA : SwapDominant A)
    (hI : F.IndependentUses agent t)
    (U V W : Finset F.Means) (_hUV : s.OneMore U V) (hVW : s.OneMore V W) :
    ∀ e ∈ marginalEnds A U V, ∀ e' ∈ marginalEnds A V W,
      F.PrefersEnd agent t e e' := by
  intro e he e' he'
  obtain ⟨heV, _h_marg⟩ := he
  obtain ⟨he'W, he'V⟩ := he'
  exact urgency_principle A hA hI V W hVW e heV e' he'W he'V

/-- **The law of marginal utility** (Rothbard, *MES*, ch. 1, p. 27):
"The greater the supply of a good, the lower the marginal utility;
the smaller the supply, the higher the marginal utility."

This is the version stated by supply SIZE. Every end that is marginal
at a supply of `n` units is preferred to every end marginal at a
supply of `n + 1` — and that holds for ANY two one-unit steps
reaching those sizes, which need not have a single unit in common.

`Homogeneous A` is needed exactly once, to say that the plan with the
`n` units below the second step is the plan with the `n` units of the
first. The fact that `e` is marginal at `n` goes unused
(`_h_marg`). -/
theorem marginal_utility
    {F : ActionFrame} [DecidableEq F.End]
    {agent : F.Agent} {t : F.Time} {s : Stock F agent t}
    (A : AllocationDisposition s) (hA : SwapDominant A)
    (hI : F.IndependentUses agent t) (hH : A.Homogeneous)
    (U V U' V' : Finset F.Means)
    (hUV : s.OneMore U V) (hU'V' : s.OneMore U' V')
    (n : ℕ) (hn : V.card = n) (hn' : V'.card = n + 1) :
    ∀ e ∈ marginalEnds A U V, ∀ e' ∈ marginalEnds A U' V',
      F.PrefersEnd agent t e e' := by
  intro e he e' he'
  obtain ⟨heV, _h_marg⟩ := he
  obtain ⟨he'V', he'U'⟩ := he'
  have hV : V ⊆ s.units := hUV.2.1
  have hU' : U' ⊆ s.units := fun x hx => hU'V'.2.1 (hU'V'.1 hx)
  have hcard : V.card = U'.card := by
    have := hU'V'.2.2
    omega
  rw [hH V hV U' hU' hcard] at heV
  exact urgency_principle A hA hI U' V' hU'V' e heV e' he'V' he'U'

#print axioms marginal_utility_chain
#print axioms marginal_utility

end Apodictic

#lint only unusedArguments
