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
  cannot be stated — Nozick's point (1977, p. 371) that "without the
  notion of a unit ... we have no way to state the law", located:
  interchangeability is a condition on STATING the law by size, not a
  premise of the ordering.

`#print axioms marginal_utility` = `[propext, World,
actual_disposition, ends_distinguishable, swap_dominance,
Quot.sound]`; `propext` and `Quot.sound` are Lean's logical
background (they ride in with the quotient-based `Finset`), not
praxeological content. The praxeological base of the law is `World`
+ `actual_disposition` + `ends_distinguishable` + `swap_dominance`,
PLUS the hypotheses in the statement: `actual_disposition A` (this
is the agent's plan), `IndependentUses` (situational), `Homogeneous A`
(situational; supply-size form only), and the sub-stocks being on
hand.

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

/-- Non-vacuity: one more unit always serves some new end — an end
served with `V` but not with `U`. Counting only; not philosophically
load-bearing. -/
theorem exists_marginal {agent : World.Agent} {t : World.Time}
    {s : Stock World agent t} (A : AllocationDisposition s)
    (U V : Finset World.Means) (hUV : s.OneMore U V) :
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

/-- **Marginal utility of the step `U → V`** (one more unit),
Rothbard's sense: the ends the extra unit adds — equivalently, the
ends that would be given up on its loss. "The marginal utility of
the supply is the end that must be given up as the result of a loss
of the unit" (*MES* p. 27); "he gives up the least urgent of the
wants which the larger stock would have satisfied" (p. 25). A set
rather than a single end: determinacy of the drop is not assumed
(see module docstring). A `Set`, not a `Finset`: set difference on
`Finset` needs decidable equality on `World.End`, which the opaque
world does not supply, and reaching for `Classical` would put
`Classical.choice` on the receipt for no praxeological reason.
Definition, not axiom — Rothbard introduces it as a definition ("is
called", "is known as"). Imputation of value from ends to units —
"actors value means strictly in accordance with their valuation of
the ends that they believe the means can serve" (p. 19) — is what
licenses calling this the utility of the *unit*. Indexed by the
step, not by a size: which ends a unit adds may depend on which
units are already on hand unless the plan is `Homogeneous`. -/
def marginalEnds {agent : World.Agent} {t : World.Time}
    {s : Stock World agent t} (A : AllocationDisposition s)
    (U V : Finset World.Means) : Set World.End :=
  {e | e ∈ A.wouldServe V ∧ e ∉ A.wouldServe U}

/-- **The law of marginal utility, along a chain of specific units**:
for `U ⊂ V ⊂ W` each one unit more, every end the step `U → V` adds
is preferred to every end the step `V → W` adds. No interchangeability
of units is needed: the chain names which units. One application of
`urgency_principle`; the marginality of `e` at the first step is
unused (`_h_marg`). -/
theorem marginal_utility_chain
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : AllocationDisposition s) (hA : actual_disposition A)
    (hI : World.IndependentUses agent t)
    (U V W : Finset World.Means) (_hUV : s.OneMore U V) (hVW : s.OneMore V W) :
    ∀ e ∈ marginalEnds A U V, ∀ e' ∈ marginalEnds A V W,
      World.PrefersEnd agent t e e' := by
  intro e he e' he'
  obtain ⟨heV, _h_marg⟩ := he
  obtain ⟨he'W, he'V⟩ := he'
  exact urgency_principle A hA hI V W hVW e heV e' he'W he'V

/-- **The law of marginal utility** (Rothbard, *MES*, ch. 1, p. 27):
"The greater the supply of a good, the lower the marginal utility;
the smaller the supply, the higher the marginal utility." By supply
SIZE: every end marginal at a supply of `n` units is preferred to
every end marginal at a supply of `n + 1` — for ANY two one-unit
steps reaching those sizes; the steps need not share a unit.

Needs `Homogeneous A`, exactly once: the plan with the `n` units
below the second step is the plan with the `n` units of the first.
The marginality of `e` at `n` is unused (`_h_marg`). -/
theorem marginal_utility
    {agent : World.Agent} {t : World.Time} {s : Stock World agent t}
    (A : AllocationDisposition s) (hA : actual_disposition A)
    (hI : World.IndependentUses agent t) (hH : A.Homogeneous)
    (U V U' V' : Finset World.Means)
    (hUV : s.OneMore U V) (hU'V' : s.OneMore U' V')
    (n : ℕ) (hn : V.card = n) (hn' : V'.card = n + 1) :
    ∀ e ∈ marginalEnds A U V, ∀ e' ∈ marginalEnds A U' V',
      World.PrefersEnd agent t e e' := by
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
