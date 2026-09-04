import Apodictic.Axioms

/-!
# Marginal Utility — Rothbard's allocation version

Second pass 2026-09-04 (first pass 2026-08-02). The law is now
stated about the *marginal utility of a supply* in Rothbard's own
sense — the end(s) that would be given up on the loss of one unit
(*MES* p. 27) — via the definition `marginalEnds` below.
`#print axioms marginal_utility` = `[propext, World,
urgency_principle, Quot.sound]`; `propext` and `Quot.sound` are
Lean's logical background (they ride in with the quotient-based
`Finset`), not praxeological content. The praxeological base of the
law is `World` + `urgency_principle` alone.

What the ledger shows (findings; logged in `_notes/`):

- The law rests entirely on the counterfactual disposition. No
  axiom about ACTUAL action is in the base at all (point-of-first-
  use, 2026-09-04): the bridge `demonstrated_preference` was never
  cited and is parked. Whether the urgency principle can itself be
  derived from such a bridge is the open research item — that is
  where Nozick's objection lives.
- Preference is over bundles (`Prefers : … → Set End → Set End → Prop`,
  2026-09-04); the law is stated over singleton bundles via
  `PrefersEnd`. Nothing about bundles is used here — the restatement
  is one abbreviation; the one-step proof is unchanged.
- No structural property of `Prefers` is forced: no transitivity,
  no totality. Rothbard's derivation PRESUPPOSES a linear value
  scale over the ends (*MES* pp. 25–26, Figure 3); our premises are
  weaker — the ordering work is done by the disposition.
- The hypothesis that `en` is *marginal* at `n` is unused (see the
  proof): the law holds for EVERY end served at `n` against every
  end marginal at `n + 1`. Rothbard's marginal-vs-marginal statement
  is weaker than his own premise delivers.
- The law is strict. So is Rothbard's: "will be less than", "the
  lower the marginal utility" (pp. 24, 27). Non-increasing is the
  neoclassical form, not his. Resolved 2026-09-04 by the text.
- Determinacy is not assumed: `marginalEnds A n` may have more than
  one element. Rothbard's "the marginal unit" presupposes exactly
  one; we do not need it for the law.
- Rothbard's remark (p. 29) that the addition-marginal unit at `n`
  and the loss-marginal unit at `n + 1` have "identical" value
  "provided that his ends and their ranking are the same" is
  DEFINITIONAL here: one disposition supplies both, so
  `marginalEnds A (n + 1)` — served at `n + 1`, not at `n` — is the
  same set read either way.
-/

namespace Apodictic

/-- Non-vacuity: within the actual supply there is always a marginal
end — one served with `n + 1` units but not with `n`. Counting only;
not philosophically load-bearing. -/
theorem exists_marginal {agent : World.Agent} {t : World.Time}
    {s : Stock World agent t} (A : AllocationDisposition s) (n : ℕ)
    (hn : n + 1 ≤ s.units.card) :
    ∃ e ∈ A.wouldServe (n + 1), e ∉ A.wouldServe n := by
  by_contra h
  have hsub : A.wouldServe (n + 1) ⊆ A.wouldServe n := by
    intro e he
    by_contra hne
    exact h ⟨e, he, hne⟩
  have hle := Finset.card_le_card hsub
  rw [A.card_eq (n + 1) hn, A.card_eq n (Nat.le_of_succ_le hn)] at hle
  exact Nat.not_succ_le_self n hle

/-- **Marginal utility of a supply of `n` units**, Rothbard's sense:
the ends that would be given up on the loss of one unit. "The
marginal utility of the supply is the end that must be given up as
the result of a loss of the unit" (*MES* p. 27); "he gives up the
least urgent of the wants which the larger stock would have
satisfied" (p. 25). A set rather than a single end: determinacy of
the drop is not assumed (see module docstring). A `Set`, not a
`Finset`: set difference on `Finset` needs decidable equality on
`World.End`, which the opaque world does not supply, and reaching
for `Classical` would put `Classical.choice` on the receipt for no
praxeological reason. Definition, not
axiom — Rothbard introduces it as a definition ("is called",
"is known as"). Imputation of value from ends to units — "actors
value means strictly in accordance with their valuation of the ends
that they believe the means can serve" (p. 19) — is what licenses
calling this the utility of the *unit*. -/
def marginalEnds {agent : World.Agent} {t : World.Time}
    {s : Stock World agent t} (A : AllocationDisposition s) (n : ℕ) :
    Set World.End :=
  {e | e ∈ A.wouldServe n ∧ e ∉ A.wouldServe (n - 1)}

/-- **The law of marginal utility** (Rothbard, *MES*, ch. 1, p. 27):
"The greater the supply of a good, the lower the marginal utility;
the smaller the supply, the higher the marginal utility." Stated
over marginal ends: every end marginal at supply `n` is preferred to
every end marginal at supply `n + 1`.

The marginality of `en` (`_h_marg`, underscored) is UNUSED by the
proof — see the module docstring. -/
theorem marginal_utility {agent : World.Agent} {t : World.Time}
    {s : Stock World agent t} (A : AllocationDisposition s) (n : ℕ) :
    ∀ en ∈ marginalEnds A n, ∀ en1 ∈ marginalEnds A (n + 1),
      World.PrefersEnd agent t en en1 := by
  intro en hen en1 hen1
  obtain ⟨h_serv, _h_marg⟩ := hen
  obtain ⟨h_serv1, h_marg1⟩ := hen1
  rw [Nat.add_sub_cancel] at h_marg1
  exact urgency_principle A n en h_serv en1 h_serv1 h_marg1

#print axioms marginal_utility

end Apodictic
