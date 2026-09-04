import Apodictic.Urgency

/-!
# Marginal Utility — Rothbard's allocation version

The law is stated about the *marginal utility of a supply* in
Rothbard's own sense — the end(s) that would be given up on the
loss of one unit (*MES* p. 27) — via the definition `marginalEnds`
below, and derived in one step from `urgency_principle`.

`#print axioms marginal_utility` = `[propext, World,
actual_disposition, ends_distinguishable, swap_dominance,
Quot.sound]`; `propext` and `Quot.sound` are Lean's logical
background (they ride in with the quotient-based `Finset`), not
praxeological content. The praxeological base of the law is `World`
+ `actual_disposition` + `ends_distinguishable` + `swap_dominance`,
PLUS the hypotheses in the statement: `actual_disposition A` (this
is the agent's plan), `IndependentUses` (situational), and
`n ≤ supply`.

What the receipt shows is read in the Verso document (part I,
findings). In brief: no axiom about ACTUAL action is cited — the law
rests on the subjunctive disposition alone; independence of uses is
a hypothesis, not an axiom; no structural property of `Prefers` is
forced; the law is strict, as Rothbard's is; determinacy of the drop
is not assumed; and the marginality of the end at `n` is unused by
the proof — the law holds for every end served at `n`.
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
    {s : Stock World agent t} (A : AllocationDisposition s)
    (hA : actual_disposition A) (hI : World.IndependentUses agent t)
    (n : ℕ) (hn : n ≤ s.units.card) :
    ∀ en ∈ marginalEnds A n, ∀ en1 ∈ marginalEnds A (n + 1),
      World.PrefersEnd agent t en en1 := by
  intro en hen en1 hen1
  obtain ⟨h_serv, _h_marg⟩ := hen
  obtain ⟨h_serv1, h_marg1⟩ := hen1
  rw [Nat.add_sub_cancel] at h_marg1
  exact urgency_principle A hA hI n hn en h_serv en1 h_serv1 h_marg1

#print axioms marginal_utility

end Apodictic
