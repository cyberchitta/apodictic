import Apodictic.Axioms

/-!
# Marginal Utility — Rothbard's allocation version

First pass completed 2026-08-02: `marginal_utility` below, with
`#print axioms` = `[propext, World, allocation_demonstrated_preference,
Quot.sound]`. Of these, `propext` and `Quot.sound` are Lean's logical
background (they ride in with the quotient-based `Finset`), not
praxeological content; the praxeological base of the law is `World` +
`allocation_demonstrated_preference` alone.

What the ledger shows (findings; logged in `_notes/`):

- `demonstrated_preference` — the actual-action axiom — does NO work
  here: the law rests entirely on the counterfactual disposition.
  Nozick's point, vindicated in the formal ledger.
- No structural property of `Prefers` is forced: no transitivity, no
  totality. The ordering work is done by the disposition, not the
  latent ranking.
- The hypothesis that the lower-supply end is *marginal* at `n` is
  unused (note the underscore): the law holds for EVERY end served
  at `n` against the end marginal at `n + 1`. Rothbard's
  marginal-vs-marginal statement is weaker than what his own
  premises deliver.
- With strict-only preference the law comes out strict — stronger
  than the textbook non-increasing form. Whether that is honest or
  an artifact of banning indifference is an open question.
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

/-- **The law of marginal utility**, allocation version (Rothbard,
*MES*, ch. 1): the marginal end at supply `n` is preferred to the
marginal end at supply `n + 1` — a larger supply's marginal unit
serves a lower-valued end.

Stated faithfully to the tradition: both ends are hypothesized
marginal. The marginality of `en` (`_h_marg`, underscored) is UNUSED
by the proof — see the module docstring. -/
theorem marginal_utility {agent : World.Agent} {t : World.Time}
    {s : Stock World agent t} (A : AllocationDisposition s) (n : ℕ)
    {en en1 : World.End}
    (h_serv : en ∈ A.wouldServe n)
    (_h_marg : en ∉ A.wouldServe (n - 1))
    (h_serv1 : en1 ∈ A.wouldServe (n + 1))
    (h_marg1 : en1 ∉ A.wouldServe n) :
    World.Prefers agent t en en1 :=
  allocation_demonstrated_preference A n en h_serv en1 h_serv1 h_marg1

#print axioms marginal_utility

end Apodictic
