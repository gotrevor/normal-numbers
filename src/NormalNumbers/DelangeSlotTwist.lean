import NormalNumbers.DelangeSlotMaster

/-!
# Rung 2, layer 5: the additive twist

Assembles `charSum_tendsto_zero` (master dichotomy) with the unfolding identity
`sum_mul_left_expand` into the twisted mean
`∑_{m ≤ N} e(jm/Q) z^{ω_{>P}(m)} = o(N)`.

Route (see `HANDOFF-2026-09-24-delange-rung1-done-rung2-assembly.md`):

1. `isCharLike_dirichlet` — a `DirichletCharacter ℂ M` is `IsCharLike M`.
2. `innerTwist_tendsto_zero` — for character-like `κ` and any `c ≠ 0`,
   `∑_{m ≤ y} κ(m) z^{ω_{>P}(c·m)} = o(y)`, by `sum_mul_left_expand` + `charSum_tendsto_zero`.
3. `coprimeClass_tendsto_zero` — orthogonality turns the indicator of a *unit* residue class
   mod `Q'` into an average of characters, giving `∑_{m ≤ y, m ≡ b [Q']} z^{ω_{>P}(c·m)} = o(y)`.
4. `classSum_reindex` — `m = e·m'` with `e = gcd(a,Q)`, `Q' = Q/e`, `b = a/e` moves a *general*
   residue class mod `Q` to a *unit* class mod `Q'`.  This is why no induction on `Q` is needed.
5. The headline: regroup `∑_{m ≤ N}` by `m % Q`.
-/

open Finset Filter Topology Complex Real

namespace NormalNumbers.DelangeSlot

/-! ### Step 1: Dirichlet characters are character-like -/

lemma isCharLike_dirichlet {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M) :
    IsCharLike M (fun n : ℕ => χ (n : ZMod M)) where
  pos := hM
  mul := by intro a b; push_cast; exact map_mul _ _ _
  per := by
    intro a b hab
    have : (a : ZMod M) = (b : ZMod M) := (ZMod.natCast_eq_natCast_iff' a b M).2 hab
    rw [this]
  zero := by
    intro n hn
    refine χ.map_nonunit ?_
    rw [ZMod.isUnit_iff_coprime]
    exact hn
  norm_le := by
    intro n
    have := DirichletCharacter.norm_le_one χ (n : ZMod M)
    simpa using this

/-! ### Step 2: the inner twisted sum -/

/-- For character-like `κ` and any fixed `c ≠ 0`, the mean of `κ(m)·z^{ω_{>P}(c·m)}`
tends to `0`. -/
theorem innerTwist_tendsto_zero {M : ℕ} {κ : ℕ → ℂ} (h : IsCharLike M κ) {z : ℂ}
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (P : ℕ) {c : ℕ} (hc : c ≠ 0) :
    Tendsto (fun y : ℕ => (∑ m ∈ Ioc 0 y, κ m * hfun z P (c * m)) / (y : ℂ)) atTop (𝓝 0) := by
  classical
  have hrw : ∀ y : ℕ, (∑ m ∈ Ioc 0 y, κ m * hfun z P (c * m)) / (y : ℂ)
      = ∑ U ∈ (bigPrimes P c).powerset, (z - 1) ^ U.card
          * (Sgsum (fun n => κ n * chiZero (∏ p ∈ U, p) n) z P y / (y : ℂ)) := by
    intro y
    rw [sum_mul_left_expand hc κ z P y, Finset.sum_div]
    exact Finset.sum_congr rfl fun U _ ↦ by ring
  simp only [hrw]
  have : Tendsto (fun y : ℕ => ∑ U ∈ (bigPrimes P c).powerset, (z - 1) ^ U.card
      * (Sgsum (fun n => κ n * chiZero (∏ p ∈ U, p) n) z P y / (y : ℂ))) atTop
      (𝓝 (∑ U ∈ (bigPrimes P c).powerset, (0 : ℂ))) := by
    refine tendsto_finsetSum _ fun U hU ↦ ?_
    have hprod : 0 < ∏ p ∈ U, p := by
      refine Finset.prod_pos fun p hp ↦ ?_
      have hpU : p ∈ bigPrimes P c := (Finset.mem_powerset.1 hU) hp
      exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hpU).1).pos
    have := charSum_tendsto_zero (h.mul_chiZero hprod) hz hz1 P
    simpa using this.const_mul ((z - 1) ^ U.card)
  simpa using this

end NormalNumbers.DelangeSlot
