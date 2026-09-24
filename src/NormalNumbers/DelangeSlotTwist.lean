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

/-! ### Step 3: a unit residue class mod `Q'` -/

/-- **Orthogonality indicator.**  For `b` coprime to `Q'`, the indicator of the residue class
`b` mod `Q'` is the character average `(φ Q')⁻¹ ∑_χ χ(b⁻¹) χ(m)`. -/
lemma indicator_eq_char_avg {Q' : ℕ} (hQ' : 0 < Q') {b : ℕ} (hb : Nat.Coprime b Q') (m : ℕ) :
    (if m % Q' = b % Q' then (1 : ℂ) else 0)
      = ((Nat.totient Q' : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ Q',
          χ ((b : ZMod Q')⁻¹) * χ ((m : ZMod Q')) := by
  classical
  have : NeZero Q' := ⟨hQ'.ne'⟩
  have hu : IsUnit (b : ZMod Q') := (ZMod.isUnit_iff_coprime b Q').2 hb
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu ((m : ZMod Q'))]
  have hφ : (Nat.totient Q' : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 hQ').ne'
  have hiff : ((b : ZMod Q') = (m : ZMod Q')) ↔ (m % Q' = b % Q') := by
    rw [ZMod.natCast_eq_natCast_iff']
    exact eq_comm
  by_cases h : m % Q' = b % Q'
  · rw [if_pos h, if_pos (hiff.2 h), inv_mul_cancel₀ hφ]
  · rw [if_neg h, if_neg (fun hc => h (hiff.1 hc)), mul_zero]

/-- **The unit-class sum.**  For `b` coprime to `Q'` and any `c ≠ 0`, the count-weighted sum
of `z^{ω_{>P}(c·m)}` over `m ≡ b (mod Q')` is `o(y)`. -/
theorem coprimeClass_tendsto_zero {Q' : ℕ} (hQ' : 0 < Q') {b : ℕ} (hb : Nat.Coprime b Q')
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (P : ℕ) {c : ℕ} (hc : c ≠ 0) :
    Tendsto (fun y : ℕ =>
        (∑ m ∈ (Ioc 0 y).filter (fun m => m % Q' = b % Q'), hfun z P (c * m)) / (y : ℂ))
      atTop (𝓝 0) := by
  classical
  have : NeZero Q' := ⟨hQ'.ne'⟩
  have hrw : ∀ y : ℕ,
      (∑ m ∈ (Ioc 0 y).filter (fun m => m % Q' = b % Q'), hfun z P (c * m)) / (y : ℂ)
      = ((Nat.totient Q' : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ Q',
          χ ((b : ZMod Q')⁻¹)
            * ((∑ m ∈ Ioc 0 y, (fun n : ℕ => χ ((n : ZMod Q'))) m * hfun z P (c * m))
                / (y : ℂ)) := by
    intro y
    rw [Finset.sum_filter]
    have : ∀ m ∈ Ioc 0 y, (if m % Q' = b % Q' then hfun z P (c * m) else 0)
        = ((Nat.totient Q' : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ Q',
            χ ((b : ZMod Q')⁻¹) * (χ ((m : ZMod Q')) * hfun z P (c * m)) := by
      intro m _
      have h1 : (if m % Q' = b % Q' then hfun z P (c * m) else 0)
          = (if m % Q' = b % Q' then (1:ℂ) else 0) * hfun z P (c * m) := by
        by_cases h : m % Q' = b % Q' <;> simp [h]
      rw [h1, indicator_eq_char_avg hQ' hb m, mul_assoc, Finset.sum_mul]
      refine congrArg _ (Finset.sum_congr rfl fun χ _ ↦ ?_)
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_comm, mul_div_assoc,
      Finset.sum_div]
    refine congrArg _ (Finset.sum_congr rfl fun χ _ ↦ ?_)
    rw [← Finset.mul_sum, mul_div_assoc]
  simp only [hrw]
  have hlim : Tendsto (fun y : ℕ => ∑ χ : DirichletCharacter ℂ Q',
      χ ((b : ZMod Q')⁻¹)
        * ((∑ m ∈ Ioc 0 y, (fun n : ℕ => χ ((n : ZMod Q'))) m * hfun z P (c * m))
            / (y : ℂ))) atTop (𝓝 (∑ _χ : DirichletCharacter ℂ Q', (0 : ℂ))) := by
    refine tendsto_finsetSum _ fun χ _ ↦ ?_
    have := innerTwist_tendsto_zero (isCharLike_dirichlet hQ' χ) hz hz1 P hc
    simpa using this.const_mul (χ ((b : ZMod Q')⁻¹))
  simpa using hlim.const_mul ((Nat.totient Q' : ℂ))⁻¹


end NormalNumbers.DelangeSlot
