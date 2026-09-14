/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyE1Down

/-!
# The two-dimensional ladder: marching `m₁` at fixed `K`, and the **tiling** of outer scales

`G4EntropyScaleGap` records the obstruction that blocks `IsNormal 2 fullReal`: the certified
outer scales of consecutive rungs do not meet, because `Xhi K k₄ + 1 < Xlo (K+4)`, and the
separation is a tower (`m₁ (K+4) ≥ 4096·m₁ K`).

**That gap is an artifact of pinning `m` to `K`.**  In the implemented schedule
`m K = m₁ K + m₂ K` with `m₁ K = 1000·8^K·K^{2K+1}` and `m₂ K = 8K²`, and the scales are
`R = 2^{2^{m₁}}`, `Y = 2^{2^m}`, `X = Y^{100}`, `Xlo = Y^{50}`.  But `m₁` is the *small-prime
cutoff exponent*, and the `entropy_E0` cone constrains it **only from below**.  Raising `m₁`
by one at fixed `K` (keeping `m₂` fixed, so the dyadic Chebyshev factor `1 + m₂ log 2` of
`Sched.dyadic_factor_le` is **unchanged**) squares `Y`, and therefore

    Xlom K (j+1)  =  Y_{j+1}^{50}  =  Y_j^{100}  =  Xm K j                (`Xlom_succ`)

— the certified windows `[Y^{50}, Y^{100}]` **tile contiguously**, with no gap at all.

This module supplies the arithmetic spine of that march:

* the marched scales `mm₁`, `mm`, `Rm`, `Ym`, `Xm`, `Xlom`, `Mcm`, and `jstar K` — the march
  length at which the rung-`K` tower reaches rung `K+4`'s floor **exactly**
  (`Xm_jstar : Xm K (jstar K) = Xlo (K+4)`);
* the two genuine `m₁`-**upper** bounds of the cone, proved for every `j ≤ jstar K`:
  `Mcm_le_two_pow_m₂` (the small-prime budget, `Mc ≤ 2^{m₂}`, cf. `Sched.Mc_le_two_pow_m₂`)
  and `four_mul_le_four_pow_N_m` (the `hfar` inequality, cf. `Sched.four_mul_le_four_pow_N`).
  Both have a factor-`K/log K` margin: the binding one reads `6K² + 31K + 81 ≤ 8K²`;
* the covering lemma `exists_tile`, and the endpoint `entropy_E1_tile` — `entropy_E1_down`'s
  conclusion at **every** outer scale in `[Xlo K, Xlo (K+4)]`, i.e. the scale gap closed.

Everything above is proved here.  The E1 chain at the marched parameters `(K, j)` —
`entropy_E1_march` — and the endpoint `entropy_E1_tile` live downstream in
`G4EntropyMTowerAssembly`, because their proof needs the three ported inputs of
`G4EntropyMTowerBig`, `G4EntropyMTowerBudget` and `G4EntropyMTowerDown`.

Nothing here claims anything about the normality of `G₄` itself.
-/

open Finset Real

namespace NormalNumbers.G4

namespace Sched

open NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The marched scales -/

/-- The marched small-prime exponent `m₁ K + j`.  `j = 0` is the implemented schedule. -/
def mm₁ (K j : ℕ) : ℕ := m₁ K + j

/-- The marched medium exponent `m K + j`.  The *difference* `mm - mm₁ = m₂ K` is fixed, which
is exactly why the dyadic Chebyshev factor of `hbig` does not move. -/
def mm (K j : ℕ) : ℕ := m K + j

/-- The marched small-prime cutoff `R = 2^{2^{mm₁}}`. -/
def Rm (K j : ℕ) : ℕ := 2 ^ (2 ^ mm₁ K j)

/-- The marched medium cutoff `Y = 2^{2^{mm}}`. -/
def Ym (K j : ℕ) : ℕ := 2 ^ (2 ^ mm K j)

/-- The marched outer scale `X = Y^{100}`. -/
def Xm (K j : ℕ) : ℕ := 2 ^ (100 * 2 ^ mm K j)

/-- The marched downward floor `Xlo = Y^{50}`. -/
def Xlom (K j : ℕ) : ℕ := 2 ^ (50 * 2 ^ mm K j)

/-- The marched moment order `Mc = 10⁵·T·mm₁`. -/
def Mcm (K j : ℕ) : ℕ := 100000 * T K * mm₁ K j

lemma mm_sub_mm₁ (K j : ℕ) : mm K j - mm₁ K j = m₂ K := by
  show (m₁ K + m₂ K) + j - (m₁ K + j) = m₂ K
  omega

lemma mm₁_le_mm (K j : ℕ) : mm₁ K j ≤ mm K j := by
  show m₁ K + j ≤ (m₁ K + m₂ K) + j
  omega

lemma mm_zero (K : ℕ) : mm K 0 = m K := by show m K + 0 = m K; omega
lemma mm₁_zero (K : ℕ) : mm₁ K 0 = m₁ K := by show m₁ K + 0 = m₁ K; omega
lemma Mcm_zero (K : ℕ) : Mcm K 0 = Mc K := by
  show 100000 * T K * mm₁ K 0 = 100000 * T K * m₁ K
  rw [mm₁_zero]

lemma Xm_zero (K : ℕ) : Xm K 0 = X K := by
  show (2 : ℕ) ^ (100 * 2 ^ mm K 0) = 2 ^ (100 * 2 ^ m K)
  rw [mm_zero]
lemma Ym_zero (K : ℕ) : Ym K 0 = Y K := by
  show (2 : ℕ) ^ (2 ^ mm K 0) = 2 ^ (2 ^ m K)
  rw [mm_zero]
lemma Rm_zero (K : ℕ) : Rm K 0 = R K := by
  show (2 : ℕ) ^ (2 ^ mm₁ K 0) = 2 ^ (2 ^ m₁ K)
  rw [mm₁_zero]

lemma Xlom_zero (K : ℕ) : Xlom K 0 = Xlo K := by
  show (2 : ℕ) ^ (50 * 2 ^ mm K 0) = (2 ^ (2 ^ m K)) ^ 50
  rw [mm_zero, ← pow_mul]
  ring_nf

/-- **The tiling identity.**  Marching `m₁` by one squares `Y`, so the next certified window
starts exactly where this one ends. -/
lemma Xlom_succ (K j : ℕ) : Xlom K (j + 1) = Xm K j := by
  show (2 : ℕ) ^ (50 * 2 ^ (m K + (j + 1))) = 2 ^ (100 * 2 ^ (m K + j))
  congr 1
  have h : (2 : ℕ) ^ (m K + (j + 1)) = 2 * 2 ^ (m K + j) := by
    rw [show m K + (j + 1) = (m K + j) + 1 by omega, pow_succ]; ring
  rw [h]; ring

lemma Xlom_le_Xm (K j : ℕ) : Xlom K j ≤ Xm K j :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### `jstar`: the march length that reaches the next rung's floor -/

lemma m₁_le_step {K : ℕ} (hK : 1 ≤ K) : m₁ K ≤ m₁ (K + 4) := by
  show 1000 * 8 ^ K * K ^ (2 * K + 1) ≤ 1000 * 8 ^ (K + 4) * (K + 4) ^ (2 * (K + 4) + 1)
  have hA : (8 : ℕ) ^ K ≤ 8 ^ (K + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB : K ^ (2 * K + 1) ≤ (K + 4) ^ (2 * (K + 4) + 1) :=
    le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) (by omega))
  exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl 1000) hA) hB

/-- `m K < m (K+4)`: the next rung's medium exponent is strictly larger. -/
lemma m_lt_step {K : ℕ} (hK : 1 ≤ K) : m K + 1 ≤ m (K + 4) := by
  have h1 := m₁_le_step hK
  have h2 : m₂ K + 1 ≤ m₂ (K + 4) := by
    show 8 * K ^ 2 + 1 ≤ 8 * (K + 4) ^ 2
    nlinarith
  show m₁ K + m₂ K + 1 ≤ m₁ (K + 4) + m₂ (K + 4)
  omega

/-- The march length at which rung `K`'s tower reaches rung `K+4`'s certificate floor. -/
def jstar (K : ℕ) : ℕ := m (K + 4) - m K - 1

lemma mm_jstar {K : ℕ} (hK : 1 ≤ K) : mm K (jstar K) + 1 = m (K + 4) := by
  have h := m_lt_step hK
  show m K + (m (K + 4) - m K - 1) + 1 = m (K + 4)
  omega

/-- **The march reaches the next rung exactly**: `Xm K (jstar K) = Xlo (K+4)`. -/
lemma Xm_jstar {K : ℕ} (hK : 1 ≤ K) : Xm K (jstar K) = Xlo (K + 4) := by
  have hj := mm_jstar hK
  have h : (2 : ℕ) ^ m (K + 4) = 2 * 2 ^ mm K (jstar K) := by
    conv_lhs => rw [← hj]
    rw [pow_succ]; ring
  have hexp : 100 * 2 ^ mm K (jstar K) = 2 ^ m (K + 4) * 50 := by rw [h]; ring
  show (2 : ℕ) ^ (100 * 2 ^ mm K (jstar K)) = (2 ^ (2 ^ m (K + 4))) ^ 50
  rw [← pow_mul, hexp]

lemma mm_le_of_le_jstar {K j : ℕ} (hK : 1 ≤ K) (hj : j ≤ jstar K) : mm K j ≤ m (K + 4) := by
  have h := mm_jstar hK
  have h2 : mm K j ≤ mm K (jstar K) := by
    show m K + j ≤ m K + jstar K
    omega
  omega

lemma mm₁_le_of_le_jstar {K j : ℕ} (hK : 1 ≤ K) (hj : j ≤ jstar K) : mm₁ K j ≤ m (K + 4) :=
  le_trans (mm₁_le_mm K j) (mm_le_of_le_jstar hK hj)

lemma Xlo_le_of_Xlom_le {K j X' : ℕ} (h : Xlom K j ≤ X') : Xlo K ≤ X' := by
  refine le_trans ?_ h
  rw [← Xlom_zero]
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul (le_refl 50) (Nat.pow_le_pow_right (by norm_num)
      (show mm K 0 ≤ mm K j by show m K + 0 ≤ m K + j; omega)))

/-! ### The two genuine upper constraints of the cone, on the whole march -/

/-- `m (K+4) ≤ 2^{3K² + 28K + 64}`. -/
lemma m_step_le_two_pow {K : ℕ} (hK : 100 ≤ K) : m (K + 4) ≤ 2 ^ (3 * K ^ 2 + 28 * K + 64) := by
  have h1 : m (K + 4) ≤ (K + 4) ^ (3 * (K + 4) + 4) := m_le (by omega)
  have h2 : (K + 4) ^ (3 * (K + 4) + 4) ≤ 2 ^ ((K + 4) * (3 * (K + 4) + 4)) :=
    pow_le_two_pow_mul _ _
  have h3 : (K + 4) * (3 * (K + 4) + 4) ≤ 3 * K ^ 2 + 28 * K + 64 := by nlinarith
  exact le_trans h1 (le_trans h2 (Nat.pow_le_pow_right (by norm_num) h3))

/-- **The small-prime budget survives the whole march.**  `Mcm K j ≤ 2^{m₂ K}` for every
`j ≤ jstar K`; the binding ladder inequality is `6K² + 31K + 81 ≤ 8K²`.
(`Sched.Mc_le_two_pow_m₂` is the `j = 0` case.) -/
theorem Mcm_le_two_pow_m₂ {K j : ℕ} (hK : 100 ≤ K) (hj : j ≤ jstar K) :
    Mcm K j ≤ 2 ^ m₂ K := by
  have hsq : 100 * K ≤ K ^ 2 := by nlinarith
  have hmm₁ : mm₁ K j ≤ m (K + 4) := mm₁_le_of_le_jstar (by omega) hj
  have hT : T K ≤ K ^ (3 * K + 3) := T_le hK
  have hT2 : K ^ (3 * K + 3) ≤ 2 ^ (K * (3 * K + 3)) := pow_le_two_pow_mul _ _
  have hT3 : T K ≤ 2 ^ (3 * K ^ 2 + 3 * K) := by
    refine le_trans hT (le_trans hT2 (Nat.pow_le_pow_right (by norm_num) ?_))
    nlinarith
  have hm := m_step_le_two_pow hK
  have h5 : (100000 : ℕ) ≤ 2 ^ 17 := by norm_num
  have hkey : (2 : ℕ) ^ 17 * 2 ^ (3 * K ^ 2 + 3 * K) * 2 ^ (3 * K ^ 2 + 28 * K + 64)
      = 2 ^ (6 * K ^ 2 + 31 * K + 81) := by
    rw [← pow_add, ← pow_add]; ring_nf
  have hexp : 6 * K ^ 2 + 31 * K + 81 ≤ 8 * K ^ 2 := by nlinarith
  show 100000 * T K * mm₁ K j ≤ 2 ^ (8 * K ^ 2)
  calc 100000 * T K * mm₁ K j
      ≤ 2 ^ 17 * 2 ^ (3 * K ^ 2 + 3 * K) * 2 ^ (3 * K ^ 2 + 28 * K + 64) :=
        Nat.mul_le_mul (Nat.mul_le_mul h5 hT3) (le_trans hmm₁ hm)
    _ = 2 ^ (6 * K ^ 2 + 31 * K + 81) := hkey
    _ ≤ 2 ^ (8 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp

/-- **The `hfar` ℕ inequality survives the whole march.**
(`Sched.four_mul_le_four_pow_N` is the `j = 0` case.) -/
theorem four_mul_le_four_pow_N_m {K j : ℕ} (hK : 100 ≤ K) (hj : j ≤ jstar K) :
    4 * K * (logP₀Nat K + mm K j + 2 * J K + 13) ≤ 4 ^ N K := by
  have hsq : 100 * K ≤ K ^ 2 := by nlinarith
  have hE : 20 * K ^ 2 + 17 * K = K * (20 * K + 17) := by ring
  have hP : logP₀Nat K ≤ 2 ^ (20 * K ^ 2 + 17 * K) := by
    refine le_trans (logP₀Nat_le hK) ?_
    rw [hE]; exact pow_le_two_pow_mul _ _
  have hM : mm K j ≤ 2 ^ (20 * K ^ 2 + 17 * K) := by
    refine le_trans (mm_le_of_le_jstar (by omega) hj) ?_
    refine le_trans (m_step_le_two_pow hK) (Nat.pow_le_pow_right (by norm_num) ?_)
    nlinarith
  have hJ2 : 2 * J K ≤ 2 ^ (20 * K ^ 2 + 17 * K) := by
    have h1 : J K ≤ K ^ 4 := J_le hK
    have h2 : K ^ 4 ≤ 2 ^ (K * 4) := pow_le_two_pow_mul _ _
    have h3 : 2 * (2 : ℕ) ^ (K * 4) = 2 ^ (K * 4 + 1) := by rw [pow_succ]; ring
    calc 2 * J K ≤ 2 * 2 ^ (K * 4) := Nat.mul_le_mul (le_refl 2) (le_trans h1 h2)
      _ = 2 ^ (K * 4 + 1) := h3
      _ ≤ 2 ^ (20 * K ^ 2 + 17 * K) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h13 : (13 : ℕ) ≤ 2 ^ (20 * K ^ 2 + 17 * K) := by
    calc (13 : ℕ) ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (20 * K ^ 2 + 17 * K) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hsum : logP₀Nat K + mm K j + 2 * J K + 13 ≤ 2 ^ (20 * K ^ 2 + 17 * K + 2) := by
    have h4 : (2 : ℕ) ^ (20 * K ^ 2 + 17 * K + 2) = 4 * 2 ^ (20 * K ^ 2 + 17 * K) := by
      rw [pow_add]; ring
    omega
  have h4K : 4 * K ≤ 2 ^ (K + 2) := by
    have hk : K ≤ 2 ^ K := (Nat.lt_two_pow_self).le
    have h4 : (2 : ℕ) ^ (K + 2) = 4 * 2 ^ K := by rw [pow_add]; ring
    omega
  have hD : (4 : ℕ) ^ N K = 2 ^ (200 * K ^ 2) := by
    show (4 : ℕ) ^ (100 * K ^ 2) = 2 ^ (200 * K ^ 2)
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  rw [hD]
  calc 4 * K * (logP₀Nat K + mm K j + 2 * J K + 13)
      ≤ 2 ^ (K + 2) * 2 ^ (20 * K ^ 2 + 17 * K + 2) := Nat.mul_le_mul h4K hsum
    _ = 2 ^ (20 * K ^ 2 + 18 * K + 4) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (200 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-! ### The covering lemma -/

/-- Every outer scale between `Xlom K 0` and `Xm K J` lies in one certified window of the
march.  This is `Xlom_succ` run `J` times. -/
lemma exists_tile_aux (K : ℕ) :
    ∀ (J X' : ℕ), Xlom K 0 ≤ X' → X' ≤ Xm K J →
      ∃ j, j ≤ J ∧ Xlom K j ≤ X' ∧ X' ≤ Xm K j := by
  intro J
  induction J with
  | zero => intro X' h0 h1; exact ⟨0, le_refl _, h0, h1⟩
  | succ J ih =>
      intro X' h0 h1
      by_cases hc : X' ≤ Xm K J
      · obtain ⟨j, hj, hj1, hj2⟩ := ih X' h0 hc
        exact ⟨j, by omega, hj1, hj2⟩
      · exact ⟨J + 1, le_refl _, by rw [Xlom_succ]; omega, h1⟩

/-- **The tiling.**  Every outer scale `X'` between rung `K`'s floor and rung `(K+4)`'s floor
sits in a certified window `[Xlom K j, Xm K j]` of the march, at some `j ≤ jstar K`.
This is exactly what `G4EntropyScaleGap.Xhi_lt_Xlo_step` says the *old* one-dimensional ladder
cannot do. -/
theorem exists_tile {K : ℕ} (hK : 100 ≤ K) {X' : ℕ}
    (hlo : Xlo K ≤ X') (hhi : X' ≤ Xlo (K + 4)) :
    ∃ j, j ≤ jstar K ∧ Xlom K j ≤ X' ∧ X' ≤ Xm K j :=
  exists_tile_aux K (jstar K) X' (by rw [Xlom_zero]; exact hlo)
    (by rw [Xm_jstar (show 1 ≤ K by omega)]; exact hhi)

/-! ### The endpoint: E1 at every outer scale up to the next rung's floor -/

end Sched

end NormalNumbers.G4
