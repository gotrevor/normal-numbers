/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerMultiplier

/-!
# `M(g,k) < g^(k+1)` — Berend–Boshernitzan's open question, answered 🧮

Berend and Boshernitzan (*On a result of Mahler on the decimal expansions of
(nα)*, Acta Arith. 66 (1994) 315–322, p. 320) prove `M(g,k) < 2g^(k+1)` and
write: *"We do not know whether it is true in general that `M(g,k) < g^(k+1)`."*

`MahlerMultiplier.lean` proves `m ≤ g^(k+1)`.  This file observes that the
same covering-lemma contraction survives at the budget `g^(k+1) − 1`
(`defect_contracts_of_bad_pred`), which gives the strict inequality:

    **for every irrational `α`, base `g ≥ 2`, and `k`-block `w`, some
    `1 ≤ m < g^(k+1)` has `w` infinitely often in `m·α`**
                                          (`mahler_multiplier_lt`),

i.e. `M(g,k) ≤ g^(k+1) − 1 < g^(k+1)` for all `g ≥ 2`, `k ≥ 1`.  Together with
their Theorem 3.2 (`M(g,k) ≥ (1 − ε)g^(k+1)` for large `k` when `g` is not a
prime power) this makes `g^(k+1)` the sharp order for every non-prime-power
base.

The arithmetic: with `Q = gᵏ` and `M = gQ − 1` the universal covering lemma
gives, for a bad orbit point and any reduced `p/q` with `q ≤ Q`,
`|qx − p| < g⁻ᵏ`,

    (gQ − 2q)·|qx − p| < 1 − q/Q.

If `g|qx − p| ≥ 1/Q` the left side is at least `(gQ − 2q)/(gQ) = 1 − 2q/(gQ)
≥ 1 − q/Q` (as `g ≥ 2`) — contradiction.  So every quality-`g⁻ᵏ`
approximation contracts to quality `g⁻ᵏ/g`, and `orbit_escapes` finishes
exactly as before.
-/

namespace NormalNumbers.Mahler

/-- **Contraction at `M = g^(k+1) − 1`.**  If the multiples `m x`,
`m ≤ g^(k+1) − 1`, all miss the cell, then every rational `ρ` with
`ρ.den ≤ gᵏ` and defect below `g⁻ᵏ` has defect below `g⁻ᵏ/g`. -/
theorem defect_contracts_of_bad_pred (g k W : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k)
    (x : ℝ) (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ g ^ (k + 1) - 1 →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (ρ : ℚ) (hden : ρ.den ≤ g ^ k)
    (hη : |(ρ.den : ℝ) * x - ρ.num| < 1 / (g : ℝ) ^ k) :
    (g : ℝ) * |(ρ.den : ℝ) * x - ρ.num| < 1 / (g : ℝ) ^ k := by
  have hcop : IsCoprime ρ.num (ρ.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact ρ.reduced
  have h := defect_bound_of_bad g k W hg hW (g ^ (k + 1) - 1) x hx hbad ρ.num ρ.den ρ.pos
    hden hcop hη
  set E : ℝ := |(ρ.den : ℝ) * x - ρ.num| with hEdef
  set Q : ℝ := (g : ℝ) ^ k with hQdef
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  have hQ0 : 0 < Q := by positivity
  have hq1 : (1 : ℝ) ≤ ρ.den := by exact_mod_cast ρ.pos
  have hqQ : (ρ.den : ℝ) ≤ Q := by rw [hQdef]; exact_mod_cast hden
  have hgk1 : 1 ≤ g ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have hM : ((g ^ (k + 1) - 1 : ℕ) : ℝ) = (g : ℝ) * Q - 1 := by
    rw [Nat.cast_sub hgk1, hQdef]; push_cast; ring
  rw [hM] at h
  have e2 : ((g : ℝ) * Q - 1 + 1 - 2 * ρ.den) * E = ((g : ℝ) * Q - 2 * ρ.den) * E := by ring
  rw [e2] at h
  by_contra hcon
  push Not at hcon
  have hgQ : (0 : ℝ) < (g : ℝ) * Q := by positivity
  have hE : 1 / ((g : ℝ) * Q) ≤ E := by
    rw [div_le_iff₀ hgQ]
    rw [div_le_iff₀ hQ0] at hcon
    linarith [show E * ((g : ℝ) * Q) = (g : ℝ) * E * Q by ring]
  have hP : 0 ≤ (g : ℝ) * Q - 2 * ρ.den := by nlinarith
  have h2 : ((g : ℝ) * Q - 2 * ρ.den) * (1 / ((g : ℝ) * Q))
      ≤ ((g : ℝ) * Q - 2 * ρ.den) * E := mul_le_mul_of_nonneg_left hE hP
  have e1 : ((g : ℝ) * Q - 2 * ρ.den) * (1 / ((g : ℝ) * Q))
      = 1 - 2 * ρ.den / ((g : ℝ) * Q) := by
    rw [mul_one_div, sub_div, div_self hgQ.ne']
  have h3 : 2 * (ρ.den : ℝ) / ((g : ℝ) * Q) ≤ ρ.den / Q := by
    rw [div_le_div_iff₀ hgQ hQ0]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ρ.den)
      (mul_nonneg (by linarith : (0 : ℝ) ≤ (g : ℝ) - 2) hQ0.le)]
  linarith

/-- **Mahler's multiplier theorem, strict form `m < g^(k+1)`.**  For every
irrational `α`, base `g ≥ 2`, and digit block `w` of length `k`, some
multiplier `1 ≤ m < g^(k+1)` has `w` occurring infinitely often in the
base-`g` expansion of `m·α`.  This answers Berend–Boshernitzan's question
(Acta Arith. 66 (1994), p. 320) whether `M(g,k) < g^(k+1)` holds in general:
it does. -/
theorem mahler_multiplier_lt (g : ℕ) (hg : 2 ≤ g) (α : ℝ) (hα : Irrational α)
    (w : List ℕ) (hwd : ∀ d ∈ w, d < g) :
    ∃ m : ℕ, 1 ≤ m ∧ m < g ^ (w.length + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  set k := w.length with hkdef
  set W := blockNatVal g w with hWdef
  have hW : W < g ^ k := blockNatVal_lt g w hwd
  set M := g ^ (k + 1) - 1 with hMdef
  have hgk1 : 1 ≤ g ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  by_contra hcon
  push Not at hcon
  choose! Nf hNf using hcon
  set N₀ := (Finset.range (M + 1)).sup Nf with hN₀def
  have hN₀ : ∀ m, m ≤ M → Nf m ≤ N₀ := fun m hm =>
    Finset.le_sup (f := Nf) (Finset.mem_range.2 (by omega))
  have hbad : ∀ n, N₀ ≤ n → ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * orbit g α n) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k) := by
    intro n hn m hm1 hmM hmem
    apply hNf m hm1 (by omega) n (le_trans (hN₀ m hmM) hn)
    rw [occursAt_iff_orbit_mem g hg _ w hwd n, orbit_nat_mul]
    exact hmem
  have hgk : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
  apply orbit_escapes g hg α hα (g ^ k) hgk N₀
  intro n hn ρ hden hsmall
  have hcastQ : ((g ^ k : ℕ) : ℝ) = (g : ℝ) ^ k := by push_cast; ring
  rw [hcastQ] at hsmall ⊢
  exact defect_contracts_of_bad_pred g k W hg hW (orbit g α n) (orbit_irrational g hg α hα n)
    (hbad n hn) ρ hden hsmall

end NormalNumbers.Mahler
