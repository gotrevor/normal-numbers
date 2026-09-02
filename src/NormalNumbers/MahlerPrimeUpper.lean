/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerRunBranch
import NormalNumbers.MahlerLowerBound

/-!
# The prime-base upper bound, sharpened to `g^(k+1) − 2g + 3` 🧮

`MahlerMultiplier.lean` proves the universal `M(g,k) ≤ g^(k+1)` by a covering
argument whose binding constraint, for a rational shadow `p/q`, is

    M ≥ g^(k+1) − q(g − 2) − 1,

worst at the **smallest** admissible denominator `q`.  At `q = 1` this is
`g^(k+1) − g + 1`, and that is what forces the clean `g^(k+1)`.

But `q = 1` says exactly that the orbit point `x_n` is within `g^(−k)` of an
integer, i.e. that `α`'s expansion has a run of `k` zeros (or of `k` digits
`g − 1`) at position `n` — and `MahlerRunBranch.lean` already settles that
branch outright at `m ≤ gᵏ` for prime `g`.  So for prime `g` the covering
sweep may be run with `q ≥ 2`, giving

    **`M(g,k) ≤ g^(k+1) − 2g + 3`**   (`mahler_multiplier_prime`).

The saving is `2g − 3`; small, but it is the first strict improvement on the
`g^(k+1)` headline at any base, and it is exactly the constant the covering
method can deliver — `PENDING_WORK.md` records why `q ≥ 3` is *not* similarly
available (for `q ≥ 2` the natural modulus `q gᵏ` shares the factor `gᵏ` with
`⌊gᵏ x⌋`, so the coprimality that drives the `q = 1` exclusion fails).

## Structure

* `orbit_run_of_den_one` — a rational shadow of denominator `1` and defect
  `< g^(−k)` at `x_n` forces `0ᵏ` or `(g−1)ᵏ` to occur at `n`.
* `defect_contracts_of_bad_two` — the covering contraction at
  `M = g^(k+1) − 2g + 3`, under `2 ≤ ρ.den`.
* `mahler_multiplier_prime` — the three-way case split.
-/

namespace NormalNumbers.Mahler

open NormalNumbers

/-- **Denominator `1` means a run.**  If some integer `p` has
`|x_n − p| < g^(−k)` where `x_n = orbit g α n` and `k ≥ 1`, then the block
`0ᵏ` or the block `(g−1)ᵏ` occurs in `α` at position `n`. -/
theorem orbit_run_of_den_one (g k : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (α : ℝ) (n : ℕ)
    (p : ℤ) (hp : |orbit g α n - p| < 1 / (g : ℝ) ^ k) :
    OccursAt g α (List.replicate k 0) n ∨
      OccursAt g α (List.replicate k (g - 1)) n := by
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hgk : (2 : ℝ) ≤ (g : ℝ) ^ k := by
    have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
    have h2 : (2 : ℝ) ^ k ≤ (g : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hgR k
    linarith
  have hgk0 : (0 : ℝ) < (g : ℝ) ^ k := by linarith
  have hinv : 1 / (g : ℝ) ^ k ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hgk0 (by norm_num)]; linarith
  set x := orbit g α n with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef, orbit]; exact Int.fract_nonneg _
  have hx1 : x < 1 := by rw [hxdef, orbit]; exact Int.fract_lt_one _
  have habs := abs_lt.1 hp
  have hp01 : p = 0 ∨ p = 1 := by
    have h1 : (p : ℝ) < 3 / 2 := by linarith [habs.1, habs.2]
    have h2 : (-1 / 2 : ℝ) < p := by linarith [habs.1, habs.2]
    have h1'' : (p : ℝ) < 2 := by linarith
    have h1' : p < 2 := by exact_mod_cast h1''
    have h2' : (0 : ℤ) ≤ p := by
      by_contra hc
      push Not at hc
      have : (p : ℝ) ≤ -1 := by exact_mod_cast (by omega : p ≤ -1)
      linarith
    omega
  have hwd0 : ∀ d ∈ List.replicate k 0, d < g := by
    intro d hd; rw [List.mem_replicate] at hd; omega
  have hwdp : ∀ d ∈ List.replicate k (g - 1), d < g := by
    intro d hd; rw [List.mem_replicate] at hd; omega
  rcases hp01 with h | h
  · left
    rw [occursAt_iff_orbit_mem g hg _ _ hwd0 n, List.length_replicate,
      blockNatVal_replicate_zero]
    subst h
    rw [← hxdef]
    constructor
    · simpa using hx0
    · have hlt : x < 1 / (g : ℝ) ^ k := by push_cast at habs; linarith [habs.2]
      simpa using hlt
  · right
    rw [occursAt_iff_orbit_mem g hg _ _ hwdp n, List.length_replicate,
      blockNatVal_replicate_pred g k (by omega)]
    subst h
    have hone : (1 : ℕ) ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
    have hcast : ((g ^ k - 1 : ℕ) : ℝ) = (g : ℝ) ^ k - 1 := by
      rw [Nat.cast_sub hone]; push_cast; ring
    rw [hcast, ← hxdef]
    have hlow : (1 : ℝ) - 1 / (g : ℝ) ^ k < x := by push_cast at habs; linarith [habs.1]
    have hmul : (1 : ℝ) - (1 : ℝ) / (g : ℝ) ^ k = ((g : ℝ) ^ k - 1) / (g : ℝ) ^ k := by
      field_simp
    have htop : ((g : ℝ) ^ k - 1 + 1) / (g : ℝ) ^ k = 1 := by
      rw [sub_add_cancel, div_self (ne_of_gt hgk0)]
    rw [htop]
    exact ⟨le_of_lt (by rw [← hmul]; exact hlow), hx1⟩

/-- **The covering contraction with `q ≥ 2`.**  If the multiples `m x`,
`1 ≤ m ≤ g^(k+1) − 2g + 3`, all miss the cell of `W`, then every rational `ρ`
with `2 ≤ ρ.den ≤ gᵏ` and defect `< g^(−k)` has defect `< g^(−k)/g`. -/
theorem defect_contracts_of_bad_two (g k W : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (hW : W < g ^ k)
    (x : ℝ) (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ g ^ (k + 1) - 2 * g + 3 →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (ρ : ℚ) (hden2 : 2 ≤ ρ.den) (hden : ρ.den ≤ g ^ k)
    (hη : |(ρ.den : ℝ) * x - ρ.num| < 1 / (g : ℝ) ^ k) :
    (g : ℝ) * |(ρ.den : ℝ) * x - ρ.num| < 1 / (g : ℝ) ^ k := by
  have hcop : IsCoprime ρ.num (ρ.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact ρ.reduced
  have h := defect_bound_of_bad g k W hg hW (g ^ (k + 1) - 2 * g + 3) x hx hbad
    ρ.num ρ.den ρ.pos hden hcop hη
  set E : ℝ := |(ρ.den : ℝ) * x - ρ.num| with hEdef
  set Q : ℝ := (g : ℝ) ^ k with hQdef
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hQ2 : (2 : ℝ) ≤ Q := by
    rw [hQdef]
    have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
    have h2 : (2 : ℝ) ^ k ≤ (g : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hgR k
    linarith
  have hQ0 : 0 < Q := by linarith
  -- the natural-number bound casts cleanly
  have hnat : 2 * g ≤ g ^ (k + 1) := by
    calc 2 * g ≤ g * g := Nat.mul_le_mul_right g hg
      _ = g ^ 2 := by ring
      _ ≤ g ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hM : ((g ^ (k + 1) - 2 * g + 3 : ℕ) : ℝ) = (g : ℝ) * Q - 2 * g + 3 := by
    rw [Nat.cast_add, Nat.cast_sub hnat]
    push_cast
    rw [hQdef]
    ring
  rw [hM] at h
  have hq2 : (2 : ℝ) ≤ ρ.den := by exact_mod_cast hden2
  have hqQ : (ρ.den : ℝ) ≤ Q := by rw [hQdef]; exact_mod_cast hden
  by_contra hcon
  push Not at hcon
  -- `E ≥ 1/(gQ)`
  have hg0 : (0 : ℝ) < g := by linarith
  have hEge : 1 / ((g : ℝ) * Q) ≤ E := by
    have h1 : 1 ≤ (g : ℝ) * E * Q := by
      have h2 := mul_le_mul_of_nonneg_right hcon hQ0.le
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hQ0)] at h2
      linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [h1]
  -- the coefficient dominates `g(Q − q)`
  have hcoef : (g : ℝ) * (Q - ρ.den) ≤ (g : ℝ) * Q - 2 * g + 3 + 1 - 2 * ρ.den := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (g : ℝ) - 2)
      (by linarith : (0 : ℝ) ≤ (ρ.den : ℝ) - 2)]
  have hcoef0 : 0 ≤ (g : ℝ) * (Q - ρ.den) := by nlinarith
  have hfin : 1 - (ρ.den : ℝ) / Q ≤ ((g : ℝ) * Q - 2 * g + 3 + 1 - 2 * ρ.den) * E := by
    calc 1 - (ρ.den : ℝ) / Q = ((g : ℝ) * (Q - ρ.den)) * (1 / ((g : ℝ) * Q)) := by
          field_simp
      _ ≤ ((g : ℝ) * (Q - ρ.den)) * E := mul_le_mul_of_nonneg_left hEge hcoef0
      _ ≤ ((g : ℝ) * Q - 2 * g + 3 + 1 - 2 * ρ.den) * E := by
          apply mul_le_mul_of_nonneg_right hcoef
          rw [hEdef]; positivity
  linarith

/-- **`M(g,k) ≤ g^(k+1) − 2g + 3` for prime `g`.**  For every irrational `α`,
prime base `g`, and nonempty digit block `w` of length `k`, some multiplier
`1 ≤ m ≤ g^(k+1) − 2g + 3` has `w` occurring infinitely often in `m·α`.

The three cases: `0ᵏ` occurs infinitely often (run branch, `m ≤ gᵏ`);
`(g−1)ᵏ` does (run branch again); or neither does, and then past some `N₁`
every rational shadow of the orbit has denominator `≥ 2`, which is exactly
what the sharpened covering contraction needs. -/
theorem mahler_multiplier_prime (g : ℕ) (hgp : g.Prime) (α : ℝ) (hα : Irrational α)
    (w : List ℕ) (hwd : ∀ d ∈ w, d < g) (hk : 1 ≤ w.length) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ g ^ (w.length + 1) - 2 * g + 3 ∧
      ∀ N, ∃ n, N ≤ n ∧ OccursAt g ((m : ℝ) * α) w n := by
  have hg : 2 ≤ g := hgp.two_le
  set k := w.length with hkdef
  set W := blockNatVal g w with hWdef
  have hW : W < g ^ k := blockNatVal_lt g w hwd
  set M := g ^ (k + 1) - 2 * g + 3 with hMdef
  have hnat : 2 * g ≤ g ^ (k + 1) := by
    calc 2 * g ≤ g * g := Nat.mul_le_mul_right g hg
      _ = g ^ 2 := by ring
      _ ≤ g ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hgkM : g ^ k ≤ M := by
    have hA : g ^ (k + 1) = g ^ k * g := by ring
    have hgek : g ≤ g ^ k := Nat.le_self_pow (by omega) g
    have keyZ : (g : ℤ) ^ k * g + 3 ≥ (g : ℤ) ^ k + 2 * g := by
      have h1 : (g : ℤ) ≤ (g : ℤ) ^ k := by exact_mod_cast hgek
      have h2 : (2 : ℤ) ≤ g := by exact_mod_cast hg
      nlinarith
    have key : g ^ k * g + 3 ≥ g ^ k + 2 * g := by exact_mod_cast keyZ
    omega
  -- Case 1: the run branch at `0ᵏ`
  by_cases hz : ∀ N, ∃ n, N ≤ n ∧ OccursAt g α (List.replicate k 0) n
  · obtain ⟨m, hm1, hm2, hm3⟩ := mahler_multiplier_of_zero_runs g hgp α hα w hwd hk hz
    exact ⟨m, hm1, le_trans hm2 hgkM, hm3⟩
  -- Case 2: the run branch at `(g−1)ᵏ`
  by_cases hp : ∀ N, ∃ n, N ≤ n ∧ OccursAt g α (List.replicate k (g - 1)) n
  · obtain ⟨m, hm1, hm2, hm3⟩ := mahler_multiplier_of_pred_runs g hgp α hα w hwd hk hp
    exact ⟨m, hm1, le_trans hm2 hgkM, hm3⟩
  -- Case 3: no runs from some point on
  push Not at hz hp
  obtain ⟨N₁, hN₁⟩ := hz
  obtain ⟨N₂, hN₂⟩ := hp
  by_contra hcon
  push Not at hcon
  choose! Nf hNf using hcon
  set N₀ := max (max N₁ N₂) ((Finset.range (M + 1)).sup Nf) with hN₀def
  have hN₀ : ∀ m, m ≤ M → Nf m ≤ N₀ := fun m hm =>
    le_trans (Finset.le_sup (f := Nf) (Finset.mem_range.2 (by omega))) (le_max_right _ _)
  have hbad : ∀ n, N₀ ≤ n → ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * orbit g α n) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k) := by
    intro n hn m hm1 hmM hmem
    apply hNf m hm1 hmM n (le_trans (hN₀ m hmM) hn)
    rw [occursAt_iff_orbit_mem g hg _ w hwd n, orbit_nat_mul]
    exact hmem
  have hgk1 : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
  apply orbit_escapes g hg α hα (g ^ k) hgk1 N₀
  intro n hn ρ hden hsmall
  have hcastQ : ((g ^ k : ℕ) : ℝ) = (g : ℝ) ^ k := by push_cast; ring
  rw [hcastQ] at hsmall ⊢
  -- the denominator is at least `2`, else a run occurs at `n`
  have hden2 : 2 ≤ ρ.den := by
    by_contra hc
    push Not at hc
    have hd1 : ρ.den = 1 := by have := ρ.pos; omega
    have hdef : |orbit g α n - ρ.num| < 1 / (g : ℝ) ^ k := by
      have : ((ρ.den : ℝ)) = 1 := by rw [hd1]; norm_num
      rw [this, one_mul] at hsmall
      exact hsmall
    rcases orbit_run_of_den_one g k hg hk α n ρ.num hdef with h | h
    · exact hN₁ n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn) h
    · exact hN₂ n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn) h
  exact defect_contracts_of_bad_two g k W hg hk hW (orbit g α n)
    (orbit_irrational g hg α hα n) (hbad n hn) ρ hden2 hden hsmall

end NormalNumbers.Mahler
