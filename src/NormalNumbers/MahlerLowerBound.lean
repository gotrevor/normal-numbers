/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerMultiplier
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# The Mahler multiplier bound cannot go below `gᵏ − 1` 🧮

**Theorem** (`mahler_lower_bound`).  For every base `g ≥ 2` and block length
`k` there are an irrational `α` and a block `w` of `k` base-`g` digits such
that **no** multiplier `1 ≤ m ≤ gᵏ − 2` has `w` occurring infinitely often
in `m·α`.  Together with `mahler_multiplier` (`m ≤ g^(k+1)` always works)
this pins the optimal universal multiplier bound `M(g,k)` to
`gᵏ − 1 ≤ M(g,k) ≤ g^(k+1)`, both sides machine-checked.

⚠️ **Superseded on the lower side for composite bases**:
`MahlerLowerBoundGeneral.lean` multiplies the same Liouville number by a
fixed integer and gets `M(g,k) ≥ t·(gᵏ − 1)` for every factorization
`g = t·c` with `c ≥ 2` — a factor `t` better than this file, and
`(g/2)(gᵏ − 1)` for every even base.  This file is the `t = 1` case, kept
because it is the shortest self-contained statement of the bound.

Berend–Boshernitzan 1994 are reported (secondary sources, see
`Literature.lean`) to show the bound cannot beat `gᵏ − 1`; the exact
quantifier structure of their statement is not held, so this file states and
proves *our own* construction rather than transcribing theirs.

## The construction

`α = liouvilleNumber g = Σᵢ g^(−i!)` (irrational by mathlib's
`liouville_liouvilleNumber`), `w = (g−1)ᵏ`.  For `m ≤ gᵏ − 2`, the base-`g`
expansion of `m·α` is a copy of the `k`-digit string of `m` at each position
`i!`, separated by long runs of zeros — so the all-`(g−1)` block never
appears once the gaps exceed `k`.  Formally we never touch digits: by
`occursAt_iff_orbit_mem` it suffices that the orbit point `{m α gⁿ}` stays
below `1 − g⁻ᵏ` for `n ≥ (k+2)!`.  With `j! ≤ n < (j+1)!` and
`d = (j+1)! − n ≥ 1`,
`m α gⁿ = (integer) + (m mod g^d)/g^d + T` where the tail
`T = m gⁿ · remainder g (j+1) < g^(−k−1)`, and `(m mod g^d)/g^d ≤ 1 − 2g⁻ᵏ`
in both regimes `d ≥ k` (use `m ≤ gᵏ − 2`) and `d < k` (use
`m mod g^d ≤ g^d − 1`).
-/

namespace NormalNumbers.Mahler

open LiouvilleNumber
open scoped Nat

/-- The all-`(g−1)` block of length `k` has value `gᵏ − 1`. -/
theorem blockNatVal_replicate_pred (g k : ℕ) (hg : 1 ≤ g) :
    blockNatVal g (List.replicate k (g - 1)) = g ^ k - 1 := by
  induction k with
  | zero => simp [blockNatVal]
  | succ k ih =>
      rw [List.replicate_succ, blockNatVal_cons, List.length_replicate, ih]
      have h1 : 1 ≤ g ^ k := Nat.one_le_pow _ _ hg
      have h2 : 1 ≤ g ^ (k + 1) := Nat.one_le_pow _ _ hg
      zify [h1, h2, hg]
      ring

/-- For `1 ≤ m ≤ gᵏ − 2` and `n ≥ (k+2)!`, the `n`-th orbit point of
`m · liouvilleNumber g` lies below `1 − g⁻ᵏ`. -/
theorem orbit_liouville_lt (g : ℕ) (hg : 2 ≤ g) (k m : ℕ) (hm1 : 1 ≤ m)
    (hm2 : m + 2 ≤ g ^ k) (n : ℕ) (hn : (k + 2)! ≤ n) :
    orbit g ((m : ℝ) * liouvilleNumber g) n < 1 - 1 / (g : ℝ) ^ k := by
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg1 : (1 : ℝ) < g := by linarith
  have hg0 : (0 : ℝ) < g := by linarith
  have hgN : 0 < g := by omega
  have hk1 : 1 ≤ k := by
    by_contra h0
    push Not at h0
    have : k = 0 := by omega
    subst this
    rw [pow_zero] at hm2
    omega
  -- the index `j` with `j! ≤ n < (j+1)!`
  have hex : ∃ j, n < (j + 1)! := ⟨n, by have := Nat.self_le_factorial (n + 1); omega⟩
  obtain ⟨j, hj1, hjmin⟩ : ∃ j, n < (j + 1)! ∧ ∀ i, i < j → ¬ n < (i + 1)! :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hjk : k + 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    have h1 : (j + 1)! ≤ (k + 2)! := Nat.factorial_le (by omega)
    omega
  have hj0 : j ! ≤ n := by
    have := hjmin (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at this
    omega
  obtain ⟨d, hd1, hFn⟩ : ∃ d, 1 ≤ d ∧ (j + 1)! = n + d := ⟨(j + 1)! - n, by omega, by omega⟩
  -- split `L = partialSum + g^{-(j+1)!} + remainder (j+1)`
  obtain ⟨p, hp₀⟩ := partialSum_eq_rat hgN j
  have hp : partialSum (g : ℝ) j = (p : ℝ) / (g : ℝ) ^ (j !) := by
    rw [hp₀]; push_cast; ring
  have hL : liouvilleNumber (g : ℝ)
      = partialSum g j + 1 / (g : ℝ) ^ (j + 1)! + remainder g (j + 1) := by
    have h1 := partialSum_add_remainder hg1 j
    have h2 := partialSum_add_remainder hg1 (j + 1)
    rw [partialSum_succ] at h2
    linarith
  set R : ℝ := remainder (g : ℝ) (j + 1) with hRdef
  have hRpos : 0 < R := remainder_pos hg1 (j + 1)
  have hRlt : R < 1 / ((g : ℝ) ^ (j + 1)!) ^ (j + 1) := remainder_lt (j + 1) hgR
  set T : ℝ := (m : ℝ) * (g : ℝ) ^ n * R with hTdef
  have hgn : (0 : ℝ) < (g : ℝ) ^ n := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmg : (0 : ℝ) < (m : ℝ) * (g : ℝ) ^ n := mul_pos hm0 hgn
  have hT0 : 0 ≤ T := by positivity
  -- the tail is below `g^(-k-1)`
  have hT : T < 1 / (g : ℝ) ^ (k + 1) := by
    have hmk : (m : ℝ) ≤ (g : ℝ) ^ k := by exact_mod_cast (by omega : m ≤ g ^ k)
    have hexp : n + 2 * k + 1 ≤ (j + 1)! * (j + 1) := by
      have h1 : k + 3 ≤ (j + 1)! := le_trans (by omega) (Nat.self_le_factorial (j + 1))
      have h2 : (k + 3) * (k + 2) ≤ (j + 1)! * j := Nat.mul_le_mul h1 hjk
      have h3 : (j + 1)! * (j + 1) = (j + 1)! * j + (j + 1)! := by ring
      nlinarith [sq_nonneg k]
    have hpow : (g : ℝ) ^ k * (g : ℝ) ^ n * (g : ℝ) ^ (k + 1)
        ≤ ((g : ℝ) ^ (j + 1)!) ^ (j + 1) := by
      rw [← pow_add, ← pow_add, ← pow_mul]
      exact pow_le_pow_right₀ hg1.le (by omega)
    have hpos : (0 : ℝ) < ((g : ℝ) ^ (j + 1)!) ^ (j + 1) := by positivity
    calc T < (m : ℝ) * (g : ℝ) ^ n * (1 / ((g : ℝ) ^ (j + 1)!) ^ (j + 1)) :=
          mul_lt_mul_of_pos_left hRlt hmg
      _ ≤ (g : ℝ) ^ k * (g : ℝ) ^ n * (1 / ((g : ℝ) ^ (j + 1)!) ^ (j + 1)) := by gcongr
      _ ≤ 1 / (g : ℝ) ^ (k + 1) := by
          rw [mul_one_div, div_le_div_iff₀ hpos (by positivity), one_mul]
          exact hpow
  -- the integer part and the fractional remainder
  set r := m % g ^ d with hrdef
  have hr_lt : r < g ^ d := Nat.mod_lt _ (by positivity)
  have hr_le : r ≤ m := Nat.mod_le _ _
  have hdiv : g ^ d * (m / g ^ d) + r = m := Nat.div_add_mod _ _
  have hgd : (0 : ℝ) < (g : ℝ) ^ d := by positivity
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by positivity
  -- the decomposition `m L gⁿ = I + (r/g^d + T)`
  have e1 : (g : ℝ) ^ n = (g : ℝ) ^ (j !) * (g : ℝ) ^ (n - j !) := by
    rw [← pow_add, Nat.add_sub_cancel' hj0]
  have e2 : (g : ℝ) ^ (j + 1)! = (g : ℝ) ^ n * (g : ℝ) ^ d := by rw [hFn, pow_add]
  have e3 : (m : ℝ) = (g : ℝ) ^ d * ((m / g ^ d : ℕ) : ℝ) + r := by
    have := congrArg (fun t : ℕ => (t : ℝ)) hdiv
    push_cast at this
    linarith
  have h1 : (m : ℝ) * ((p : ℝ) / (g : ℝ) ^ (j !)) * (g : ℝ) ^ n
      = (m : ℝ) * p * (g : ℝ) ^ (n - j !) := by
    rw [e1]; field_simp
  have h2 : (m : ℝ) * (1 / (g : ℝ) ^ (j + 1)!) * (g : ℝ) ^ n = (m : ℝ) / (g : ℝ) ^ d := by
    rw [e2]; field_simp
  have h2' : (m : ℝ) / (g : ℝ) ^ d = ((m / g ^ d : ℕ) : ℝ) + (r : ℝ) / (g : ℝ) ^ d := by
    rw [e3]; field_simp
  have hI : (m : ℝ) * liouvilleNumber g * (g : ℝ) ^ n
      = ((m * p * g ^ (n - j !) + m / g ^ d : ℕ) : ℝ) + ((r : ℝ) / (g : ℝ) ^ d + T) := by
    calc (m : ℝ) * liouvilleNumber g * (g : ℝ) ^ n
        = (m : ℝ) * ((p : ℝ) / (g : ℝ) ^ (j !)) * (g : ℝ) ^ n
          + (m : ℝ) * (1 / (g : ℝ) ^ (j + 1)!) * (g : ℝ) ^ n
          + (m : ℝ) * (g : ℝ) ^ n * R := by rw [hL, hp]; ring
      _ = (m : ℝ) * p * (g : ℝ) ^ (n - j !)
          + (((m / g ^ d : ℕ) : ℝ) + (r : ℝ) / (g : ℝ) ^ d) + T := by rw [h1, h2, h2']
      _ = ((m * p * g ^ (n - j !) + m / g ^ d : ℕ) : ℝ)
          + ((r : ℝ) / (g : ℝ) ^ d + T) := by push_cast; ring
  -- bounding the fractional remainder
  have hr_bound : (r : ℝ) / (g : ℝ) ^ d ≤ 1 - 2 / (g : ℝ) ^ k := by
    rcases le_or_gt k d with hkd | hdk
    · have hgkd : (g : ℝ) ^ k ≤ (g : ℝ) ^ d := pow_le_pow_right₀ hg1.le hkd
      have hrm : (r : ℝ) + 2 ≤ (g : ℝ) ^ k := by
        have : r + 2 ≤ g ^ k := by omega
        exact_mod_cast this
      calc (r : ℝ) / (g : ℝ) ^ d ≤ r / (g : ℝ) ^ k :=
            div_le_div_of_nonneg_left (by positivity) hgk hgkd
        _ ≤ ((g : ℝ) ^ k - 2) / (g : ℝ) ^ k := by gcongr; linarith
        _ = 1 - 2 / (g : ℝ) ^ k := by rw [sub_div, div_self hgk.ne']
    · have hgd' : (g : ℝ) ^ d ≤ (g : ℝ) ^ (k - 1) := pow_le_pow_right₀ hg1.le (by omega)
      have hr1 : (r : ℝ) + 1 ≤ (g : ℝ) ^ d := by
        have : r + 1 ≤ g ^ d := hr_lt
        exact_mod_cast this
      have hgk1 : (g : ℝ) ^ k = (g : ℝ) ^ (k - 1) * g := by
        rw [← pow_succ, Nat.sub_add_cancel hk1]
      have hgk1' : (0 : ℝ) < (g : ℝ) ^ (k - 1) := by positivity
      have hA : 2 / (g : ℝ) ^ k ≤ 1 / (g : ℝ) ^ (k - 1) := by
        rw [hgk1, div_le_div_iff₀ (by positivity) hgk1', one_mul]
        nlinarith
      have hB : 1 / (g : ℝ) ^ (k - 1) ≤ 1 / (g : ℝ) ^ d :=
        one_div_le_one_div_of_le hgd hgd'
      have hC : (r : ℝ) / (g : ℝ) ^ d ≤ 1 - 1 / (g : ℝ) ^ d := by
        rw [le_sub_iff_add_le, ← add_div, div_le_one hgd]; linarith
      linarith
  have hTk : 1 / (g : ℝ) ^ (k + 1) ≤ 1 / (g : ℝ) ^ k :=
    one_div_le_one_div_of_le hgk (pow_le_pow_right₀ hg1.le (by omega))
  have h1k : (0 : ℝ) < 1 / (g : ℝ) ^ k := by positivity
  have h2k : (2 : ℝ) / (g : ℝ) ^ k = 2 * (1 / (g : ℝ) ^ k) := by ring
  have hy0 : 0 ≤ (r : ℝ) / (g : ℝ) ^ d + T := by positivity
  have hy1 : (r : ℝ) / (g : ℝ) ^ d + T < 1 := by linarith
  rw [orbit, fract_eq_of_eq_int_add ((m * p * g ^ (n - j !) + m / g ^ d : ℕ) : ℤ)
    (by rw [Int.cast_natCast]; exact hI) hy0 hy1]
  linarith

/-- **The Mahler multiplier bound cannot go below `gᵏ − 1`.**  For every base
`g ≥ 2` and block length `k` there are an irrational `α` and a block `w` of
`k` digits such that no multiplier `1 ≤ m ≤ gᵏ − 2` has `w` occurring
infinitely often in `m·α`: `w` occurs at no position `n ≥ (k+2)!` at all.
Witnesses: `α = liouvilleNumber g`, `w = (g−1)ᵏ`.  (Paired with
`mahler_multiplier`: `gᵏ − 1 ≤ M(g,k) ≤ g^(k+1)`.) -/
theorem mahler_lower_bound (g : ℕ) (hg : 2 ≤ g) (k : ℕ) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < g) ∧
      ∀ m : ℕ, 1 ≤ m → m + 2 ≤ g ^ k →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) w n := by
  have hwd : ∀ d ∈ List.replicate k (g - 1), d < g := by
    intro d hd
    rw [List.mem_replicate] at hd
    omega
  refine ⟨liouvilleNumber g, List.replicate k (g - 1),
    (liouville_liouvilleNumber hg).irrational, List.length_replicate .., hwd, ?_⟩
  intro m hm1 hm2
  refine ⟨(k + 2)!, fun n hn hocc => ?_⟩
  rw [occursAt_iff_orbit_mem g hg _ _ hwd n, List.length_replicate,
    blockNatVal_replicate_pred g k (by omega)] at hocc
  have hlt := orbit_liouville_lt g hg k m hm1 hm2 n hn
  have hcast : ((g ^ k - 1 : ℕ) : ℝ) = (g : ℝ) ^ k - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]; push_cast; ring
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by positivity
  have hcell : ((g : ℝ) ^ k - 1) / (g : ℝ) ^ k = 1 - 1 / (g : ℝ) ^ k := by
    rw [sub_div, div_self hgk.ne']
  rw [hcast, hcell] at hocc
  exact absurd hocc.1 (not_le.2 hlt)

end NormalNumbers.Mahler
