/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerLowerBound

/-!
# The Mahler multiplier bound: the lower side, `t·(gᵏ − 1)` (B–B 1994, Thm 3.1) 🧮

⚠️ **Attribution (2026-09-02, after the primary source was read).**  The bound
`M(g,k) ≥ a(gᵏ − 1)` for a proper divisor `a ∣ g` is **Berend–Boshernitzan
1994, Theorem 3.1** (Acta Arith. 66, p. 318), with the same witness
`α = (g/a)·Σⱼ g^(−nⱼ)`; `M(10,k) ≥ 8(10ᵏ − 1)` is their **Example 3.1**.
This file is a formalization of a known theorem, written before the paper
was available; the exposition below predates the attribution.

`MahlerLowerBound.lean` proves `M(g,k) ≥ gᵏ − 1` (the bound our secondary
sources attribute to Berend–Boshernitzan 1994) from the Liouville number
`Σ g^(−i!)`.  This file shows that construction is **far from optimal**:
multiplying the Liouville number by a fixed integer `B` gives

    M(g,k) ≥ min { m ≥ 1 : m·B contains `(g−1)ᵏ` in base g }

and choosing `B = g/t` for a divisor `t ∣ g` with `2t ≤ g` yields

    **M(g,k) ≥ t·(gᵏ − 1)**            (`mahler_lower_bound_divisor`)

for every such `t`; in particular, for every **even** base,

    **M(g,k) ≥ (g/2)·(gᵏ − 1)**        (`mahler_lower_bound_even`)

which, against `mahler_multiplier`'s `M(g,k) ≤ g^(k+1)`, pins the optimal
universal multiplier to within a factor `2 + o(1)`:

    (g/2)(gᵏ − 1)  ≤  M(g,k)  ≤  g^(k+1)      (`g` even).

Base 10, `k = 1`: `45 ≤ M(10,1) ≤ 100` from this file (and `≥ 72` from
`B = 125`, a witness of the same shape — see the numeric remark below),
against `9 ≤ M(10,1)` from the classical construction.

## Why the multiple works

Write `L = liouvilleNumber g = Σᵢ g^(−i!)` and take `α = B·L`.  Then
`m·α = (m B)·L`, so *every* multiplier question about `α` is a question
about the single integer `N = m B`: the base-`g` expansion of `N·L` is a
copy of the digit string of `N`, right-aligned at each position `i!`, with
long zero gaps in between.  A block of `k` consecutive `(g−1)`s can
therefore only occur inside one copy, i.e. iff `(g−1)ᵏ` occurs in `N`
itself.  Formally we never touch digits: `occursAt_iff_orbit_mem` turns
this into the orbit estimate `orbit_liouvilleMul_lt`, whose hypothesis is
the arithmetic shadow of "no `k` consecutive `(g−1)` digits":

    `∀ d ≥ k,  N % g^d + g^(d−k) + 1 ≤ g^d`.

(`N % g^d ≥ g^d − g^(d−k)` says exactly that digits `d−1, …, d−k` of `N`
are all `g−1`.)

## Why `B = g/t` beats `B = 1`

With `c = g/t ≥ 2` and `m = q t + s` (`0 ≤ s < t`) we get
`m·B = q·g + s·c` with `s·c ≤ g − c ≤ g − 2`: the *last* digit of `m B` is
never `g − 1`, so a run of `(g−1)`s must live in `q = ⌊m/t⌋`, and the
smallest integer containing `(g−1)ᵏ` is `gᵏ − 1`.  Hence every
`m < t(gᵏ − 1)` is defeated — the multiplier budget is stretched by the
factor `t`.  `t = 1` recovers `MahlerLowerBound.lean`.

## Numeric remark (not formalized)

An exhaustive search over `B ≤ 4·10⁵` for `g ≤ 12`, `k ≤ 2` finds the
optimum of `min{m : (g−1)ᵏ ⊆ m·B}` to be exactly `t(gᵏ − 1)` for the best
admissible `t` — where `t` may exceed the largest proper divisor of `g`
if the low-order block of `B` merely avoids *runs* of `(g−1)`s rather than
the digit `g−1` itself (`g = 10`: `B = 125`, `t = 8`, giving `72` and
`792` for `k = 1, 2`; `g = 6, k = 2`: `B = 243` gives `187 > 4·35`).  Only
the divisor family is formalized here.
-/

namespace NormalNumbers.Mahler

open LiouvilleNumber
open scoped Nat

/-- Real-arithmetic core of the `d ≥ k` branch: with `D = g^(d−k)`, `A = g^k`
(so `g^d = D·A`), a remainder `r ≤ D·A − D − 1` plus a tail `T < 1/(D·A)`
stays below `1 − 1/A`. -/
private theorem cell_bound_ge (A D r T : ℝ) (hA : 0 < A) (hD : 0 < D) (hr : 0 ≤ r)
    (hle : r + D + 1 ≤ D * A) (hT0 : 0 ≤ T) (hT : T < 1 / (D * A)) :
    r / (D * A) + T < 1 - 1 / A := by
  have hDA : 0 < D * A := mul_pos hD hA
  have hstep : r / (D * A) ≤ 1 - 1 / A - 1 / (D * A) := by
    rw [div_le_iff₀ hDA]
    have hid : (1 - 1 / A - 1 / (D * A)) * (D * A) = D * A - D - 1 := by field_simp
    rw [hid]; linarith
  linarith

/-- Real-arithmetic core of the `d < k` branch: with `Q = g^d ≤ P = g^(k−1)`,
a remainder `r ≤ Q − 1` plus a tail `T < 1/(P g²)` stays below `1 − 1/(P g)`,
because `1/(P g) + 1/(P g²) ≤ 1/P` once `g + 1 ≤ g²`. -/
private theorem cell_bound_lt (g P Q r T : ℝ) (hg : 2 ≤ g) (hP : 0 < P) (hQ : 0 < Q)
    (hQP : Q ≤ P) (hr : 0 ≤ r) (hle : r + 1 ≤ Q) (_hT0 : 0 ≤ T)
    (hT : T < 1 / (P * g * g)) :
    r / Q + T < 1 - 1 / (P * g) := by
  have hg0 : (0 : ℝ) < g := by linarith
  have hstep : r / Q ≤ 1 - 1 / Q := by
    rw [le_sub_iff_add_le, ← add_div, div_le_one hQ]; linarith
  have hPQ : 1 / P ≤ 1 / Q := one_div_le_one_div_of_le hQ hQP
  have hgg : (0 : ℝ) ≤ g * g - g - 1 := by nlinarith
  have hfin : (0 : ℝ) ≤ P * P * g * (g * g - g - 1) :=
    mul_nonneg (by positivity) hgg
  have hsum : 1 / (P * g) + 1 / (P * g * g) ≤ 1 / P := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hP]
    nlinarith [hfin]
  linarith

/-- **Core estimate.**  Let `N ≤ g^K` be a positive integer none of whose
base-`g` digit windows of length `k` is all-`(g−1)` (the hypothesis
`hmod`).  Then for `n ≥ (K+k+2)!` the `n`-th orbit point of `N·liouvilleNumber g`
stays below `1 − g⁻ᵏ`, i.e. the block `(g−1)ᵏ` never occurs that late. -/
theorem orbit_liouvilleMul_lt (g k K N : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (hN1 : 1 ≤ N) (hNK : N ≤ g ^ K)
    (hmod : ∀ d, k ≤ d → N % g ^ d + g ^ (d - k) + 1 ≤ g ^ d)
    (n : ℕ) (hn : (K + k + 2)! ≤ n) :
    orbit g ((N : ℝ) * liouvilleNumber g) n < 1 - 1 / (g : ℝ) ^ k := by
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg1 : (1 : ℝ) < g := by linarith
  have hg0 : (0 : ℝ) < g := by linarith
  have hgN : 0 < g := by omega
  -- the index `j` with `j! ≤ n < (j+1)!`
  have hex : ∃ j, n < (j + 1)! := ⟨n, by have := Nat.self_le_factorial (n + 1); omega⟩
  obtain ⟨j, hj1, hjmin⟩ : ∃ j, n < (j + 1)! ∧ ∀ i, i < j → ¬ n < (i + 1)! :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hjk : K + k + 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    have h1 : (j + 1)! ≤ (K + k + 2)! := Nat.factorial_le (by omega)
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
  set T : ℝ := (N : ℝ) * (g : ℝ) ^ n * R with hTdef
  have hgn : (0 : ℝ) < (g : ℝ) ^ n := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNg : (0 : ℝ) < (N : ℝ) * (g : ℝ) ^ n := mul_pos hN0 hgn
  have hT0 : 0 ≤ T := by positivity
  -- the tail is below `g^(-(d+k+1))`
  have hT : T < 1 / (g : ℝ) ^ (d + k + 1) := by
    have hNK' : (N : ℝ) ≤ (g : ℝ) ^ K := by exact_mod_cast hNK
    have hfac : 1 ≤ (j + 1)! := Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    have hexp : K + n + (d + k + 1) ≤ (j + 1)! * (j + 1) := by
      have h1 : K + k + 1 ≤ (j + 1)! * j := le_trans (by omega) (Nat.le_mul_of_pos_left j hfac)
      have h2 : (j + 1)! * (j + 1) = (j + 1)! * j + (j + 1)! := by ring
      omega
    have hpow : (g : ℝ) ^ K * (g : ℝ) ^ n * (g : ℝ) ^ (d + k + 1)
        ≤ ((g : ℝ) ^ (j + 1)!) ^ (j + 1) := by
      rw [← pow_add, ← pow_add, ← pow_mul]
      exact pow_le_pow_right₀ hg1.le (by omega)
    have hpos : (0 : ℝ) < ((g : ℝ) ^ (j + 1)!) ^ (j + 1) := by positivity
    calc T < (N : ℝ) * (g : ℝ) ^ n * (1 / ((g : ℝ) ^ (j + 1)!) ^ (j + 1)) :=
          mul_lt_mul_of_pos_left hRlt hNg
      _ ≤ (g : ℝ) ^ K * (g : ℝ) ^ n * (1 / ((g : ℝ) ^ (j + 1)!) ^ (j + 1)) := by gcongr
      _ ≤ 1 / (g : ℝ) ^ (d + k + 1) := by
          rw [mul_one_div, div_le_div_iff₀ hpos (by positivity), one_mul]
          exact hpow
  -- the integer part and the fractional remainder
  set r := N % g ^ d with hrdef
  have hr_lt : r < g ^ d := Nat.mod_lt _ (by positivity)
  have hdiv : g ^ d * (N / g ^ d) + r = N := Nat.div_add_mod _ _
  have hgd : (0 : ℝ) < (g : ℝ) ^ d := by positivity
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by positivity
  -- the decomposition `N L gⁿ = I + (r/g^d + T)`
  have e1 : (g : ℝ) ^ n = (g : ℝ) ^ (j !) * (g : ℝ) ^ (n - j !) := by
    rw [← pow_add, Nat.add_sub_cancel' hj0]
  have e2 : (g : ℝ) ^ (j + 1)! = (g : ℝ) ^ n * (g : ℝ) ^ d := by rw [hFn, pow_add]
  have e3 : (N : ℝ) = (g : ℝ) ^ d * ((N / g ^ d : ℕ) : ℝ) + r := by
    have := congrArg (fun t : ℕ => (t : ℝ)) hdiv
    push_cast at this
    linarith
  have h1 : (N : ℝ) * ((p : ℝ) / (g : ℝ) ^ (j !)) * (g : ℝ) ^ n
      = (N : ℝ) * p * (g : ℝ) ^ (n - j !) := by
    rw [e1]; field_simp
  have h2 : (N : ℝ) * (1 / (g : ℝ) ^ (j + 1)!) * (g : ℝ) ^ n = (N : ℝ) / (g : ℝ) ^ d := by
    rw [e2]; field_simp
  have h2' : (N : ℝ) / (g : ℝ) ^ d = ((N / g ^ d : ℕ) : ℝ) + (r : ℝ) / (g : ℝ) ^ d := by
    rw [e3]; field_simp
  have hI : (N : ℝ) * liouvilleNumber g * (g : ℝ) ^ n
      = ((N * p * g ^ (n - j !) + N / g ^ d : ℕ) : ℝ) + ((r : ℝ) / (g : ℝ) ^ d + T) := by
    calc (N : ℝ) * liouvilleNumber g * (g : ℝ) ^ n
        = (N : ℝ) * ((p : ℝ) / (g : ℝ) ^ (j !)) * (g : ℝ) ^ n
          + (N : ℝ) * (1 / (g : ℝ) ^ (j + 1)!) * (g : ℝ) ^ n
          + (N : ℝ) * (g : ℝ) ^ n * R := by rw [hL, hp]; ring
      _ = (N : ℝ) * p * (g : ℝ) ^ (n - j !)
          + (((N / g ^ d : ℕ) : ℝ) + (r : ℝ) / (g : ℝ) ^ d) + T := by rw [h1, h2, h2']
      _ = ((N * p * g ^ (n - j !) + N / g ^ d : ℕ) : ℝ)
          + ((r : ℝ) / (g : ℝ) ^ d + T) := by push_cast; ring
  -- the fractional part, bounded below `1 − g⁻ᵏ`
  have hmain : (r : ℝ) / (g : ℝ) ^ d + T < 1 - 1 / (g : ℝ) ^ k := by
    rcases le_or_gt k d with hkd | hdk
    · -- `d ≥ k`: the hypothesis gives `r ≤ g^d − g^(d−k) − 1`
      have hsplit : (g : ℝ) ^ d = (g : ℝ) ^ (d - k) * (g : ℝ) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hkd]
      have hrR : (r : ℝ) + (g : ℝ) ^ (d - k) + 1 ≤ (g : ℝ) ^ (d - k) * (g : ℝ) ^ k := by
        have h0 := hmod d hkd
        have h1 : ((r + g ^ (d - k) + 1 : ℕ) : ℝ) ≤ ((g ^ d : ℕ) : ℝ) := by exact_mod_cast h0
        push_cast at h1
        rw [← hsplit]; linarith
      have hTd : T < 1 / ((g : ℝ) ^ (d - k) * (g : ℝ) ^ k) := by
        rw [← hsplit]
        have hpow : (g : ℝ) ^ d ≤ (g : ℝ) ^ (d + k + 1) := pow_le_pow_right₀ hg1.le (by omega)
        have := one_div_le_one_div_of_le hgd hpow
        linarith
      have := cell_bound_ge ((g : ℝ) ^ k) ((g : ℝ) ^ (d - k)) r T hgk (by positivity)
        (by positivity) hrR hT0 hTd
      rw [hsplit]; exact this
    · -- `d < k`: `r ≤ g^d − 1` already suffices, the tail being `< g^(−k−1)`
      have hPk : (g : ℝ) ^ k = (g : ℝ) ^ (k - 1) * g := by
        rw [← pow_succ, Nat.sub_add_cancel hk]
      have hPk1 : (g : ℝ) ^ (d + k + 1) = (g : ℝ) ^ (k - 1) * g * g * (g : ℝ) ^ d := by
        have hexp : d + k + 1 = (k - 1) + 1 + 1 + d := by omega
        rw [hexp, pow_add, pow_succ, pow_succ]
      have hrR : (r : ℝ) + 1 ≤ (g : ℝ) ^ d := by
        have : r + 1 ≤ g ^ d := hr_lt
        exact_mod_cast this
      have hQP : (g : ℝ) ^ d ≤ (g : ℝ) ^ (k - 1) := pow_le_pow_right₀ hg1.le (by omega)
      have hTk : T < 1 / ((g : ℝ) ^ (k - 1) * g * g) := by
        have hd0 : (1 : ℝ) ≤ (g : ℝ) ^ d := one_le_pow₀ hg1.le
        have hX : (0 : ℝ) < (g : ℝ) ^ (k - 1) * g * g := by positivity
        have hb : (g : ℝ) ^ (k - 1) * g * g ≤ (g : ℝ) ^ (d + k + 1) := by
          rw [hPk1]
          nlinarith [mul_nonneg hX.le (sub_nonneg.2 hd0)]
        have := one_div_le_one_div_of_le hX hb
        linarith
      have := cell_bound_lt g ((g : ℝ) ^ (k - 1)) ((g : ℝ) ^ d) r T hgR (by positivity) hgd
        hQP (by positivity) hrR hT0 hTk
      rw [hPk]; exact this
  have hy0 : 0 ≤ (r : ℝ) / (g : ℝ) ^ d + T := by positivity
  have h1k : (0 : ℝ) < 1 / (g : ℝ) ^ k := by positivity
  have hy1 : (r : ℝ) / (g : ℝ) ^ d + T < 1 := by linarith
  rw [orbit, fract_eq_of_eq_int_add ((N * p * g ^ (n - j !) + N / g ^ d : ℕ) : ℤ)
    (by rw [Int.cast_natCast]; exact hI) hy0 hy1]
  linarith

/-- **The general lower bound.**  Fix `B ≥ 1` and a multiplier budget `M`.
If for every `1 ≤ m ≤ M` the integer `m·B` has no `k` consecutive `(g−1)`
digits (stated arithmetically: `m·B % g^d + g^(d−k) + 1 ≤ g^d` for all
`d ≥ k`), then `α = B · liouvilleNumber g` and `w = (g−1)ᵏ` witness that no
multiplier `1 ≤ m ≤ M` puts `w` infinitely often into `m·α`.  Hence
`M(g,k) > M`. -/
theorem mahler_lower_bound_general (g : ℕ) (hg : 2 ≤ g) (k : ℕ) (hk : 1 ≤ k)
    (B : ℕ) (hB : 1 ≤ B) (M K : ℕ) (hMK : M * B ≤ g ^ K)
    (havoid : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∀ d, k ≤ d → (m * B) % g ^ d + g ^ (d - k) + 1 ≤ g ^ d) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < g) ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ M →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) w n := by
  have hwd : ∀ d ∈ List.replicate k (g - 1), d < g := by
    intro d hd
    rw [List.mem_replicate] at hd
    omega
  refine ⟨(B : ℝ) * liouvilleNumber g, List.replicate k (g - 1),
    ((liouville_liouvilleNumber hg).irrational).natCast_mul (by omega),
    List.length_replicate .., hwd, ?_⟩
  intro m hm1 hmM
  refine ⟨(K + k + 2)!, fun n hn hocc => ?_⟩
  rw [occursAt_iff_orbit_mem g hg _ _ hwd n, List.length_replicate,
    blockNatVal_replicate_pred g k (by omega)] at hocc
  have hmul : (m : ℝ) * ((B : ℝ) * liouvilleNumber g) = ((m * B : ℕ) : ℝ) * liouvilleNumber g := by
    push_cast; ring
  rw [hmul] at hocc
  have hlt := orbit_liouvilleMul_lt g k K (m * B) hg hk
    (Nat.one_le_iff_ne_zero.2 (by positivity)) (le_trans (Nat.mul_le_mul_right B hmM) hMK)
    (havoid m hm1 hmM) n hn
  have hcast : ((g ^ k - 1 : ℕ) : ℝ) = (g : ℝ) ^ k - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]; push_cast; ring
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by positivity
  have hcell : ((g : ℝ) ^ k - 1) / (g : ℝ) ^ k = 1 - 1 / (g : ℝ) ^ k := by
    rw [sub_div, div_self hgk.ne']
  rw [hcast, hcell] at hocc
  exact absurd hocc.1 (not_le.2 hlt)

/-! ### The divisor construction

For a factorization `g = t·c` with `c ≥ 2`, the multiplier `B = c` defeats
every `m < t(gᵏ − 1)`: writing `m = q t + s` we get `m c = q g + s c` with
`s c ≤ g − c ≤ g − 2`, so the last base-`g` digit of `m c` is never `g − 1`
and a run of `k` of them must sit inside `q ≤ gᵏ − 2`. -/

/-- `m·c` splits as `e + q·g` with `q = ⌊m/t⌋ ≤ gᵏ − 2` and `e = (m % t)·c ≤ g − 2`. -/
theorem divisor_split (g t c k m : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hc : t * c = g) (hc2 : 2 ≤ c) (hmlt : m + 1 ≤ t * (g ^ k - 1)) :
    ∃ q e : ℕ, m * c = e + q * g ∧ e + 2 ≤ g ∧ q + 2 ≤ g ^ k := by
  have hgk1 : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
  obtain ⟨q, r, hqr, hr⟩ : ∃ q r : ℕ, m = t * q + r ∧ r < t :=
    ⟨m / t, m % t, (Nat.div_add_mod m t).symm, Nat.mod_lt _ (by omega)⟩
  refine ⟨q, r * c, ?_, ?_, ?_⟩
  · rw [← hc, hqr]; ring
  · have he : r * c + c ≤ g := by
      rw [← hc]
      calc r * c + c = (r + 1) * c := by ring
        _ ≤ t * c := Nat.mul_le_mul_right c (by omega)
    omega
  · have h2 : t * q < t * (g ^ k - 1) := by omega
    have h3 : q < g ^ k - 1 := lt_of_mul_lt_mul_left h2 (Nat.zero_le t)
    omega

/-- Size bound: `m·c ≤ g^(k+1) − g − 2` for every `m < t(gᵏ − 1)`. -/
theorem divisor_size (g t c k m : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hc : t * c = g) (hc2 : 2 ≤ c) (hmlt : m + 1 ≤ t * (g ^ k - 1)) :
    m * c + g + 2 ≤ g ^ (k + 1) := by
  obtain ⟨q, e, hmc, he2, hq2⟩ := divisor_split g t c k m hg hk ht hc hc2 hmlt
  have hps : g ^ (k + 1) = g ^ k * g := pow_succ g k
  have hqg : q * g ≤ (g ^ k - 2) * g := Nat.mul_le_mul_right g (by omega)
  have hsub : (g ^ k - 2) * g = g ^ k * g - 2 * g := by rw [Nat.sub_mul]
  have hgk2 : 2 * g ≤ g ^ k * g := Nat.mul_le_mul_right g (by omega)
  omega

/-- The arithmetic heart of the divisor construction: no `k` consecutive
`(g−1)` digits in `m·c`, for every `1 ≤ m < t(gᵏ − 1)`. -/
theorem avoid_of_divisor (g t c k m : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hc : t * c = g) (hc2 : 2 ≤ c) (hmlt : m + 1 ≤ t * (g ^ k - 1)) :
    ∀ d, k ≤ d → (m * c) % g ^ d + g ^ (d - k) + 1 ≤ g ^ d := by
  obtain ⟨q, e, hmc, he2, hq2⟩ := divisor_split g t c k m hg hk ht hc hc2 hmlt
  have hsize := divisor_size g t c k m hg hk ht hc hc2 hmlt
  have hg0 : 0 < g := by omega
  intro d hkd
  rcases eq_or_lt_of_le hkd with hdk | hdk
  · -- `d = k`: the last base-`g` digit of `m c` is `e ≤ g − 2`, never `g − 1`
    subst hdk
    simp only [Nat.sub_self, pow_zero]
    have hmodlt : (m * c) % g ^ k < g ^ k := Nat.mod_lt _ (by positivity)
    by_contra hcon
    have heq : (m * c) % g ^ k = g ^ k - 1 := by omega
    -- reduce mod `g`
    have hdvd : g ∣ g ^ k := dvd_pow_self g (by omega)
    have hred : (m * c) % g ^ k % g = (m * c) % g := Nat.mod_mod_of_dvd _ hdvd
    have hmg : (m * c) % g = e := by
      rw [hmc, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    -- but `(gᵏ − 1) % g = g − 1`
    have hA : 1 ≤ g ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
    have hAk : g ^ k = g * g ^ (k - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hk]
    have hgA : g ≤ g * g ^ (k - 1) := Nat.le_mul_of_pos_right g (by omega)
    have hms : g * (g ^ (k - 1) - 1) = g * g ^ (k - 1) - g := by
      rw [Nat.mul_sub, mul_one]
    have hrw : g ^ k - 1 = (g - 1) + g * (g ^ (k - 1) - 1) := by omega
    have hfin : (g ^ k - 1) % g = g - 1 := by
      rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [heq, hfin] at hred
    omega
  · -- `d ≥ k+1`: the size bound alone suffices
    have hkd1 : k + 1 ≤ d := hdk
    have hmclt : m * c < g ^ d := by
      have : g ^ (k + 1) ≤ g ^ d := Nat.pow_le_pow_right (by omega) hkd1
      omega
    rw [Nat.mod_eq_of_lt hmclt]
    rcases eq_or_lt_of_le hkd1 with hd1 | hd2
    · subst hd1
      simp only [Nat.add_sub_cancel_left, pow_one]
      omega
    · have h1 : g ^ (k + 1) ≤ g ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : g ^ (d - k) ≤ g ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : g ^ d = g ^ (d - 1) * g := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      have h4 : 2 * g ^ (d - 1) ≤ g ^ (d - 1) * g := by
        have := Nat.mul_le_mul_left (g ^ (d - 1)) hg
        omega
      omega

/-- **`M(g,k) ≥ t·(gᵏ − 1)` for every factorization `g = t·c` with `c ≥ 2`.**
There are an irrational `α` and a `k`-digit block `w` such that no multiplier
`1 ≤ m < t(gᵏ − 1)` has `w` occurring infinitely often in `m·α`.  Witnesses:
`α = c · liouvilleNumber g`, `w = (g−1)ᵏ`.  `t = 1` recovers
`mahler_lower_bound`; every factorization with `t > 1` beats it. -/
theorem mahler_lower_bound_divisor (g t c k : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hc : t * c = g) (hc2 : 2 ≤ c) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < g) ∧
      ∀ m : ℕ, 1 ≤ m → m + 1 ≤ t * (g ^ k - 1) →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) w n := by
  set M := t * (g ^ k - 1) - 1 with hMdef
  have hgk2 : 2 ≤ g ^ k := by
    calc 2 ≤ g := hg
      _ = g ^ 1 := (pow_one g).symm
      _ ≤ g ^ k := Nat.pow_le_pow_right (by omega) hk
  have hMpos : 1 ≤ t * (g ^ k - 1) := by
    have := Nat.mul_le_mul ht (show 1 ≤ g ^ k - 1 by omega)
    simpa using this
  have hMK : M * c ≤ g ^ (k + 1) := by
    have := divisor_size g t c k M hg hk ht hc hc2 (by omega)
    omega
  obtain ⟨α, w, hirr, hlen, hdig, hmain⟩ :=
    mahler_lower_bound_general g hg k hk c (by omega) M (k + 1) hMK
      (fun m hm1 hmM => avoid_of_divisor g t c k m hg hk ht hc hc2 (by omega))
  exact ⟨α, w, hirr, hlen, hdig, fun m hm1 hm2 => hmain m hm1 (by omega)⟩

/-- **`M(g,k) ≥ (g/2)·(gᵏ − 1)` for every even base.**  Against
`mahler_multiplier`'s `M(g,k) ≤ g^(k+1)` this pins the optimal universal
multiplier bound to within a factor `2 + o(1)`, and beats the classical
`gᵏ − 1` by the factor `g/2`. -/
theorem mahler_lower_bound_even (g k : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (hev : 2 ∣ g) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < g) ∧
      ∀ m : ℕ, 1 ≤ m → m + 1 ≤ (g / 2) * (g ^ k - 1) →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) w n := by
  obtain ⟨t, ht⟩ := hev
  have h2 : g / 2 = t := by omega
  rw [h2]
  exact mahler_lower_bound_divisor g t 2 k hg hk (by omega) (by omega) le_rfl

end NormalNumbers.Mahler
