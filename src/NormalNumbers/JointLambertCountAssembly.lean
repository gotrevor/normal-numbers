/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertCountRate
import NormalNumbers.JointLambertRescaledTail

/-!
# The counting analogue of the joint small-tail theorem

`exists_joint_small_tail_all_bases_rescaled` produces **one** offset carrying the prescribed
divisor data and a small base tail in every base.  The count needs a whole `Finset` of such
offsets inside `[0, N)`, of cardinality at least `N exp(-C (log log N)² log log log N)`.

`exists_joint_small_tail_count` is exactly that statement, in the offset convention of
`jointWordCount` (data at `m + 1`, so `m` is the offset and the first requested digit is
`m + 1`).  It is the *only* remaining hole in the ratified headlines: given it,
`jointWords_quantitative` follows by `floor_digit_of_common_offset` plus
`jointWordCount_ge_of_subset`, with no further estimate.

## Content locator for the hole

The proof is §§3–5 of `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md`.  Every *estimate* it needs
is already proved and `#print axioms`-clean; what is missing is the arithmetic wiring:

1. **Height and pool.**  `k = countK X`, `L = k³`.  Take `P` from
   `exists_candidate_indices_every_height c`, then the allocation primes in `(L, 2L)` from
   `exists_prime_allocation_small_pool` avoiding `P`, then `R, A, B, Q` from
   `exists_joint_progression`.  `jointB_le` at `L := k³` gives
   `B ≤ (2k³)^(1 + c · killPoolSize k r) ≤ (2k³)^(1 + c k²)` via `killPoolSize_le_sq`, which
   is the hypothesis `exists_candidate_indices_every_height` wants.
2. **Candidates.**  `M = ⌊X/B⌋ + 1`; at least `M/(4 log X)` indices `m < M` have `u + mB`
   prime and `≤ X`.  That index set is the `Finset` the Markov step filters.
3. **Tail.**  `three_range_tail_le` with `Y = 2QX`, `J = ⌊(log₂ X)²⌋`, `H = ⌈√Y⌉`.  The
   resulting cost, divided by `M/(4 log X)`, is bounded by
   `eventually_near_cost_small` and `eventually_middle_cost_small` (the far term is
   `(2Y + 2J + 2)2^{-J}`, negligible since `2^J = X^{log₂ X}`).  Needs `k < L < J`
   eventually, and `jointA_tau_le` for `τ(A)`.
4. **Markov.**  `card_good_ge_half` at the fixed threshold `2δ`.  The surviving indices map
   injectively to offsets `Q p - r - 1` (injective because `A > 0`).
5. **All `N`.**  `k_N = countK N`, `D_N = 2(2k_N³)^(a-1)`, `X = ⌊N/D_N⌋`; `eventually_rate_le`
   converts `X/(8 B log X)` into `N exp(-C (log log N)² log log log N)`.

No step above is believed to be blocked; the remaining work is bookkeeping of floors and of
the `Finset` images, not a new estimate.
-/

namespace NormalNumbers.JointLambert

open Finset Filter NormalNumbers.SwingC2


/-! ### Monotonicity of the height schedule

The all-`N` transfer of §5 applies the chosen-height theorem at `X = ⌊N/D_N⌋ ≤ N` and needs
`k_X ≤ k_N`, i.e. `countK` monotone.  It is, and elementarily so. -/

/-- `Real.log` is monotone along `ℕ`, including at `0` (where it is `0` and the right side is
nonnegative). -/
theorem log_natCast_mono {X Y : ℕ} (h : X ≤ Y) : Real.log (X : ℝ) ≤ Real.log (Y : ℝ) := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simpa using Real.log_natCast_nonneg Y
  · have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    exact Real.log_le_log hX0 (by exact_mod_cast h)

/-- **`countK` is monotone above the threshold `log X ≥ 1`.**  `k_X ≤ k_N` whenever
`X ≤ N` and `log X ≥ 1`.

The hypothesis is not decorative: `Real.log` is *not* monotone through `0`, so for tiny `X`
with `log X < 1` the inner `log (log X)` can decrease.  The transfer only ever uses the
inequality at large `X`, where it holds. -/
theorem countK_le_countK {X Y : ℕ} (hX : 1 ≤ Real.log (X : ℝ)) (h : X ≤ Y) :
    countK X ≤ countK Y := by
  refine Nat.ceil_le_ceil ?_
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := log_natCast_mono h
  have hinner : Real.log (Real.log (X : ℝ)) ≤ Real.log (Real.log (Y : ℝ)) :=
    Real.log_le_log (by linarith) hlog
  rw [Real.logb, Real.logb]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hinner hl2.le) (by norm_num)

/-- **The chosen-height good-offset theorem** (§§3–4).  At every sufficiently large
caller-chosen height `X` the CRT construction produces a modulus `B` in the small-pool range,
a step `D` bounding the rescaling `2Q`, and a `Finset` of at least `X/(8 B log X)` *starts*
`n < D·X`, each carrying the prescribed divisor data at `n` and a base tail below `ε/2` in
every base `b ≥ 2`.

This is steps 1–4 of the module docstring: pool and CRT, candidate count, three-range tail,
Markov.  `exists_joint_small_tail_count` is its §5 transfer to every `N`, using
`countK_le_countK` and `eventually_rate_le`.

TODO(assembly): the five inputs are `exists_candidate_indices_every_height`,
`exists_prime_allocation_small_pool`, `exists_joint_progression`, `three_range_tail_le`
(with `jointA_tau_le`, `eventually_near_cost_small`, `eventually_middle_cost_small`) and
`card_good_ge_half`. -/
theorem exists_good_starts_at_height {c a r : ℕ} (hc : 2 ≤ c) (ha : 2 ≤ a) (hr : 1 ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      ∃ B D : ℕ, r < countK X ∧ 0 < B ∧ 0 < D ∧
        B ≤ (2 * (countK X) ^ 3) ^ (1 + c * (countK X) ^ 2) ∧
        D ≤ 2 * (2 * (countK X) ^ 3) ^ (a - 1) ∧
        ∃ T : Finset ℕ,
          (X : ℝ) / (8 * (B : ℝ) * Real.log (X : ℝ)) ≤ (T.card : ℝ) ∧
          (∀ n ∈ T, 1 ≤ n ∧ n < D * X) ∧
          (∀ n ∈ T, ∀ j, j < countK X → j ≠ r → c ^ (j + 1) ∣ tau (n + j)) ∧
          (∀ n ∈ T, tau (n + r) = 2 * a) ∧
          (∀ n ∈ T, ∀ b : ℕ, 2 ≤ b →
            0 ≤ ∑' t : ℕ, (tau (n + countK X + t) : ℝ) / (b : ℝ) ^ (countK X + t + 1) ∧
            ∑' t : ℕ, (tau (n + countK X + t) : ℝ) / (b : ℝ) ^ (countK X + t + 1)
              < ε / 2) := by
  sorry

/-! ### The §5 all-`N` transfer: the height schedule `X = ⌊N/D_N⌋` -/

/-- The rescaling step of §5: `D_N = 2(2k_N³)^(a-1)`, an upper bound for `2Q`. -/
noncomputable def countD (a X : ℕ) : ℕ := 2 * (2 * (countK X) ^ 3) ^ (a - 1)

/-- `D_N > 0`.  The hypothesis `1 ≤ countK X` is needed, not cosmetic: at `countK X = 0`
and `a > 1` the product `2·(2·0³)^(a-1)` is `0`. -/
theorem countD_pos {a X : ℕ} (hk : 1 ≤ countK X) : 0 < countD a X := by
  rw [countD]
  have h : 0 < 2 * (countK X) ^ 3 := by positivity
  exact Nat.mul_pos (by norm_num) (Nat.pow_pos h)

/-- `K (log N)^d ≤ N` eventually, for every constant `K > 0` and exponent `d`. -/
theorem eventually_polylog_le {K : ℝ} (hK : 0 < K) (d : ℕ) :
    ∀ᶠ N : ℕ in atTop, K * (Real.log (N : ℝ)) ^ d ≤ (N : ℝ) := by
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := d)).def
    (show (0 : ℝ) < 1 / K by positivity)
  have hbase : ∀ᶠ x : ℝ in atTop, K * (Real.log x) ^ d ≤ x := by
    filter_upwards [hlo, eventually_ge_atTop (1 : ℝ)] with x hx h1
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogpos : (0 : ℝ) ≤ Real.log x := Real.log_nonneg h1
    have hnorm : Real.log x ^ d ≤ 1 / K * x := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hlogpos,
        abs_of_nonneg hx0.le, id] using hx
    have := mul_le_mul_of_nonneg_left hnorm hK.le
    calc K * (Real.log x) ^ d ≤ K * (1 / K * x) := this
      _ = x := by field_simp
  exact Filter.eventually_atTop.2 (by
    obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1
      (tendsto_natCast_atTop_atTop (R := ℝ).eventually hbase)
    exact ⟨n0, hn0⟩)

/-- **The height goes to infinity.**  `⌊N / D_N⌋ ≥ m` eventually, for every `m`: `D_N` is
polylogarithmic in `N` because `k_N ≤ 6 log log N ≤ 6 log N`. -/
theorem eventually_height_ge (a m : ℕ) :
    ∀ᶠ N : ℕ in atTop, m ≤ N / countD a N := by
  set K : ℝ := ((m : ℝ) + 1) * (2 * 432 ^ (a - 1)) with hKdef
  have hK : 0 < K := by rw [hKdef]; positivity
  filter_upwards [eventually_polylog_le hK (3 * (a - 1)), eventually_countK_le,
    eventually_ge_atTop 3] with N hpoly hk hN3
  obtain ⟨hk1, hkle⟩ := hk
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hlogN1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    -- `log N ≥ 1` because `log log N` exists and `countK N ≥ 1`
    by_contra hcon
    push_neg at hcon
    have hle : Real.log (Real.log (N : ℝ)) ≤ 0 :=
      Real.log_nonpos (Real.log_natCast_nonneg N) hcon.le
    have hk1R : (1 : ℝ) ≤ (countK N : ℝ) := by exact_mod_cast hk1
    linarith
  -- `k_N ≤ 6 log N`
  have hμ : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_self (Real.log_natCast_nonneg N)
  have hkN : (countK N : ℝ) ≤ 6 * Real.log (N : ℝ) := by linarith
  -- `2 k_N³ ≤ 432 (log N)³`
  have hcube : 2 * (countK N : ℝ) ^ 3 ≤ 432 * (Real.log (N : ℝ)) ^ 3 := by
    have h := pow_le_pow_left₀ (show (0:ℝ) ≤ (countK N : ℝ) by positivity) hkN 3
    nlinarith [h]
  have hDreal : ((countD a N : ℕ) : ℝ)
      ≤ 2 * 432 ^ (a - 1) * (Real.log (N : ℝ)) ^ (3 * (a - 1)) := by
    have hp : ((2 * (countK N) ^ 3 : ℕ) : ℝ) ^ (a - 1)
        ≤ (432 * (Real.log (N : ℝ)) ^ 3) ^ (a - 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      push_cast
      exact hcube
    have hexp : (432 * (Real.log (N : ℝ)) ^ 3) ^ (a - 1)
        = 432 ^ (a - 1) * (Real.log (N : ℝ)) ^ (3 * (a - 1)) := by
      rw [mul_pow, ← pow_mul]
    rw [countD]
    push_cast
    push_cast at hp
    rw [hexp] at hp
    linarith
  -- conclude
  have hmD : ((m : ℝ) + 1) * ((countD a N : ℕ) : ℝ) ≤ (N : ℝ) := by
    have h1 : ((m : ℝ) + 1) * ((countD a N : ℕ) : ℝ)
        ≤ ((m : ℝ) + 1) * (2 * 432 ^ (a - 1) * (Real.log (N : ℝ)) ^ (3 * (a - 1))) :=
      mul_le_mul_of_nonneg_left hDreal (by positivity)
    have h2 : ((m : ℝ) + 1) * (2 * 432 ^ (a - 1) * (Real.log (N : ℝ)) ^ (3 * (a - 1)))
        = K * (Real.log (N : ℝ)) ^ (3 * (a - 1)) := by rw [hKdef]; ring
    rw [h2] at h1
    linarith
  have hnat : m * countD a N ≤ N := by
    have h : ((m * countD a N : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      nlinarith [hmD, Nat.cast_nonneg (α := ℝ) (countD a N)]
    exact_mod_cast h
  exact (Nat.le_div_iff_mul_le (countD_pos (a := a) hk1)).mpr (by omega)

/-- **The counting joint small-tail theorem.**  For fixed `c, a, r` and a fixed margin `ε`,
there are `C > 0` and `N₀` such that every `N ≥ N₀` admits a killed-window height `k > r`
and a `Finset` of at least `N exp(-C (log log N)² log log log N)` offsets `m < N`, each
carrying the prescribed divisor data at `m + 1` and a base tail below `ε/2` in **every** base
`b ≥ 2` simultaneously.

This is the counting analogue of `exists_joint_small_tail_all_bases_rescaled`, which returns
a single offset.  See the module docstring for the content locator of the proof. -/
theorem exists_joint_small_tail_count {c a r : ℕ} (hc : 2 ≤ c) (ha : 2 ≤ a) (hr : 1 ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∃ k : ℕ, r < k ∧ ∃ T : Finset ℕ,
        (N : ℝ) * Real.exp (-C * (Real.log (Real.log (N : ℝ))) ^ 2
            * Real.log (Real.log (Real.log (N : ℝ)))) ≤ (T.card : ℝ) ∧
        (∀ m ∈ T, m < N) ∧
        (∀ m ∈ T, ∀ j, j < k → j ≠ r → c ^ (j + 1) ∣ tau (m + 1 + j)) ∧
        (∀ m ∈ T, tau (m + 1 + r) = 2 * a) ∧
        (∀ m ∈ T, ∀ b : ℕ, 2 ≤ b →
          0 ≤ ∑' t : ℕ, (tau (m + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) ∧
          ∑' t : ℕ, (tau (m + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) < ε / 2) := by
  sorry

end NormalNumbers.JointLambert
