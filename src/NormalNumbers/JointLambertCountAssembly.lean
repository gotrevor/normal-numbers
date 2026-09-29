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
  classical
  obtain ⟨X0, hheight⟩ := exists_good_starts_at_height hc ha hr hε
  obtain ⟨C, hC, N1, hrate⟩ := eventually_rate_le c a
  obtain ⟨N2, hN2⟩ := eventually_atTop.1
    ((eventually_height_ge a (max X0 3)).and (eventually_countK_le.and
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 : ℝ))))
  refine ⟨C, hC, max (max N1 N2) 3, fun N hN => ?_⟩
  have hNN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hXge, ⟨hkN1, hkNle⟩, hlogN1⟩ := hN2 N hNN2
  set D : ℕ := countD a N with hDdef
  set X : ℕ := N / D with hXdef
  have hDpos : 0 < D := countD_pos (a := a) hkN1
  have hX0 : X0 ≤ X := le_trans (le_max_left _ _) hXge
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hXge
  have hDX : D * X ≤ N := by
    rw [hXdef, Nat.mul_comm]
    exact Nat.div_mul_le_self N D
  have hNlt : N < D * (X + 1) := by
    have h1 := Nat.div_add_mod N D
    have h2 := Nat.mod_lt N hDpos
    have : D * X + N % D = N := by rw [hXdef]; omega
    have hmul : D * (X + 1) = D * X + D := by ring
    omega
  obtain ⟨B, Dx, hrk, hBpos, hDxpos, hBle, hDxle, T, hcard, hmem, hkill, hsurv, hall⟩ :=
    hheight X hX0
  set k : ℕ := countK X with hkdef
  -- real setup
  have hXR : (0 : ℝ) < (X : ℝ) := by
    have : (0 : ℕ) < X := by omega
    exact_mod_cast this
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hlogX1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by
    have h3 : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
    have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) he
      _ ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) h3
  have hXN : X ≤ N := by
    calc X ≤ D * X := Nat.le_mul_of_pos_left _ hDpos
      _ ≤ N := hDX
  have hkmono : k ≤ countK N := countK_le_countK (by linarith) hXN
  -- `k ≥ 2`, directly from `r < k` and `r ≥ 1`
  have hk1 : 1 ≤ k := by omega
  -- the offsets fit inside `[0, N)`
  have hnlt : ∀ n ∈ T, n < N := by
    intro n hn
    obtain ⟨-, hnDX⟩ := hmem n hn
    have hDxD : Dx ≤ D := by
      rw [hDdef, countD]
      refine le_trans hDxle ?_
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left
        (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hkmono 3)) _)
    calc n < Dx * X := hnDX
      _ ≤ D * X := Nat.mul_le_mul_right X hDxD
      _ ≤ N := hDX
  -- the shifted good set
  refine ⟨k, hrk, T.image (fun n => n - 1), ?_, ?_, ?_, ?_, ?_⟩
  · -- the count
    have hinj : Set.InjOn (fun n => n - 1) T := by
      intro x hx y hy hxy
      have h1 := (hmem x hx).1
      have h2 := (hmem y hy).1
      simp only at hxy
      omega
    rw [Finset.card_image_of_injOn hinj]
    refine le_trans ?_ hcard
    -- `N exp(-C μ²ν) ≤ X / (8 B log X)`
    set μ : ℝ := Real.log (Real.log (N : ℝ)) with hμdef
    set ν : ℝ := Real.log (Real.log (Real.log (N : ℝ))) with hνdef
    have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBpos
    have hden : (0 : ℝ) < 8 * (B : ℝ) * Real.log (X : ℝ) := by
      have : (0 : ℝ) < Real.log (X : ℝ) := by linarith
      positivity
    have hlogXN : Real.log (X : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log hXR (by exact_mod_cast hXN)
    have hloglogXN : Real.log (Real.log (X : ℝ)) ≤ μ := by
      rw [hμdef]
      exact Real.log_le_log (by linarith) hlogXN
    -- `log N ≤ log 2 + log D + log X`
    have hlogNle : Real.log (N : ℝ) ≤ Real.log 2 + Real.log (D : ℝ) + Real.log (X : ℝ) := by
      have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
      have hle : (N : ℝ) ≤ 2 * ((D : ℝ) * (X : ℝ)) := by
        have h1 : (N : ℝ) ≤ ((D * (X + 1) : ℕ) : ℝ) := by exact_mod_cast hNlt.le
        have h2 : ((D * (X + 1) : ℕ) : ℝ) = (D : ℝ) * ((X : ℝ) + 1) := by push_cast; ring
        have h3 : (1 : ℝ) ≤ (X : ℝ) := by
          have : (1 : ℕ) ≤ X := by omega
          exact_mod_cast this
        rw [h2] at h1
        nlinarith [h1, hDR, h3]
      calc Real.log (N : ℝ) ≤ Real.log (2 * ((D : ℝ) * (X : ℝ))) :=
            Real.log_le_log hNR hle
        _ = Real.log 2 + Real.log (D : ℝ) + Real.log (X : ℝ) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity)
              (by positivity)]
            ring
    -- `log D = log 2 + (a-1) log(2 k_N³)`
    have hlogD : Real.log (D : ℝ)
        = Real.log 2 + ((a - 1 : ℕ) : ℝ) * Real.log (2 * (countK N : ℝ) ^ 3) := by
      have hcast : ((D : ℕ) : ℝ) = 2 * (2 * (countK N : ℝ) ^ 3) ^ (a - 1) := by
        rw [hDdef, countD]; push_cast; ring
      rw [hcast, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    -- `log B ≤ (1 + c k_N²) log(2 k_N³)`
    have hkNR : (1 : ℝ) ≤ (countK N : ℝ) := by exact_mod_cast hkN1
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hlog2k3N : (0 : ℝ) ≤ Real.log (2 * (countK N : ℝ) ^ 3) := by
      refine Real.log_nonneg ?_
      have : (1 : ℝ) ≤ (countK N : ℝ) ^ 3 := one_le_pow₀ hkNR
      linarith
    have hlogB : Real.log (B : ℝ)
        ≤ (1 + (c : ℝ) * (countK N : ℝ) ^ 2) * Real.log (2 * (countK N : ℝ) ^ 3) := by
      have hcast : (((2 * k ^ 3) ^ (1 + c * k ^ 2) : ℕ) : ℝ)
          = (2 * (k : ℝ) ^ 3) ^ (1 + c * k ^ 2) := by push_cast; ring
      have h1 : Real.log (B : ℝ) ≤ Real.log (((2 * k ^ 3) ^ (1 + c * k ^ 2) : ℕ) : ℝ) :=
        Real.log_le_log (by linarith) (by exact_mod_cast hBle)
      rw [hcast, Real.log_pow] at h1
      have hmono1 : Real.log (2 * (k : ℝ) ^ 3) ≤ Real.log (2 * (countK N : ℝ) ^ 3) := by
        refine Real.log_le_log (by positivity) ?_
        have := pow_le_pow_left₀ (show (0:ℝ) ≤ (k:ℝ) by linarith)
          (show (k : ℝ) ≤ (countK N : ℝ) by exact_mod_cast hkmono) 3
        linarith
      have hmono2 : ((1 + c * k ^ 2 : ℕ) : ℝ) ≤ 1 + (c : ℝ) * (countK N : ℝ) ^ 2 := by
        have := pow_le_pow_left₀ (show (0:ℝ) ≤ (k:ℝ) by linarith)
          (show (k : ℝ) ≤ (countK N : ℝ) by exact_mod_cast hkmono) 2
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) c]
      have hlogk3nn : (0 : ℝ) ≤ Real.log (2 * (k : ℝ) ^ 3) := by
        refine Real.log_nonneg ?_
        have : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hkR
        linarith
      calc Real.log (B : ℝ) ≤ ((1 + c * k ^ 2 : ℕ) : ℝ) * Real.log (2 * (k : ℝ) ^ 3) := h1
        _ ≤ (1 + (c : ℝ) * (countK N : ℝ) ^ 2) * Real.log (2 * (countK N : ℝ) ^ 3) := by
            refine mul_le_mul hmono2 hmono1 hlogk3nn ?_
            have : (0 : ℝ) ≤ (c : ℝ) * (countK N : ℝ) ^ 2 := by positivity
            linarith
    -- `log(8 B log X) = log 8 + log B + log log X`
    have hlogden : Real.log (8 * (B : ℝ) * Real.log (X : ℝ))
        = Real.log 8 + Real.log (B : ℝ) + Real.log (Real.log (X : ℝ)) := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num)
        (by linarith)]
    have hrateN := hrate N hNN1
    have hlog8N : Real.log (8 * Real.log (N : ℝ)) = Real.log 8 + μ := by
      rw [Real.log_mul (by norm_num) (by linarith), hμdef]
    have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have haR : ((a - 1 : ℕ) : ℝ) ≤ (a : ℝ) := by
      have : (a - 1 : ℕ) ≤ a := Nat.sub_le a 1
      exact_mod_cast this
    -- the key inequality
    have hkey : Real.log (N : ℝ)
        ≤ Real.log (X : ℝ) - Real.log (8 * (B : ℝ) * Real.log (X : ℝ)) + C * μ ^ 2 * ν := by
      rw [hlogden]
      rw [hlog8N] at hrateN
      set Lg : ℝ := Real.log (2 * (countK N : ℝ) ^ 3) with hLgdef
      have e1 : Real.log (N : ℝ) - Real.log (X : ℝ)
          ≤ Real.log 2 + (Real.log 2 + ((a - 1 : ℕ) : ℝ) * Lg) := by
        rw [← hlogD]; linarith [hlogNle]
      have hPQ : ((a - 1 : ℕ) : ℝ) * Lg ≤ (a : ℝ) * Lg :=
        mul_le_mul_of_nonneg_right haR hlog2k3N
      have hexp : (1 + (c : ℝ) * (countK N : ℝ) ^ 2 + (a : ℝ)) * Lg
          = (1 + (c : ℝ) * (countK N : ℝ) ^ 2) * Lg + (a : ℝ) * Lg := by ring
      rw [hexp] at hrateN
      linarith [hrateN, e1, hlogB, hloglogXN, hPQ, hl2]
    -- exponentiate
    have hGpos : (0 : ℝ) < (X : ℝ) / (8 * (B : ℝ) * Real.log (X : ℝ)) := by positivity
    have hlogG : Real.log ((X : ℝ) / (8 * (B : ℝ) * Real.log (X : ℝ)))
        = Real.log (X : ℝ) - Real.log (8 * (B : ℝ) * Real.log (X : ℝ)) :=
      Real.log_div (ne_of_gt hXR) (ne_of_gt hden)
    calc (N : ℝ) * Real.exp (-C * μ ^ 2 * ν)
        = Real.exp (Real.log (N : ℝ) + -C * μ ^ 2 * ν) := by
          rw [Real.exp_add, Real.exp_log hNR]
      _ ≤ Real.exp (Real.log ((X : ℝ) / (8 * (B : ℝ) * Real.log (X : ℝ)))) := by
          refine Real.exp_le_exp.mpr ?_
          rw [hlogG]
          linarith [hkey]
      _ = (X : ℝ) / (8 * (B : ℝ) * Real.log (X : ℝ)) := Real.exp_log hGpos
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have h1 := (hmem n hn).1
    have h2 := hnlt n hn
    omega
  · intro m hm j hj hjr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have h1 := (hmem n hn).1
    have hrw : n - 1 + 1 = n := by omega
    rw [hrw]
    exact hkill n hn j hj hjr
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have h1 := (hmem n hn).1
    have hrw : n - 1 + 1 = n := by omega
    rw [hrw]
    exact hsurv n hn
  · intro m hm b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have h1 := (hmem n hn).1
    have hrw : n - 1 + 1 = n := by omega
    rw [hrw]
    exact hall n hn b hb

end NormalNumbers.JointLambert
