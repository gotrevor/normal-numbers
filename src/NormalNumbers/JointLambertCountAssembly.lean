/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertCountRate
import NormalNumbers.JointLambertRescaledTail
import NormalNumbers.JointLambertSmallPool
import NormalNumbers.JointLambertCountCandidates

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

/-! ### Step A: the binary tail *is* the three-range expression

`three_range_tail_le` bounds `∑_j τ(n+j)2^{-j}` split at `J`.  The digit reader
`floor_digit_of_common_offset` consumes the *tsum* `∑' t τ(n+k+t)/2^(k+t)`.  These are the
same number, which is what lets the counting route reuse the frozen tail estimate. -/


/-- **The binary tail is exactly the three-range expression.** -/
theorem binTail_eq_three_range (n k J : ℕ) (hkJ : k ≤ J) :
    ∑' t : ℕ, (tau (n + k + t) : ℝ) / 2 ^ (k + t)
      = (∑ j ∈ Ico k J, (tau (n + j) : ℝ) * (1 / 2 : ℝ) ^ j)
        + (1 / 2 : ℝ) ^ J * ∑' t : ℕ, (tau (n + J + t) : ℝ) / 2 ^ t := by
  set f : ℕ → ℝ := fun t => (tau (n + k + t) : ℝ) / 2 ^ (k + t) with hf
  have hsumf : Summable f := by
    refine ((summable_tau_div (n + k)).mul_right ((1 : ℝ) / 2 ^ k)).congr ?_
    intro t
    simp only [hf]
    rw [pow_add]
    ring
  set D := J - k with hD
  have hsplit := hsumf.sum_add_tsum_nat_add D
  have hfin : ∑ t ∈ range D, f t = ∑ j ∈ Ico k J, (tau (n + j) : ℝ) * (1 / 2 : ℝ) ^ j := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by rw [hD]) fun t _ => ?_
    simp only [hf]
    rw [show n + k + t = n + (k + t) by omega]
    rw [div_pow, one_pow]
    ring
  have htail : ∑' i : ℕ, f (i + D)
      = (1 / 2 : ℝ) ^ J * ∑' t : ℕ, (tau (n + J + t) : ℝ) / 2 ^ t := by
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    simp only [hf]
    rw [show n + k + (i + D) = n + J + i by omega,
      show k + (i + D) = J + i by omega, pow_add, div_pow, one_pow]
    field_simp
  rw [← hsplit, hfin, htail]


/-! ### Step C: the window `H` does not outgrow the candidate range `M`

`three_range_tail_le`'s bracket is `W = 2M(1 + log H) + 2H`, so the `2H` term is only
harmless if `H = O(M)`.  It is, but `B³ ≤ X` alone is a factor two short; the fix is to run
the (uniform in `c`) schedule feasibility at the inflated exponent `4c+4`. -/


/-- **The small-pool modulus is a twelfth root of the height.**  `eventually_schedule_feasible`
only asserts `B³ ≤ X`, which is a factor `2` short of what the window comparison `H ≤ M`
needs.  Applying it at the *inflated* pool exponent `4c+4` — legitimate, since the schedule
is feasible for every fixed `c` — upgrades the cube to a twelfth power with no new
analysis. -/
theorem eventually_modulus_pow_twelve_le (c : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ B : ℕ, 1 ≤ B →
      B ≤ (2 * (countK X) ^ 3) ^ (1 + c * (countK X) ^ 2) → (B : ℝ) ^ 12 ≤ (X : ℝ) := by
  filter_upwards [eventually_schedule_feasible (4 * c + 4)
    (show (0:ℝ) < 1 by norm_num) (show (0:ℝ) < 1 by norm_num),
    eventually_countK_ge 1] with X hsched hk1 B hB1 hBle
  set k : ℕ := countK X with hkdef
  have hpow : B ^ 4 ≤ (2 * k ^ 3) ^ (1 + (4 * c + 4) * k ^ 2) := by
    calc B ^ 4 ≤ ((2 * k ^ 3) ^ (1 + c * k ^ 2)) ^ 4 := Nat.pow_le_pow_left hBle 4
      _ = (2 * k ^ 3) ^ (4 * (1 + c * k ^ 2)) := by rw [← pow_mul]; ring_nf
      _ ≤ (2 * k ^ 3) ^ (1 + (4 * c + 4) * k ^ 2) := by
          refine Nat.pow_le_pow_right (by positivity) ?_
          have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
          nlinarith [hk2]
  have h4 : 1 ≤ B ^ 4 := Nat.one_le_pow _ _ (by omega)
  have := (hsched (B ^ 4) h4 hpow).1
  calc (B : ℝ) ^ 12 = (((B ^ 4 : ℕ) : ℝ)) ^ 3 := by push_cast; ring
    _ ≤ (X : ℝ) := this

/-- **`H ≤ M`: the window `H = ⌈√Y⌉` is below the candidate range `M = ⌊X/B⌋ + 1`.**
With `Λ¹² ≤ X`, `B, Q ≤ Λ`, `Y = 2QX + J` and `J ≤ X`, one has `√Y · B ≤ X`. -/
theorem sqrt_window_mul_le {B Q X J Λ : ℕ} (hB1 : 1 ≤ B) (hΛ : 2 ≤ Λ) (hBΛ : B ≤ Λ)
    (hQΛ : Q ≤ Λ) (hJX : J ≤ X) (hX : (Λ : ℝ) ^ 12 ≤ (X : ℝ)) :
    Nat.sqrt (2 * Q * X + J) * B ≤ X := by
  set Y : ℕ := 2 * Q * X + J with hY
  have hsq : Nat.sqrt Y * Nat.sqrt Y ≤ Y := by
    have := Nat.sqrt_le' Y; nlinarith [this]
  -- `(√Y · B)² ≤ Y · Λ² ≤ (2Λ+1)X · Λ² ≤ X · X`
  have hYle : Y ≤ (2 * Λ + 1) * X := by
    have h1 : 2 * Q * X ≤ 2 * Λ * X := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hQΛ)
    calc Y ≤ 2 * Λ * X + X := by omega
      _ = (2 * Λ + 1) * X := by ring
  have hΛX : (2 * Λ + 1) * Λ * Λ ≤ X := by
    have hΛR : (2 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
    have hkey : (((2 * Λ + 1) * Λ * Λ : ℕ) : ℝ) ≤ (Λ : ℝ) ^ 12 := by
      push_cast
      have h9 : (3 : ℝ) ≤ (Λ : ℝ) ^ 9 := by
        calc (3 : ℝ) ≤ 2 ^ 9 := by norm_num
          _ ≤ (Λ : ℝ) ^ 9 := by
              exact pow_le_pow_left₀ (by norm_num) hΛR 9
      have h12 : (Λ : ℝ) ^ 12 = (Λ : ℝ) ^ 3 * (Λ : ℝ) ^ 9 := by ring
      have hp3 : (0 : ℝ) < (Λ : ℝ) ^ 3 := by positivity
      have hsq3 : (Λ : ℝ) ^ 2 ≤ (Λ : ℝ) ^ 3 := by nlinarith [hΛR]
      have hfin : (3 : ℝ) * (Λ : ℝ) ^ 3 ≤ (Λ : ℝ) ^ 12 := by
        rw [h12]
        nlinarith [mul_nonneg hp3.le (sub_nonneg.2 h9)]
      nlinarith [hsq3, hfin]
    have : (((2 * Λ + 1) * Λ * Λ : ℕ) : ℝ) ≤ (X : ℝ) := le_trans hkey hX
    exact_mod_cast this
  have hmain : (Nat.sqrt Y * B) * (Nat.sqrt Y * B) ≤ X * X := by
    calc (Nat.sqrt Y * B) * (Nat.sqrt Y * B) = (Nat.sqrt Y * Nat.sqrt Y) * (B * B) := by ring
      _ ≤ Y * (Λ * Λ) := Nat.mul_le_mul hsq (Nat.mul_le_mul hBΛ hBΛ)
      _ ≤ ((2 * Λ + 1) * X) * (Λ * Λ) := Nat.mul_le_mul_right _ hYle
      _ = ((2 * Λ + 1) * Λ * Λ) * X := by ring
      _ ≤ X * X := Nat.mul_le_mul_right _ hΛX
  exact Nat.le_of_mul_le_mul_left (by nlinarith [hmain]) (by omega : 0 < 1)

/-! ### Step B: the CRT data and the candidate `Finset` at every chosen height

Steps 1–2 of the module docstring, assembled: pool, allocation avoiding `P`, CRT, and the
candidate count.  `P` is chosen from `exists_candidate_indices_every_height` *before* the
allocation, and `exists_prime_allocation_small_pool` dodges it, which is what makes
`Coprime B P` available to the prime-supply bound. -/

/-- **CRT data and candidate indices at every large chosen height `X`.**  With
`k = countK X` and `L = k³`, there are a pool prime `q ∈ (k³, 2k³)`, allocation primes `p`
in the same interval, and a CRT solution `R, u` such that the arithmetic progression
`m ↦ R + m·A` carries the prescribed divisor data, the near-range coprimality on `[k, L)`,
the small-pool size bounds `Q ≤ (2k³)^(a-1)` and `B ≤ (2k³)^(1+ck²)`, and at least
`M/(4 log X)` of the `M = ⌊X/B⌋+1` indices `m` have `u + mB` prime and `≤ X`. -/
theorem exists_candidate_data_at_height {c a r : ℕ} (hc : 2 ≤ c) (ha : 2 ≤ a) (hr : 1 ≤ r) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      ∃ (q R u : ℕ) (p : ℕ → ℕ → ℕ),
        r < countK X ∧ 2 ≤ countK X ∧
        (countK X) ^ 3 < q ∧ q < 2 * (countK X) ^ 3 ∧ q.Prime ∧
        (∀ j t, j ∈ killedIdx (countK X) r → t < j + 1 → (p j t).Prime) ∧
        0 < R ∧ R < jointA c a (countK X) r q p ∧
        1 ≤ u ∧ u < jointB c (countK X) r q p ∧
        jointA c a (countK X) r q p
          = jointQ a q * jointB c (countK X) r q p ∧
        (∀ m j, j < countK X → j ≠ r →
          c ^ (j + 1) ∣ tau (R + m * jointA c a (countK X) r q p + j)) ∧
        (∀ m, (u + m * jointB c (countK X) r q p).Prime →
          tau (R + m * jointA c a (countK X) r q p + r) = 2 * a) ∧
        (∀ j, countK X ≤ j → j < (countK X) ^ 3 →
          Nat.Coprime (R + j) (jointA c a (countK X) r q p)) ∧
        jointQ a q ≤ (2 * (countK X) ^ 3) ^ (a - 1) ∧
        jointB c (countK X) r q p ≤ (2 * (countK X) ^ 3) ^ (1 + c * (countK X) ^ 2) ∧
        ((X / jointB c (countK X) r q p + 1 : ℕ) : ℝ) / (4 * Real.log (X : ℝ))
          ≤ (((range (X / jointB c (countK X) r q p + 1)).filter
              (fun m => (u + m * jointB c (countK X) r q p).Prime ∧
                u + m * jointB c (countK X) r q p ≤ X)).card : ℝ) := by
  classical
  obtain ⟨K, hpool⟩ := eventually_small_prime_pool
  obtain ⟨X1, hcand⟩ := exists_candidate_indices_every_height c
  obtain ⟨X2, hk⟩ := eventually_atTop.1 (eventually_countK_ge (max K (max (r + 1) 2)))
  refine ⟨max X1 X2, fun X hX => ?_⟩
  have hX1 : X1 ≤ X := le_trans (le_max_left _ _) hX
  have hX2 : X2 ≤ X := le_trans (le_max_right _ _) hX
  have hkge := hk X hX2
  set k : ℕ := countK X with hkdef
  have hkK : K ≤ k := le_trans (le_max_left _ _) hkge
  have hkr : r < k := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hkge
    omega
  have hk2 : 2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hkge
  obtain ⟨P, hPprime, hPcount⟩ := hcand X hX1
  obtain ⟨q, p, hqS, hpS, hpqne, hpinj, havoid⟩ :=
    exists_prime_allocation_small_pool hpool c k r P hkK
  have hqdata : q.Prime ∧ k ^ 3 < q ∧ q < 2 * k ^ 3 := by
    obtain ⟨hmem, hpr⟩ := Finset.mem_filter.mp hqS
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hmem
    exact ⟨hpr, h1, h2⟩
  have hpdata : ∀ j t, j ∈ killedIdx k r → t < j + 1 →
      (p j t).Prime ∧ k ^ 3 < p j t ∧ p j t < 2 * k ^ 3 := by
    intro j t hj ht
    obtain ⟨hmem, hpr⟩ := Finset.mem_filter.mp (hpS j t hj ht)
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hmem
    exact ⟨hpr, h1, h2⟩
  have hkL : k ≤ k ^ 3 := Nat.le_self_pow (by norm_num) k
  have hqr : r < jointQ a q := by
    have h1 : q ^ 1 ≤ q ^ (a - 1) := Nat.pow_le_pow_right hqdata.1.pos (by omega)
    rw [pow_one] at h1
    simp only [jointQ]
    have : r < k ^ 3 := by omega
    omega
  obtain ⟨R, u, hR0, hRA, hu1, huB, hRr, hAQB, humod, hcopuB, hres_r, hres_j, hkill,
      hsurv, htail⟩ :=
    exists_joint_progression (L := k ^ 3) (p := p) hc ha hr hkr hkL hqdata.1 hqdata.2.1 hqr
      (fun j t hjk hjr ht => (hpdata j t (mem_killedIdx.mpr ⟨hjr, hjk⟩) ht).1)
      (fun j t hjk hjr ht => (hpdata j t (mem_killedIdx.mpr ⟨hjr, hjk⟩) ht).2.1)
      (fun j t hjk hjr ht => hpqne j t (mem_killedIdx.mpr ⟨hjr, hjk⟩) ht)
      (fun j t j' t' hjk hjr ht hj'k hj'r ht' he =>
        hpinj j t j' t' (mem_killedIdx.mpr ⟨hjr, hjk⟩) ht (mem_killedIdx.mpr ⟨hj'r, hj'k⟩) ht' he)
  have hQle : jointQ a q ≤ (2 * k ^ 3) ^ (a - 1) := jointQ_le hqdata.2.2
  have hBle : jointB c k r q p ≤ (2 * k ^ 3) ^ (1 + c * k ^ 2) := by
    refine le_trans (jointB_le hqdata.2.2 fun j t hj ht => (hpdata j t hj ht).2.2) ?_
    exact Nat.pow_le_pow_right (by positivity)
      (Nat.add_le_add_left (Nat.mul_le_mul le_rfl (killPoolSize_le_sq k r)) 1)
  have hB1 : 1 ≤ jointB c k r q p := by omega
  have hcopBP : Nat.Coprime (jointB c k r q p) P := by
    rcases hPprime with rfl | hP
    · exact Nat.coprime_one_right _
    · exact ((Nat.Prime.coprime_iff_not_dvd hP).mpr (havoid hP.ne_one)).symm
  have hcount := hPcount (jointB c k r q p) u hB1 hBle huB hcopuB hcopBP
  exact ⟨q, R, u, p, hkr, hk2, hqdata.2.1, hqdata.2.2, hqdata.1,
    fun j t hj ht => (hpdata j t hj ht).1, hR0, hRA, hu1, huB, hAQB, hkill, hsurv, htail,
    hQle, hBle, hcount⟩



/-! ### Step D: the two logarithmic bookkeeping bounds of step 3

`J ≤ X` (needed by `sqrt_window_mul_le`) and `log H = O(log X)` (needed to turn the
bracket `W = 2M(1+log H) + 2H` into `O(M log X)`). -/


/-- `Nat.log 2 n ≤ 2 log n`, the real-valued form of `2^(Nat.log 2 n) ≤ n`. -/
theorem natLog_two_le {n : ℕ} (hn : 1 ≤ n) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hR : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by exact_mod_cast hpow
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    have := Real.log_le_log (by positivity) hR
    rwa [Real.log_pow] at this
  have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  nlinarith [hlog, hl2, Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)]

/-- `log(√Y + 1) ≤ 2 log X + 2` whenever `Y ≤ 3X²`: the `log H` factor of the
three-range bracket costs only `O(log X)`. -/
theorem log_window_le {X Y : ℕ} (hX : 1 ≤ X) (hY : Y ≤ 3 * (X * X)) :
    Real.log ((Nat.sqrt Y + 1 : ℕ) : ℝ) ≤ 2 * Real.log (X : ℝ) + 2 := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hHle : (Nat.sqrt Y + 1 : ℕ) ≤ 4 * (X * X) := by
    have h1 : Nat.sqrt Y ≤ Y := Nat.sqrt_le_self Y
    have h2 : 1 ≤ X * X := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hHR : ((Nat.sqrt Y + 1 : ℕ) : ℝ) ≤ 4 * (X : ℝ) * (X : ℝ) := by
    have h : ((Nat.sqrt Y + 1 : ℕ) : ℝ) ≤ ((4 * (X * X) : ℕ) : ℝ) := by exact_mod_cast hHle
    push_cast at h ⊢; linarith
  have hstep := Real.log_le_log (by positivity) hHR
  refine le_trans hstep ?_
  have hrw : Real.log (4 * (X : ℝ) * (X : ℝ)) = Real.log 4 + 2 * Real.log (X : ℝ) := by
    rw [show (4 : ℝ) * (X : ℝ) * (X : ℝ) = 4 * ((X : ℝ) * (X : ℝ)) by ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity)]
    ring
  rw [hrw]
  have : Real.log 4 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  linarith

/-- **`J ≤ X` eventually**, uniformly in the window bound `Y₀ ≤ 2X²`: `countJ` is
`k³ + O(log X) = O((log X)³)`. -/
theorem eventually_countJ_le : ∀ᶠ X : ℕ in atTop,
    ∀ Y0 : ℕ, Y0 ≤ 2 * (X * X) → countJ (countK X) Y0 X ≤ X := by
  filter_upwards [eventually_countK_le, eventually_polylog_le
    (show (0:ℝ) < 244 by norm_num) 3, eventually_ge_atTop 3,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 : ℝ)]
    with X hk hpoly hX3 hlog1 Y0 hY0
  obtain ⟨hk1, hkle⟩ := hk
  simp only [Function.comp] at hlog1
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by
    have : (1 : ℕ) ≤ X := by omega
    exact_mod_cast this
  have hL : (1 : ℝ) ≤ Real.log (X : ℝ) := hlog1
  set L : ℝ := Real.log (X : ℝ) with hLdef
  -- `k ≤ 6 log X`
  have hμ : Real.log (Real.log (X : ℝ)) ≤ Real.log (X : ℝ) :=
    Real.log_le_self (Real.log_natCast_nonneg X)
  have hkR : (countK X : ℝ) ≤ 6 * L := by linarith [hμ, hkle]
  have hk3 : ((countK X : ℕ) : ℝ) ^ 3 ≤ 216 * L ^ 3 := by
    have h := pow_le_pow_left₀ (show (0:ℝ) ≤ ((countK X : ℕ) : ℝ) by positivity) hkR 3
    nlinarith [h]
  -- the two `Nat.log` terms
  have hY1 : Y0 + 1 ≤ 3 * (X * X) := by
    have h2 : 1 ≤ X * X := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hlY : ((Nat.log 2 (Y0 + 1) : ℕ) : ℝ) ≤ 4 * L + 4 := by
    refine le_trans (natLog_two_le (by omega)) ?_
    have h1 : ((Y0 + 1 : ℕ) : ℝ) ≤ 3 * (X : ℝ) * (X : ℝ) := by
      have h : ((Y0 + 1 : ℕ) : ℝ) ≤ ((3 * (X * X) : ℕ) : ℝ) := by exact_mod_cast hY1
      push_cast at h ⊢; linarith
    have h2 := Real.log_le_log (by positivity) h1
    have hrw : Real.log (3 * (X : ℝ) * (X : ℝ)) = Real.log 3 + 2 * L := by
      rw [show (3 : ℝ) * (X : ℝ) * (X : ℝ) = 3 * ((X : ℝ) * (X : ℝ)) by ring,
        Real.log_mul (by norm_num) (by positivity),
        Real.log_mul (by positivity) (by positivity), hLdef]
      ring
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
    rw [hrw] at h2
    linarith
  have hlX : ((Nat.log 2 (X + 1) : ℕ) : ℝ) ≤ 2 * L + 2 := by
    refine le_trans (natLog_two_le (by omega)) ?_
    have h1 : ((X + 1 : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by push_cast; linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (by positivity)] at h2
    have := Real.log_two_lt_d9
    rw [hLdef]
    linarith
  -- assemble
  have hJR : ((countJ (countK X) Y0 X : ℕ) : ℝ) ≤ 244 * L ^ 3 := by
    have hJn : ((countJ (countK X) Y0 X : ℕ) : ℝ)
        = ((countK X : ℕ) : ℝ) ^ 3
          + 2 * (((Nat.log 2 (Y0 + 1) : ℕ) : ℝ) + 1 + (((Nat.log 2 (X + 1) : ℕ) : ℝ) + 1)) := by
      simp only [countJ]; push_cast; ring
    have hL3 : L ≤ L ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ L by linarith)
        (show (0:ℝ) ≤ L - 1 by linarith)) (show (0:ℝ) ≤ L + 1 by linarith)]
    rw [hJn]
    linarith [hk3, hlY, hlX, hL3]
  have : ((countJ (countK X) Y0 X : ℕ) : ℝ) ≤ (X : ℝ) := le_trans hJR hpoly
  exact_mod_cast this

/-- The near+middle Markov budget: `12ML(2x+2y) ≤ θM/(16L)` from `L²x, L²y ≤ θ/768`. -/
theorem near_middle_budget {MR Lg x y θ : ℝ} (hMR : 0 < MR) (hLg : 1 ≤ Lg) (hθ : 0 < θ)
    (e1 : Lg ^ 2 * x ≤ θ / 768) (e2 : Lg ^ 2 * y ≤ θ / 768) :
    (12 * MR * Lg) * (2 * x + 2 * y) ≤ θ * MR / (16 * Lg) := by
  have hLg0 : (0 : ℝ) < Lg := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hsum : Lg ^ 2 * (x + y) ≤ θ / 384 := by nlinarith [e1, e2]
  nlinarith [hsum, hMR, hLg0, mul_pos hMR hLg0]

/-- The far-range Markov budget. -/
theorem far_budget {XR Lg θ : ℝ} (hX : 0 < XR) (hLg : 1 ≤ Lg) (hθ : 0 < θ)
    (h6 : (384 / θ) * Lg ≤ XR) : (24 : ℝ) / (XR + 1) ^ 2 ≤ θ / (16 * Lg) := by
  have hLg0 : (0 : ℝ) < Lg := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 384 * Lg ≤ θ * XR := by
    have := mul_le_mul_of_nonneg_left h6 hθ.le
    calc 384 * Lg = θ * ((384 / θ) * Lg) := by field_simp
      _ ≤ θ * XR := this
  nlinarith [h1, hθ, hX, sq_nonneg XR]

set_option maxHeartbeats 2000000 in
/-- **The chosen-height good-offset theorem** (§§3–4).  At every sufficiently large
caller-chosen height `X` the CRT construction produces a modulus `B` in the small-pool range,
a step `D` bounding the rescaling `2Q`, and a `Finset` of at least `X/(8 B log X)` *starts*
`n < D·X`, each carrying the prescribed divisor data at `n` and a base tail below `ε/2` in
every base `b ≥ 2`.

This is steps 1–4 of the module docstring: pool and CRT, candidate count, three-range tail,
Markov.  `exists_joint_small_tail_count` is its §5 transfer to every `N`, using
`countK_le_countK` and `eventually_rate_le`.

Proved from `exists_candidate_data_at_height` (pool, CRT, candidates),
`three_range_tail_le` at the adaptive split point `J = countJ` (with `jointA_tau_le`,
`log_window_le`, `sqrt_window_mul_le`, `far_cost_le`, `eventually_near_cost_small`,
`eventually_middle_cost_small`), `binTail_eq_three_range`, `card_good_ge_half`, and the
injection `m ↦ R + mA`. -/
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
  classical
  set θ : ℝ := ε / 2 with hθdef
  have hθ : 0 < θ := by rw [hθdef]; linarith
  refine eventually_atTop.1 ?_
  filter_upwards [eventually_atTop.2 (exists_candidate_data_at_height hc ha hr),
    eventually_modulus_pow_twelve_le c, eventually_countJ_le,
    eventually_near_cost_small (show (0:ℝ) < θ / 768 by positivity),
    eventually_middle_cost_small a c (show (0:ℝ) < θ / 768 by positivity),
    eventually_polylog_le (show (0:ℝ) < 384 / θ by positivity) 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 : ℝ),
    eventually_countK_ge a, eventually_ge_atTop 3]
    with X hdata hX2 hX3 hX4 hX5 hX6 hX7 hka hx8
  have hlog1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by simpa [Function.comp] using hX7
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (0 : ℕ) < X := by omega
    exact_mod_cast this
  obtain ⟨q, R, u, p, hkr, hk2, hqlo, hqhi, hqp, hpp, hR0, hRA, hu1, huB, hAQB,
    hkill, hsurv, hcop, hQle, hBle, hcount⟩ := hdata
  set k : ℕ := countK X with hkdef
  set B : ℕ := jointB c k r q p with hBdef
  set Q : ℕ := jointQ a q with hQdef
  set A : ℕ := jointA c a k r q p with hAdef
  have hB0 : 0 < B := by omega
  have hA0 : 0 < A := by omega
  have hQ0 : 0 < Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · rw [h, zero_mul] at hAQB; omega
    · exact h
  set Λ : ℕ := (2 * k ^ 3) ^ (1 + c * k ^ 2) with hΛdef
  have hΛ2 : 2 ≤ Λ := by
    rw [hΛdef]
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ (2 * k ^ 3) ^ 1 := Nat.pow_le_pow_left (by nlinarith [hk2]) 1
      _ ≤ (2 * k ^ 3) ^ (1 + c * k ^ 2) := Nat.pow_le_pow_right (by nlinarith [hk2]) (by omega)
  have hQΛ : Q ≤ Λ := by
    refine le_trans hQle ?_
    rw [hΛdef]
    refine Nat.pow_le_pow_right (by nlinarith [hk2]) ?_
    have hkk : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k
    have : 2 * k ≤ c * k ^ 2 := by nlinarith [hkk, hc]
    omega
  -- ### the height schedule at `X`
  have hΛ12 : (Λ : ℝ) ^ 12 ≤ (X : ℝ) := hX2 Λ (by omega) le_rfl
  have hBΛ : B ≤ Λ := hBle
  have hΛX : Λ ≤ X := by
    have hΛR : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast (by omega : 1 ≤ Λ)
    have : (Λ : ℝ) ≤ (Λ : ℝ) ^ 12 := le_self_pow₀ hΛR (by norm_num)
    have : (Λ : ℝ) ≤ (X : ℝ) := le_trans this hΛ12
    exact_mod_cast this
  have hBX : B ≤ X := le_trans hBΛ hΛX
  set M : ℕ := X / B + 1 with hMdef
  set Y0 : ℕ := 2 * Q * X with hY0def
  have hY0X : Y0 ≤ 2 * (X * X) := by
    rw [hY0def]
    have : Q ≤ X := le_trans hQΛ hΛX
    calc 2 * Q * X ≤ 2 * X * X := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
      _ = 2 * (X * X) := by ring
  set J : ℕ := countJ k Y0 X with hJdef
  have hJX : J ≤ X := hX3 Y0 hY0X
  set Y : ℕ := Y0 + J with hYdef
  set H : ℕ := Nat.sqrt Y + 1 with hHdef
  have hkL : k ≤ k ^ 3 := Nat.le_self_pow (by norm_num) k
  have hLJ : k ^ 3 ≤ J := le_countJ k Y0 X
  have hX1n : 1 ≤ X := by omega
  -- window and candidate-range comparison
  have hHM : H ≤ M := by
    have := sqrt_window_mul_le (B := B) (Q := Q) (X := X) (J := J) (Λ := Λ)
      (by omega) hΛ2 hBΛ hQΛ hJX hΛ12
    have hdiv : Nat.sqrt Y ≤ X / B := (Nat.le_div_iff_mul_le (by omega)).2 this
    rw [hHdef, hMdef]
    omega
  -- window bound for the tail ranges
  have hbd : ∀ j, j < J → ∀ m, m < M → (R + j) + m * A ≤ H ^ 2 :=
    progression_window_le_sq hAQB hRA (by omega) hBX (le_refl M) (by rw [hYdef])
  have hYm : ∀ m, m < M → R + m * A ≤ Y := by
    intro m hm
    have := progression_le_window hAQB hRA (by omega) hBX hm
    rw [hYdef, hY0def]; omega
  -- ### the total tail over the whole progression
  set f : ℕ → ℝ := fun m => ∑' t : ℕ, (tau (R + m * A + k + t) : ℝ) / 2 ^ (k + t) with hfdef
  have hfnn : ∀ m, 0 ≤ f m := by
    intro m
    exact tsum_nonneg fun t => by positivity
  have hfeq : ∀ m, f m = (∑ j ∈ Ico k J, (tau (R + j + m * A) : ℝ) * (1 / 2 : ℝ) ^ j)
      + (1 / 2 : ℝ) ^ J * ∑' t : ℕ, (tau ((R + m * A) + J + t) : ℝ) / 2 ^ t := by
    intro m
    rw [hfdef]
    simp only
    rw [binTail_eq_three_range (R + m * A) k J (le_trans hkL hLJ)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show R + m * A + j = R + j + m * A from by ring]
  set E : ℝ := (2 * (M : ℝ) * (1 + Real.log (H : ℝ)) + 2 * (H : ℝ))
      * (2 * (1 / 2 : ℝ) ^ k + (tau A : ℝ) * (2 * (1 / 2 : ℝ) ^ (k ^ 3)))
    + (M : ℝ) * ((2 * (Y : ℝ) + 2 * (J : ℝ) + 2) * (1 / 2 : ℝ) ^ J) with hEdef
  have htot : ∑ m ∈ range M, f m ≤ E := by
    rw [Finset.sum_congr rfl fun m _ => hfeq m]
    exact three_range_tail_le hA0 hR0 (by omega) hkL hLJ hbd hcop hYm
  -- ### the total tail is below the Markov budget
  set Lg : ℝ := Real.log (X : ℝ) with hLgdef
  set MR : ℝ := (M : ℝ) with hMRdef
  have hMR0 : (0 : ℝ) < MR := by
    rw [hMRdef]
    have : 0 < M := by omega
    exact_mod_cast this
  have hHMR : (H : ℝ) ≤ MR := by rw [hMRdef]; exact_mod_cast hHM
  have hY3 : Y ≤ 3 * (X * X) := by
    have h1 : 1 ≤ X * X := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hXXX : X ≤ X * X := Nat.le_mul_of_pos_left _ (by omega)
    rw [hYdef]; omega
  have hlogH : Real.log (H : ℝ) ≤ 2 * Lg + 2 := by
    rw [hHdef, hLgdef]
    exact log_window_le hX1n hY3
  have hbracket : 2 * MR * (1 + Real.log (H : ℝ)) + 2 * (H : ℝ) ≤ 12 * MR * Lg := by
    have h1 : 2 * MR * (1 + Real.log (H : ℝ)) ≤ 2 * MR * (3 + 2 * Lg) := by
      have := mul_le_mul_of_nonneg_left (show 1 + Real.log (H : ℝ) ≤ 3 + 2 * Lg by linarith)
        (show (0:ℝ) ≤ 2 * MR by linarith)
      linarith [this]
    have h2 : 2 * MR * (3 + 2 * Lg) + 2 * MR ≤ 12 * MR * Lg := by
      have hL : (1 : ℝ) ≤ Lg := hlog1
      nlinarith [hMR0, hL]
    linarith [h1, h2, hHMR]
  have htauA : (tau A : ℝ) ≤ ((a : ℝ) + 1) * ((c : ℝ) + 1) ^ (k ^ 2) := by
    have := jointA_tau_le (c := c) (a := a) (k := k) (r := r) (q := q) (p := p) hc ha hqp hpp
    have h : ((tau A : ℕ) : ℝ) ≤ (((a + 1) * (c + 1) ^ (k ^ 2) : ℕ) : ℝ) := by
      rw [hAdef]; exact_mod_cast this
    push_cast at h
    exact h
  have hpk : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
  have hpL : (0 : ℝ) < (1 / 2 : ℝ) ^ (k ^ 3) := by positivity
  have hpart1 : (2 * MR * (1 + Real.log (H : ℝ)) + 2 * (H : ℝ))
      * (2 * (1 / 2 : ℝ) ^ k + (tau A : ℝ) * (2 * (1 / 2 : ℝ) ^ (k ^ 3)))
      ≤ θ * MR / (16 * Lg) := by
    have hfac0 : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ k + (tau A : ℝ) * (2 * (1 / 2 : ℝ) ^ (k ^ 3)) := by
      positivity
    have hstep1 : (2 * MR * (1 + Real.log (H : ℝ)) + 2 * (H : ℝ))
        * (2 * (1 / 2 : ℝ) ^ k + (tau A : ℝ) * (2 * (1 / 2 : ℝ) ^ (k ^ 3)))
        ≤ (12 * MR * Lg)
          * (2 * (1 / 2 : ℝ) ^ k
            + (((a : ℝ) + 1) * ((c : ℝ) + 1) ^ (k ^ 2)) * (2 * (1 / 2 : ℝ) ^ (k ^ 3))) := by
      have h2 : (2 * (1 / 2 : ℝ) ^ k + (tau A : ℝ) * (2 * (1 / 2 : ℝ) ^ (k ^ 3)))
          ≤ 2 * (1 / 2 : ℝ) ^ k
            + (((a : ℝ) + 1) * ((c : ℝ) + 1) ^ (k ^ 2)) * (2 * (1 / 2 : ℝ) ^ (k ^ 3)) := by
        nlinarith [htauA, hpL]
      exact mul_le_mul hbracket h2 hfac0 (by positivity)
    refine le_trans hstep1 ?_
    have hre : (12 * MR * Lg)
        * (2 * (1 / 2 : ℝ) ^ k
          + (((a : ℝ) + 1) * ((c : ℝ) + 1) ^ (k ^ 2)) * (2 * (1 / 2 : ℝ) ^ (k ^ 3)))
        = (12 * MR * Lg) * (2 * ((1 / 2 : ℝ) ^ k)
          + 2 * (((a : ℝ) + 1) * ((c : ℝ) + 1) ^ (k ^ 2) * (1 / 2 : ℝ) ^ (k ^ 3))) := by
      ring
    rw [hre]
    exact near_middle_budget hMR0 hlog1 hθ hX4 hX5
  have hpart2 : MR * ((2 * (Y : ℝ) + 2 * (J : ℝ) + 2) * (1 / 2 : ℝ) ^ J)
      ≤ θ * MR / (16 * Lg) := by
    have hXY0 : X ≤ Y0 := by
      rw [hY0def]
      calc X = 1 * X := by ring
        _ ≤ 2 * Q * X := Nat.mul_le_mul_right _ (by omega)
    have hfar : (2 * ((Y0 : ℝ) + (J : ℝ)) + 2 * (J : ℝ) + 2) * (1 / 2 : ℝ) ^ J
        ≤ 24 / ((X : ℝ) + 1) ^ 2 := far_cost_le hX1n hXY0
    have hYR : (Y : ℝ) = (Y0 : ℝ) + (J : ℝ) := by rw [hYdef]; push_cast; ring
    rw [hYR]
    have hLg0 : (0 : ℝ) < Lg := by linarith
    have hkey : (24 : ℝ) / ((X : ℝ) + 1) ^ 2 ≤ θ / (16 * Lg) := by
      have h6 : (384 / θ) * Lg ^ 1 ≤ (X : ℝ) := hX6
      rw [pow_one] at h6
      exact far_budget hX0 hlog1 hθ h6
    calc MR * ((2 * ((Y0 : ℝ) + (J : ℝ)) + 2 * (J : ℝ) + 2) * (1 / 2 : ℝ) ^ J)
        ≤ MR * (24 / ((X : ℝ) + 1) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hfar hMR0.le
      _ ≤ MR * (θ / (16 * Lg)) := mul_le_mul_of_nonneg_left hkey hMR0.le
      _ = θ * MR / (16 * Lg) := by ring
  have hE : E ≤ θ * (MR / (4 * Lg)) / 2 := by
    have hLg0 : (0 : ℝ) < Lg := by linarith
    rw [hEdef]
    have : θ * MR / (16 * Lg) + θ * MR / (16 * Lg) = θ * (MR / (4 * Lg)) / 2 := by
      field_simp; ring
    linarith [hpart1, hpart2]
  -- ### Markov and the injection into offsets
  set T0 : Finset ℕ := (range M).filter
    (fun m => (u + m * B).Prime ∧ u + m * B ≤ X) with hT0def
  have hT0sub : T0 ⊆ range M := Finset.filter_subset _ _
  have hT0prime : ∀ m ∈ T0, (u + m * B).Prime := by
    intro m hm
    rw [hT0def, Finset.mem_filter] at hm
    exact hm.2.1
  have hsum : ∑ m ∈ T0, f m ≤ E :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hT0sub fun i _ _ => hfnn i) htot
  have hc0 : MR / (4 * Lg) ≤ (T0.card : ℝ) := hcount
  have hgood := card_good_ge_half hθ (fun m _ => hfnn m) hsum hc0 hE
  set G : Finset ℕ := T0.filter (fun m => f m ≤ θ) with hGdef
  have hGmem : ∀ m ∈ G, m ∈ T0 ∧ f m ≤ θ := by
    intro m hm
    rw [hGdef, Finset.mem_filter] at hm
    exact hm
  set T : Finset ℕ := G.image (fun m => R + m * A) with hTdef
  have hinj : Set.InjOn (fun m => R + m * A) G := by
    intro x _ y _ hxy
    simp only at hxy
    have : x * A = y * A := by omega
    exact Nat.eq_of_mul_eq_mul_right hA0 this
  have hTcard : (T.card : ℝ) = (G.card : ℝ) := by
    rw [hTdef, Finset.card_image_of_injOn hinj]
  have hXMB : (X : ℝ) ≤ MR * (B : ℝ) := by
    have hlt : X < M * B := by
      rw [hMdef]
      exact (Nat.div_lt_iff_lt_mul (show 0 < B by omega)).1 (Nat.lt_succ_self _)
    have hltR : (X : ℝ) < MR * (B : ℝ) := by
      rw [hMRdef]; exact_mod_cast hlt
    linarith
  refine ⟨B, 2 * (2 * k ^ 3) ^ (a - 1), hkr, hB0, by positivity, hBle, le_refl _, T, ?_,
    ?_, ?_, ?_, ?_⟩
  · -- cardinality
    have hLg0 : (0 : ℝ) < Lg := by linarith
    have hB0R : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB0
    rw [hTcard]
    refine le_trans ?_ hgood
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hre : MR / (4 * Lg) * (8 * (B : ℝ) * Lg) = 2 * (MR * (B : ℝ)) := by
      field_simp; ring
    rw [hre]
    linarith [hXMB]
  · -- range
    intro n hn
    obtain ⟨m, hmG, rfl⟩ := Finset.mem_image.1 (by rwa [hTdef] at hn)
    have hmT0 : m ∈ T0 := (hGmem m hmG).1
    have hmM : m < M := Finset.mem_range.1 (hT0sub hmT0)
    have hmA : m * A ≤ Q * X := by
      have hmle : m ≤ X / B := by rw [hMdef] at hmM; omega
      calc m * A = Q * (m * B) := by rw [hAQB]; ring
        _ ≤ Q * (X / B * B) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmle)
        _ ≤ Q * X := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    have hRQB : R + 1 ≤ Q * B := by rw [hAQB] at hRA; omega
    have hQBX : Q * B ≤ Q * X := Nat.mul_le_mul_left _ hBX
    have hQD : 2 * (Q * X) ≤ 2 * (2 * k ^ 3) ^ (a - 1) * X := by
      have : 2 * (Q * X) = 2 * Q * X := by ring
      rw [this]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hQle)
    refine ⟨by omega, ?_⟩
    have hQX : 1 ≤ Q * X := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  · -- divisor data
    intro n hn j hj hjr
    obtain ⟨m, hmG, rfl⟩ := Finset.mem_image.1 (by rwa [hTdef] at hn)
    exact hkill m j hj hjr
  · -- surviving slot
    intro n hn
    obtain ⟨m, hmG, rfl⟩ := Finset.mem_image.1 (by rwa [hTdef] at hn)
    exact hsurv m (hT0prime m (hGmem m hmG).1)
  · -- base tails
    intro n hn b hb
    obtain ⟨m, hmG, rfl⟩ := Finset.mem_image.1 (by rwa [hTdef] at hn)
    have hfθ : f m ≤ θ := (hGmem m hmG).2
    obtain ⟨h0, hle⟩ := base_tail_le_half_binary_tail (R + m * A) k hb
    refine ⟨h0, lt_of_le_of_lt hle ?_⟩
    have : (∑' t : ℕ, (tau (R + m * A + k + t) : ℝ) / 2 ^ (k + t)) = f m := rfl
    rw [this]
    rw [hθdef] at hfθ
    linarith

/-! ### The §5 all-`N` transfer: the height schedule `X = ⌊N/D_N⌋` -/

/-- The rescaling step of §5: `D_N = 2(2k_N³)^(a-1)`, an upper bound for `2Q`. -/
noncomputable def countD (a X : ℕ) : ℕ := 2 * (2 * (countK X) ^ 3) ^ (a - 1)

/-- `D_N > 0`.  The hypothesis `1 ≤ countK X` is needed, not cosmetic: at `countK X = 0`
and `a > 1` the product `2·(2·0³)^(a-1)` is `0`. -/
theorem countD_pos {a X : ℕ} (hk : 1 ≤ countK X) : 0 < countD a X := by
  rw [countD]
  have h : 0 < 2 * (countK X) ^ 3 := by positivity
  exact Nat.mul_pos (by norm_num) (Nat.pow_pos h)

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
