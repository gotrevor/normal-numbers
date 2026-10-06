/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponentStretch

/-!
# The exponent sets the normal profile: `x` is normal to `3ˢt` iff `t > 3^{s(μ₀−1)}`

Ren, 2026-10-06 (`/create`, after the stretch referee).  The stretch points
`x = cantorExpReal μ₀ ω` are normal to every base prime to 3 and to no power of 3; for bases
`b = 3ˢ t` with `s ≥ 1`, `t > 1`, `3 ∤ t`, nothing was claimed
(`CantorExactExponent.not_isNormal_of_three_dvd_of_small` covers only `2 log₃ b < μ₀`).

**Conjecture (frozen here).**  For rational `μ₀ > 2` and almost every `ω`, `x` is normal to base
`b = 3ˢ t` exactly when `t > 3^{s(μ₀−1)}` (`ProfileOK`).  One formula covers all bases: `s = 0`
gives every base prime to 3, and `t = 1` gives no power of 3.  The threshold is power-invariant
(`b ↦ bᵏ` scales `s` and `log t` alike), as normality must be.  It is never attained, because
`3^{s(μ₀−1)}` is an integer prime to 3 only when it is 1.  Examples at `μ₀ ∈ (2, 2.26)`: normal
to 12, 15 and 21, not normal to 6, 18 or 36.  Base 12 switches off at `μ₀ = 1 + log₃ 4 ≈ 2.26`.

**Mechanism: one window, two sides.**  Let the run be `[a, E)`, `E = ⌈μ₀ a⌉`, and write `L = log₃ t`.
* *Not normal* when `μ₀ > 1 + L/s`.  For `j ≥ a/s`, `bʲ P/3^a ∈ ℤ`, so base-`b` digits
  `j ∈ (a/s, E/log₃ b)` are `0`: a zero run of length `≍ a`.  Its block frequency beats
  `b^{−ℓ}` for every `ℓ` (`not_isNormal_of_not_profileOK`, elementary).
* *Normal* when `μ₀ < 1 + L/s`.  The Fourier coefficient of the coin law at `h·bⁿ` sees only the
  ternary places `[sn, (s+L)n]`, where the digits of `h tⁿ` sit.  A run covers that window iff
  `sn ≥ a` and `(s+L)n ≤ μ₀ a`, which is possible iff `μ₀ > 1 + L/s`.  Below the threshold every
  window keeps `≥ a(1 − μ₀ s/(s+L))` free places, linear in `n`, so the Cassels–Schmidt second moment
  (`CantorLiouvilleAll.secondMoment_le_b`, with the orbit of `t` mod `3ᵏ` in place of `b`)
  should go through.  This is `ae_isNormal_of_profileOK` (open node).

So the threshold where the Fourier side breaks is the same threshold where the explicit zero
runs appear.  Known-false sibling: `t = 1` (powers of 3).  There the frequencies' digits are a fixed
word shifted, with no orbit to average over, and the mechanism correctly gives nothing.

Prior art (one search, 2026-10-06): Schmidt (1960) gives sets of normal bases closed under
multiplicative dependence; Becher–Slaman give prescribed simple-normality profiles outside `K`.
We found no profile for points of `K` that depends on the exponent.
-/

open MeasureTheory Filter

namespace NormalNumbers.CantorExactExponentProfile

open CantorLiouville CantorExactExponent CantorExpGeneric Derandomize CantorExactExponentStretch

/-- The profile condition for `b = 3ˢ t` (`s = v₃ b`, `t = b / 3ˢ`): `3^{s(μ₀−1)} < t`. -/
def ProfileOK (μ₀ : ℚ) (b : ℕ) : Prop :=
  (3 : ℝ) ^ ((padicValNat 3 b : ℝ) * ((μ₀ : ℝ) - 1)) < ((b / 3 ^ padicValNat 3 b : ℕ) : ℝ)

/-- Bases prime to 3 always pass. -/
theorem profileOK_of_not_dvd (μ₀ : ℚ) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) : ProfileOK μ₀ b := by
  unfold ProfileOK
  rw [padicValNat.eq_zero_of_not_dvd h3]
  simp only [CharP.cast_eq_zero, zero_mul, Real.rpow_zero, pow_zero, Nat.div_one]
  exact_mod_cast hb

/-- Powers of 3 never pass (for `μ₀ ≥ 1`). -/
theorem not_profileOK_three_pow (μ₀ : ℚ) (hμ : 1 ≤ μ₀) (s : ℕ) : ¬ ProfileOK μ₀ (3 ^ s) := by
  unfold ProfileOK
  rw [padicValNat.prime_pow (p := 3) s, Nat.div_self (by positivity)]
  push Not
  have : (0 : ℝ) ≤ (s : ℝ) * ((μ₀ : ℝ) - 1) := by
    have : (1 : ℝ) ≤ μ₀ := by exact_mod_cast hμ
    positivity
  simpa using Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) this

/-- **Block lemma.**  On a run, once `3^a ∣ bʲ`, the orbit point `{bʲx}` lies in `[0, b^{−ℓ})`. -/
theorem fract_lt_of_run_block {μ₀ : ℚ} (hμ : 1 < μ₀) (ω : ℕ → Bool) {b s : ℕ} (hb : 2 ≤ b)
    (hs : 3 ^ s ∣ b) {k j ℓ : ℕ} (hj1 : expRunStart μ₀ k ≤ s * j)
    (hj2 : b ^ (j + ℓ + 1) ≤ 3 ^ expRunEnd μ₀ (expRunStart μ₀ k)) :
    Int.fract (cantorExpReal μ₀ ω * (b : ℝ) ^ j) < 1 / (b : ℝ) ^ ℓ := by
  set A := expRunStart μ₀ k
  set T := expRunEnd μ₀ A
  set t := tl (expFree μ₀) ω T
  have hx : cantorExpReal μ₀ ω = (hd (expFree μ₀) ω A : ℝ) / 3 ^ A + t :=
    cantorExpReal_trunc hμ ω k
  have ht0 : 0 ≤ t := tl_nonneg _ _ _
  have ht1 : t ≤ 1 / 3 ^ T := tl_le _ _ _
  obtain ⟨q, hq⟩ : 3 ^ A ∣ b ^ j := by
    refine (pow_dvd_pow 3 hj1).trans ?_
    rw [pow_mul]; exact pow_dvd_pow_of_dvd hs j
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbj : (b : ℝ) ^ j = 3 ^ A * q := by exact_mod_cast hq
  have heq : cantorExpReal μ₀ ω * (b : ℝ) ^ j =
      (((hd (expFree μ₀) ω A * q : ℕ) : ℤ) : ℝ) + t * (b : ℝ) ^ j := by
    rw [hx, add_mul, hbj]; push_cast; field_simp
  have hT : (b : ℝ) ^ (j + ℓ + 1) ≤ 3 ^ T := by exact_mod_cast hj2
  have h3T : (0 : ℝ) < 3 ^ T := by positivity
  have hbl : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have hlt : t * (b : ℝ) ^ j < 1 / (b : ℝ) ^ ℓ := by
    have hbj2 : (b : ℝ) ^ j * ((b : ℝ) ^ ℓ * b) ≤ 3 ^ T := by
      rw [← pow_succ, ← pow_add, ← add_assoc]; exact hT
    have hbj0 : (0 : ℝ) ≤ (b : ℝ) ^ j := by positivity
    calc t * (b : ℝ) ^ j ≤ 1 / 3 ^ T * (b : ℝ) ^ j := by gcongr
      _ ≤ 1 / 3 ^ T * (3 ^ T / ((b : ℝ) ^ ℓ * b)) := by
          gcongr; rw [le_div_iff₀ (by positivity)]; exact hbj2
      _ = 1 / ((b : ℝ) ^ ℓ * b) := by field_simp
      _ < 1 / (b : ℝ) ^ ℓ := by
          apply one_div_lt_one_div_of_lt hbl; nlinarith
  have h0 : 0 ≤ t * (b : ℝ) ^ j := by positivity
  rw [heq, Int.fract_intCast_add, Int.fract_eq_self.2 ⟨h0, hlt.trans_le ?_⟩]
  · exact hlt
  · rw [div_le_one hbl]; exact one_le_pow₀ (by linarith)

/-- `3^{s(μ₀−1)}` is never an integer prime to 3 when `s ≥ 1`, `μ₀ > 1`. -/
theorem ne_rpow_of_not_dvd {μ₀ : ℚ} (hμ : 1 < μ₀) {s t : ℕ} (hs : 1 ≤ s) (ht : ¬ 3 ∣ t) :
    (t : ℝ) ≠ (3 : ℝ) ^ ((s : ℝ) * ((μ₀ : ℝ) - 1)) := by
  intro h
  set q := μ₀.den
  have hq : (μ₀ : ℝ) * q = μ₀.num := by exact_mod_cast Rat.mul_den_eq_num μ₀
  have hnum : (q : ℤ) < μ₀.num := by
    have h1 : (1 : ℚ) * q < μ₀ * q := by
      exact mul_lt_mul_of_pos_right hμ (by exact_mod_cast μ₀.den_pos)
    rw [Rat.mul_den_eq_num, one_mul] at h1; exact_mod_cast h1
  set p : ℕ := s * (μ₀.num - q).toNat
  have hp : ((s : ℝ) * ((μ₀ : ℝ) - 1)) * q = (p : ℝ) := by
    have : ((μ₀.num - q).toNat : ℤ) = μ₀.num - q := Int.toNat_of_nonneg (by omega)
    have : (((μ₀.num - q).toNat : ℕ) : ℝ) = (μ₀.num : ℝ) - q := by exact_mod_cast this
    simp only [p]; push_cast; rw [this, ← hq]; ring
  have hpow : (t : ℝ) ^ q = (3 : ℝ) ^ p := by
    rw [h, ← Real.rpow_mul_natCast (by norm_num), hp, Real.rpow_natCast]
  have hN : t ^ q = 3 ^ p := by exact_mod_cast hpow
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (by
    simp only [p]; apply mul_ne_zero (by omega); omega)
  have : 3 ∣ t ^ q := by rw [hN]; exact dvd_pow_self 3 (by omega)
  exact ht (Nat.prime_three.dvd_of_dvd_pow this)

/-- **Not normal past the threshold, for every `ω`.**  Confidence 90%.

English proof.  Let `s = v₃ b ≥ 1` (if `s = 0` then `ProfileOK` holds), `b = 3ˢt`, and
`θ = log₃ b / s`; `¬ ProfileOK` with `t ≠ 3^{s(μ₀−1)}` gives `θ < μ₀`.  Along run `k`
(`a = a_k`, `E = ⌈μ₀ a⌉`), `x = P/3^a + ε` with `0 ≤ ε < 3^{−E}`.  For `j ≥ ⌈a/s⌉`,
`bʲP/3^a ∈ ℤ`, so `{bʲx} = bʲε < b^{j}3^{−E}`, and the base-`b` digit `j + 1` is `0` whenever
`b^{j+1} ≤ 3^E`.  So the digits on `(⌈a/s⌉, ⌊E/log₃ b⌋)` vanish, a run of length
`≥ a(μ₀/log₃ b − 1/s) − 2 = c·N`, `c = 1 − θ/μ₀ > 0`, ending at `N = E/log₃ b`.  For any `ℓ`
with `b^{−ℓ} < c/2`, the block `0^ℓ` then has frequency `≥ c/2` at `N`, infinitely often,
contradicting normality.  The `ℓ = 1` case of this argument is `not_isNormal_of_three_dvd_of_small`. -/
theorem not_isNormal_of_not_profileOK (μ₀ : ℚ) (hμ : 1 < μ₀) (ω : ℕ → Bool) {b : ℕ}
    (hb : 2 ≤ b) (hP : ¬ ProfileOK μ₀ b) : ¬ IsNormal b (cantorExpReal μ₀ ω) := by
  intro hn
  rw [isNormal_iff_equidistributed_orbit b hb] at hn
  by_cases h3 : 3 ∣ b
  swap; · exact hP (profileOK_of_not_dvd μ₀ hb h3)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set s := padicValNat 3 b with hs_def
  set t := b / 3 ^ s with ht_def
  have hs1 : 1 ≤ s := one_le_padicValNat_of_dvd (by omega) h3
  have hsd : 3 ^ s ∣ b := pow_padicValNat_dvd
  have hbt : b = 3 ^ s * t := (Nat.mul_div_cancel' hsd).symm
  have ht3 : ¬ 3 ∣ t := by
    intro h
    have h' : 3 ^ (s + 1) ∣ 3 ^ s * t := by rw [pow_succ]; exact Nat.mul_dvd_mul_left (3 ^ s) h
    rw [← hbt] at h'
    exact pow_succ_padicValNat_not_dvd (by omega) h'
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, mul_zero] at hbt; omega
    · exact h
  have hμR : (1 : ℝ) < μ₀ := by exact_mod_cast hμ
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have htlt : (t : ℝ) < (3 : ℝ) ^ ((s : ℝ) * ((μ₀ : ℝ) - 1)) := by
    unfold ProfileOK at hP; push Not at hP
    exact lt_of_le_of_ne hP (ne_rpow_of_not_dvd hμ hs1 ht3)
  set L := Real.logb 3 b with hL_def
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlb : 0 < Real.log b := Real.log_pos (by linarith)
  have hL0 : 0 < L := Real.logb_pos (by norm_num) (by linarith)
  have hLlt : L < s * μ₀ := by
    have h1 : Real.logb 3 t < (s : ℝ) * ((μ₀ : ℝ) - 1) :=
      (Real.logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast htpos)).2 htlt
    have h2 : L = s + Real.logb 3 t := by
      rw [hL_def, hbt]; push_cast
      rw [Real.logb_mul (by positivity) (by exact_mod_cast htpos.ne'), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num), mul_one]
    rw [h2]; nlinarith
  set c := 1 - L / (s * μ₀) with hc_def
  have hsμ : 0 < (s : ℝ) * μ₀ := by positivity
  have hc0 : 0 < c := by rw [hc_def, sub_pos, div_lt_one hsμ]; exact hLlt
  obtain ⟨ℓ, hℓ⟩ := exists_pow_lt_of_lt_one (half_pos hc0)
    (show (1 : ℝ) / b < 1 by rw [div_lt_one (by linarith)]; linarith)
  rw [one_div_pow] at hℓ
  have hbl : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have hI := hn 0 (1 / (b : ℝ) ^ ℓ) le_rfl (by positivity)
    (by rw [div_le_one hbl]; exact one_le_pow₀ (by linarith))
  rw [sub_zero] at hI
  have hlt : 1 / (b : ℝ) ^ ℓ < 3 * c / 4 := by linarith
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hI.eventually (gt_mem_nhds hlt))
  obtain ⟨K, hK⟩ := exists_nat_gt (L * (4 * (ℓ + 3) / c + N0 + 1))
  set k := K
  set A := expRunStart μ₀ k
  set T := expRunEnd μ₀ A
  set n := Nat.log b (3 ^ T)
  have hkA := lt_expRunStart hμ k
  have hlog : 3 ^ T < b ^ (n + 1) := Nat.lt_pow_succ_log_self (by omega) _
  have hpow : b ^ n ≤ 3 ^ T := Nat.pow_log_le_self b (by positivity)
  have hTn : (T : ℝ) < (n + 1) * L := by
    have h1 : (T : ℝ) * Real.log 3 < (n + 1) * Real.log b := by
      have : ((3 ^ T : ℕ) : ℝ) < ((b ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast hlog
      have := Real.log_lt_log (by positivity) this
      push_cast at this; rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
    rw [hL_def, Real.logb, mul_div_assoc', lt_div_iff₀ hl3]; exact h1
  have hTA : (μ₀ : ℝ) * A ≤ T := expRunEnd_ge_r μ₀ A
  have hkAR : (k : ℝ) < A := by exact_mod_cast hkA
  have hA0 : (0 : ℝ) ≤ A := by positivity
  -- `A / s ≤ (n+1)(1-c)`
  have hAs : (A : ℝ) / s ≤ (n + 1) * (1 - c) := by
    rw [hc_def, sub_sub_cancel, div_le_iff₀ (by linarith)]
    have : (n + 1) * (L / (s * μ₀)) * s = (n + 1) * L / μ₀ := by field_simp
    rw [this, le_div_iff₀ (by linarith)]; nlinarith
  -- `n` is large
  have hnbig : 4 * (ℓ + 3) / c + N0 < n := by
    have : (k : ℝ) < (n + 1) * L := by nlinarith
    have h2 : L * (4 * (ℓ + 3) / c + N0 + 1) < (n + 1) * L := by
      have : (K : ℝ) = k := rfl
      linarith
    nlinarith
  have hnN0 : N0 ≤ n := by
    have : (N0 : ℝ) < n := by
      have : 0 ≤ 4 * (ℓ + 3) / c := by positivity
      linarith
    exact_mod_cast this.le
  have hcn : 4 * (ℓ + 3) < c * n := by
    have : 4 * (ℓ + 3) / c < n := by
      have : (0 : ℝ) ≤ N0 := by positivity
      linarith
    rw [div_lt_iff₀ hc0] at this; linarith
  set J0 := A / s + 1
  have hJ0 : (J0 : ℝ) ≤ A / s + 1 := by
    simp only [J0]; push_cast; gcongr; exact Nat.cast_div_le
  have hvis : n - ℓ - 1 - J0 ≤ visitCount (orbit b (cantorExpReal μ₀ ω)) 0 (1 / (b : ℝ) ^ ℓ) n := by
    unfold visitCount
    have : Finset.Ico J0 (n - ℓ - 1) ⊆ (Finset.range n).filter
        (fun j => orbit b (cantorExpReal μ₀ ω) j ∈ Set.Ico 0 (1 / (b : ℝ) ^ ℓ)) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico, orbit]
      refine ⟨by omega, Int.fract_nonneg _, fract_lt_of_run_block (k := k) hμ ω hb hsd ?_ ?_⟩
      · have := Nat.lt_div_mul_add (a := A) (show 0 < s by omega)
        have h2 : s * J0 ≤ s * j := Nat.mul_le_mul_left _ hj.1
        have h3 : s * J0 = A / s * s + s := by rw [mul_add, mul_one, mul_comm]
        omega
      · exact (Nat.pow_le_pow_right (by omega) (by omega)).trans hpow
    simpa using Finset.card_le_card this
  have hcnt : (n : ℝ) - ℓ - 1 - J0 ≤ visitCount (orbit b (cantorExpReal μ₀ ω)) 0 (1 / (b : ℝ) ^ ℓ) n := by
    have h1 : ((n - ℓ - 1 - J0 : ℕ) : ℝ) ≤ visitCount (orbit b (cantorExpReal μ₀ ω)) 0 (1 / (b : ℝ) ^ ℓ) n := by
      exact_mod_cast hvis
    have h2 : (n : ℝ) ≤ ((n - ℓ - 1 - J0 : ℕ) : ℝ) + ℓ + 1 + J0 := by
      have : n ≤ (n - ℓ - 1 - J0) + ℓ + 1 + J0 := by omega
      exact_mod_cast this
    linarith
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℝ) ≤ 4 * (ℓ + 3) / c := by positivity
    have : (0 : ℝ) ≤ N0 := by positivity
    linarith
  have := hN0 n hnN0
  rw [div_lt_iff₀ hnpos] at this
  have hc1 : c ≤ 1 := by
    rw [hc_def]; have : 0 ≤ L / (s * μ₀) := by positivity
    linarith
  nlinarith

/-! ## The crux: what the window sees (2026-10-06 lap 1)

The kickoff's port of `CantorLiouvilleAll.secondMoment_le_b` controls the ternary digits of
`h(bᵈ−1)tᵐ` mod `3ʲ` with `3ʲ ≤ N`, i.e. the *low* `O(log N)` digits, through the orbit of `t`.
For `m` in the **shadow** of a run (`a ≤ sm < E`), the places `[sm, E)` are forced, so the
Fourier coefficient sees only digits of `h(bᵈ−1)tᵐ` at relative positions `≥ E − sm`, which is
linear in `N` for most shadow `m`.  No orbit mod `3ʲ` with `3ʲ ≤ N` reaches them
(`t^{m₀+3^{r−v}i}` moves digit `r` only along steps `3^{r−v} ≫ N`).  The shadow is a positive
fraction of `[0, E/s)` (`shadow_card_ge`), so the trivial bound on it contributes `O(1)` per run
to the Davenport–Erdős–LeVeque sum, which diverges.  The digits that remain controllable are
the *top* ones, set by `{m log₃ t}`; with a power discrepancy bound (`LogDiscrepancy`, from
Baker's theorem) the top `ε log N` digits suffice, and they are free because
`(s+L)m > μ₀ a` below the threshold (`window_covered_imp`). -/

/-- **Window lemma.**  A run `[a, μ₀a]` covers the frequency window `[sm, (s+L)m]` only past
the threshold `μ₀ ≥ 1 + L/s`. -/
theorem window_covered_imp {s m a L μ₀ : ℝ} (hs : 0 < s) (hm : 0 < m) (hL : 0 ≤ L) (ha : 0 < a)
    (h1 : a ≤ s * m) (h2 : (s + L) * m ≤ μ₀ * a) : 1 + L / s ≤ μ₀ := by
  have hμ : 0 ≤ μ₀ := by
    by_contra h; push Not at h; nlinarith
  have : (s + L) * m ≤ μ₀ * (s * m) := h2.trans (mul_le_mul_of_nonneg_left h1 hμ)
  rw [show 1 + L / s = (s + L) / s by field_simp, div_le_iff₀ hs]
  nlinarith

/-- **The shadow is a positive fraction.**  Among `m < E/s` (where the frequencies `bᵐ` reach the
run end), those with `a ≤ sm` (window start inside or past the run start) number at least
`E/s − a/s − 1`; with `E ≥ μ₀ a` this is `≥ (1 − 1/μ₀)·E/s − 1`. -/
theorem shadow_card_ge (s a E : ℕ) (hs : 0 < s) :
    E / s - a / s - 1 ≤ ((Finset.range (E / s)).filter (fun m => a ≤ s * m)).card := by
  have : Finset.Ico (a / s + 1) (E / s) ⊆ (Finset.range (E / s)).filter (fun m => a ≤ s * m) := by
    intro m hm
    simp only [Finset.mem_Ico] at hm
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hm.2, ?_⟩
    have := Nat.lt_div_mul_add (a := a) hs
    have h2 : s * (a / s + 1) ≤ s * m := Nat.mul_le_mul_left _ hm.1
    have h3 : s * (a / s + 1) = a / s * s + s := by rw [mul_add, mul_one, mul_comm]
    omega
  have := Finset.card_le_card this
  simp at this; omega

/-- **Reopen condition: power discrepancy of `{m log₃ t + β}`**, uniformly in the shift `β`. -/
def LogDiscrepancy (t : ℕ) : Prop :=
  ∃ C κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 1 ≤ N → ∀ β u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 →
    |(visitCount (fun m => Int.fract (m * Real.logb 3 t + β)) u v N : ℝ) - N * (v - u)| ≤
      C * (N : ℝ) ^ (1 - κ)

/-- **Literature (Baker 1966; Baker–Wüstholz 1993, with Erdős–Turán).**  For `t ≥ 2` prime to 3,
`|q log t − p log 3| ≥ q^{−C}` (effective linear forms in two logarithms), hence a power
discrepancy bound for `{m log₃ t + β}`, uniform in `β` (Erdős–Turán with `H = N^κ`).  Faithful
or weaker: the transcription asks only for some `κ > 0`. -/
def Literature.BakerLogDiscrepancy : Prop :=
  ∀ t : ℕ, 2 ≤ t → ¬ 3 ∣ t → LogDiscrepancy t

/-- Power savings are summable along `CantorLiouville.sched` (`sched j ≥ e^{√j}`). -/
theorem summable_sched_rpow {δ : ℝ} (hδ : 0 < δ) :
    Summable fun j => ((sched j : ℕ) : ℝ) ^ (-δ) := by
  have hB := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (ev_log_le (r := 1 / 2) (ε := δ / 2)
    (by norm_num) (by positivity))
  refine Summable.of_norm_bounded_eventually summable_inv_sq_nat ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hB, eventually_ge_atTop 1] with j hjB hj1
  have hs : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hs.le _), ← exp_neg_two_log j hj1]
  calc (sched j : ℝ) ^ (-δ) ≤ (Real.exp (Real.sqrt j)) ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (exp_sqrt_le_sched j hj1) (by linarith)
    _ = Real.exp (-(δ * Real.sqrt j)) := by rw [← Real.exp_mul]; ring_nf
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        rw [Real.sqrt_eq_rpow]; nlinarith

/-- **Power-saving second moment for `3 ∣ b` below the threshold**, given the Baker input.
Confidence 60%.  This is the analytic core of `ae_isNormal_of_profileOK_of_baker`; the English
proof is in that docstring (non-shadow `m` by the orbit of `t`, shadow `m` by top digits). -/
theorem secondMoment_le_profile (hB : Literature.BakerLogDiscrepancy) (μ₀ : ℚ) (hμ : 2 < μ₀)
    {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) (hP : ProfileOK μ₀ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ ω, ‖∑ k ∈ Finset.range N, DecayAeNormal.ee (h * (b : ℝ) ^ k * pt (expFree μ₀) ω)‖ ^ 2
        ∂ExplicitSquare.coinMeasure ≤ C * (N : ℝ) ^ (2 - δ) := by
  sorry

/-- **The crux, conditional on the top-digit input.**  Confidence 60%.  English proof: split the
pair sum by `m`.  Outside every shadow, the window `[sm, sm + log₃N/2)` is free and the orbit
count of `sum_Hf_le_b` (with `t`) applies.  In the shadow, use the top `ε log N` digits of
`h(bᵈ−1)tᵐ`, which sit at free places because `(s+L)m > μ₀a` (`window_covered_imp`) and are
fixed by `{(m+d) log₃ t + β_{h,d}}`; `LogDiscrepancy` bounds the number of `m` whose top digits
are degenerate by `N(2/3)^{εlog N} + C N^{1−κ} 3^{ε log N}`, a power saving for small `ε`.
Then `ae_isNormal_of_secondMoment` along `CantorLiouville.sched`. -/
theorem ae_isNormal_of_profileOK_of_baker (hB : Literature.BakerLogDiscrepancy) (μ₀ : ℚ)
    (hμ : 2 < μ₀) :
    ∀ᵐ ω ∂coins, ∀ b : ℕ, 2 ≤ b → ProfileOK μ₀ b → IsNormal b (cantorExpReal μ₀ ω) := by
  have h1 : (1 : ℚ) < μ₀ := by linarith
  have hthree : ∀ᵐ ω ∂coins, ∀ b : ℕ, 2 ≤ b → 3 ∣ b →
      ProfileOK μ₀ b → IsNormal b (cantorExpReal μ₀ ω) := by
    rw [ae_all_iff]
    intro b
    by_cases hb : 2 ≤ b
    swap; · exact Eventually.of_forall fun _ h => absurd h hb
    by_cases h3 : 3 ∣ b
    swap; · exact Eventually.of_forall fun _ _ h => absurd h h3
    by_cases hPb : ProfileOK μ₀ b
    swap; · exact Eventually.of_forall fun _ _ _ h => absurd h hPb
    have : ∀ᵐ ω ∂coins, IsNormal b (cantorExpReal μ₀ ω) := by
      rw [coins_eq_coinMeasure]
      refine CantorLiouvilleAll.ae_isNormal_of_secondMoment ExplicitSquare.coinMeasure hb _
        (measurable_pt (expFree μ₀)) sched sched_strictMono sched_ratio ?_
      intro h hh
      obtain ⟨C, δ, hδ, hC⟩ := secondMoment_le_profile hB μ₀ hμ hb h3 hPb h hh
      refine ((summable_sched_rpow hδ).mul_left (max C 0)).of_nonneg_of_le
        (fun j => div_nonneg (integral_nonneg fun ω => by positivity) (by positivity)) (fun j => ?_)
      have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
      rw [div_le_iff₀ (by positivity)]
      calc _ ≤ C * (sched j : ℝ) ^ (2 - δ) := hC _ (one_le_sched j)
        _ ≤ max C 0 * (sched j : ℝ) ^ (2 - δ) := by gcongr; exact le_max_left _ _
        _ = _ := by
          rw [mul_assoc, ← Real.rpow_natCast _ 2, ← Real.rpow_add hN]; congr 2; push_cast; ring
    exact this.mono fun _ h _ _ _ => h
  filter_upwards [ae_isNormal_of_coprime_three μ₀ h1, hthree] with ω hω1 hω2 b hb hPb
  by_cases h3 : 3 ∣ b
  · exact hω2 b hb h3 hPb
  · exact hω1 b hb h3

/-- **Normal below the threshold, a.e.**  Open node; confidence 70% true, but the elementary route
below is BLOCKED in the shadow (see `shadow_card_ge`, Maze row "elementary orbit port to 3 ∣ b");
the live route is `ae_isNormal_of_profileOK_of_baker` plus a proof of `LogDiscrepancy`.

English proof (sketch).  For `3 ∤ b` this is `ae_isNormal_of_coprime_three`.  Let `b = 3ˢt` with
`s ≥ 1`, `t > 3^{s(μ₀−1)}`, `L = log₃ t`.
1. *Window.*  In the coin law, the Fourier coefficient at `ξ = h·bᵐ·(bᵈ − 1)` (the pair terms
   of the second moment; `bᵈ − 1` is prime to 3) is a product of `|cos(2πξ/3^{p+1})|` over
   the free places `p`.  Factors with `p + 1 ≤ sm` are 1, and so are factors with `p` beyond the
   top digit of `ξ`.  The window is `[sm, (s+L)m + d log₃ b + O(log |h|)]`.
2. *Free count.*  A run `[a, μ₀a)` covers `[sm, (s+L)m]` only if `μ₀ > 1 + L/s`.  Below the
   threshold, the free places in the window number at least `a(1 − μ₀ s/(s+L)) − O(1)` for the
   worst run, which is linear in `m`.  Earlier runs are negligible because `a_{k+1}/a_k → ∞`.
3. *Digit changes.*  The ternary digits of `ξ` on the window are those of `h(bᵈ−1)tᵐ` shifted
   by `sm`.  As `m` varies, `tᵐ mod 3ᵏ` runs through a subgroup of index `≤ 3^{v₃(t²−1)}`
   (`padicValNat_pow_sub_one_le` for `t`), so the counting of
   `CantorLiouvilleAll.sum_Hf_le_b` applies with `t` in place of `b`.  This gives a summable
   second moment along `CantorLiouville.sched`, and `ae_isNormal_of_secondMoment` concludes.

Sibling check: for `t = 1` step 3 has a trivial orbit, and the frequencies' digits are one word
shifted.  The argument stops there, as it must, since `x` is never normal to a power of 3. -/
theorem ae_isNormal_of_profileOK (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∀ᵐ ω ∂coins, ∀ b : ℕ, 2 ≤ b → ProfileOK μ₀ b → IsNormal b (cantorExpReal μ₀ ω) := by
  sorry

/-- **Headline: the exponent sets the normal profile.**  For every rational `μ₀ > 2` there is a
computable `x ∈ K` with irrationality exponent exactly `μ₀` such that, for every base `b ≥ 2`,
`x` is normal to `b` iff `b = 3ˢt` with `t > 3^{s(μ₀−1)}`.  Confidence 65% (the node above, plus
the derandomizer taking the extra bases: `exists_computable_normal_avoid`'s test family must
include the `3 ∣ b` second moments). -/
theorem exists_computable_mem_cantorSet_irrExponent_normalProfile (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∃ e : ℕ → Bool, Computable e ∧ cantorExpReal μ₀ e ∈ cantorSet ∧
      HasIrrExponent (cantorExpReal μ₀ e) μ₀ ∧
      ∀ b : ℕ, 2 ≤ b → (IsNormal b (cantorExpReal μ₀ e) ↔ ProfileOK μ₀ b) := by
  sorry

end NormalNumbers.CantorExactExponentProfile
