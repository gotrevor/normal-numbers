import NormalNumbers.G4WiringSparse
import NormalNumbers.PrimeModelRadical

/-!
# Prime model, assembly part A: complex phase algebra

Elementary complex-number and real inequalities used by the end-to-end assembly of the
frozen `KMT_quant₂` (`papers/prime-model-assembly-2026-09-22.md`).  Nothing here is
arithmetic: these are the inequalities behind E1 (restoring primes above `y`) and E5 (the
model phase contracts, uniformly in the frequency `h`).

* `norm_one_add_le_exp` : `|1+w| ≤ exp(Re w + |w|²/2)` for every `w ∈ ℂ` (global; no `|w|<1`).
* `norm_prod_sub_prod_le` : `|∏ a − ∏ b| ≤ ∑ |a − b|` for `1`-bounded factors.
* `norm_pow_sub_pow_le` : `|z^{a+c} − z^a| ≤ 2c` for `|z| = 1`.
* `sum_inv_sq_le` : distinct naturals `> k` have `∑ 1/n² ≤ 1/k`.
* `exists_site_re_nonpos` : the least nontrivial window site has `Re z ≤ 0` (the site phase is
  `e(m/4)` with `4 ∤ m`).
* `model_phase_norm_le` : `‖∏_i (1 + A/p_i)‖ ≤ e^{2k} exp(−∑_i 1/p_i)` when `Re A ≤ −1`, `|A| ≤ 2k`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.PhaseAlgebra

open NormalNumbers.G4 NormalNumbers.G4Sparse

/-- `|1+w|² = 1 + (2 Re w + |w|²) ≤ exp(2 Re w + |w|²)`; take square roots. -/
theorem norm_one_add_le_exp (w : ℂ) : ‖1 + w‖ ≤ Real.exp (w.re + ‖w‖ ^ 2 / 2) := by
  have hsq : ‖1 + w‖ ^ 2 = 1 + (2 * w.re + ‖w‖ ^ 2) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hexp : (Real.exp (w.re + ‖w‖ ^ 2 / 2)) ^ 2 = Real.exp (2 * w.re + ‖w‖ ^ 2) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hkey : ‖1 + w‖ ^ 2 ≤ (Real.exp (w.re + ‖w‖ ^ 2 / 2)) ^ 2 := by
    rw [hsq, hexp]
    have := Real.add_one_le_exp (2 * w.re + ‖w‖ ^ 2)
    linarith
  have h2 := Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (Real.exp_nonneg _)] at h2

/-- Telescoping: `|∏ a − ∏ b| ≤ ∑ |a − b|` when every factor has norm `≤ 1`. -/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  revert ha hb
  refine Finset.induction_on s ?_ ?_
  · intro _ _; simp
  · intro x t hx ih ha hb
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx]
    have hax : ‖a x‖ ≤ 1 := ha x (Finset.mem_insert_self _ _)
    have hBt : ‖∏ i ∈ t, b i‖ ≤ 1 := by
      rw [Complex.norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _)
        (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have ihd : ‖∏ i ∈ t, a i - ∏ i ∈ t, b i‖ ≤ ∑ i ∈ t, ‖a i - b i‖ :=
      ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
        (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have hsplit : a x * ∏ i ∈ t, a i - b x * ∏ i ∈ t, b i
        = a x * (∏ i ∈ t, a i - ∏ i ∈ t, b i) + (a x - b x) * ∏ i ∈ t, b i := by ring
    rw [hsplit]
    have h1 : ‖a x * (∏ i ∈ t, a i - ∏ i ∈ t, b i) + (a x - b x) * ∏ i ∈ t, b i‖
        ≤ ‖a x‖ * ‖∏ i ∈ t, a i - ∏ i ∈ t, b i‖ + ‖a x - b x‖ * ‖∏ i ∈ t, b i‖ := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul]
    have h2 : ‖a x‖ * ‖∏ i ∈ t, a i - ∏ i ∈ t, b i‖ ≤ ∑ i ∈ t, ‖a i - b i‖ := by
      calc ‖a x‖ * ‖∏ i ∈ t, a i - ∏ i ∈ t, b i‖
          ≤ 1 * ‖∏ i ∈ t, a i - ∏ i ∈ t, b i‖ := by
            exact mul_le_mul_of_nonneg_right hax (norm_nonneg _)
        _ = ‖∏ i ∈ t, a i - ∏ i ∈ t, b i‖ := one_mul _
        _ ≤ ∑ i ∈ t, ‖a i - b i‖ := ihd
    have h3 : ‖a x - b x‖ * ‖∏ i ∈ t, b i‖ ≤ ‖a x - b x‖ := by
      calc ‖a x - b x‖ * ‖∏ i ∈ t, b i‖ ≤ ‖a x - b x‖ * 1 :=
            mul_le_mul_of_nonneg_left hBt (norm_nonneg _)
        _ = ‖a x - b x‖ := mul_one _
    linarith

/-- `|z^c − 1| ≤ c |z − 1|` for `|z| = 1`. -/
theorem norm_pow_sub_one_le (z : ℂ) (hz : ‖z‖ = 1) (c : ℕ) :
    ‖z ^ c - 1‖ ≤ c * ‖z - 1‖ := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hrw : z ^ (c + 1) - 1 = z * (z ^ c - 1) + (z - 1) := by ring
    rw [hrw]
    have h1 : ‖z * (z ^ c - 1) + (z - 1)‖ ≤ ‖z ^ c - 1‖ + ‖z - 1‖ := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, hz, one_mul]
    have h2 : ((c : ℝ) + 1) * ‖z - 1‖ = (c : ℝ) * ‖z - 1‖ + ‖z - 1‖ := by ring
    push_cast
    rw [h2]
    linarith

/-- `|z^{a+c} − z^a| ≤ 2c` for `|z| = 1`. -/
theorem norm_pow_sub_pow_le (z : ℂ) (hz : ‖z‖ = 1) (a c : ℕ) :
    ‖z ^ (a + c) - z ^ a‖ ≤ 2 * c := by
  have hrw : z ^ (a + c) - z ^ a = z ^ a * (z ^ c - 1) := by ring
  rw [hrw, norm_mul, norm_pow, hz, one_pow, one_mul]
  have h2 : ‖z - 1‖ ≤ 2 := by
    calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hz]; norm_num
  have h3 := norm_pow_sub_one_le z hz c
  have hc : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  nlinarith

/-- Distinct naturals exceeding `k ≥ 1` have `∑ 1/n² ≤ ∑_{n>k} 1/(n(n−1)) = 1/k`. -/
theorem sum_inv_sq_le {ι : Type*} [Fintype ι] (p : ι → ℕ) (hinj : Function.Injective p)
    {k : ℕ} (hk : 1 ≤ k) (hkp : ∀ i, k < p i) :
    ∑ i, (1 : ℝ) / ((p i : ℝ) ^ 2) ≤ 1 / k := by
  classical
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  -- telescoping bound over `Ioc k M`
  have tel : ∀ M : ℕ, k ≤ M → ∑ n ∈ Finset.Ioc k M, (1 : ℝ) / ((n : ℝ) ^ 2)
      ≤ 1 / (k : ℝ) - 1 / (M : ℝ) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [Finset.sum_Ioc_succ_top hM]
      have hMR : (1 : ℝ) ≤ (M : ℝ) := le_trans hkR (by exact_mod_cast hM)
      have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
      have hM10 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
      have key : (1 : ℝ) / ((M : ℝ) + 1) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M : ℝ) + 1) := by
        have hid : (1 : ℝ) / (M : ℝ) - 1 / ((M : ℝ) + 1) = 1 / ((M : ℝ) * ((M : ℝ) + 1)) := by
          field_simp
          ring
        rw [hid]
        refine one_div_le_one_div_of_le (by positivity) ?_
        nlinarith
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith
  -- transfer to the image finset
  set s : Finset ℕ := Finset.image p Finset.univ with hs
  have hsum : ∑ i, (1 : ℝ) / ((p i : ℝ) ^ 2) = ∑ n ∈ s, (1 : ℝ) / ((n : ℝ) ^ 2) := by
    rw [hs, Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
  rw [hsum]
  rcases Finset.eq_empty_or_nonempty s with hempty | hne
  · rw [hempty]
    simp only [Finset.sum_empty]
    positivity
  · set M : ℕ := s.max' hne with hM
    have hMs : M ∈ s := s.max'_mem hne
    have hmem : ∀ n ∈ s, k < n ∧ n ≤ M := by
      intro n hn
      refine ⟨?_, s.le_max' n hn⟩
      rw [hs, Finset.mem_image] at hn
      obtain ⟨i, -, rfl⟩ := hn
      exact hkp i
    have hkM : k ≤ M := le_of_lt (hmem M hMs).1
    have hsub : s ⊆ Finset.Ioc k M := by
      intro n hn
      exact Finset.mem_Ioc.mpr (hmem n hn)
    have hstep : ∑ n ∈ s, (1 : ℝ) / ((n : ℝ) ^ 2)
        ≤ ∑ n ∈ Finset.Ioc k M, (1 : ℝ) / ((n : ℝ) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    have hfin := tel M hkM
    have hMnn : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith

/-- The site phases of the window: site `j+1` (for `j : Fin k`) carries `e(h/4^{j+1})`.  This is
exactly the phase attached to `ω_S(n+j+1)` in `truncTailS`. -/
noncomputable def zPhase (h : ℤ) (k : ℕ) : Fin k → ℂ :=
  fun j => ePhase ((h : ℝ) / (4 : ℝ) ^ (j.val + 1))

@[simp] lemma norm_zPhase (h : ℤ) (k : ℕ) (j : Fin k) : ‖zPhase h k j‖ = 1 :=
  norm_ePhase _

/-- **The least nontrivial site has `Re z ≤ 0`.**  If `j₀ ∈ [1,k]` is least with `h/4^{j₀} ∉ ℤ`
then `h/4^{j₀−1} = m ∈ ℤ` (minimality, or `j₀ = 1`) and `h/4^{j₀} = m/4` with `4 ∤ m`, so the
phase is `e(m/4) ∈ {i, −1, −i}`.  Uniform in `h`: no constant depends on it. -/
theorem exists_site_re_nonpos (k : ℕ) (h : ℤ) (hntw : NontrivialWindow k h) :
    ∃ j : Fin k, (zPhase h k j).re ≤ 0 := by
  classical
  have hphase_re : ∀ x : ℝ, (ePhase x).re = Real.cos (2 * Real.pi * x) := by
    intro x
    have hx : ePhase x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
      unfold ePhase; congr 1; push_cast; ring
    rw [hx, Complex.exp_ofReal_mul_I_re]
  have hex : ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ ¬ (∃ m : ℤ, (h : ℝ) / (4 : ℝ) ^ j = m) := hntw
  obtain ⟨hj1, hjk, hjP⟩ := Nat.find_spec hex
  set j₀ := Nat.find hex with hj₀
  -- the predecessor site is integral
  have hpred : ∃ m : ℤ, (h : ℝ) / (4 : ℝ) ^ (j₀ - 1) = m := by
    rcases eq_or_lt_of_le hj1 with heq | hlt
    · have h0 : j₀ - 1 = 0 := by omega
      rw [h0]
      exact ⟨h, by norm_num⟩
    · have hlt' : j₀ - 1 < j₀ := by omega
      have hmin := Nat.find_min hex hlt'
      push Not at hmin
      exact hmin (by omega) (by omega)
  obtain ⟨m, hm⟩ := hpred
  have hsucc : j₀ - 1 + 1 = j₀ := by omega
  have h4 : (h : ℝ) / (4 : ℝ) ^ j₀ = (m : ℝ) / 4 := by
    rw [← hsucc, pow_succ, ← div_div, hm]
  have hm4 : ¬ ((4 : ℤ) ∣ m) := by
    rintro ⟨q, rfl⟩
    refine hjP ⟨q, ?_⟩
    rw [h4]
    push_cast
    ring_nf
  -- write m = 4q + r with r ∈ {1,2,3}
  have hmm : (m : ℝ) = ((m % 4 : ℤ) : ℝ) + 4 * ((m / 4 : ℤ) : ℝ) := by
    have hz : m = m % 4 + 4 * (m / 4) := by omega
    exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) hz
  have hr : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
    have h0 : m % 4 ≠ 0 := fun hc => hm4 (Int.dvd_of_emod_eq_zero hc)
    have h1 : 0 ≤ m % 4 := Int.emod_nonneg m (by norm_num)
    have h2 : m % 4 < 4 := Int.emod_lt_of_pos m (by norm_num)
    omega
  refine ⟨⟨j₀ - 1, by omega⟩, ?_⟩
  have hz : zPhase h k ⟨j₀ - 1, by omega⟩ = ePhase (((m % 4 : ℤ) : ℝ) / 4) := by
    rw [zPhase]
    simp only [hsucc]
    rw [h4]
    have hsplit : (m : ℝ) / 4 = ((m % 4 : ℤ) : ℝ) / 4 + ((m / 4 : ℤ) : ℤ) := by
      rw [hmm]; ring
    rw [hsplit, ePhase_add_int]
  rw [hz, hphase_re]
  rcases hr with hr1 | hr2 | hr3
  · rw [hr1, show (2 * Real.pi * (((1 : ℤ) : ℝ) / 4)) = Real.pi / 2 by push_cast; ring,
      Real.cos_pi_div_two]
  · rw [hr2, show (2 * Real.pi * (((2 : ℤ) : ℝ) / 4)) = Real.pi by push_cast; ring, Real.cos_pi]
    norm_num
  · rw [hr3, show (2 * Real.pi * (((3 : ℤ) : ℝ) / 4)) = Real.pi + Real.pi / 2 by push_cast; ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi, Real.cos_pi]
    norm_num

/-- **E5, model phase contraction.**  With `A = ∑_j (z_j − 1)`, `|z_j| = 1`, some `Re z_{j₀} ≤ 0`
(so `Re A ≤ −1`, `|A| ≤ 2k`), and distinct primes `p_i > k`:
`‖∏_i (1 + A/p_i)‖ ≤ exp(∑_i (Re A/p_i + |A|²/(2p_i²))) ≤ e^{2k} · exp(−∑_i 1/p_i)`. -/
theorem model_phase_norm_le {ι : Type*} [Fintype ι] (p : ι → ℕ) (hinj : Function.Injective p)
    {k : ℕ} (hk : 1 ≤ k) (hkp : ∀ i, k < p i) (z : Fin k → ℂ) (hz : ∀ j, ‖z j‖ = 1)
    (j₀ : Fin k) (hre : (z j₀).re ≤ 0) :
    ‖∏ i, (1 + (∑ j, (z j - 1)) / (p i : ℂ))‖
      ≤ Real.exp (2 * k) * Real.exp (- ∑ i, (1 : ℝ) / (p i : ℝ)) := by
  classical
  set A : ℂ := ∑ j, (z j - 1) with hA
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hp : ∀ i, (0 : ℝ) < (p i : ℝ) := by
    intro i
    have : 0 < p i := lt_of_le_of_lt (Nat.zero_le k) (hkp i)
    exact_mod_cast this
  -- Re A ≤ −1
  have hterm : ∀ j : Fin k, (z j - 1).re ≤ 0 := by
    intro j
    have h1 : (z j).re ≤ ‖z j‖ := Complex.re_le_norm (z j)
    rw [hz j] at h1
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hAre : A.re ≤ -1 := by
    have hre_sum : A.re = ∑ j, (z j - 1).re := by rw [hA, Complex.re_sum]
    rw [hre_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
    have h1 : (z j₀ - 1).re ≤ -1 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have h2 : ∑ j ∈ Finset.univ.erase j₀, (z j - 1).re ≤ 0 :=
      Finset.sum_nonpos (fun j _ => hterm j)
    linarith
  -- ‖A‖ ≤ 2k
  have hAnorm : ‖A‖ ≤ 2 * (k : ℝ) := by
    calc ‖A‖ ≤ ∑ j, ‖z j - 1‖ := by rw [hA]; exact norm_sum_le _ _
      _ ≤ ∑ _j : Fin k, (2 : ℝ) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          calc ‖z j - 1‖ ≤ ‖z j‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [hz j]; norm_num
      _ = 2 * (k : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hA2 : ‖A‖ ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith [norm_nonneg A]
  -- pointwise exponent bound
  have hstep : ∀ i : ι, (A / (p i : ℂ)).re + ‖A / (p i : ℂ)‖ ^ 2 / 2
      ≤ -(1 / (p i : ℝ)) + 2 * (k : ℝ) ^ 2 * (1 / (p i : ℝ) ^ 2) := by
    intro i
    have hpi := hp i
    have hu : (0 : ℝ) < 1 / (p i : ℝ) := by positivity
    rw [Complex.div_natCast_re, norm_div, Complex.norm_natCast]
    have hrw1 : A.re / (p i : ℝ) = A.re * (1 / (p i : ℝ)) := by ring
    have hrw2 : (‖A‖ / (p i : ℝ)) ^ 2 / 2 = ‖A‖ ^ 2 * (1 / (p i : ℝ)) ^ 2 / 2 := by
      rw [div_pow]; ring
    rw [hrw1, hrw2]
    have e1 : (0 : ℝ) ≤ (-(A.re + 1)) * (1 / (p i : ℝ)) :=
      mul_nonneg (by linarith) hu.le
    have e2 : (0 : ℝ) ≤ (4 * (k : ℝ) ^ 2 - ‖A‖ ^ 2) * (1 / (p i : ℝ)) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have e3 : (1 / (p i : ℝ)) ^ 2 = 1 / (p i : ℝ) ^ 2 := by rw [div_pow]; norm_num
    rw [e3] at e2 ⊢
    nlinarith [e1, e2]
  calc ‖∏ i, (1 + A / (p i : ℂ))‖
      = ∏ i, ‖1 + A / (p i : ℂ)‖ := Complex.norm_prod _ _
    _ ≤ ∏ i, Real.exp ((A / (p i : ℂ)).re + ‖A / (p i : ℂ)‖ ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => norm_one_add_le_exp _)
    _ = Real.exp (∑ i, ((A / (p i : ℂ)).re + ‖A / (p i : ℂ)‖ ^ 2 / 2)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (2 * (k : ℝ) + -∑ i, (1 : ℝ) / (p i : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        calc ∑ i, ((A / (p i : ℂ)).re + ‖A / (p i : ℂ)‖ ^ 2 / 2)
            ≤ ∑ i, (-(1 / (p i : ℝ)) + 2 * (k : ℝ) ^ 2 * (1 / (p i : ℝ) ^ 2)) :=
              Finset.sum_le_sum (fun i _ => hstep i)
          _ = -(∑ i, (1 : ℝ) / (p i : ℝ)) + 2 * (k : ℝ) ^ 2 * ∑ i, (1 : ℝ) / (p i : ℝ) ^ 2 := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib]
          _ ≤ -(∑ i, (1 : ℝ) / (p i : ℝ)) + 2 * (k : ℝ) ^ 2 * (1 / (k : ℝ)) := by
              have := sum_inv_sq_le p hinj hk hkp
              nlinarith [sq_nonneg (k : ℝ)]
          _ = 2 * (k : ℝ) + -∑ i, (1 : ℝ) / (p i : ℝ) := by
              field_simp
              ring
    _ = Real.exp (2 * (k : ℝ)) * Real.exp (-∑ i, (1 : ℝ) / (p i : ℝ)) := Real.exp_add _ _

/-- The window mean is `1`-bounded (trivial bound used in regime R1). -/
theorem norm_windowMeanS_le_one (S : ℕ → Prop) [DecidablePred S] (J : ℕ) (h : ℤ) (x : ℕ) :
    ‖windowMeanS S J h x‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [windowMeanS, prefixMean]
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  rw [windowMeanS, prefixMean, norm_div, Complex.norm_natCast, div_le_one hxR]
  calc ‖∑ n ∈ Finset.range x, ePhase ((h : ℝ) * truncTailS S J n)‖
      ≤ ∑ n ∈ Finset.range x, ‖ePhase ((h : ℝ) * truncTailS S J n)‖ := norm_sum_le _ _
    _ = (x : ℝ) := by
        rw [Finset.sum_congr rfl (fun n _ => norm_ePhase _), Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, mul_one]

end NormalNumbers.PrimeModel.PhaseAlgebra
