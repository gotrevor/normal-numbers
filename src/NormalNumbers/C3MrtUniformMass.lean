/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtWindowMass

/-!
# `UniformResonantMass`, assembled

`C3MrtWindowMass` proved every leaf.  This file does the assembly: the resonant primes are
fibred by (resonance window index `m`, half-unit block index `j = ⌊2 log p⌋`), each fibre is
an interval of `log p` of length `≤ 1` and is handed to `interval_mass_le`, and the resulting
bounds are summed — the main terms harmonically in `m` (`sum_inv_gap_le`), the
Brun–Titchmarsh errors geometrically in `m` AND in `j` (`sum_exp_neg_le` twice).
-/

open Finset Real

namespace NormalNumbers

namespace CastingOut

/-- The resonance height `γ_m = |arg z − 2πm|`. -/
noncomputable def resGamma (z : ℂ) (m : ℤ) : ℝ := |z.arg - 2 * π * m|

/-- The bottom of the `m`-th resonance window, in the variable `log p`. -/
noncomputable def winHeight (z : ℂ) (t δ : ℝ) (m : ℤ) : ℝ := (resGamma z m - δ) / |t|

/-- The length of a resonance window, in the variable `log p`. -/
noncomputable def winLen (t δ : ℝ) : ℝ := 2 * δ / |t|


/-- A geometric tail on an `Icc` of block indices. -/
theorem sum_exp_neg_Icc_le {c : ℝ} (hc : 0 < c) (j₀ j₁ : ℕ) :
    ∑ j ∈ Finset.Icc j₀ j₁, Real.exp (-(c * j)) ≤ (1 + 1 / c) * Real.exp (-(c * j₀)) := by
  have hIcc : Finset.Icc j₀ j₁ = Finset.Ico j₀ (j₁ + 1) := by
    ext x; simp [Nat.lt_succ_iff]
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hrw : ∀ i ∈ Finset.range (j₁ + 1 - j₀),
      Real.exp (-(c * ((j₀ + i : ℕ) : ℝ))) = Real.exp (-(c * j₀)) * Real.exp (-(c * i)) := by
    intro i _
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum, mul_comm]
  exact mul_le_mul_of_nonneg_right (sum_exp_neg_le hc _) (Real.exp_pos _).le

/-- **The mass of one resonance window.**  The primes with `log p ≥ A` that fall into the
`m`-th `δ`-window carry reciprocal mass at most `32·L/a + 7·10⁶·exp(−a/16)·exp(−A/16)`,
where `a` is the window's height and `L` its length.

The window is cut into half-unit blocks in `log p`; each block is an interval of length
`≤ 1` and goes to `interval_mass_le`.  The main terms are bounded by the lowest block
(`a₀ ≥ a`) times the number `≤ 2L+2` of blocks; the Brun–Titchmarsh errors decay
geometrically in the block index. -/
theorem sharp_window_mass_le {z : ℂ} (hz : ‖z‖ = 1) {t δ A : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ resEps z)
    (ht : t ≠ 0) (hA : 16 ≤ A) {m : ℤ} {G : Finset ℕ}
    (hG : ∀ p ∈ G, p.Prime ∧ A ≤ Real.log p ∧ |(primePhase z t p).arg| < δ ∧
      windowIndexW z t δ p = m) :
    ∑ p ∈ G, (p : ℝ)⁻¹ ≤ 32 * winLen t δ / winHeight z t δ m
      + 7000000 * Real.exp (-(winHeight z t δ m / 16)) * Real.exp (-(A / 16)) := by
  classical
  have htpos : (0 : ℝ) < |t| := abs_pos.2 ht
  set a : ℝ := winHeight z t δ m with ha_def
  set L : ℝ := winLen t δ with hL_def
  have hγ : 2 * δ ≤ resGamma z m := le_trans (by linarith) (two_resEps_le_abs_shift z m)
  have hapos : (0 : ℝ) < a := by
    rw [ha_def, winHeight]; exact div_pos (by rw [resGamma] at hγ ⊢; linarith) htpos
  have hL0 : (0 : ℝ) < L := by rw [hL_def, winLen]; positivity
  -- every prime of `G` lies in the window `(a, a+L)` and above `A`
  have hwin : ∀ p ∈ G, a < Real.log p ∧ Real.log p < a + L ∧ A ≤ Real.log p ∧ p.Prime := by
    intro p hp
    obtain ⟨hpp, hpA, hres, hidx⟩ := hG p hp
    have hp2 : 2 ≤ p := hpp.two_le
    obtain ⟨h1, h2⟩ := windowIndexW_spec hz hp2 hδ hres
    rw [hidx] at h1 h2
    refine ⟨?_, ?_, hpA, hpp⟩
    · rw [ha_def, winHeight, div_lt_iff₀ htpos]
      rw [resGamma]
      linarith [h1]
    · have hsum : a + L = (resGamma z m + δ) / |t| := by
        rw [ha_def, hL_def, winHeight, winLen]
        field_simp
        ring
      rw [hsum, lt_div_iff₀ htpos, resGamma]
      linarith [h2]
  -- fibre by the half-unit block index
  set j₀ : ℕ := ⌊2 * max a A⌋₊ with hj0
  set j₁ : ℕ := ⌊2 * (a + L)⌋₊ with hj1
  have hmaps : ∀ p ∈ G, ⌊2 * Real.log p⌋₊ ∈ Finset.Icc j₀ j₁ := by
    intro p hp
    obtain ⟨h1, h2, h3, _⟩ := hwin p hp
    refine Finset.mem_Icc.2 ⟨Nat.floor_le_floor ?_, Nat.floor_le_floor ?_⟩
    · exact mul_le_mul_of_nonneg_left (max_le h1.le h3) (by norm_num)
    · exact mul_le_mul_of_nonneg_left h2.le (by norm_num)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p : ℕ => (p : ℝ)⁻¹)]
  set l : ℝ := min L 1 with hl_def
  have hl0 : (0 : ℝ) < l := lt_min hL0 (by norm_num)
  have hl1 : l ≤ 1 := min_le_right _ _
  have hj0ge : (32 : ℝ) ≤ (j₀ : ℝ) := by
    have : (32 : ℕ) ≤ j₀ := by
      rw [hj0]
      refine Nat.le_floor ?_
      have : A ≤ max a A := le_max_right _ _
      push_cast
      linarith
    exact_mod_cast this
  -- the per-block bound
  have hblock : ∀ j ∈ Finset.Icc j₀ j₁,
      ∑ p ∈ G.filter (fun p : ℕ => ⌊2 * Real.log p⌋₊ = j), (p : ℝ)⁻¹
        ≤ 8 * l / a + 100000 * (Real.exp (1 / 16) * Real.exp (-((1 / 16 : ℝ) * j))) := by
    intro j hj
    have hjge : (32 : ℝ) ≤ (j : ℝ) := by
      have := (Finset.mem_Icc.1 hj).1
      have : (j₀ : ℝ) ≤ (j : ℝ) := by exact_mod_cast this
      linarith
    set a₀ : ℝ := max a ((j : ℝ) / 2 - 1 / 2) with ha0
    have ha0a : a ≤ a₀ := le_max_left _ _
    have ha0j : (j : ℝ) / 2 - 1 / 2 ≤ a₀ := le_max_right _ _
    have ha0pos : (0 : ℝ) < a₀ := lt_of_lt_of_le hapos ha0a
    have ha0log : Real.log 2 ≤ a₀ := by
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (x := (2:ℝ)) (by norm_num); linarith
      linarith
    have hGw : ∀ p ∈ G.filter (fun p : ℕ => ⌊2 * Real.log p⌋₊ = j),
        a₀ < Real.log p ∧ Real.log p < a₀ + l := by
      intro p hp
      obtain ⟨hpG, hpj⟩ := Finset.mem_filter.1 hp
      obtain ⟨h1, h2, h3, hpp⟩ := hwin p hpG
      have hlogpos : (0 : ℝ) ≤ 2 * Real.log p := by
        have : (0:ℝ) < Real.log p := lt_of_lt_of_le (by linarith) h3
        linarith
      have hfl : ((j : ℕ) : ℝ) ≤ 2 * Real.log p := by
        rw [← hpj]; exact Nat.floor_le hlogpos
      have hfu : 2 * Real.log p < (j : ℝ) + 1 := by
        rw [← hpj]
        exact_mod_cast Nat.lt_floor_add_one (2 * Real.log p)
      constructor
      · rw [ha0]
        exact max_lt h1 (by linarith)
      · rcases le_total L 1 with hLc | hLc
        · have : l = L := by rw [hl_def, min_eq_left hLc]
          rw [this]
          linarith [ha0a]
        · have : l = 1 := by rw [hl_def, min_eq_right hLc]
          rw [this]
          linarith [ha0j]
    have hmass := interval_mass_le ha0log hl0 hl1
      (fun p hp => (hwin p (Finset.mem_filter.1 hp).1).2.2.2) hGw
    refine le_trans hmass (add_le_add ?_ ?_)
    · exact div_le_div_of_nonneg_left (by positivity) hapos ha0a
    · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : (j : ℝ) / 2 - 1 / 2 ≤ a₀ := ha0j
      linarith
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the main term
  have hcard : ((Finset.Icc j₀ j₁).card : ℝ) ≤ 2 * L + 2 := by
    rcases le_or_gt j₀ j₁ with hle | hgt
    · rw [Nat.card_Icc]
      have h1 : ((j₁ : ℝ)) ≤ 2 * (a + L) := by
        rw [hj1]; exact Nat.floor_le (by positivity)
      have h2 : 2 * a - 1 ≤ (j₀ : ℝ) := by
        have := Nat.lt_floor_add_one (2 * max a A)
        have h3 : (2 : ℝ) * a ≤ 2 * max a A := by
          have := le_max_left a A; linarith
        have h4 : (2 : ℝ) * max a A < (j₀ : ℝ) + 1 := by rw [hj0]; exact_mod_cast this
        linarith
      have : ((j₁ + 1 - j₀ : ℕ) : ℝ) = (j₁ : ℝ) + 1 - (j₀ : ℝ) := by
        have : j₀ ≤ j₁ + 1 := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [this]
      linarith
    · rw [Nat.card_Icc]
      have : j₁ + 1 - j₀ = 0 := by omega
      rw [this]
      simp
      linarith
  have hmain : ((Finset.Icc j₀ j₁).card : ℝ) * (8 * l / a) ≤ 32 * L / a := by
    have hlL : l * (2 * L + 2) ≤ 4 * L := by
      rcases le_total L 1 with hLc | hLc
      · have : l = L := by rw [hl_def, min_eq_left hLc]
        rw [this]; nlinarith
      · have : l = 1 := by rw [hl_def, min_eq_right hLc]
        rw [this]; linarith
    have h8 : (0:ℝ) ≤ 8 * l / a := by positivity
    calc ((Finset.Icc j₀ j₁).card : ℝ) * (8 * l / a) ≤ (2 * L + 2) * (8 * l / a) :=
          mul_le_mul_of_nonneg_right hcard h8
      _ = 8 * (l * (2 * L + 2)) / a := by ring
      _ ≤ 8 * (4 * L) / a := by
          refine div_le_div_of_nonneg_right ?_ hapos.le
          linarith
      _ = 32 * L / a := by ring
  -- the error term
  have herr : 100000 * (Real.exp (1 / 16) * ∑ j ∈ Finset.Icc j₀ j₁, Real.exp (-((1/16 : ℝ) * j)))
      ≤ 7000000 * Real.exp (-(a / 16)) * Real.exp (-(A / 16)) := by
    have hgeo := sum_exp_neg_Icc_le (c := (1/16 : ℝ)) (by norm_num) j₀ j₁
    have hj0lb : a + A - 1 ≤ (j₀ : ℝ) := by
      have := Nat.lt_floor_add_one (2 * max a A)
      have h4 : (2 : ℝ) * max a A < (j₀ : ℝ) + 1 := by rw [hj0]; exact_mod_cast this
      have h5 : a + A ≤ 2 * max a A := by
        rcases le_total a A with h | h
        · have : max a A = A := max_eq_right h
          rw [this]; linarith
        · have : max a A = a := max_eq_left h
          rw [this]; linarith
      linarith
    have hexp : Real.exp (-((1/16 : ℝ) * j₀)) ≤ Real.exp (1/16) * (Real.exp (-(a/16)) * Real.exp (-(A/16))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      linarith
    have he1 : Real.exp (1/16 : ℝ) ≤ 2 := by
      have h := Real.add_one_le_exp (-(1/16 : ℝ))
      have hpos : (0:ℝ) < Real.exp (1/16 : ℝ) := Real.exp_pos _
      have hinv : Real.exp (-(1/16 : ℝ)) = (Real.exp (1/16 : ℝ))⁻¹ := Real.exp_neg _
      rw [hinv] at h
      have h2 : (15/16 : ℝ) ≤ (Real.exp (1/16 : ℝ))⁻¹ := by linarith
      rw [le_inv_comm₀ (by norm_num) hpos] at h2
      calc Real.exp (1/16 : ℝ) ≤ (15/16 : ℝ)⁻¹ := h2
        _ ≤ 2 := by norm_num
    have hnn : (0:ℝ) ≤ Real.exp (-(a/16)) * Real.exp (-(A/16)) := by positivity
    calc 100000 * (Real.exp (1 / 16) * ∑ j ∈ Finset.Icc j₀ j₁, Real.exp (-((1/16 : ℝ) * j)))
        ≤ 100000 * (Real.exp (1/16) * ((1 + 1 / (1/16 : ℝ)) * Real.exp (-((1/16:ℝ) * j₀)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeo (Real.exp_pos _).le) (by norm_num)
      _ ≤ 100000 * (2 * (17 * (2 * (Real.exp (-(a/16)) * Real.exp (-(A/16)))))) := by
          have hstep : (1 + 1/(1/16:ℝ)) * Real.exp (-((1/16:ℝ) * j₀))
              ≤ 17 * (2 * (Real.exp (-(a/16)) * Real.exp (-(A/16)))) := by
            have : (1 + 1/(1/16:ℝ)) = 17 := by norm_num
            rw [this]
            refine mul_le_mul_of_nonneg_left (le_trans hexp ?_) (by norm_num)
            exact mul_le_mul_of_nonneg_right he1 hnn
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine le_trans (mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le) ?_
          refine mul_le_mul_of_nonneg_right he1 (by positivity)
      _ = 7000000 * Real.exp (-(a/16)) * Real.exp (-(A/16)) - 200000 * (Real.exp (-(a/16)) * Real.exp (-(A/16))) := by ring
      _ ≤ 7000000 * Real.exp (-(a/16)) * Real.exp (-(A/16)) := by nlinarith [hnn]
  linarith [hmain, herr]


/-- **The mass of all the high resonant primes.**  Summed over the window index.

The main terms `64δ/(γ_m − δ)` are harmonic in `m` (`sum_inv_gap_le`); the Brun–Titchmarsh
errors decay geometrically in `m`, because the `m`-th window sits at height `≳ π|m|/|t|`
(`sum_exp_neg_le` at `c = π/(32|t|)`, exactly as its docstring advertises). -/
theorem resonant_big_mass_le {z : ℂ} (hz : ‖z‖ = 1) {t δ A : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ resEps z) (ht : t ≠ 0) (hA : 16 ≤ A) {Y : ℕ} {G : Finset ℕ}
    (hG : ∀ p ∈ G, p.Prime ∧ (p : ℝ) ≤ Y ∧ |(primePhase z t p).arg| < δ ∧ A ≤ Real.log p) :
    ∑ p ∈ G, (p : ℝ)⁻¹
      ≤ 128 + 128 * δ * ((2 / π) * (1 + Real.log (⌈(|t| * Real.log Y + δ + π) / (2 * π)⌉₊)))
        + 14000000 * (1 + 32 * |t| / π) * Real.exp (-(A / 16)) := by
  classical
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have htpos : (0 : ℝ) < |t| := abs_pos.2 ht
  have hδpi : δ ≤ π / 2 := by
    refine le_trans hδ ?_
    rw [resEps]
    have := Complex.abs_arg_le_pi z
    linarith
  set T : ℝ := |t| * Real.log Y with hT
  set K : ℕ := ⌈(T + δ + π) / (2 * π)⌉₊ with hK
  have hmaps : ∀ p ∈ G, windowIndexW z t δ p ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro p hp
    obtain ⟨hpp, hpY, hres, _⟩ := hG p hp
    have hp2 : 2 ≤ p := hpp.two_le
    have hlog : |t| * Real.log p ≤ T := by
      rw [hT]
      refine mul_le_mul_of_nonneg_left ?_ htpos.le
      refine Real.log_le_log ?_ hpY
      have := hpp.pos
      exact_mod_cast this
    have := abs_windowIndexW_le hz hp2 hδ hres hlog
    rw [← hK] at this
    exact Finset.mem_Icc.2 ⟨by linarith [abs_le.1 this |>.1], (abs_le.1 this).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p : ℕ => (p : ℝ)⁻¹)]
  set fmain : ℝ → ℝ := fun x => if 1 ≤ x then 64 * δ / (2 * π * x - π - δ) else 64 with hfm
  set ferr : ℝ → ℝ :=
    fun x => 7000000 * Real.exp (-(π / (32 * |t|) * x)) * Real.exp (-(A / 16)) with hfe
  have hfmnn : ∀ x, 0 ≤ fmain x := by
    intro x
    rw [hfm]
    by_cases h : 1 ≤ x
    · simp only [if_pos h]
      rcases le_or_gt (2 * π * x - π - δ) 0 with hd | hd
      · have : 64 * δ / (2 * π * x - π - δ) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) hd
        -- impossible: the denominator is positive for x ≥ 1
        exfalso
        nlinarith
      · positivity
    · simp only [if_neg h]; norm_num
  have hfenn : ∀ x, 0 ≤ ferr x := by intro x; rw [hfe]; positivity
  -- the per-window bound, put in the symmetric shape
  have hstep : ∀ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      ∑ p ∈ G.filter (fun p : ℕ => windowIndexW z t δ p = m), (p : ℝ)⁻¹
        ≤ fmain |(m : ℝ)| + ferr |(m : ℝ)| := by
    intro m _
    have hsharp := sharp_window_mass_le (z := z) (t := t) (δ := δ) (A := A) hz hδ0 hδ ht hA
      (m := m) (G := G.filter (fun p : ℕ => windowIndexW z t δ p = m))
      (fun p hp => by
        obtain ⟨hpG, hpm⟩ := Finset.mem_filter.1 hp
        obtain ⟨h1, _, h3, h4⟩ := hG p hpG
        exact ⟨h1, h4, h3, hpm⟩)
    refine le_trans hsharp (add_le_add ?_ ?_)
    · -- the main term is `64δ/(γ_m − δ)`
      have hγ : 2 * δ ≤ resGamma z m := le_trans (by linarith) (two_resEps_le_abs_shift z m)
      have hden : (0 : ℝ) < resGamma z m - δ := by linarith
      have heq : 32 * winLen t δ / winHeight z t δ m = 64 * δ / (resGamma z m - δ) := by
        rw [winLen, winHeight]
        field_simp
        ring
      rw [heq, hfm]
      by_cases h1 : (1 : ℝ) ≤ |(m : ℝ)|
      · simp only [if_pos h1]
        have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := h1
        have hlow : 2 * π * |(m : ℝ)| - π ≤ resGamma z m := by
          have h2 : |z.arg| ≤ π := Complex.abs_arg_le_pi z
          have h3 := abs_sub_abs_le_abs_sub (2 * π * (m : ℝ)) z.arg
          rw [abs_sub_comm] at h3
          have h4 : |2 * π * (m : ℝ)| = 2 * π * |(m : ℝ)| := by
            rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * π)]
          rw [resGamma]
          linarith [h4 ▸ h3]
        have hd2 : (0 : ℝ) < 2 * π * |(m : ℝ)| - π - δ := by nlinarith
        refine div_le_div_of_nonneg_left (by positivity) hd2 ?_
        linarith
      · simp only [if_neg h1]
        rw [div_le_iff₀ hden]
        linarith
    · -- the error term decays in `|m|`
      rw [hfe]
      have hmul : (7000000 : ℝ) * Real.exp (-(winHeight z t δ m / 16)) * Real.exp (-(A / 16))
          ≤ 7000000 * Real.exp (-(π / (32 * |t|) * |(m : ℝ)|)) * Real.exp (-(A / 16)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
        have hγ : 2 * δ ≤ resGamma z m := le_trans (by linarith) (two_resEps_le_abs_shift z m)
        have hlow : 2 * π * |(m : ℝ)| - π ≤ resGamma z m := by
          have h2 : |z.arg| ≤ π := Complex.abs_arg_le_pi z
          have h3 := abs_sub_abs_le_abs_sub (2 * π * (m : ℝ)) z.arg
          rw [abs_sub_comm] at h3
          have h4 : |2 * π * (m : ℝ)| = 2 * π * |(m : ℝ)| := by
            rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * π)]
          rw [resGamma]
          linarith [h4 ▸ h3]
        have hge : π / 2 * |(m : ℝ)| ≤ resGamma z m - δ := by
          rcases eq_or_ne m 0 with h1 | h1
          · subst h1
            simp only [Int.cast_zero, abs_zero, mul_zero]
            linarith
          · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
              have : (1 : ℤ) ≤ |m| := Int.one_le_abs (by omega)
              have h2 : ((1 : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast this
              rwa [Int.cast_abs, Int.cast_one] at h2
            nlinarith
        have hw : π / 2 * |(m : ℝ)| / |t| ≤ winHeight z t δ m := by
          rw [winHeight, div_le_div_iff_of_pos_right htpos]
          exact hge
        have : π / (32 * |t|) * |(m : ℝ)| ≤ winHeight z t δ m / 16 := by
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 16)]
          have : π / (32 * |t|) * |(m : ℝ)| * 16 = π / 2 * |(m : ℝ)| / |t| := by
            field_simp; ring
          rw [this]; exact hw
        linarith
      exact hmul
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hsym := sum_Icc_symm_le (K := K) (fun x => fmain x + ferr x)
    (fun x => add_nonneg (hfmnn x) (hfenn x))
  refine le_trans hsym ?_
  rw [Finset.sum_add_distrib]
  -- the main sum
  have hmainsum : ∑ j ∈ Finset.range (K + 1), fmain (j : ℝ)
      ≤ 64 + 64 * δ * ((2 / π) * (1 + Real.log K)) := by
    rw [Finset.sum_range_succ' (fun j : ℕ => fmain (j : ℝ)) K]
    have h0 : fmain ((0 : ℕ) : ℝ) = 64 := by
      rw [hfm]; norm_num
    have hre : ∑ i ∈ Finset.range K, fmain (((i + 1 : ℕ) : ℝ))
        = ∑ m ∈ Finset.Icc 1 K, fmain ((m : ℕ) : ℝ) := by
      have hIcc : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
        ext x; simp [Nat.lt_succ_iff]
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    rw [h0, hre]
    have hbody : ∀ m ∈ Finset.Icc 1 K,
        fmain ((m : ℕ) : ℝ) = 64 * δ * (2 * π * (m : ℝ) - π - δ)⁻¹ := by
      intro m hm
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
        have := (Finset.mem_Icc.1 hm).1
        exact_mod_cast this
      rw [hfm]
      simp only [if_pos hm1]
      rw [div_eq_mul_inv]
    rw [Finset.sum_congr rfl hbody, ← Finset.mul_sum]
    have := sum_inv_gap_le (δ := δ) hδ0.le hδpi K
    nlinarith [this, hδ0]
  -- the error sum
  have herrsum : ∑ j ∈ Finset.range (K + 1), ferr (j : ℝ)
      ≤ 7000000 * (1 + 32 * |t| / π) * Real.exp (-(A / 16)) := by
    have hbody : ∀ j ∈ Finset.range (K + 1),
        ferr ((j : ℕ) : ℝ)
          = (7000000 * Real.exp (-(A / 16))) * Real.exp (-(π / (32 * |t|) * (j : ℝ))) := by
      intro j _; rw [hfe]; ring
    rw [Finset.sum_congr rfl hbody, ← Finset.mul_sum]
    have hc : (0 : ℝ) < π / (32 * |t|) := by positivity
    have hgeo := sum_exp_neg_le hc (K + 1)
    have hinv : 1 / (π / (32 * |t|)) = 32 * |t| / π := by field_simp
    rw [hinv] at hgeo
    have hnn : (0 : ℝ) ≤ 7000000 * Real.exp (-(A / 16)) := by positivity
    calc (7000000 * Real.exp (-(A / 16))) * ∑ j ∈ Finset.range (K + 1),
            Real.exp (-(π / (32 * |t|) * (j : ℝ)))
        ≤ (7000000 * Real.exp (-(A / 16))) * (1 + 32 * |t| / π) :=
          mul_le_mul_of_nonneg_left hgeo hnn
      _ = 7000000 * (1 + 32 * |t| / π) * Real.exp (-(A / 16)) := by ring
  nlinarith [hmainsum, herrsum, Real.exp_pos (-(A/16))]


/-- At `t = 0` nothing resonates: the phase is `z` itself, and `|arg z| ≥ 2δ`. -/
theorem resonantMass_zero {z : ℂ} (hz : ‖z‖ = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ resEps z)
    (Y : ℕ) : resonantMass z 0 Y δ = 0 := by
  classical
  rw [resonantMass]
  refine Finset.sum_eq_zero ?_
  intro p hp
  exfalso
  obtain ⟨hpm, hres⟩ := Finset.mem_filter.1 hp
  have hpp : p.Prime := (Erdos67b.mem_primesUpTo.1 hpm).1
  obtain ⟨h1, _⟩ := windowIndexW_spec hz hpp.two_le hδ hres
  have hgap : 2 * δ ≤ |z.arg - 2 * π * windowIndexW z 0 δ p| :=
    le_trans (by linarith) (two_resEps_le_abs_shift z _)
  rw [abs_zero, zero_mul] at h1
  linarith

set_option maxHeartbeats 2000000 in
/-- **`UniformResonantMass`, discharged.**  The resonant primes carry reciprocal mass at most
`100δ(log log Y + log(2+|t|)) + C`, uniformly in `t` and `Y`.

The cutoff is `A = 16 log(2·10⁸(2+|t|))`, chosen so that the Brun–Titchmarsh error of
`resonant_big_mass_le` is `≤ 1`; the primes below it cost `log(A+1) + mertensBound`, which
`log_le_mul_sub` at slope `7δ/8` turns into `14δ log(2+|t|) + O_δ(1)` — and `14 + 85.4 < 100`
is exactly the budget the window sum leaves. -/
theorem uniformResonantMass_holds : UniformResonantMass := by
  classical
  intro z δ hz hδ0 hδ
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hδpi : δ ≤ π / 2 := by
    refine le_trans hδ ?_
    rw [resEps]
    have := Complex.abs_arg_le_pi z
    linarith
  have hlog2 : (0.6931 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2u : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := (2:ℝ)) (by norm_num); linarith
  have hδ4 : δ ≤ 2 := by linarith [Real.pi_le_four]
  have hlogδ : Real.log (7 * δ / 8) ≤ 7 * δ / 8 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hΛpos : (0 : ℝ) < Real.log 200000000 := Real.log_pos (by norm_num)
  have hmert := Erdos67b.PrimeEstimates.mertensBound_nonneg
  refine ⟨500 + 2000 * δ + 20 * δ * Real.log 200000000 - Real.log (7 * δ / 8) + Erdos67b.PrimeEstimates.mertensBound, ?_, ?_⟩
  · have : (0:ℝ) ≤ 20 * δ * Real.log 200000000 := by positivity
    linarith
  intro t Y hY
  -- `log log Y ≥ −1`
  have hlY : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) (by exact_mod_cast hY)
  have hlYpos : (0 : ℝ) < Real.log Y := by linarith
  have hloglog : (-0.443 : ℝ) ≤ Real.log (Real.log Y) := by
    have hll : Real.log (Real.log 2) ≤ Real.log (Real.log Y) :=
      Real.log_le_log (by linarith) hlY
    have hinv : Real.log (Real.log 2) = -Real.log ((Real.log 2)⁻¹) := by
      rw [Real.log_inv]; ring
    have hup : Real.log ((Real.log 2)⁻¹) ≤ (Real.log 2)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hinvle : (Real.log 2)⁻¹ ≤ 1.443 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith [hinv ▸ hll]
  have hlt2 : Real.log 2 ≤ Real.log (2 + |t|) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hbracket : (0 : ℝ) ≤ Real.log (Real.log Y) + Real.log (2 + |t|) := by linarith
  have hbr : (0 : ℝ) ≤ 100 * δ * (Real.log (Real.log Y) + Real.log (2 + |t|)) :=
    mul_nonneg (by positivity) hbracket
  rcases eq_or_ne t 0 with rfl | ht
  · rw [resonantMass_zero hz hδ0 hδ]
    nlinarith [hbr, hlogδ, hmert, hδ4, hδ0]
  -- the cutoff `A = 16 log(2·10⁸(2+|t|))`
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hXpos : (0 : ℝ) < 200000000 * (2 + |t|) := by positivity
  set s : ℝ := Real.log (2 + |t|) with hsdef
  set Λ : ℝ := Real.log 200000000 with hΛdef
  set A : ℝ := 16 * Real.log (200000000 * (2 + |t|)) with hAdef
  have hs0 : (0 : ℝ) < s := by
    rw [hsdef]; exact Real.log_pos (by linarith)
  have hΛ1 : (1 : ℝ) ≤ Λ := by
    rw [hΛdef, Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hAsplit : A = 16 * Λ + 16 * s := by
    rw [hAdef, hΛdef, hsdef, Real.log_mul (by norm_num) (by positivity)]; ring
  have hA16 : (16 : ℝ) ≤ A := by rw [hAsplit]; nlinarith
  have hexpA : Real.exp (-(A / 16)) = (200000000 * (2 + |t|))⁻¹ := by
    rw [hAdef, show (16 : ℝ) * Real.log (200000000 * (2 + |t|)) / 16
      = Real.log (200000000 * (2 + |t|)) by ring, Real.exp_neg, Real.exp_log hXpos]
  clear_value A s Λ
  -- the error term is at most 1
  have herr : 14000000 * (1 + 32 * |t| / π) * Real.exp (-(A / 16)) ≤ 1 := by
    rw [hexpA]
    have h32 : 32 * |t| / π ≤ 11 * |t| := by
      rw [div_le_iff₀ hpi]
      nlinarith [Real.pi_gt_three, habs]
    have hnum : 14000000 * (1 + 32 * |t| / π) ≤ 200000000 * (2 + |t|) := by
      nlinarith [h32, habs]
    rw [mul_inv_le_iff₀ hXpos] at *
    linarith [hnum]
  -- the window count
  have hlogY2 : Real.log 2 ≤ Real.log Y := hlY
  set Kc : ℕ := ⌈(|t| * Real.log Y + δ + π) / (2 * π)⌉₊ with hKcdef
  have hKle : ((Kc : ℕ) : ℝ) ≤ 8 * ((2 + |t|) * Real.log Y) := by
    rw [hKcdef]
    have hnn : (0 : ℝ) ≤ (|t| * Real.log Y + δ + π) / (2 * π) := by positivity
    have hceil := Nat.ceil_lt_add_one (R := ℝ) hnn
    have hdiv : (|t| * Real.log Y + δ + π) / (2 * π) ≤ (|t| * Real.log Y + δ + π) / 6 := by
      refine div_le_div_of_nonneg_left (by positivity) (by norm_num) ?_
      linarith [Real.pi_gt_three]
    have h4 : π ≤ 4 := Real.pi_le_four
    have hmain : (|t| * Real.log Y + δ + π) / 6 + 1 ≤ 8 * ((2 + |t|) * Real.log Y) := by
      rw [div_add' _ _ _ (by norm_num : (6:ℝ) ≠ 0), div_le_iff₀ (by norm_num : (0:ℝ) < 6)]
      nlinarith [hlogY2, hlog2, habs, hδ4, h4, mul_nonneg habs hlYpos.le]
    linarith
  clear_value Kc
  have hlogK : Real.log Kc ≤ Real.log 8 + (s + Real.log (Real.log Y)) := by
    have hrhs : Real.log (8 * ((2 + |t|) * Real.log Y)) = Real.log 8 + (s + Real.log (Real.log Y)) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
        hsdef]
    rw [← hrhs]
    rcases Nat.eq_zero_or_pos Kc with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      refine Real.log_nonneg ?_
      nlinarith [hlogY2, hlog2, habs]
    · refine Real.log_le_log ?_ hKle
      exact_mod_cast hpos
  have hlogKnn : (0 : ℝ) ≤ Real.log Kc := Real.log_natCast_nonneg _
  -- the small primes
  set B : ℕ := ⌈Real.exp A⌉₊ with hBdef
  have hexpA0 : (1 : ℝ) ≤ Real.exp A := Real.one_le_exp (by linarith)
  have hBge : Real.exp A ≤ (B : ℝ) := by rw [hBdef]; exact Nat.le_ceil _
  have hBlt : (B : ℝ) < Real.exp A + 1 := by
    rw [hBdef]; exact Nat.ceil_lt_add_one (R := ℝ) (Real.exp_pos A).le
  clear_value B
  have hB2 : 2 ≤ B := by
    have hge2 : (2 : ℝ) ≤ Real.exp A := by
      have h1 : Real.exp 1 ≤ Real.exp A := Real.exp_le_exp.2 (by linarith)
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have : (2 : ℝ) ≤ (B : ℝ) := by linarith
    exact_mod_cast this
  have hlogB : Real.log B ≤ A + 1 := by
    have hBle : (B : ℝ) ≤ Real.exp (A + 1) := by
      have h2 : Real.exp A + 1 ≤ Real.exp (A + 1) := by
        rw [Real.exp_add]
        nlinarith [Real.add_one_le_exp (1 : ℝ), hexpA0]
      linarith
    have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
    have := Real.log_le_log hBpos hBle
    rwa [Real.log_exp] at this
  have hlogBpos : (0 : ℝ) < Real.log B := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2
    linarith
  have habsorb : Real.log (Real.log B) ≤ 14 * δ * s + ((7 * δ / 8) * (16 * Λ + 1) - 1 -
      Real.log (7 * δ / 8)) := by
    have h1 : Real.log (Real.log B) ≤ Real.log (A + 1) := Real.log_le_log hlogBpos hlogB
    have h2 := log_le_mul_sub (c := 7 * δ / 8) (by positivity) (u := A + 1) (by linarith)
    have h3 : (7 * δ / 8) * (A + 1) = 14 * δ * s + (7 * δ / 8) * (16 * Λ + 1) := by
      rw [hAsplit]; ring
    linarith [h3 ▸ h2]
  -- put it together
  set X : ℝ := Real.log (Real.log Y) with hXdef
  have hlog8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (x := (8:ℝ)) (by norm_num); linarith
  have hstep1 : 128 * δ * ((2 / π) * (1 + Real.log Kc))
      ≤ 128 * δ * ((2 / 3) * (1 + (Real.log 8 + (s + X)))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul ?_ (by linarith [hlogK]) (by linarith) (by norm_num)
    · rw [div_le_div_iff₀ hpi (by norm_num)]
      linarith [Real.pi_gt_three]
  have h_a : δ * Real.log 8 ≤ δ * 7 := mul_le_mul_of_nonneg_left hlog8 hδ0.le
  have h_b : (0:ℝ) ≤ δ * s := by positivity
  have h_c : (0:ℝ) ≤ δ * (X + 0.443) := mul_nonneg hδ0.le (by linarith)
  have h_d : (0:ℝ) ≤ δ * Λ := mul_nonneg hδ0.le (by linarith)
  -- split the resonant primes at the cutoff
  rw [resonantMass, ← Finset.sum_filter_add_sum_filter_not
    ((Erdos67b.primesUpTo Y).filter (fun p => |(primePhase z t p).arg| < δ))
    (fun p => A ≤ Real.log p)]
  have hbig := resonant_big_mass_le (z := z) (t := t) (δ := δ) (A := A) (Y := Y) hz hδ0 hδ ht hA16
    (G := ((Erdos67b.primesUpTo Y).filter (fun p => |(primePhase z t p).arg| < δ)).filter
      (fun p => A ≤ Real.log p))
    (fun p hp => by
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      obtain ⟨hp3, hp4⟩ := Finset.mem_filter.1 hp1
      obtain ⟨hpp, hpY⟩ := Erdos67b.mem_primesUpTo.1 hp3
      exact ⟨hpp, by exact_mod_cast hpY, hp4, hp2⟩)
  rw [← hKcdef] at hbig
  have hsmall := small_prime_mass_le (B := B) hB2
    (G := ((Erdos67b.primesUpTo Y).filter (fun p => |(primePhase z t p).arg| < δ)).filter
      (fun p => ¬ A ≤ Real.log p))
    (fun p hp => by
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      obtain ⟨hp3, _⟩ := Finset.mem_filter.1 hp1
      obtain ⟨hpp, _⟩ := Erdos67b.mem_primesUpTo.1 hp3
      refine ⟨hpp, ?_⟩
      have hplt : Real.log p < A := lt_of_not_ge hp2
      have hppos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpp.pos
      have hlt : (p : ℝ) < Real.exp A := by
        rw [← Real.exp_log hppos]; exact Real.exp_lt_exp.2 hplt
      exact Nat.cast_le.mp (le_trans hlt.le hBge))
  linarith [hbig, hsmall, herr, habsorb, hstep1, h_a, h_b, h_c, h_d, hmert, hδ0]



/-! ## The named input is gone: the unconditional consequences -/

/-- **TT's hypothesis (3.3) for `z^ω`, unconditionally.**  `ttNonPretentious_of_uniformResonantMass`
with its one hypothesis discharged. -/
theorem ttNonPretentious_zOmegaNat {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {κ : ℝ}
    (hκ : κ ≤ ttExponent z) :
    ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ → TTNonPretentious (zOmegaNat z) X L :=
  ttNonPretentious_of_uniformResonantMass uniformResonantMass_holds hz hz1 hκ

/-- **`LogToNaturalCorrelationNZ 2` from the ONE named open problem.**  After this file the
`D = 2` layer rests on `TwoPointNaturalCorrelationNoExc` alone. -/
theorem logToNaturalCorrelationNZ_two_of_noExc' (h : TwoPointNaturalCorrelationNoExc) :
    LogToNaturalCorrelationNZ 2 :=
  logToNaturalCorrelationNZ_two_of_noExc h uniformResonantMass_holds

/-- **The `D = 2` natural-density depth rung**, from `TwoPointNaturalCorrelationNoExc` and
`ProgressionLogRung 2` ALONE. -/
theorem depthAvg_two_tendsto_of_noExc (h : TwoPointNaturalCorrelationNoExc) {b Q : ℕ}
    (hQ : 0 < Q) (P j : ℕ) (hh : ℤ) (hζ : depthRoot b hh 0 ≠ 1) (hrung : ProgressionLogRung 2) :
    Filter.Tendsto (fun N : ℕ => depthAvg b P Q j hh 2 N) Filter.atTop (nhds 0) :=
  depthAvg_two_tendsto_of_named h uniformResonantMass_holds hQ P j hh hζ hrung

#print axioms NormalNumbers.CastingOut.sharp_window_mass_le
#print axioms NormalNumbers.CastingOut.resonant_big_mass_le
#print axioms NormalNumbers.CastingOut.uniformResonantMass_holds
#print axioms NormalNumbers.CastingOut.ttNonPretentious_zOmegaNat
#print axioms NormalNumbers.CastingOut.depthAvg_two_tendsto_of_noExc

end CastingOut

end NormalNumbers
