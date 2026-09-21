import NormalNumbers.G4WiringRough

/-!
# ONE summatory node under the whole SD sector (`RoughSummatory`)

`KICKOFF-2026-09-20-summatory-node-lap.md`.  Every window and half-window sum in the two surviving
nodes (`RoughIndependenceAt h 2`, `ParityDiscrepancy h`) is a difference of partial sums of the
rough phase product.  This file freezes ONE Selberg–Delange-with-shifts statement about those
partial sums, **restricted to parity classes**, and derives both nodes from it.

`RoughSummatory` is never proved here — it is the frozen analytic node (blueprint probe 11).
-/

open Filter Topology Finset
open scoped BigOperators

namespace NormalNumbers.G4

open NormalNumbers.PrimeLambert

/-! ### Leaf 1: the summatory node and its elementary identities -/

/-- The rough phase product over a site set `s` at `m`: `∏_{j∈s} e(h ω_{>2}(m+j)/4^j)`. -/
noncomputable def roughProd (h : ℤ) (s : Finset ℕ) (m : ℕ) : ℂ := ∏ j ∈ s, roughPhase h j m

/-- Summatory function of `roughProd` over `m < M` in the residue class `a mod 2`. -/
noncomputable def roughClassSum (h : ℤ) (s : Finset ℕ) (a M : ℕ) : ℂ :=
  ∑ m ∈ (Finset.range M).filter (fun m => m % 2 = a), roughProd h s m

/-- The Selberg–Delange exponent of a site set: `Σ_{j∈s} (e(h/4^j) − 1)`. -/
noncomputable def sdExponent (h : ℤ) (s : Finset ℕ) : ℂ :=
  ∑ j ∈ s, (ePhase ((h : ℝ) / (4 : ℝ) ^ j) - 1)

/-- Main term of one parity class at scale `M`: `(c/2) · M · (log M)^κ`. -/
noncomputable def sdMain (c κ : ℂ) (M : ℕ) : ℂ :=
  c / 2 * (M : ℂ) * (((Real.log M : ℝ)) : ℂ) ^ κ

/-- **The summatory node (frozen conjecture; blueprint probe 11).**  Selberg–Delange with shifts for
the rough phase product, on each parity class, for the prefixes `[1,k]` and the singletons `{k}`,
`1 ≤ k ≤ windowJ M`: main term `(c_s/2)·M·(log M)^{κ_s}` with `κ_s = sdExponent h s`, the SAME
constant `c_s` on both classes; relative error `C/log M` for prefixes and `C·4^{-k}/log M` for
singletons (analytic in `z_k`, exact at `z_k = 1`); constants bounded above, bounded away from `0`,
and `c_{\{k\}} → 1` geometrically. -/
def RoughSummatory (h : ℤ) : Prop :=
  ∃ (c : Finset ℕ → ℂ) (B C δ : ℝ), 0 ≤ C ∧ 0 < δ ∧
    (∀ s, ‖c s‖ ≤ B) ∧
    (∀ k, 1 ≤ k → δ ≤ ‖c (Finset.Icc 1 k)‖ ∧ δ ≤ ‖c {k}‖) ∧
    (∀ k, 1 ≤ k → ‖c {k} - 1‖ ≤ B * ((1:ℝ)/4) ^ k) ∧
    ∀ᶠ M : ℕ in atTop, ∀ a, a < 2 → ∀ k, 1 ≤ k → k ≤ windowJ M →
      ‖roughClassSum h (Finset.Icc 1 k) a M
          - sdMain (c (Finset.Icc 1 k)) (sdExponent h (Finset.Icc 1 k)) M‖
        ≤ C / Real.log M * ((M : ℝ) * Real.log M ^ (sdExponent h (Finset.Icc 1 k)).re)
      ∧ ‖roughClassSum h {k} a M - sdMain (c {k}) (sdExponent h {k}) M‖
        ≤ C * ((1:ℝ)/4) ^ k / Real.log M * ((M : ℝ) * Real.log M ^ (sdExponent h {k}).re)

lemma roughProd_singleton (h : ℤ) (k m : ℕ) : roughProd h {k} m = roughPhase h k m := by
  simp [roughProd]

lemma norm_roughProd (h : ℤ) (s : Finset ℕ) (m : ℕ) : ‖roughProd h s m‖ = 1 := by
  rw [roughProd, norm_prod]
  exact Finset.prod_eq_one (fun j _ => norm_ePhase _)

/-- Both classes together give the plain partial sum. -/
theorem roughClassSum_zero_add_one (h : ℤ) (s : Finset ℕ) (M : ℕ) :
    roughClassSum h s 0 M + roughClassSum h s 1 M = ∑ m ∈ Finset.range M, roughProd h s m := by
  classical
  rw [roughClassSum, roughClassSum]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range M) (fun m => m % 2 = 0)]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext m; simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

/-- The exponent is additive along prefixes. -/
theorem sdExponent_Icc_succ (h : ℤ) (k : ℕ) :
    sdExponent h (Finset.Icc 1 (k+1)) = sdExponent h (Finset.Icc 1 k) + sdExponent h {k+1} := by
  rw [sdExponent, sdExponent, sdExponent, Finset.sum_singleton]
  by_cases hk : 1 ≤ k + 1
  · rw [Finset.sum_Icc_succ_top hk]
  · omega

/-- The window quantities are differences of the summatory function. -/
theorem roughPrefixMean_eq_classSum (N : ℕ) (h : ℤ) (k : ℕ) (hN : 0 < N) :
    roughPrefixMean N h k
      = ((roughClassSum h (Finset.Icc 1 k) 0 (2*N) + roughClassSum h (Finset.Icc 1 k) 1 (2*N))
          - (roughClassSum h (Finset.Icc 1 k) 0 N + roughClassSum h (Finset.Icc 1 k) 1 N)) / N := by
  rw [roughClassSum_zero_add_one, roughClassSum_zero_add_one, roughPrefixMean, winMean]
  congr 1
  rw [← Finset.sum_Ico_eq_sub _ (by omega : N ≤ 2 * N)]
  rfl

theorem roughSiteMean_eq_classSum (N : ℕ) (h : ℤ) (k : ℕ) (hN : 0 < N) :
    roughSiteMean N h k 2
      = ((roughClassSum h {k} 0 (2*N) + roughClassSum h {k} 1 (2*N))
          - (roughClassSum h {k} 0 N + roughClassSum h {k} 1 N)) / N := by
  rw [roughClassSum_zero_add_one, roughClassSum_zero_add_one, roughSiteMean_eq_winMean, winMean]
  congr 1
  rw [← Finset.sum_Ico_eq_sub _ (by omega : N ≤ 2 * N)]
  exact Finset.sum_congr rfl (fun m _ => (roughProd_singleton h k m).symm)

/-! ### Leaf 2: analytic toolbox -/

/-- `Re (e(t) − 1) ≤ 0`. -/
lemma re_ePhase_sub_one_nonpos (t : ℝ) : (ePhase t - 1).re ≤ 0 := by
  have h1 : (ePhase t).re ≤ ‖ePhase t‖ := Complex.re_le_norm _
  rw [norm_ePhase] at h1
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma re_sdExponent_nonpos (h : ℤ) (s : Finset ℕ) : (sdExponent h s).re ≤ 0 := by
  rw [sdExponent, Complex.re_sum]
  exact Finset.sum_nonpos (fun j _ => re_ePhase_sub_one_nonpos _)

/-- `‖e(h/4^j) − 1‖ ≤ 4π|h|·4^{-j}`. -/
lemma norm_ePhase_site_sub_one (h : ℤ) (j : ℕ) :
    ‖ePhase ((h : ℝ) / (4:ℝ)^j) - 1‖ ≤ 4 * Real.pi * |(h : ℝ)| * ((1:ℝ)/4) ^ j := by
  have hd : ‖ePhase ((h : ℝ) / (4:ℝ)^j) - ePhase 0‖ ≤ 4 * Real.pi * |(h : ℝ) / (4:ℝ)^j - 0| :=
    norm_ePhase_sub _ _
  have h4 : (0 : ℝ) < (4:ℝ)^j := by positivity
  have habs2 : |(h : ℝ) / (4:ℝ)^j - 0| = |(h:ℝ)| * ((1:ℝ)/4)^j := by
    rw [sub_zero, abs_div, abs_of_pos h4, div_pow, one_pow]
    field_simp
  rw [ePhase_zero, habs2] at hd
  calc ‖ePhase ((h : ℝ) / (4:ℝ)^j) - 1‖ ≤ 4 * Real.pi * (|(h:ℝ)| * ((1:ℝ)/4)^j) := hd
    _ = 4 * Real.pi * |(h : ℝ)| * ((1:ℝ)/4) ^ j := by ring

lemma norm_sdExponent_le (h : ℤ) (s : Finset ℕ) :
    ‖sdExponent h s‖ ≤ 4 * Real.pi * |(h : ℝ)| * ∑ j ∈ s, ((1:ℝ)/4) ^ j := by
  rw [sdExponent, Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => norm_ePhase_site_sub_one h j))

lemma norm_sdExponent_singleton (h : ℤ) (k : ℕ) :
    ‖sdExponent h {k}‖ ≤ 4 * Real.pi * |(h : ℝ)| * ((1:ℝ)/4) ^ k := by
  simpa using norm_sdExponent_le h {k}

lemma norm_sdExponent_Icc (h : ℤ) (k : ℕ) :
    ‖sdExponent h (Finset.Icc 1 k)‖ ≤ 4 * Real.pi * |(h : ℝ)| := by
  refine (norm_sdExponent_le h (Finset.Icc 1 k)).trans ?_
  have hIcc : Finset.Icc 1 k = Finset.Ico 1 (k+1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have h1 : ∑ j ∈ Finset.Icc 1 k, ((1:ℝ)/4) ^ j ≤ 1 := by
    rw [hIcc]
    have := sum_quarter_pow_Ico_le 1 (k+1)
    norm_num at this ⊢
    linarith
  have h2 : (0:ℝ) ≤ 4 * Real.pi * |(h : ℝ)| := by positivity
  nlinarith [h1, h2, Finset.sum_nonneg (fun (j : ℕ) (_ : j ∈ Finset.Icc 1 k) =>
    (by positivity : (0:ℝ) ≤ ((1:ℝ)/4) ^ j))]

/-- `((ab : ℝ) : ℂ)^κ = (a:ℂ)^κ (b:ℂ)^κ` for positive reals. -/
lemma ofReal_mul_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (κ : ℂ) :
    (((a * b : ℝ)) : ℂ) ^ κ = ((a : ℝ) : ℂ) ^ κ * ((b : ℝ) : ℂ) ^ κ := by
  have hab : (0:ℝ) < a * b := mul_pos ha hb
  rw [Complex.cpow_def_of_ne_zero (by simpa using Complex.ofReal_ne_zero.mpr hab.ne'),
    Complex.cpow_def_of_ne_zero (by simpa using Complex.ofReal_ne_zero.mpr ha.ne'),
    Complex.cpow_def_of_ne_zero (by simpa using Complex.ofReal_ne_zero.mpr hb.ne'),
    ← Complex.exp_add, ← Complex.ofReal_log hab.le, ← Complex.ofReal_log ha.le,
    ← Complex.ofReal_log hb.le, Real.log_mul ha.ne' hb.ne']
  push_cast
  ring_nf

lemma norm_ofReal_cpow {a : ℝ} (ha : 0 < a) (κ : ℂ) :
    ‖((a : ℝ) : ℂ) ^ κ‖ = a ^ κ.re := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]

/-- Monotonicity of the window schedule. -/
lemma windowJ_mono {M N : ℕ} (hMN : M ≤ N) : windowJ M ≤ windowJ N := by
  rw [windowJ, windowJ]
  exact Nat.succ_le_succ (Nat.log_mono_right (Nat.log_mono_right hMN))

/-- `K (log N)^n ≤ N` eventually. -/
lemma eventually_const_mul_log_pow_le (n : ℕ) (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K * Real.log N ^ n ≤ (N : ℝ) := by
  have hlim : Tendsto (fun x : ℝ => Real.log x ^ n / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  have hlim' : Tendsto (fun N : ℕ => Real.log N ^ n / (1 * (N:ℝ) + 0)) atTop (𝓝 0) :=
    hlim.comp tendsto_natCast_atTop_atTop
  have hK : (0:ℝ) < 1 / (|K| + 1) := by positivity
  have hev := (hlim'.eventually (eventually_lt_nhds hK))
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
  simp only [one_mul, add_zero] at hN
  have h1 : Real.log N ^ n ≤ (N:ℝ) / (|K| + 1) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_lt_div_iff₀ hNpos (by positivity)] at hN
    nlinarith [hN]
  have h2 : K ≤ |K| := le_abs_self K
  have hlnn : (0:ℝ) ≤ Real.log N ^ n :=
    pow_nonneg (Real.log_nonneg (by exact_mod_cast hN0 : (1:ℝ) ≤ N)) n
  have h3 : K * Real.log N ^ n ≤ |K| * Real.log N ^ n :=
    mul_le_mul_of_nonneg_right h2 hlnn
  have h4 : |K| * Real.log N ^ n ≤ |K| * ((N:ℝ) / (|K| + 1)) :=
    mul_le_mul_of_nonneg_left h1 (abs_nonneg K)
  have h5 : |K| * ((N:ℝ) / (|K| + 1)) ≤ (N:ℝ) := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg K, hNpos.le]
  linarith

/-! ### Leaf 3: from the node to the window quantities -/

section Wiring

variable {h : ℤ}

end Wiring

/-! ### Leaf 4–6: the wirings -/

/-- **Wiring 1**: the summatory node gives the rough factorisation. -/
theorem roughIndependenceAt_two_of_summatory {h : ℤ} (hS : RoughSummatory h) :
    RoughIndependenceAt h 2 := by
  sorry

/-- **Wiring 2**: the summatory node gives the parity node. -/
theorem parityDiscrepancy_of_summatory {h : ℤ} (hh : h ≠ 0) (hc : ¬ ChowlaSector h)
    (hS : RoughSummatory h) : ParityDiscrepancy h := by
  sorry

/-- **Headline**: off the Chowla sector the G₄ window law rests on ONE analytic input. -/
theorem isNormal_G4_of_summatory
    (hSD : ∀ h : ℤ, h ≠ 0 → ¬ ChowlaSector h → RoughSummatory h)
    (hCh : ∀ h : ℤ, h ≠ 0 → ChowlaSector h → WindowDecay h)
    (hSite : SiteDecayFull) : IsNormal 4 (primeLambertAtBase 4) :=
  isNormal_G4_of_parity
    (fun h hh hc => ⟨roughIndependenceAt_two_of_summatory (hSD h hh hc),
      parityDiscrepancy_of_summatory hh hc (hSD h hh hc)⟩) hCh hSite

end NormalNumbers.G4
