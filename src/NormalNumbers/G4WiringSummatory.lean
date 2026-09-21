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

/-- One parity class: the window difference tracks the main-term difference with error `3E/L`. -/
lemma node_winDiff {s : Finset ℕ} {c κ : ℂ} {E : ℝ} {N a : ℕ}
    (hE : 0 ≤ E) (hκre : κ.re ≤ 0) (hN : 0 < N) (hL1 : 1 ≤ Real.log N)
    (hA : ‖roughClassSum h s a N - sdMain c κ N‖
        ≤ E / Real.log N * ((N : ℝ) * Real.log N ^ κ.re))
    (hB : ‖roughClassSum h s a (2*N) - sdMain c κ (2*N)‖
        ≤ E / Real.log ((2*N : ℕ) : ℝ)
            * (((2*N : ℕ) : ℝ) * Real.log ((2*N : ℕ) : ℝ) ^ κ.re)) :
    ‖(roughClassSum h s a (2*N) - roughClassSum h s a N)
        - (sdMain c κ (2*N) - sdMain c κ N)‖
      ≤ 3 * E / Real.log N * ((N : ℝ) * Real.log N ^ κ.re) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hL0 : (0:ℝ) < Real.log N := lt_of_lt_of_le one_pos hL1
  have hcast : ((2*N : ℕ) : ℝ) = 2 * (N:ℝ) := by push_cast; ring
  have hlog2 : Real.log ((2*N : ℕ) : ℝ) = Real.log 2 + Real.log N := by
    rw [hcast, Real.log_mul (by norm_num) hNR.ne']
  have hlog2pos : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have hge : Real.log N ≤ Real.log ((2*N : ℕ) : ℝ) := by rw [hlog2]; linarith
  have hrp : Real.log ((2*N : ℕ) : ℝ) ^ κ.re ≤ Real.log N ^ κ.re :=
    Real.rpow_le_rpow_of_nonpos hL0 hge hκre
  have hrpnn : (0:ℝ) ≤ Real.log N ^ κ.re := Real.rpow_nonneg hL0.le _
  have hrpnn2 : (0:ℝ) ≤ Real.log ((2*N : ℕ) : ℝ) ^ κ.re :=
    Real.rpow_nonneg (by linarith) _
  have hstep : E / Real.log ((2*N : ℕ) : ℝ) * (((2*N : ℕ) : ℝ) * Real.log ((2*N : ℕ) : ℝ) ^ κ.re)
      ≤ 2 * (E / Real.log N * ((N : ℝ) * Real.log N ^ κ.re)) := by
    have h1 : E / Real.log ((2*N : ℕ) : ℝ) ≤ E / Real.log N :=
      div_le_div_of_nonneg_left hE hL0 hge
    have h2 : ((2*N : ℕ) : ℝ) * Real.log ((2*N : ℕ) : ℝ) ^ κ.re
        ≤ 2 * ((N : ℝ) * Real.log N ^ κ.re) := by
      calc ((2*N : ℕ) : ℝ) * Real.log ((2*N : ℕ) : ℝ) ^ κ.re
          ≤ ((2*N : ℕ) : ℝ) * Real.log N ^ κ.re :=
            mul_le_mul_of_nonneg_left hrp (by positivity)
        _ = 2 * ((N : ℝ) * Real.log N ^ κ.re) := by rw [hcast]; ring
    have h3 : (0:ℝ) ≤ E / Real.log ((2*N : ℕ) : ℝ) := by positivity
    have h4 : (0:ℝ) ≤ 2 * ((N : ℝ) * Real.log N ^ κ.re) := by positivity
    calc E / Real.log ((2*N : ℕ) : ℝ) * (((2*N : ℕ) : ℝ) * Real.log ((2*N : ℕ) : ℝ) ^ κ.re)
        ≤ E / Real.log ((2*N : ℕ) : ℝ) * (2 * ((N : ℝ) * Real.log N ^ κ.re)) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ ≤ E / Real.log N * (2 * ((N : ℝ) * Real.log N ^ κ.re)) :=
          mul_le_mul_of_nonneg_right h1 h4
      _ = 2 * (E / Real.log N * ((N : ℝ) * Real.log N ^ κ.re)) := by ring
  have hsplit : (roughClassSum h s a (2*N) - roughClassSum h s a N)
      - (sdMain c κ (2*N) - sdMain c κ N)
      = (roughClassSum h s a (2*N) - sdMain c κ (2*N))
        - (roughClassSum h s a N - sdMain c κ N) := by ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have hfin : ‖roughClassSum h s a (2*N) - sdMain c κ (2*N)‖
      ≤ 2 * (E / Real.log N * ((N : ℝ) * Real.log N ^ κ.re)) := le_trans hB hstep
  have : 3 * E / Real.log N * ((N : ℝ) * Real.log N ^ κ.re)
      = 2 * (E / Real.log N * ((N : ℝ) * Real.log N ^ κ.re))
        + E / Real.log N * ((N : ℝ) * Real.log N ^ κ.re) := by ring
  rw [this]
  exact add_le_add hfin hA

/-- The main-term difference, normalised. -/
lemma sdMain_diff_eq {c κ : ℂ} {N : ℕ} (hN : 0 < N) (hL1 : 1 ≤ Real.log N) :
    (sdMain c κ (2*N) - sdMain c κ N) * 2 / (N : ℂ)
      = c * ((Real.log N : ℝ) : ℂ) ^ κ
        * (2 * (((1 + Real.log 2 / Real.log N : ℝ)) : ℂ) ^ κ - 1) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hL0 : (0:ℝ) < Real.log N := lt_of_lt_of_le one_pos hL1
  have hcast : ((2*N : ℕ) : ℝ) = 2 * (N:ℝ) := by push_cast; ring
  have hx : (0:ℝ) < 1 + Real.log 2 / Real.log N := by positivity
  have hlog2 : Real.log ((2*N : ℕ) : ℝ)
      = Real.log N * (1 + Real.log 2 / Real.log N) := by
    rw [hcast, Real.log_mul (by norm_num) hNR.ne']
    field_simp
    ring
  have hcpow : (((Real.log ((2*N : ℕ) : ℝ)) : ℝ) : ℂ) ^ κ
      = ((Real.log N : ℝ) : ℂ) ^ κ * (((1 + Real.log 2 / Real.log N : ℝ)) : ℂ) ^ κ := by
    rw [hlog2, ofReal_mul_cpow hL0 hx]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [sdMain, sdMain, hcpow]
  have h2N : ((2*N : ℕ) : ℂ) = 2 * (N : ℂ) := by push_cast; ring
  rw [h2N]
  field_simp

/-- **The window approximation.**  Both parity classes together: the window mean of `roughProd`
is `c (log N)^κ` up to a relative `O(1/log N)`. -/
lemma node_winApprox {s : Finset ℕ} {c κ : ℂ} {E Bκ : ℝ} {N : ℕ}
    (hE : 0 ≤ E) (hκre : κ.re ≤ 0) (hκn : ‖κ‖ ≤ Bκ) (hBκ : 0 ≤ Bκ)
    (hN : 0 < N) (hL1 : 1 ≤ Real.log N) (hLB : Bκ ≤ Real.log N)
    (hA : ∀ a, a < 2 → ‖roughClassSum h s a N - sdMain c κ N‖
        ≤ E / Real.log N * ((N : ℝ) * Real.log N ^ κ.re))
    (hB : ∀ a, a < 2 → ‖roughClassSum h s a (2*N) - sdMain c κ (2*N)‖
        ≤ E / Real.log ((2*N : ℕ) : ℝ)
            * (((2*N : ℕ) : ℝ) * Real.log ((2*N : ℕ) : ℝ) ^ κ.re)) :
    ‖((roughClassSum h s 0 (2*N) + roughClassSum h s 1 (2*N))
          - (roughClassSum h s 0 N + roughClassSum h s 1 N)) / (N : ℂ)
        - c * ((Real.log N : ℝ) : ℂ) ^ κ‖
      ≤ (6 * E + 4 * ‖c‖ * Bκ) / Real.log N * Real.log N ^ κ.re := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hL0 : (0:ℝ) < Real.log N := lt_of_lt_of_le one_pos hL1
  have hrpnn : (0:ℝ) ≤ Real.log N ^ κ.re := Real.rpow_nonneg hL0.le _
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set L : ℝ := Real.log N with hLdef
  set x : ℝ := Real.log 2 / L with hxdef
  have hd0 := node_winDiff (h := h) hE hκre hN hL1 (hA 0 (by norm_num)) (hB 0 (by norm_num))
  have hd1 := node_winDiff (h := h) hE hκre hN hL1 (hA 1 (by norm_num)) (hB 1 (by norm_num))
  set D : ℂ := (roughClassSum h s 0 (2*N) + roughClassSum h s 1 (2*N))
      - (roughClassSum h s 0 N + roughClassSum h s 1 N) with hD
  set Md : ℂ := sdMain c κ (2*N) - sdMain c κ N with hMd
  have hDsplit : D - 2 * Md
      = ((roughClassSum h s 0 (2*N) - roughClassSum h s 0 N) - Md)
        + ((roughClassSum h s 1 (2*N) - roughClassSum h s 1 N) - Md) := by
    rw [hD]; ring
  have hDnorm : ‖D - 2 * Md‖ ≤ 6 * E / L * ((N : ℝ) * L ^ κ.re) := by
    rw [hDsplit]
    refine (norm_add_le _ _).trans ?_
    have : 6 * E / L * ((N : ℝ) * L ^ κ.re)
        = 3 * E / L * ((N : ℝ) * L ^ κ.re) + 3 * E / L * ((N : ℝ) * L ^ κ.re) := by ring
    rw [this]
    exact add_le_add hd0 hd1
  -- divide by N
  have hdiv : ‖D / (N:ℂ) - 2 * Md / (N:ℂ)‖ ≤ 6 * E / L * L ^ κ.re := by
    have heq : D / (N:ℂ) - 2 * Md / (N:ℂ) = (D - 2 * Md) / (N:ℂ) := by ring
    rw [heq, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hNR]
    calc ‖D - 2 * Md‖ ≤ 6 * E / L * ((N : ℝ) * L ^ κ.re) := hDnorm
      _ = 6 * E / L * L ^ κ.re * (N:ℝ) := by ring
  -- the main term
  have hmain : 2 * Md / (N:ℂ)
      = c * ((L : ℝ) : ℂ) ^ κ * (2 * (((1 + x : ℝ)) : ℂ) ^ κ - 1) := by
    rw [hxdef, hLdef]
    rw [← sdMain_diff_eq (c := c) (κ := κ) hN hL1]
    rw [hMd]; ring
  have hxnn : (0:ℝ) ≤ x := by rw [hxdef]; positivity
  have hlog2lt : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkx : ‖κ‖ * x ≤ 1 := by
    rw [hxdef]
    have h1 : ‖κ‖ * (Real.log 2 / L) ≤ Bκ * (Real.log 2 / L) :=
      mul_le_mul_of_nonneg_right hκn (by positivity)
    have h2 : Bκ * (Real.log 2 / L) ≤ Bκ * (1 / L) := by
      refine mul_le_mul_of_nonneg_left ?_ hBκ
      rw [div_le_div_iff_of_pos_right hL0]
      nlinarith [hlog2lt, hL0]
    have h3 : Bκ * (1 / L) ≤ 1 := by
      rw [mul_one_div, div_le_one hL0]; exact hLB
    linarith
  have hcpow := norm_ofReal_one_add_cpow_sub_one_le x hxnn κ hkx
  have hmainclose : ‖c * ((L : ℝ) : ℂ) ^ κ * (2 * (((1 + x : ℝ)) : ℂ) ^ κ - 1)
      - c * ((L : ℝ) : ℂ) ^ κ‖ ≤ 4 * ‖c‖ * Bκ / L * L ^ κ.re := by
    have heq : c * ((L : ℝ) : ℂ) ^ κ * (2 * (((1 + x : ℝ)) : ℂ) ^ κ - 1)
        - c * ((L : ℝ) : ℂ) ^ κ
        = c * ((L : ℝ) : ℂ) ^ κ * (2 * ((((1 + x : ℝ)) : ℂ) ^ κ - 1)) := by ring
    rw [heq, norm_mul, norm_mul, norm_ofReal_cpow hL0, norm_mul]
    have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [h2]
    have hstep : 2 * ‖(((1 + x : ℝ)) : ℂ) ^ κ - 1‖ ≤ 4 * (‖κ‖ * x) := by linarith [hcpow]
    have hkxb : ‖κ‖ * x ≤ Bκ * Real.log 2 / L := by
      rw [hxdef]
      have := mul_le_mul_of_nonneg_right hκn (by positivity : (0:ℝ) ≤ Real.log 2 / L)
      calc ‖κ‖ * (Real.log 2 / L) ≤ Bκ * (Real.log 2 / L) := this
        _ = Bκ * Real.log 2 / L := by ring
    have hfin : 2 * ‖(((1 + x : ℝ)) : ℂ) ^ κ - 1‖ ≤ 4 * Bκ / L := by
      have h5 : Bκ * Real.log 2 / L ≤ Bκ / L := by
        rw [div_le_div_iff_of_pos_right hL0]
        nlinarith [hBκ, hlog2lt, hlog2pos, hL0]
      have hgoal : (4:ℝ) * Bκ / L = 4 * (Bκ / L) := by ring
      have hkxb2 : ‖κ‖ * x ≤ Bκ / L := le_trans hkxb h5
      rw [hgoal]
      linarith [hstep, hkxb2]
    have hcnn : (0:ℝ) ≤ ‖c‖ := norm_nonneg _
    calc ‖c‖ * L ^ κ.re * (2 * ‖(((1 + x : ℝ)) : ℂ) ^ κ - 1‖)
        ≤ ‖c‖ * L ^ κ.re * (4 * Bκ / L) := by
          exact mul_le_mul_of_nonneg_left hfin (by positivity)
      _ = 4 * ‖c‖ * Bκ / L * L ^ κ.re := by ring
  calc ‖D / (N:ℂ) - c * ((L : ℝ) : ℂ) ^ κ‖
      ≤ ‖D / (N:ℂ) - 2 * Md / (N:ℂ)‖
        + ‖2 * Md / (N:ℂ) - c * ((L : ℝ) : ℂ) ^ κ‖ := by
        have := norm_add_le (D / (N:ℂ) - 2 * Md / (N:ℂ))
          (2 * Md / (N:ℂ) - c * ((L : ℝ) : ℂ) ^ κ)
        simpa using this
    _ ≤ 6 * E / L * L ^ κ.re + 4 * ‖c‖ * Bκ / L * L ^ κ.re := by
        refine add_le_add hdiv ?_
        rw [hmain]; exact hmainclose
    _ = (6 * E + 4 * ‖c‖ * Bκ) / L * L ^ κ.re := by ring

/-- **Packaging**: the node gives uniform approximations for the rough prefix and site means. -/
theorem summatory_means_approx {h : ℤ} (hS : RoughSummatory h) :
    ∃ (c : Finset ℕ → ℂ) (B A δ : ℝ), 0 ≤ A ∧ 0 < δ ∧ 0 ≤ B ∧
      (∀ s, ‖c s‖ ≤ B) ∧
      (∀ k, 1 ≤ k → δ ≤ ‖c (Finset.Icc 1 k)‖ ∧ δ ≤ ‖c {k}‖) ∧
      (∀ k, 1 ≤ k → ‖c {k} - 1‖ ≤ B * ((1:ℝ)/4) ^ k) ∧
      (∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ windowJ N →
        ‖roughPrefixMean N h k
            - c (Finset.Icc 1 k) * ((Real.log N : ℝ) : ℂ) ^ sdExponent h (Finset.Icc 1 k)‖
          ≤ A / Real.log N * Real.log N ^ (sdExponent h (Finset.Icc 1 k)).re
        ∧ ‖roughSiteMean N h k 2 - c {k} * ((Real.log N : ℝ) : ℂ) ^ sdExponent h {k}‖
          ≤ A * ((1:ℝ)/4) ^ k / Real.log N * Real.log N ^ (sdExponent h {k}).re)
      ∧ (∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ windowJ N → ∀ a, a < 2 → ∀ b, b < 2 →
        ‖(roughClassSum h (Finset.Icc 1 k) a (2*N) - roughClassSum h (Finset.Icc 1 k) a N)
            - (roughClassSum h (Finset.Icc 1 k) b (2*N) - roughClassSum h (Finset.Icc 1 k) b N)‖
          ≤ A / Real.log N
              * ((N : ℝ) * Real.log N ^ (sdExponent h (Finset.Icc 1 k)).re)
        ∧ ‖(roughClassSum h {k} a (2*N) - roughClassSum h {k} a N)
            - (roughClassSum h {k} b (2*N) - roughClassSum h {k} b N)‖
          ≤ A * ((1:ℝ)/4) ^ k / Real.log N
              * ((N : ℝ) * Real.log N ^ (sdExponent h {k}).re)) := by
  classical
  obtain ⟨c, B, C, δ, hC, hδ, hcB, hclow, hcone, hev⟩ := hS
  have hBnn : (0:ℝ) ≤ B := le_trans (norm_nonneg _) (hcB ∅)
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  set K : ℝ := 4 * Real.pi * |(h : ℝ)| with hK
  have hKnn : (0:ℝ) ≤ K := by rw [hK]; positivity
  set A : ℝ := 6 * C + 4 * B * K with hA
  have hAnn : (0:ℝ) ≤ A := by rw [hA]; positivity
  have hdouble : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by show n ≤ 2 * n; omega) tendsto_id
  have hev2 := hdouble.eventually hev
  have hlogK : ∀ᶠ N : ℕ in atTop, max 1 K ≤ Real.log N := by
    have := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop (max 1 K)
  refine ⟨c, B, A, δ, hAnn, hδ, hBnn, hcB, hclow, hcone, ?_, ?_⟩
  · filter_upwards [hev, hev2, hlogK, eventually_gt_atTop 0] with N hN hN2 hNlog hN0
    intro k hk1 hkJ
    have hL1 : (1:ℝ) ≤ Real.log N := le_trans (le_max_left _ _) hNlog
    have hLK : K ≤ Real.log N := le_trans (le_max_right _ _) hNlog
    have hkJ2 : k ≤ windowJ (2 * N) := le_trans hkJ (windowJ_mono (by omega))
    have hq : (0:ℝ) < ((1:ℝ)/4) ^ k := by positivity
    have hq1 : ((1:ℝ)/4) ^ k ≤ 1 := by
      exact pow_le_one₀ (by norm_num) (by norm_num)
    constructor
    · -- prefix
      have hkey := node_winApprox (h := h) (s := Finset.Icc 1 k)
        (c := c (Finset.Icc 1 k)) (κ := sdExponent h (Finset.Icc 1 k)) (E := C) (Bκ := K)
        hC (re_sdExponent_nonpos h _) (by rw [hK]; exact norm_sdExponent_Icc h k) hKnn hN0 hL1 hLK
        (fun a ha => (hN a ha k hk1 hkJ).1) (fun a ha => (hN2 a ha k hk1 hkJ2).1)
      rw [roughPrefixMean_eq_classSum N h k hN0]
      refine le_trans hkey ?_
      have hrp : (0:ℝ) ≤ Real.log N ^ (sdExponent h (Finset.Icc 1 k)).re :=
        Real.rpow_nonneg (by linarith) _
      have hLpos : (0:ℝ) < Real.log N := by linarith
      have h1 : 6 * C + 4 * ‖c (Finset.Icc 1 k)‖ * K ≤ A := by
        rw [hA]
        nlinarith [hcB (Finset.Icc 1 k), hKnn, norm_nonneg (c (Finset.Icc 1 k))]
      have h2 : (6 * C + 4 * ‖c (Finset.Icc 1 k)‖ * K) / Real.log N ≤ A / Real.log N :=
        div_le_div_of_nonneg_right h1 hLpos.le
      exact mul_le_mul_of_nonneg_right h2 hrp
    · -- singleton
      have hkey := node_winApprox (h := h) (s := ({k} : Finset ℕ))
        (c := c {k}) (κ := sdExponent h {k}) (E := C * ((1:ℝ)/4) ^ k)
        (Bκ := K * ((1:ℝ)/4) ^ k)
        (by positivity) (re_sdExponent_nonpos h _)
        (by rw [hK]; simpa [mul_assoc] using norm_sdExponent_singleton h k)
        (by positivity) hN0 hL1
        (by nlinarith [hLK, hKnn, hq, hq1])
        (fun a ha => (hN a ha k hk1 hkJ).2) (fun a ha => (hN2 a ha k hk1 hkJ2).2)
      rw [roughSiteMean_eq_classSum N h k hN0]
      refine le_trans hkey ?_
      have hrp : (0:ℝ) ≤ Real.log N ^ (sdExponent h {k}).re :=
        Real.rpow_nonneg (by linarith) _
      have hLpos : (0:ℝ) < Real.log N := by linarith
      have h1 : 6 * (C * ((1:ℝ)/4) ^ k) + 4 * ‖c {k}‖ * (K * ((1:ℝ)/4) ^ k)
          ≤ A * ((1:ℝ)/4) ^ k := by
        rw [hA]
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr (hcB ({k} : Finset ℕ))) hKnn) hq.le]
      have h2 : (6 * (C * ((1:ℝ)/4) ^ k) + 4 * ‖c {k}‖ * (K * ((1:ℝ)/4) ^ k)) / Real.log N
          ≤ A * ((1:ℝ)/4) ^ k / Real.log N :=
        div_le_div_of_nonneg_right h1 hLpos.le
      exact mul_le_mul_of_nonneg_right h2 hrp
  · filter_upwards [hev, hev2, hlogK, eventually_gt_atTop 0] with N hN hN2 hNlog hN0
    intro k hk1 hkJ a ha b hb
    have hL1 : (1:ℝ) ≤ Real.log N := le_trans (le_max_left _ _) hNlog
    have hLpos : (0:ℝ) < Real.log N := by linarith
    have hkJ2 : k ≤ windowJ (2 * N) := le_trans hkJ (windowJ_mono (by omega))
    have hq : (0:ℝ) < ((1:ℝ)/4) ^ k := by positivity
    have hrpP : (0:ℝ) ≤ (N : ℝ) * Real.log N ^ (sdExponent h (Finset.Icc 1 k)).re := by
      have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      positivity
    have hrpS : (0:ℝ) ≤ (N : ℝ) * Real.log N ^ (sdExponent h {k}).re := by
      have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      positivity
    constructor
    · have hda := node_winDiff (h := h) (s := Finset.Icc 1 k) (c := c (Finset.Icc 1 k))
        (κ := sdExponent h (Finset.Icc 1 k)) (E := C) (a := a) hC
        (re_sdExponent_nonpos h _) hN0 hL1 (hN a ha k hk1 hkJ).1 (hN2 a ha k hk1 hkJ2).1
      have hdb := node_winDiff (h := h) (s := Finset.Icc 1 k) (c := c (Finset.Icc 1 k))
        (κ := sdExponent h (Finset.Icc 1 k)) (E := C) (a := b) hC
        (re_sdExponent_nonpos h _) hN0 hL1 (hN b hb k hk1 hkJ).1 (hN2 b hb k hk1 hkJ2).1
      have hsplit : (roughClassSum h (Finset.Icc 1 k) a (2*N)
            - roughClassSum h (Finset.Icc 1 k) a N)
          - (roughClassSum h (Finset.Icc 1 k) b (2*N) - roughClassSum h (Finset.Icc 1 k) b N)
          = ((roughClassSum h (Finset.Icc 1 k) a (2*N) - roughClassSum h (Finset.Icc 1 k) a N)
              - (sdMain (c (Finset.Icc 1 k)) (sdExponent h (Finset.Icc 1 k)) (2*N)
                  - sdMain (c (Finset.Icc 1 k)) (sdExponent h (Finset.Icc 1 k)) N))
            - ((roughClassSum h (Finset.Icc 1 k) b (2*N) - roughClassSum h (Finset.Icc 1 k) b N)
              - (sdMain (c (Finset.Icc 1 k)) (sdExponent h (Finset.Icc 1 k)) (2*N)
                  - sdMain (c (Finset.Icc 1 k)) (sdExponent h (Finset.Icc 1 k)) N)) := by ring
      rw [hsplit]
      refine (norm_sub_le _ _).trans ?_
      have hAC : 6 * C ≤ A := by rw [hA]; nlinarith [hBnn, hKnn]
      have hfin : 3 * C / Real.log N * ((N : ℝ) * Real.log N ^
            (sdExponent h (Finset.Icc 1 k)).re)
          + 3 * C / Real.log N * ((N : ℝ) * Real.log N ^
            (sdExponent h (Finset.Icc 1 k)).re)
          ≤ A / Real.log N * ((N : ℝ) * Real.log N ^
            (sdExponent h (Finset.Icc 1 k)).re) := by
        have h1 : 3 * C / Real.log N + 3 * C / Real.log N ≤ A / Real.log N := by
          rw [← add_div, div_le_div_iff_of_pos_right hLpos]; linarith
        nlinarith [hrpP, h1]
      linarith [hda, hdb, hfin]
    · have hE : (0:ℝ) ≤ C * ((1:ℝ)/4) ^ k := by positivity
      have hda := node_winDiff (h := h) (s := ({k} : Finset ℕ)) (c := c {k})
        (κ := sdExponent h {k}) (E := C * ((1:ℝ)/4) ^ k) (a := a) hE
        (re_sdExponent_nonpos h _) hN0 hL1 (hN a ha k hk1 hkJ).2 (hN2 a ha k hk1 hkJ2).2
      have hdb := node_winDiff (h := h) (s := ({k} : Finset ℕ)) (c := c {k})
        (κ := sdExponent h {k}) (E := C * ((1:ℝ)/4) ^ k) (a := b) hE
        (re_sdExponent_nonpos h _) hN0 hL1 (hN b hb k hk1 hkJ).2 (hN2 b hb k hk1 hkJ2).2
      have hsplit : (roughClassSum h {k} a (2*N) - roughClassSum h {k} a N)
          - (roughClassSum h {k} b (2*N) - roughClassSum h {k} b N)
          = ((roughClassSum h {k} a (2*N) - roughClassSum h {k} a N)
              - (sdMain (c {k}) (sdExponent h {k}) (2*N) - sdMain (c {k}) (sdExponent h {k}) N))
            - ((roughClassSum h {k} b (2*N) - roughClassSum h {k} b N)
              - (sdMain (c {k}) (sdExponent h {k}) (2*N)
                  - sdMain (c {k}) (sdExponent h {k}) N)) := by ring
      rw [hsplit]
      refine (norm_sub_le _ _).trans ?_
      have hAC : 6 * (C * ((1:ℝ)/4) ^ k) ≤ A * ((1:ℝ)/4) ^ k := by
        rw [hA]
        nlinarith [mul_nonneg (mul_nonneg hBnn hKnn) hq.le]
      have h1 : 3 * (C * ((1:ℝ)/4) ^ k) / Real.log N + 3 * (C * ((1:ℝ)/4) ^ k) / Real.log N
          ≤ A * ((1:ℝ)/4) ^ k / Real.log N := by
        rw [← add_div, div_le_div_iff_of_pos_right hLpos]; linarith
      nlinarith [hda, hdb, hrpS, h1]

end Wiring

/-! ### Leaf 5 support: parity bookkeeping -/

lemma classSum_window (h : ℤ) (s : Finset ℕ) (a N : ℕ) :
    roughClassSum h s a (2*N) - roughClassSum h s a N
      = ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => n % 2 = a), roughProd h s n := by
  classical
  rw [roughClassSum, roughClassSum, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ico_eq_sub _ (by omega : N ≤ 2 * N)]

/-- Exact parity count on `[a,b)`. -/
lemma card_parity_Ico (t : ℕ) (ht : t < 2) (a b : ℕ) (hab : a ≤ b) :
    2 * ((Finset.Ico a b).filter (fun n => n % 2 = t)).card + (if b % 2 = t then 1 else 0)
      = (b - a) + (if a % 2 = t then 1 else 0) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
      rw [show b + 1 = b.succ from rfl, Nat.Ico_succ_right_eq_insert_Ico hb, Finset.filter_insert]
      by_cases hbt : b % 2 = t
      · rw [if_pos hbt, Finset.card_insert_of_notMem (by simp)]
        have h2 : ¬ (b.succ % 2 = t) := by omega
        rw [if_pos hbt] at ih
        rw [if_neg h2]
        omega
      · rw [if_neg hbt]
        have h2 : b.succ % 2 = t := by omega
        rw [if_neg hbt] at ih
        rw [if_pos h2]
        omega

/-- Evens and odds in `[a,b)` differ in count by at most one. -/
lemma card_parity_Ico_le (t : ℕ) (ht : t < 2) (a b : ℕ) (hab : a ≤ b) :
    2 * ((Finset.Ico a b).filter (fun n => n % 2 = t)).card ≤ (b - a) + 1
    ∧ (b - a) ≤ 2 * ((Finset.Ico a b).filter (fun n => n % 2 = t)).card + 1 := by
  have h := card_parity_Ico t ht a b hab
  by_cases h1 : b % 2 = t <;> by_cases h2 : a % 2 = t <;>
    simp only [h1, h2, if_pos, if_neg, if_true, if_false] at h <;> omega

/-- `parityDisc` in terms of the class difference. -/
lemma norm_parityDisc_le (N j : ℕ) (r : ℕ → ℂ) (hr : ∀ n, ‖r n‖ ≤ 1) (D : ℝ)
    (hdiff : ‖(∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j), r n)
        - ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j), r n‖ ≤ D) :
    ‖parityDisc N j r‖ ≤ (N:ℝ)/2 * D + (N:ℝ)/2 := by
  classical
  set S : Finset ℕ := Finset.Ico N (2*N) with hSdef
  set Se : ℂ := ∑ n ∈ S.filter (fun n => 2 ∣ n + j), r n with hSe
  set So : ℂ := ∑ n ∈ S.filter (fun n => ¬ 2 ∣ n + j), r n with hSo
  set en : ℕ := (S.filter (fun n => 2 ∣ n + j)).card with hen
  set on : ℕ := (S.filter (fun n => ¬ 2 ∣ n + j)).card with hon
  have hcards : en + on = N := by
    rw [hen, hon, Finset.card_filter_add_card_filter_not, hSdef, Nat.card_Ico]
    omega
  have hfe : S.filter (fun n => 2 ∣ n + j) = S.filter (fun n => n % 2 = j % 2) := by
    refine Finset.filter_congr (fun n _ => ?_)
    constructor <;> intro hh <;> omega
  have hpar := card_parity_Ico_le (j % 2) (by omega) N (2*N) (by omega)
  rw [← hfe] at hpar
  have hparity : 2 * en ≤ N + 1 ∧ N ≤ 2 * en + 1 := by
    rw [hen]
    constructor
    · have := hpar.1; omega
    · have := hpar.2; omega
  have hZ : |((on : ℤ) - (en : ℤ))| ≤ 1 := abs_le.mpr ⟨by omega, by omega⟩
  have hdc : ‖((on : ℂ) - (en : ℂ))‖ ≤ 1 := by
    have heq : ((on : ℂ) - (en : ℂ)) = (((on : ℤ) - (en : ℤ) : ℤ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_intCast]
    exact_mod_cast hZ
  have hT : ‖Se + So‖ ≤ (N:ℝ) := by
    rw [hSe, hSo, Finset.sum_filter_add_sum_filter_not]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ S, ‖r n‖ ≤ ∑ _n ∈ S, (1:ℝ) := Finset.sum_le_sum (fun n _ => hr n)
      _ = (N:ℝ) := by rw [Finset.sum_const, hSdef, Nat.card_Ico,
            show 2 * N - N = N from by omega]; simp
  have hid : parityDisc N j r
      = ((on : ℂ) + (en : ℂ)) / 2 * (Se - So) + ((on : ℂ) - (en : ℂ)) / 2 * (Se + So) := by
    rw [parityDisc, ← hSe, ← hSo, ← hen, ← hon]
    ring
  have hsum : ((on : ℂ) + (en : ℂ)) = (N : ℂ) := by
    rw [← Nat.cast_add, show on + en = N from by omega]
  rw [hid, hsum]
  refine (norm_add_le _ _).trans ?_
  have hDnn : (0:ℝ) ≤ D := le_trans (norm_nonneg _) hdiff
  have h1 : ‖(N : ℂ) / 2 * (Se - So)‖ ≤ (N:ℝ)/2 * D := by
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hdiff (by positivity)
  have h2 : ‖((on : ℂ) - (en : ℂ)) / 2 * (Se + So)‖ ≤ (N:ℝ)/2 := by
    rw [norm_mul, norm_div, Complex.norm_ofNat]
    have hnn : (0:ℝ) ≤ ‖Se + So‖ := norm_nonneg _
    have := mul_le_mul hdc hT hnn (by norm_num)
    calc ‖(on : ℂ) - (en : ℂ)‖ / 2 * ‖Se + So‖
        = (‖(on : ℂ) - (en : ℂ)‖ * ‖Se + So‖) / 2 := by ring
      _ ≤ (1 * (N:ℝ)) / 2 := by linarith [this]
      _ = (N:ℝ)/2 := by ring
  linarith

/-- The full site mean is the half-average times the rough site mean, up to the parity gap. -/
lemma fullSiteMean_sub_halfAvg_mul (N : ℕ) (h : ℤ) (j : ℕ) (hj : 1 ≤ j) (hN : 0 < N) :
    fullSiteMean N h j - halfAvg h j * roughSiteMean N h j 2
      = (ePhase ((h:ℝ)/(4:ℝ)^j) - 1) / 2
        * (((∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j), roughPhase h j n)
           - ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j), roughPhase h j n) / N) := by
  classical
  set S : Finset ℕ := Finset.Ico N (2*N) with hSdef
  set α : ℂ := ePhase ((h:ℝ)/(4:ℝ)^j) with hα
  set Se : ℂ := ∑ n ∈ S.filter (fun n => 2 ∣ n + j), roughPhase h j n with hSe
  set So : ℂ := ∑ n ∈ S.filter (fun n => ¬ 2 ∣ n + j), roughPhase h j n with hSo
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hfull : ∑ n ∈ S, ePhase ((h:ℝ) * omegaR (n + j) / (4:ℝ)^j) = α * Se + So := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun n => 2 ∣ n + j), hSe, hSo, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [fullPhase_eq h j n hj, if_pos (Finset.mem_filter.mp hn).2]
    · refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [fullPhase_eq h j n hj, if_neg (Finset.mem_filter.mp hn).2, one_mul]
  have hrough : roughSiteMean N h j 2 = (Se + So) / N := by
    rw [roughSiteMean_eq_winMean, winMean, hSe, hSo, Finset.sum_filter_add_sum_filter_not]
  have hfs : fullSiteMean N h j = (α * Se + So) / N := by
    rw [fullSiteMean, ← hfull]
  rw [hfs, hrough, halfAvg, ← hα]
  field_simp
  ring

lemma parityDisc_class_diff (h : ℤ) (s : Finset ℕ) (N j : ℕ) :
    (∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j), roughProd h s n)
      - ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j), roughProd h s n
    = (roughClassSum h s (j%2) (2*N) - roughClassSum h s (j%2) N)
      - (roughClassSum h s ((j+1)%2) (2*N) - roughClassSum h s ((j+1)%2) N) := by
  classical
  rw [classSum_window, classSum_window]
  congr 1
  · exact Finset.sum_congr (Finset.filter_congr
      (fun n _ => by constructor <;> intro hh <;> omega)) (fun _ _ => rfl)
  · exact Finset.sum_congr (Finset.filter_congr
      (fun n _ => by constructor <;> intro hh <;> omega)) (fun _ _ => rfl)

lemma log_le_of_rpow_le {L z c : ℝ} (hL1 : 1 ≤ L) (m : ℕ) (hc : 0 ≤ c)
    (hpow : L ^ ((m : ℝ) + 1) ≤ c) (hz : -(m:ℝ) ≤ z) : L ≤ c * L ^ z := by
  have h2 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL1
  have h1 : L ^ (-(m:ℝ)) ≤ L ^ z := Real.rpow_le_rpow_of_exponent_le hL1 hz
  have h3 : L ^ ((m:ℝ)+1) * L ^ (-(m:ℝ)) = L := by
    rw [← Real.rpow_add h2]
    norm_num
  calc L = L ^ ((m:ℝ)+1) * L ^ (-(m:ℝ)) := h3.symm
    _ ≤ c * L ^ z := mul_le_mul hpow h1 (Real.rpow_nonneg h2.le _) hc

lemma eventually_rpow_log_le (m : ℕ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ ((m:ℝ)+1) ≤ c * (N:ℝ) := by
  have h := eventually_const_mul_log_pow_le (m+1) (1/c)
  filter_upwards [h] with N hN
  have heq : Real.log N ^ ((m:ℝ)+1) = Real.log N ^ (m+1) := by
    rw [show ((m:ℝ)+1) = (((m+1 : ℕ) : ℝ)) from by push_cast; ring, Real.rpow_natCast]
  rw [heq]
  have h2 := mul_le_mul_of_nonneg_left hN hc.le
  have h3 : c * (1 / c * Real.log N ^ (m+1)) = Real.log N ^ (m+1) := by field_simp
  rw [h3] at h2
  exact h2

lemma neg_bound_le_re {z : ℂ} {K : ℝ} (hz : ‖z‖ ≤ K) : -K ≤ z.re := by
  have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have h2 := abs_le.mp (le_trans h1 hz)
  linarith [h2.1]

/-- **Elementary tail regime (open, elementary).**  For `j > windowJ N` the node says nothing, but
nothing is needed: `4^j ≥ 4^{windowJ N} ≳ (log₂ N)²` while `ω_{>2}(n+j) ≤ log₂(2N+j)`, so every
`roughPhase h j n` is within `O(1/log N)` of `1`; hence `parityDisc N j (roughPhase h j)` — which
vanishes identically when the phase is constant — is `O(N²/log N)`, and `‖fullSiteMean N h j‖ ≥ 1/2`
in the same range.

MISSING (purely elementary, no analytic input): the two inequalities
`‖parityDisc N j r‖ ≤ N² · sup_n ‖r n − 1‖` and
`sup_{n ∈ [N,2N)} ‖roughPhase h j n − 1‖ ≤ 4π|h| · (log₂(2N) + j) / 4^j ≤ C / log N` for
`j > windowJ N`, using `omegaR_le_log` and `Nat.lt_pow_succ_log_self`. -/
theorem parityDisc_tail_small (h : ℤ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
    ∀ j, windowJ N < j → ‖parityDisc N j (roughPhase h j)‖
      ≤ C / Real.log N * ((N:ℝ)^2 * ‖fullSiteMean N h j‖) := by
  sorry

/-! ### Leaf 4–6: the wirings -/

/-! ### Leaf 3: uniform lower bounds on partial products -/

lemma prod_ge_one_sub_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (g ε : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hε : ∀ i ∈ s, 0 ≤ ε i) (hlb : ∀ i ∈ s, 1 - ε i ≤ g i) :
    1 - ∑ i ∈ s, ε i ≤ ∏ i ∈ s, g i := by
  classical
  have hmin := one_sub_sum_le_prod s (fun i => min (g i) 1) ε hε
    (fun i hi => le_min (hg i hi) zero_le_one) (fun _ _ => min_le_right _ _)
    (fun i hi => le_min (hlb i hi) (by linarith [hε i hi]))
  refine hmin.trans (Finset.prod_le_prod (fun i hi => le_min (hg i hi) zero_le_one)
    (fun i _ => min_le_left _ _))

/-- Split a partial product at a cut `j₀`: a crude positive bound below the cut, a Weierstrass
bound above it. -/
lemma prod_Icc_split_lower (J j₀ : ℕ) (hj₀1 : 1 ≤ j₀) (g ε : ℕ → ℝ) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hlow : ∀ j, 1 ≤ j → p ≤ g j) (hεnn : ∀ j, 0 ≤ ε j)
    (hlb : ∀ j, j₀ ≤ j → 1 - ε j ≤ g j)
    (hsum : ∀ K, ∑ j ∈ Finset.Icc j₀ K, ε j ≤ 1/2) :
    p ^ j₀ / 2 ≤ ∏ j ∈ Finset.Icc 1 J, g j := by
  classical
  have hgnn : ∀ j, 1 ≤ j → 0 ≤ g j := fun j hj => le_trans hp0.le (hlow j hj)
  by_cases hcase : J < j₀
  · have hp : ∏ j ∈ Finset.Icc 1 J, p ≤ ∏ j ∈ Finset.Icc 1 J, g j :=
      Finset.prod_le_prod (fun i _ => hp0.le) (fun i hi => hlow i (Finset.mem_Icc.mp hi).1)
    have hcard : (Finset.Icc 1 J).card = J := by simp
    rw [Finset.prod_const, hcard] at hp
    have hmono : p ^ j₀ ≤ p ^ J := pow_le_pow_of_le_one hp0.le hp1 (by omega)
    have : (0:ℝ) < p ^ j₀ := by positivity
    linarith
  · push_neg at hcase
    have hIcc : Finset.Icc 1 J = Finset.Ico 1 (J+1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hIcc2 : Finset.Icc j₀ J = Finset.Ico j₀ (J+1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hsplit := Finset.prod_Ico_consecutive g (by omega : 1 ≤ j₀) (by omega : j₀ ≤ J + 1)
    rw [hIcc, ← hsplit]
    have hhead : p ^ j₀ ≤ ∏ j ∈ Finset.Ico 1 j₀, g j := by
      have hp : ∏ j ∈ Finset.Ico 1 j₀, p ≤ ∏ j ∈ Finset.Ico 1 j₀, g j :=
        Finset.prod_le_prod (fun i _ => hp0.le) (fun i hi => hlow i (Finset.mem_Ico.mp hi).1)
      have hcard : (Finset.Ico 1 j₀).card = j₀ - 1 := by simp
      rw [Finset.prod_const, hcard] at hp
      have hmono : p ^ j₀ ≤ p ^ (j₀ - 1) := pow_le_pow_of_le_one hp0.le hp1 (by omega)
      linarith
    have htail : (1:ℝ)/2 ≤ ∏ j ∈ Finset.Ico j₀ (J+1), g j := by
      rw [← hIcc2]
      have := prod_ge_one_sub_sum (Finset.Icc j₀ J) g ε
        (fun i hi => le_trans hp0.le (hlow i (by have := (Finset.mem_Icc.mp hi).1; omega)))
        (fun i _ => hεnn i) (fun i hi => hlb i (Finset.mem_Icc.mp hi).1)
      linarith [hsum J]
    have hheadnn : (0:ℝ) ≤ ∏ j ∈ Finset.Ico 1 j₀, g j :=
      Finset.prod_nonneg (fun i hi => hgnn i (Finset.mem_Ico.mp hi).1)
    have hppos : (0:ℝ) < p ^ j₀ := by positivity
    nlinarith [hhead, htail, hheadnn]

/-- A cut `j₀ ≥ 1` making the geometric tail summable below `1/2`. -/
lemma exists_geom_cut (B' : ℝ) (hB' : 0 ≤ B') :
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ K : ℕ, ∑ j ∈ Finset.Icc j₀ K, B' * ((1:ℝ)/4) ^ j ≤ 1/2 := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (x := 3 / (8 * (B' + 1)))
    (by positivity) (by norm_num : ((1:ℝ)/4) < 1)
  refine ⟨m + 1, by omega, fun K => ?_⟩
  have hIcc : Finset.Icc (m+1) K = Finset.Ico (m+1) (K+1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, ← Finset.mul_sum]
  have hgeom := sum_quarter_pow_Ico_le (m+1) (K+1)
  have hq : ((1:ℝ)/4) ^ (m+1) ≤ ((1:ℝ)/4) ^ m := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hsum : ∑ j ∈ Finset.Ico (m+1) (K+1), ((1:ℝ)/4) ^ j ≤ (4/3) * ((1:ℝ)/4) ^ m := by
    nlinarith [hgeom, hq]
  have hsnn : (0:ℝ) ≤ ∑ j ∈ Finset.Ico (m+1) (K+1), ((1:ℝ)/4) ^ j :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hmlt : ((1:ℝ)/4) ^ m < 3 / (8 * (B' + 1)) := hm
  have hkey : B' * ((4:ℝ)/3 * ((1:ℝ)/4) ^ m) ≤ 1/2 := by
    rw [lt_div_iff₀ (by positivity)] at hmlt
    nlinarith [hB', hmlt, pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) m]
  nlinarith [hB', hsum, hsnn, hkey]

/-- `∏_{j≤J} L^{Re z_j} = L^{Re κ_J}`. -/
lemma prod_rpow_sdExponent (L : ℝ) (hL : 0 < L) (h : ℤ) (J : ℕ) :
    ∏ j ∈ Finset.Icc 1 J, L ^ (sdExponent h {j}).re
      = L ^ (sdExponent h (Finset.Icc 1 J)).re := by
  induction J with
  | zero =>
      rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from by decide, Finset.prod_empty, sdExponent,
        Finset.sum_empty]
      simp [Real.rpow_zero]
  | succ J ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ J + 1), ih, sdExponent_Icc_succ,
        Complex.add_re, Real.rpow_add hL]

/-- `∏_{j≤J} (L:ℂ)^{z_j} = (L:ℂ)^{κ_J}`. -/
lemma prod_cpow_sdExponent (L : ℝ) (hL : 0 < L) (h : ℤ) (J : ℕ) :
    ∏ j ∈ Finset.Icc 1 J, ((L : ℝ) : ℂ) ^ sdExponent h {j}
      = ((L : ℝ) : ℂ) ^ sdExponent h (Finset.Icc 1 J) := by
  have hLc : ((L : ℝ) : ℂ) ≠ 0 := by simpa using hL.ne'
  induction J with
  | zero =>
      rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from by decide, Finset.prod_empty, sdExponent,
        Finset.sum_empty, Complex.cpow_zero]
  | succ J ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ J + 1), ih, sdExponent_Icc_succ,
        Complex.cpow_add _ _ hLc]

/-- The site constants have partial products bounded away from `0`, uniformly in `J`. -/
lemma exists_const_prod_lower {c : Finset ℕ → ℂ} {B δ : ℝ} (hBnn : 0 ≤ B) (hδ : 0 < δ)
    (hclow : ∀ k, 1 ≤ k → δ ≤ ‖c (Finset.Icc 1 k)‖ ∧ δ ≤ ‖c {k}‖)
    (hcone : ∀ k, 1 ≤ k → ‖c {k} - 1‖ ≤ B * ((1:ℝ)/4) ^ k) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ J, δ' ≤ ∏ j ∈ Finset.Icc 1 J, ‖c {j}‖ := by
  obtain ⟨j₀, hj₀1, hj₀⟩ := exists_geom_cut B hBnn
  refine ⟨(min δ 1) ^ j₀ / 2, by positivity, fun J => ?_⟩
  refine prod_Icc_split_lower J j₀ hj₀1 (fun j => ‖c {j}‖) (fun j => B * ((1:ℝ)/4) ^ j)
    (min δ 1) (lt_min hδ one_pos) (min_le_right _ _)
    (fun j hj => le_trans (min_le_left _ _) (hclow j hj).2)
    (fun j => by positivity) (fun j hj => ?_) hj₀
  have hjj : 1 ≤ j := by omega
  have h1 := hcone j hjj
  have h2 : ‖(1:ℂ)‖ - ‖c {j}‖ ≤ ‖(1:ℂ) - c {j}‖ := norm_sub_norm_le _ _
  rw [norm_one] at h2
  rw [norm_sub_rev] at h1
  linarith

lemma roughWindowMean_eq_prefixMean (N J : ℕ) (h : ℤ) :
    roughWindowMean N J h 2 = roughPrefixMean N h J := roughWindowMean_eq_winMean N J h

lemma cpow_ofReal_ne_zero {L : ℝ} (hL : 0 < L) (κ : ℂ) : ((L : ℝ) : ℂ) ^ κ ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (by simpa using hL.ne')]
  exact Complex.exp_ne_zero _

set_option maxHeartbeats 1000000 in
/-- **Wiring 1**: the summatory node gives the rough factorisation. -/
theorem roughIndependenceAt_two_of_summatory {h : ℤ} (hS : RoughSummatory h) :
    RoughIndependenceAt h 2 := by
  classical
  obtain ⟨c, B, A, δ, hAnn, hδ, hBnn, hcB, hclow, hcone, hev, hdiff⟩ :=
    summatory_means_approx hS
  obtain ⟨δc, hδc, hδcJ⟩ := exists_const_prod_lower hBnn hδ hclow hcone
  obtain ⟨j₀, hj₀1, hj₀⟩ := exists_geom_cut (B + 1) (by linarith)
  set p : ℝ := min (δ/2) 1 with hpdef
  have hp0 : 0 < p := lt_min (by positivity) one_pos
  set δ' : ℝ := p ^ j₀ / 2 with hδ'def
  have hδ'0 : 0 < δ' := by positivity
  set Ctot : ℝ := (A + 2*A*B/(3*δ)) / δ' with hCtot
  refine ⟨fun J => c (Finset.Icc 1 J) / ∏ j ∈ Finset.Icc 1 J, c {j}, B / δc, Ctot, ?_, ?_⟩
  · intro J
    rw [norm_div, norm_prod]
    have h1 : δc ≤ ∏ j ∈ Finset.Icc 1 J, ‖c {j}‖ := hδcJ J
    have h2 : ‖c (Finset.Icc 1 J)‖ ≤ B := hcB _
    have h3 : (0:ℝ) < ∏ j ∈ Finset.Icc 1 J, ‖c {j}‖ := lt_of_lt_of_le hδc h1
    rw [div_le_div_iff₀ h3 hδc]
    nlinarith [norm_nonneg (c (Finset.Icc 1 J)), hδc.le, h1, h2, hBnn]
  · have hbig : ∀ᶠ N : ℕ in atTop, (1 + A + 2*A/δ : ℝ) ≤ Real.log N := by
      have := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact this.eventually_ge_atTop _
    filter_upwards [hev, hbig, eventually_gt_atTop 0] with N hN hNlog hN0
    set J : ℕ := windowJ N with hJ
    set L : ℝ := Real.log N with hLdef
    have hd2 : (0:ℝ) ≤ 2*A/δ := by positivity
    have hL1 : (1:ℝ) ≤ L := by linarith
    have hL0 : (0:ℝ) < L := by linarith
    have hLA : A ≤ L := by linarith
    have hLδ : 2*A/δ ≤ L := by linarith
    have hJ1 : 1 ≤ J := by rw [hJ, windowJ]; omega
    set κ : ℂ := sdExponent h (Finset.Icc 1 J) with hκ
    set q : ℕ → ℝ := fun j => ((1:ℝ)/4) ^ j with hq
    have hqpos : ∀ j, (0:ℝ) < q j := fun j => by rw [hq]; positivity
    have hq1 : ∀ j, q j ≤ 1 := fun j => pow_le_one₀ (by norm_num) (by norm_num)
    -- the site data
    set r : ℕ → ℝ := fun j => L ^ (sdExponent h {j}).re with hr
    have hrpos : ∀ j, (0:ℝ) < r j := fun j => Real.rpow_pos_of_pos hL0 _
    set S : ℕ → ℂ := fun j => roughSiteMean N h j 2 with hSdef
    have hSj : ∀ j, 1 ≤ j → j ≤ J → ‖S j - c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j}‖
        ≤ A * q j / L * r j := fun j hj1 hjJ => (hN j hj1 hjJ).2
    -- lower bound for each normalised site mean
    set g : ℕ → ℝ := fun j => ‖S j‖ / r j with hg
    have hgS : ∀ j, ‖S j‖ = g j * r j := fun j => by
      rw [hg]; field_simp [(hrpos j).ne']
    have hglow : ∀ j, 1 ≤ j → j ≤ J → ‖c {j}‖ - A * q j / L ≤ g j := by
      intro j hj1 hjJ
      have h1 := hSj j hj1 hjJ
      have h2 : ‖c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j}‖ - ‖S j‖
          ≤ ‖c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j} - S j‖ := norm_sub_norm_le _ _
      rw [norm_sub_rev] at h2
      rw [norm_mul, norm_ofReal_cpow hL0] at h2
      have h3 : ‖c {j}‖ * r j - A * q j / L * r j ≤ ‖S j‖ := by
        rw [hr]; linarith [h1, h2]
      rw [hg, le_div_iff₀ (hrpos j)]
      linarith [h3]
    have hgp : ∀ j, 1 ≤ j → j ≤ J → p ≤ g j := by
      intro j hj1 hjJ
      refine le_trans (min_le_left _ _) ?_
      have h1 := hglow j hj1 hjJ
      have h2 : δ ≤ ‖c {j}‖ := (hclow j hj1).2
      have h3 : A * q j / L ≤ δ/2 := by
        rw [div_le_iff₀ hL0]
        have hqa : A * q j ≤ A := by nlinarith [hAnn, hq1 j, hqpos j]
        have hmul : (δ/2) * (2*A/δ) ≤ (δ/2) * L :=
          mul_le_mul_of_nonneg_left hLδ (by positivity)
        have heq : (δ/2) * (2*A/δ) = A := by field_simp
        rw [heq] at hmul
        nlinarith [hqa, hmul]
      linarith
    have hgeps : ∀ j, 1 ≤ j → j ≤ J → 1 - (B+1) * q j ≤ g j := by
      intro j hj1 hjJ
      have h1 := hglow j hj1 hjJ
      have h2 : ‖(1:ℂ)‖ - ‖c {j}‖ ≤ ‖(1:ℂ) - c {j}‖ := norm_sub_norm_le _ _
      rw [norm_one, norm_sub_rev] at h2
      have h3 := hcone j hj1
      have h4 : A * q j / L ≤ q j := by
        rw [div_le_iff₀ hL0]
        nlinarith [hLA, hqpos j, hAnn]
      rw [hq] at *
      linarith
    -- the product of site means
    have hprodg : δ' ≤ ∏ j ∈ Finset.Icc 1 J, g j := by
      rw [hδ'def]
      have hp1 : p ≤ 1 := min_le_right _ _
      have hsplit := prod_Icc_split_lower J j₀ hj₀1 (fun j => if j ≤ J then g j else 1)
        (fun j => (B+1) * q j) p hp0 hp1 ?_ (fun j => by rw [hq]; positivity) ?_ hj₀
      · refine hsplit.trans_eq (Finset.prod_congr rfl (fun j hj => ?_))
        rw [if_pos (Finset.mem_Icc.mp hj).2]
      · intro j hj1
        by_cases hjJ : j ≤ J
        · rw [if_pos hjJ]; exact hgp j hj1 hjJ
        · rw [if_neg hjJ]; exact hp1
      · intro j hjj
        by_cases hjJ : j ≤ J
        · rw [if_pos hjJ]; exact hgeps j (by omega) hjJ
        · rw [if_neg hjJ]
          have : (0:ℝ) ≤ (B+1) * q j := by rw [hq]; positivity
          linarith
    have hprodS : δ' * L ^ κ.re ≤ ∏ j ∈ Finset.Icc 1 J, ‖S j‖ := by
      have heq : ∏ j ∈ Finset.Icc 1 J, ‖S j‖
          = (∏ j ∈ Finset.Icc 1 J, g j) * ∏ j ∈ Finset.Icc 1 J, r j := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun j _ => hgS j)
      have hrprod : ∏ j ∈ Finset.Icc 1 J, r j = L ^ κ.re := by
        rw [hr, hκ]; exact prod_rpow_sdExponent L hL0 h J
      rw [heq, hrprod]
      have hrp : (0:ℝ) < L ^ κ.re := Real.rpow_pos_of_pos hL0 _
      nlinarith [hprodg, hrp, hδ'0]
    -- the relative perturbations
    set w : ℕ → ℂ := fun j => S j / (c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j}) - 1 with hw
    have hcne : ∀ j, 1 ≤ j → c {j} ≠ 0 := by
      intro j hj hzero
      have := (hclow j hj).2
      rw [hzero, norm_zero] at this; linarith
    have hSfac : ∀ j, 1 ≤ j → S j
        = c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j} * (1 + w j) := by
      intro j hj
      have hd : c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j} ≠ 0 :=
        mul_ne_zero (hcne j hj) (cpow_ofReal_ne_zero hL0 _)
      have h1 : (1 : ℂ) + w j = S j / (c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j}) := by
        rw [hw]; ring
      rw [h1, mul_div_cancel₀ _ hd]
    have hwnorm : ∀ j, 1 ≤ j → j ≤ J → ‖w j‖ ≤ A * q j / (δ * L) := by
      intro j hj1 hjJ
      have h1 := hSj j hj1 hjJ
      have hd : c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j} ≠ 0 :=
        mul_ne_zero (hcne j hj1) (cpow_ofReal_ne_zero hL0 _)
      have heq : w j = (S j - c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j})
          / (c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j}) := by
        rw [hw, sub_div, div_self hd]
      have h2 : δ ≤ ‖c {j}‖ := (hclow j hj1).2
      have h3 : (0:ℝ) < r j := hrpos j
      have hcpos : (0:ℝ) < ‖c {j}‖ := lt_of_lt_of_le hδ h2
      have h4 : ‖S j - c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j}‖ ≤ A * q j / L * r j := h1
      have h5 : (0:ℝ) ≤ A * q j := by rw [hq]; positivity
      rw [heq, norm_div, norm_mul, norm_ofReal_cpow hL0]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hb1 : ‖S j - c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j}‖ * (δ * L)
          ≤ (A * q j / L * r j) * (δ * L) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      have hb2 : (A * q j / L * r j) * (δ * L) = A * q j * (δ * r j) := by
        field_simp
      have hb3 : A * q j * (δ * r j) ≤ A * q j * (‖c {j}‖ * r j) := by
        refine mul_le_mul_of_nonneg_left ?_ h5
        exact mul_le_mul_of_nonneg_right h2 h3.le
      have hrj : r j = L ^ (sdExponent h {j}).re := rfl
      rw [← hrj]
      linarith [hb1, hb2, hb3]
    have hwsum : ∑ j ∈ Finset.Icc 1 J, ‖w j‖ ≤ A / (3 * δ * L) := by
      have h1 : ∑ j ∈ Finset.Icc 1 J, ‖w j‖ ≤ ∑ j ∈ Finset.Icc 1 J, A * q j / (δ * L) :=
        Finset.sum_le_sum (fun j hj => hwnorm j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)
      have h2 : ∑ j ∈ Finset.Icc 1 J, A * q j / (δ * L)
          = (A / (δ * L)) * ∑ j ∈ Finset.Icc 1 J, q j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [hq]; ring)
      have hIcc : Finset.Icc 1 J = Finset.Ico 1 (J+1) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      have h3 : ∑ j ∈ Finset.Icc 1 J, q j ≤ 1/3 := by
        rw [hIcc, hq]
        have := sum_quarter_pow_Ico_le 1 (J+1)
        norm_num at this ⊢
        linarith
      have h4 : (0:ℝ) < A / (δ * L) + 1 := by positivity
      have h5 : (0:ℝ) ≤ A / (δ * L) := by positivity
      have h6 : A / (δ * L) * (1/3) = A / (3 * δ * L) := by field_simp
      have h7 : (A / (δ * L)) * ∑ j ∈ Finset.Icc 1 J, q j ≤ (A / (δ * L)) * (1/3) :=
        mul_le_mul_of_nonneg_left h3 h5
      linarith [h1, h2, h6, h7]
    have hwsumhalf : ∑ j ∈ Finset.Icc 1 J, ‖w j‖ ≤ 1/2 := by
      refine hwsum.trans ?_
      rw [div_le_iff₀ (by positivity)]
      have hm := mul_le_mul_of_nonneg_left hLδ hδ.le
      have heq2 : δ * (2*A/δ) = 2*A := by field_simp
      rw [heq2] at hm
      linarith [hm, hAnn]
    -- product of the perturbations
    have hprodw : ‖(1:ℂ) - ∏ j ∈ Finset.Icc 1 J, (1 + w j)‖ ≤ 2 * (A / (3 * δ * L)) := by
      have hrel := norm_prod_sub_prod_rel (Finset.Icc 1 J) (fun _ => (1:ℂ))
        (fun j => 1 + w j) (fun j => ‖w j‖) (fun j => norm_nonneg _)
        (fun j _ => by simp [norm_sub_rev])
      simp only [Finset.prod_const_one, norm_one, Finset.prod_const_one, mul_one] at hrel
      have hpo := prod_one_add_le (Finset.Icc 1 J) (fun j => ‖w j‖) (fun j => norm_nonneg _)
        hwsumhalf
      have : ((∏ j ∈ Finset.Icc 1 J, (1 + ‖w j‖)) - 1) ≤ 2 * ∑ j ∈ Finset.Icc 1 J, ‖w j‖ := by
        linarith [hpo]
      calc ‖(1:ℂ) - ∏ j ∈ Finset.Icc 1 J, (1 + w j)‖
          ≤ (∏ j ∈ Finset.Icc 1 J, (1 + ‖w j‖)) - 1 := hrel
        _ ≤ 2 * ∑ j ∈ Finset.Icc 1 J, ‖w j‖ := this
        _ ≤ 2 * (A / (3 * δ * L)) := by linarith [hwsum]
    -- assemble
    have hprodSfac : ∏ j ∈ Finset.Icc 1 J, S j
        = (∏ j ∈ Finset.Icc 1 J, c {j}) * ((L : ℝ) : ℂ) ^ κ
          * ∏ j ∈ Finset.Icc 1 J, (1 + w j) := by
      have h1 : ∏ j ∈ Finset.Icc 1 J, S j
          = ∏ j ∈ Finset.Icc 1 J, (c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j} * (1 + w j)) :=
        Finset.prod_congr rfl (fun j hj => hSfac j (Finset.mem_Icc.mp hj).1)
      rw [h1, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hκ,
        prod_cpow_sdExponent L hL0 h J]
    have hcprodne : (∏ j ∈ Finset.Icc 1 J, c {j}) ≠ 0 := by
      intro hzero
      have := hδcJ J
      rw [← norm_prod] at this
      rw [hzero, norm_zero] at this
      linarith
    have hmain : roughWindowMean N J h 2
        - (c (Finset.Icc 1 J) / ∏ j ∈ Finset.Icc 1 J, c {j}) * ∏ j ∈ Finset.Icc 1 J, S j
        = (roughPrefixMean N h J - c (Finset.Icc 1 J) * ((L : ℝ) : ℂ) ^ κ)
          + c (Finset.Icc 1 J) * ((L : ℝ) : ℂ) ^ κ
            * (1 - ∏ j ∈ Finset.Icc 1 J, (1 + w j)) := by
      rw [roughWindowMean_eq_prefixMean, hprodSfac]
      field_simp
      ring
    have hPref : ‖roughPrefixMean N h J - c (Finset.Icc 1 J) * ((L : ℝ) : ℂ) ^ κ‖
        ≤ A / L * L ^ κ.re := (hN J hJ1 le_rfl).1
    have hrpκ : (0:ℝ) < L ^ κ.re := Real.rpow_pos_of_pos hL0 _
    have hfinal : ‖roughWindowMean N J h 2
        - (c (Finset.Icc 1 J) / ∏ j ∈ Finset.Icc 1 J, c {j}) * ∏ j ∈ Finset.Icc 1 J, S j‖
        ≤ (A + 2*A*B/(3*δ)) / L * L ^ κ.re := by
      rw [hmain]
      refine (norm_add_le _ _).trans ?_
      have h2 : ‖c (Finset.Icc 1 J) * ((L : ℝ) : ℂ) ^ κ
          * (1 - ∏ j ∈ Finset.Icc 1 J, (1 + w j))‖
          ≤ B * L ^ κ.re * (2 * (A / (3 * δ * L))) := by
        rw [norm_mul, norm_mul, norm_ofReal_cpow hL0]
        refine mul_le_mul ?_ hprodw (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right (hcB _) hrpκ.le
      have h3 : B * L ^ κ.re * (2 * (A / (3 * δ * L))) = 2*A*B/(3*δ) / L * L ^ κ.re := by
        field_simp
      rw [h3] at h2
      have : (A + 2*A*B/(3*δ)) / L * L ^ κ.re
          = A / L * L ^ κ.re + 2*A*B/(3*δ) / L * L ^ κ.re := by ring
      rw [this]
      exact add_le_add hPref h2
    refine hfinal.trans ?_
    rw [hCtot]
    have hstep : (A + 2*A*B/(3*δ)) / δ' / L * (δ' * L ^ κ.re)
        = (A + 2*A*B/(3*δ)) / L * L ^ κ.re := by field_simp
    calc (A + 2*A*B/(3*δ)) / L * L ^ κ.re
        = (A + 2*A*B/(3*δ)) / δ' / L * (δ' * L ^ κ.re) := hstep.symm
      _ ≤ (A + 2*A*B/(3*δ)) / δ' / L * ∏ j ∈ Finset.Icc 1 J, ‖S j‖ := by
          refine mul_le_mul_of_nonneg_left hprodS ?_
          have : (0:ℝ) ≤ A + 2*A*B/(3*δ) := by positivity
          positivity

set_option maxHeartbeats 2000000 in
/-- **Wiring 2**: the summatory node gives the parity node (the class main terms cancel exactly;
the lower bound on `∏‖fullSiteMean‖` comes from the node's own main terms and `|cos(πh/4^j)| > 0`
off the Chowla sector).  The range `j > windowJ N`, where the node says nothing, is the elementary
`parityDisc_tail_small`. -/
theorem parityDiscrepancy_of_summatory {h : ℤ} (hh : h ≠ 0) (hc : ¬ ChowlaSector h)
    (hS : RoughSummatory h) : ParityDiscrepancy h := by
  classical
  obtain ⟨c, B, A, δ, hAnn, hδ, hBnn, hcB, hclow, hcone, hev, hdiff⟩ := summatory_means_approx hS
  obtain ⟨δh, hδh0, hhalf⟩ := exists_halfAvg_lower hh hc
  obtain ⟨Ct, hCt0, hCtev⟩ := parityDisc_tail_small h
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  set K : ℝ := 4 * Real.pi * |(h:ℝ)| with hK
  have hKnn : (0:ℝ) ≤ K := by rw [hK]; positivity
  set p : ℝ := min (δ/2) 1 with hpdef
  have hp0 : (0:ℝ) < p := lt_min (by positivity) one_pos
  have hp1 : p ≤ 1 := min_le_right _ _
  set p₂ : ℝ := min (δh * p / 2) 1 with hp2def
  have hp20 : (0:ℝ) < p₂ := lt_min (by positivity) one_pos
  have hp21 : p₂ ≤ 1 := min_le_right _ _
  obtain ⟨j₁, hj₁1, hj₁⟩ :=
    exists_geom_cut (2*Real.pi*|(h:ℝ)| + B + 1 + K*A) (by positivity)
  set δ₂ : ℝ := p₂ ^ j₁ / 2 with hδ₂def
  have hδ₂0 : (0:ℝ) < δ₂ := by positivity
  set m : ℕ := ⌈K⌉₊ with hmdef
  have hmK : K ≤ (m : ℝ) := Nat.le_ceil _
  set C' : ℝ := A/p₂ + A/δ₂ + 1 + Ct with hC'def
  have hC'1 : (1:ℝ) ≤ C' := by
    rw [hC'def]
    have : (0:ℝ) ≤ A/p₂ := by positivity
    have h2 : (0:ℝ) ≤ A/δ₂ := by positivity
    linarith
  have hC'p : A ≤ C' * p₂ := by
    rw [hC'def]
    have h1 : A / p₂ * p₂ = A := by field_simp
    nlinarith [hp20, hCt0, div_nonneg hAnn hδ₂0.le, h1]
  have hC'δ : A ≤ C' * δ₂ := by
    rw [hC'def]
    have h1 : A / δ₂ * δ₂ = A := by field_simp
    nlinarith [hδ₂0, hCt0, div_nonneg hAnn hp20.le, h1]
  have hCtle : Ct ≤ C' := by
    rw [hC'def]
    have : (0:ℝ) ≤ A/p₂ := by positivity
    have h2 : (0:ℝ) ≤ A/δ₂ := by positivity
    linarith
  refine ⟨C', ?_⟩
  have hlogbig : ∀ᶠ N : ℕ in atTop,
      (1 + K + A + 2*A/δ + 2*K*A/(δh*p) : ℝ) ≤ Real.log N := by
    have := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop _
  filter_upwards [hev, hdiff, hCtev, hlogbig,
    eventually_rpow_log_le m (min p₂ δ₂) (lt_min hp20 hδ₂0), eventually_gt_atTop 0]
    with N hN hND hNt hNlog hNpow hN0
  set J : ℕ := windowJ N with hJdef
  set L : ℝ := Real.log N with hLdef
  have hbits : (0:ℝ) ≤ 2*A/δ ∧ (0:ℝ) ≤ 2*K*A/(δh*p) := ⟨by positivity, by positivity⟩
  have hL1 : (1:ℝ) ≤ L := by linarith [hbits.1, hbits.2, hKnn, hAnn]
  have hL0 : (0:ℝ) < L := by linarith
  have hLK : K ≤ L := by linarith [hbits.1, hbits.2, hAnn]
  have hLA : A ≤ L := by linarith [hbits.1, hbits.2, hKnn]
  have hLδ : 2*A/δ ≤ L := by linarith [hbits.2, hKnn, hAnn]
  have hLhp : 2*K*A/(δh*p) ≤ L := by linarith [hbits.1, hKnn, hAnn]
  have hJ1 : 1 ≤ J := by rw [hJdef, windowJ]; omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  set q : ℕ → ℝ := fun j => ((1:ℝ)/4) ^ j with hqdef
  have hqpos : ∀ j, (0:ℝ) < q j := fun j => by rw [hqdef]; positivity
  have hq1 : ∀ j, q j ≤ 1 := fun j => pow_le_one₀ (by norm_num) (by norm_num)
  set r : ℕ → ℝ := fun j => L ^ (sdExponent h {j}).re with hrdef
  have hrpos : ∀ j, (0:ℝ) < r j := fun j => Real.rpow_pos_of_pos hL0 _
  set κ : ℂ := sdExponent h (Finset.Icc 1 J) with hκdef
  have hκre : (0:ℝ) < L ^ κ.re := Real.rpow_pos_of_pos hL0 _
  -- per-site facts in the node range
  have hsite : ∀ j, 1 ≤ j → j ≤ J →
      ‖parityDisc N j (roughPhase h j)‖ ≤ (N:ℝ)/2 * (A * q j / L * ((N:ℝ) * r j)) + (N:ℝ)/2
      ∧ p₂ * r j ≤ ‖fullSiteMean N h j‖
      ∧ (1 - (2*Real.pi*|(h:ℝ)| + B + 1 + K*A) * q j) * r j ≤ ‖fullSiteMean N h j‖ := by
    intro j hj1 hjJ
    have hfun : roughPhase h j = roughProd h {j} :=
      funext (fun n => (roughProd_singleton h j n).symm)
    set D : ℝ := A * q j / L * ((N:ℝ) * r j) with hDdef
    have hDnn : (0:ℝ) ≤ D := by rw [hDdef]; positivity
    have hdd : ‖(∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j), roughProd h {j} n)
        - ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j), roughProd h {j} n‖ ≤ D := by
      rw [parityDisc_class_diff]
      exact (hND j hj1 hjJ (j % 2) (by omega) ((j+1) % 2) (by omega)).2
    have hpd : ‖parityDisc N j (roughPhase h j)‖ ≤ (N:ℝ)/2 * D + (N:ℝ)/2 := by
      rw [hfun]
      exact norm_parityDisc_le N j _ (fun n => le_of_eq (norm_roughProd h {j} n)) D hdd
    -- the rough site mean
    have hS1 : ‖roughSiteMean N h j 2 - c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j}‖
        ≤ A * q j / L * r j := (hN j hj1 hjJ).2
    have hglow : ‖c {j}‖ * r j - A * q j / L * r j ≤ ‖roughSiteMean N h j 2‖ := by
      have h2 : ‖c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j}‖ - ‖roughSiteMean N h j 2‖
          ≤ ‖c {j} * ((L : ℝ) : ℂ) ^ sdExponent h {j} - roughSiteMean N h j 2‖ :=
        norm_sub_norm_le _ _
      rw [norm_sub_rev] at h2
      rw [norm_mul, norm_ofReal_cpow hL0] at h2
      have : r j = L ^ (sdExponent h {j}).re := rfl
      rw [← this] at h2
      linarith [hS1, h2]
    have hAqL : A * q j / L ≤ q j := by
      rw [div_le_iff₀ hL0]; nlinarith [hLA, hqpos j, hAnn]
    have hAqL2 : A * q j / L ≤ δ/2 := by
      rw [div_le_iff₀ hL0]
      have hqa : A * q j ≤ A := by nlinarith [hAnn, hq1 j, hqpos j]
      have hmul : (δ/2) * (2*A/δ) ≤ (δ/2) * L := mul_le_mul_of_nonneg_left hLδ (by positivity)
      have heq : (δ/2) * (2*A/δ) = A := by field_simp
      rw [heq] at hmul
      linarith
    have hrp : p * r j ≤ ‖roughSiteMean N h j 2‖ := by
      have h1 : δ ≤ ‖c {j}‖ := (hclow j hj1).2
      have : p ≤ δ/2 := min_le_left _ _
      nlinarith [hglow, hrpos j, hAqL2, h1]
    have hre : (1 - (B+1) * q j) * r j ≤ ‖roughSiteMean N h j 2‖ := by
      have h2 : ‖(1:ℂ)‖ - ‖c {j}‖ ≤ ‖(1:ℂ) - c {j}‖ := norm_sub_norm_le _ _
      rw [norm_one, norm_sub_rev] at h2
      have h3 : ‖c {j} - 1‖ ≤ B * q j := hcone j hj1
      nlinarith [hglow, hrpos j, hAqL, h2, h3]
    -- the full site mean
    have hfullclose : ‖fullSiteMean N h j - halfAvg h j * roughSiteMean N h j 2‖
        ≤ K * A / 2 * q j / L * r j := by
      rw [fullSiteMean_sub_halfAvg_mul N h j hj1 hN0, norm_mul, norm_div, norm_div,
        Complex.norm_ofNat, Complex.norm_natCast]
      have h1 : ‖ePhase ((h:ℝ)/(4:ℝ)^j) - 1‖ ≤ K * q j := by
        exact norm_ePhase_site_sub_one h j
      have hdd' : ‖(∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j), roughPhase h j n)
          - ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j), roughPhase h j n‖ ≤ D := by
        rw [hfun]; exact hdd
      have h3 : ‖(∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + j), roughPhase h j n)
          - ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + j), roughPhase h j n‖ / (N:ℝ)
          ≤ D / (N:ℝ) := by
        exact div_le_div_of_nonneg_right hdd' hNR.le
      have h4 : D / (N:ℝ) = A * q j / L * r j := by
        rw [hDdef]; field_simp
      rw [h4] at h3
      have h5 : ‖ePhase ((h:ℝ)/(4:ℝ)^j) - 1‖ / 2 ≤ K * q j / 2 := by linarith
      have h6 : (0:ℝ) ≤ ‖ePhase ((h:ℝ)/(4:ℝ)^j) - 1‖ / 2 := by positivity
      have h7 : (0:ℝ) ≤ A * q j / L * r j := by positivity
      have h8 := mul_le_mul h5 h3 (by positivity) (by positivity)
      have h9 : K * q j / 2 * (A * q j / L * r j) ≤ K * A / 2 * q j / L * r j := by
        have hqq : q j * q j ≤ q j := by nlinarith [hqpos j, hq1 j]
        have : K * q j / 2 * (A * q j / L * r j) = (K * A / 2 / L * r j) * (q j * q j) := by
          field_simp <;> ring
        rw [this]
        have hcoef : (0:ℝ) ≤ K * A / 2 / L * r j := by positivity
        have := mul_le_mul_of_nonneg_left hqq hcoef
        calc (K * A / 2 / L * r j) * (q j * q j) ≤ (K * A / 2 / L * r j) * q j := this
          _ = K * A / 2 * q j / L * r j := by field_simp <;> ring
      linarith [h8, h9]
    have hFlow : ‖halfAvg h j‖ * ‖roughSiteMean N h j 2‖ - K * A / 2 * q j / L * r j
        ≤ ‖fullSiteMean N h j‖ := by
      have h1 : ‖halfAvg h j * roughSiteMean N h j 2‖ - ‖fullSiteMean N h j‖
          ≤ ‖halfAvg h j * roughSiteMean N h j 2 - fullSiteMean N h j‖ := norm_sub_norm_le _ _
      rw [norm_sub_rev] at h1
      rw [norm_mul] at h1
      linarith [hfullclose, h1]
    refine ⟨hpd, ?_, ?_⟩
    · -- crude uniform bound
      have h1 : δh ≤ ‖halfAvg h j‖ := hhalf j hj1
      have h2 : δh * (p * r j) ≤ ‖halfAvg h j‖ * ‖roughSiteMean N h j 2‖ := by
        refine mul_le_mul h1 hrp (by positivity) (norm_nonneg _)
      have h3 : K * A / 2 * q j / L * r j ≤ δh * p / 2 * r j := by
        have hq' : q j ≤ 1 := hq1 j
        have hkey : K * A / 2 * q j / L ≤ δh * p / 2 := by
          rw [div_le_iff₀ hL0]
          have hmul : (δh*p/2) * (2*K*A/(δh*p)) ≤ (δh*p/2) * L :=
            mul_le_mul_of_nonneg_left hLhp (by positivity)
          have heq : (δh*p/2) * (2*K*A/(δh*p)) = K*A := by field_simp <;> ring
          rw [heq] at hmul
          nlinarith [hq', hqpos j, hKnn, hAnn, mul_nonneg hKnn hAnn]
        exact mul_le_mul_of_nonneg_right hkey (hrpos j).le
      have h4 : p₂ ≤ δh * p / 2 := min_le_left _ _
      nlinarith [hFlow, h2, h3, h4, hrpos j]
    · -- the geometric bound
      have h1 : 1 - 2*Real.pi*|(h:ℝ)| * q j ≤ ‖halfAvg h j‖ := by
        exact norm_halfAvg_ge h j
      have h1' : ‖halfAvg h j‖ ≤ 1 := norm_halfAvg_le_one h j
      have h2 : (1 - (B+1) * q j) * r j ≤ ‖roughSiteMean N h j 2‖ := hre
      have hrjpos := hrpos j
      have hprod : (1 - 2*Real.pi*|(h:ℝ)| * q j - (B+1) * q j) * r j
          ≤ ‖halfAvg h j‖ * ‖roughSiteMean N h j 2‖ := by
        rcases le_or_gt (1 - 2*Real.pi*|(h:ℝ)| * q j) 0 with hneg | hpos
        · have hb : (0:ℝ) ≤ (B+1) * q j := by positivity
          have : (1 - 2*Real.pi*|(h:ℝ)| * q j - (B+1) * q j) * r j ≤ 0 := by
            nlinarith [hrjpos, hneg, hb]
          have : (0:ℝ) ≤ ‖halfAvg h j‖ * ‖roughSiteMean N h j 2‖ := by positivity
          linarith
        · have hA1 : (1 - 2*Real.pi*|(h:ℝ)| * q j) * ‖roughSiteMean N h j 2‖
              ≤ ‖halfAvg h j‖ * ‖roughSiteMean N h j 2‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          have hA2 : (1 - 2*Real.pi*|(h:ℝ)| * q j) * ((1 - (B+1) * q j) * r j)
              ≤ (1 - 2*Real.pi*|(h:ℝ)| * q j) * ‖roughSiteMean N h j 2‖ :=
            mul_le_mul_of_nonneg_left h2 hpos.le
          have hA3 : (1 - 2*Real.pi*|(h:ℝ)| * q j - (B+1) * q j) * r j
              ≤ (1 - 2*Real.pi*|(h:ℝ)| * q j) * ((1 - (B+1) * q j) * r j) := by
            have hexp : (1 - 2*Real.pi*|(h:ℝ)| * q j) * ((1 - (B+1) * q j) * r j)
                - (1 - 2*Real.pi*|(h:ℝ)| * q j - (B+1) * q j) * r j
                = (2*Real.pi*|(h:ℝ)| * q j) * ((B+1) * q j) * r j := by ring
            have hnn : (0:ℝ) ≤ (2*Real.pi*|(h:ℝ)| * q j) * ((B+1) * q j) * r j := by
              have := hqpos j
              have := hrjpos
              positivity
            linarith [hexp, hnn]
          linarith
      have h3 : K * A / 2 * q j / L * r j ≤ K * A * q j * r j := by
        have hkey : K * A / 2 * q j / L ≤ K * A * q j := by
          rw [div_le_iff₀ hL0]
          nlinarith [hL1, mul_nonneg (mul_nonneg hKnn hAnn) (hqpos j).le]
        exact mul_le_mul_of_nonneg_right hkey hrjpos.le
      have hexp2 : (1 - (2*Real.pi*|(h:ℝ)| + B + 1 + K*A) * q j) * r j
          = (1 - 2*Real.pi*|(h:ℝ)| * q j - (B+1) * q j) * r j - K * A * q j * r j := by ring
      rw [hexp2]
      linarith [hFlow, hprod, h3]
  -- the product of full site means
  have hprodF : δ₂ * L ^ κ.re ≤ ∏ j ∈ Finset.Icc 1 J, ‖fullSiteMean N h j‖ := by
    set G : ℕ → ℝ := fun j => if j ≤ J then ‖fullSiteMean N h j‖ / r j else 1 with hGdef
    have hGsplit := prod_Icc_split_lower J j₁ hj₁1 G
      (fun j => (2*Real.pi*|(h:ℝ)| + B + 1 + K*A) * q j) p₂ hp20 hp21 ?_
      (fun j => by positivity) ?_ hj₁
    · have heq : ∏ j ∈ Finset.Icc 1 J, ‖fullSiteMean N h j‖
          = (∏ j ∈ Finset.Icc 1 J, G j) * ∏ j ∈ Finset.Icc 1 J, r j := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun j hj => ?_)
        show ‖fullSiteMean N h j‖ = (if j ≤ J then ‖fullSiteMean N h j‖ / r j else 1) * r j
        rw [if_pos (Finset.mem_Icc.mp hj).2]
        field_simp [(hrpos j).ne']
      have hrprod : ∏ j ∈ Finset.Icc 1 J, r j = L ^ κ.re := by
        rw [hrdef, hκdef]; exact prod_rpow_sdExponent L hL0 h J
      rw [heq, hrprod]
      nlinarith [hGsplit, hκre, hδ₂0]
    · intro j hj1
      by_cases hjJ : j ≤ J
      · simp only [hGdef]
        rw [if_pos hjJ, le_div_iff₀ (hrpos j)]
        exact (hsite j hj1 hjJ).2.1
      · simp only [hGdef]
        rw [if_neg hjJ]
        exact hp21
    · intro j hjj
      by_cases hjJ : j ≤ J
      · simp only [hGdef]
        rw [if_pos hjJ, le_div_iff₀ (hrpos j)]
        exact (hsite j (by omega) hjJ).2.2
      · simp only [hGdef]
        rw [if_neg hjJ]
        have : (0:ℝ) ≤ (2*Real.pi*|(h:ℝ)| + B + 1 + K*A) * q j := by positivity
        linarith
  have hminpow : L ^ ((m:ℝ)+1) ≤ min p₂ δ₂ * (N:ℝ) := hNpow
  constructor
  · -- site clause
    intro j hj1
    by_cases hjJ : j ≤ J
    · obtain ⟨hpd, hFp, -⟩ := hsite j hj1 hjJ
      have hrej : -((m:ℝ)) ≤ (sdExponent h {j}).re :=
        le_trans (by linarith [hmK]) (neg_bound_le_re (norm_sdExponent_singleton h j |>.trans
          (by nlinarith [hq1 j, hqpos j, hKnn, hK] : 4 * Real.pi * |(h:ℝ)| * ((1:ℝ)/4)^j ≤ K)))
      have hLabs : L ≤ p₂ * (N:ℝ) * r j :=
        log_le_of_rpow_le hL1 m (by positivity)
          (le_trans hminpow (by nlinarith [min_le_left p₂ δ₂, hNR.le])) hrej
      have hfin : (N:ℝ)/2 * (A * q j / L * ((N:ℝ) * r j)) + (N:ℝ)/2
          ≤ C' / L * ((N:ℝ)^2 * ‖fullSiteMean N h j‖) := by
        have hR : C' * p₂ * (N:ℝ)^2 * r j / L
            ≤ C' / L * ((N:ℝ)^2 * ‖fullSiteMean N h j‖) := by
          have h1 : C' * p₂ * (N:ℝ)^2 * r j / L = C' / L * ((N:ℝ)^2 * (p₂ * r j)) := by
            field_simp <;> ring
          rw [h1]
          have h2 : (0:ℝ) ≤ C' / L := by positivity
          refine mul_le_mul_of_nonneg_left ?_ h2
          exact mul_le_mul_of_nonneg_left hFp (by positivity)
        refine le_trans ?_ hR
        have hterm1 : (N:ℝ)/2 * (A * q j / L * ((N:ℝ) * r j))
            ≤ C' * p₂ * (N:ℝ)^2 * r j / L / 2 := by
          have hq' : q j ≤ 1 := hq1 j
          have h1 : (N:ℝ)/2 * (A * q j / L * ((N:ℝ) * r j))
              = (A * q j) * ((N:ℝ)^2 * r j) / L / 2 := by field_simp <;> ring
          have h2 : C' * p₂ * (N:ℝ)^2 * r j / L / 2
              = (C' * p₂) * ((N:ℝ)^2 * r j) / L / 2 := by ring
          rw [h1, h2]
          have hAq : A * q j ≤ C' * p₂ := by nlinarith [hC'p, hAnn, hq', hqpos j]
          have hnn : (0:ℝ) ≤ ((N:ℝ)^2 * r j) / L / 2 := by positivity
          have e1 : (A * q j) * ((N:ℝ)^2 * r j) / L / 2
              = (A * q j) * (((N:ℝ)^2 * r j) / L / 2) := by ring
          have e2 : (C' * p₂) * ((N:ℝ)^2 * r j) / L / 2
              = (C' * p₂) * (((N:ℝ)^2 * r j) / L / 2) := by ring
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_right hAq hnn
        have hterm2 : (N:ℝ)/2 ≤ C' * p₂ * (N:ℝ)^2 * r j / L / 2 := by
          have hkey : L ≤ C' * p₂ * (N:ℝ) * r j := by
            nlinarith [hLabs, mul_nonneg (mul_nonneg (mul_nonneg
              (sub_nonneg.mpr hC'1) hp20.le) hNR.le) (hrpos j).le]
          have h1 := mul_le_mul_of_nonneg_right hkey hNR.le
          have h2 : C' * p₂ * (N:ℝ)^2 * r j / L / 2
              = (C' * p₂ * (N:ℝ)^2 * r j) / (2*L) := by ring
          rw [h2, le_div_iff₀ (by positivity)]
          calc (N:ℝ)/2 * (2*L) = L * (N:ℝ) := by ring
            _ ≤ (C' * p₂ * (N:ℝ) * r j) * (N:ℝ) := h1
            _ = C' * p₂ * (N:ℝ)^2 * r j := by ring
        linarith
      exact le_trans hpd hfin
    · push_neg at hjJ
      refine le_trans (hNt j hjJ) ?_
      have h1 : Ct / L ≤ C' / L := div_le_div_of_nonneg_right hCtle hL0.le
      have h2 : (0:ℝ) ≤ (N:ℝ)^2 * ‖fullSiteMean N h j‖ := by positivity
      exact mul_le_mul_of_nonneg_right h1 h2
  · -- window clause
    have hfun0 : (fun n => ePhase ((h:ℝ) * roughTail 2 J n)) = roughProd h (Finset.Icc 1 J) :=
      funext (fun n => ePhase_roughTail_prod h J n)
    have hdd0 : ‖(∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => 2 ∣ n + 0),
          roughProd h (Finset.Icc 1 J) n)
        - ∑ n ∈ (Finset.Ico N (2*N)).filter (fun n => ¬ 2 ∣ n + 0),
          roughProd h (Finset.Icc 1 J) n‖ ≤ A / L * ((N:ℝ) * L ^ κ.re) := by
      rw [parityDisc_class_diff]
      simpa using (hND J hJ1 le_rfl 0 (by norm_num) 1 (by norm_num)).1
    have hpd0 : ‖parityDisc N 0 (fun n => ePhase ((h:ℝ) * roughTail 2 J n))‖
        ≤ (N:ℝ)/2 * (A / L * ((N:ℝ) * L ^ κ.re)) + (N:ℝ)/2 := by
      rw [hfun0]
      exact norm_parityDisc_le N 0 _ (fun n => le_of_eq (norm_roughProd h _ n)) _ hdd0
    have hreJ : -((m:ℝ)) ≤ κ.re :=
      le_trans (by linarith [hmK]) (neg_bound_le_re (hκdef ▸ norm_sdExponent_Icc h J))
    have hLabs : L ≤ δ₂ * (N:ℝ) * L ^ κ.re :=
      log_le_of_rpow_le hL1 m (by positivity)
        (le_trans hminpow (by nlinarith [min_le_right p₂ δ₂, hNR.le])) hreJ
    refine le_trans hpd0 ?_
    have hR : C' * δ₂ * (N:ℝ)^2 * L ^ κ.re / L
        ≤ C' / L * ((N:ℝ)^2 * ∏ j ∈ Finset.Icc 1 J, ‖fullSiteMean N h j‖) := by
      have h1 : C' * δ₂ * (N:ℝ)^2 * L ^ κ.re / L
          = C' / L * ((N:ℝ)^2 * (δ₂ * L ^ κ.re)) := by field_simp <;> ring
      rw [h1]
      have h2 : (0:ℝ) ≤ C' / L := by positivity
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprodF (by positivity)) h2
    refine le_trans ?_ hR
    have hterm1 : (N:ℝ)/2 * (A / L * ((N:ℝ) * L ^ κ.re))
        ≤ C' * δ₂ * (N:ℝ)^2 * L ^ κ.re / L / 2 := by
      have h1 : (N:ℝ)/2 * (A / L * ((N:ℝ) * L ^ κ.re))
          = A * ((N:ℝ)^2 * L ^ κ.re) / L / 2 := by field_simp <;> ring
      have h2 : C' * δ₂ * (N:ℝ)^2 * L ^ κ.re / L / 2
          = (C' * δ₂) * ((N:ℝ)^2 * L ^ κ.re) / L / 2 := by ring
      rw [h1, h2]
      have hnn : (0:ℝ) ≤ ((N:ℝ)^2 * L ^ κ.re) / L / 2 := by positivity
      have e1 : A * ((N:ℝ)^2 * L ^ κ.re) / L / 2
          = A * (((N:ℝ)^2 * L ^ κ.re) / L / 2) := by ring
      have e2 : (C' * δ₂) * ((N:ℝ)^2 * L ^ κ.re) / L / 2
          = (C' * δ₂) * (((N:ℝ)^2 * L ^ κ.re) / L / 2) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hC'δ hnn
    have hterm2 : (N:ℝ)/2 ≤ C' * δ₂ * (N:ℝ)^2 * L ^ κ.re / L / 2 := by
      have hkey : L ≤ C' * δ₂ * (N:ℝ) * L ^ κ.re := by
        nlinarith [hLabs, mul_nonneg (mul_nonneg (mul_nonneg
          (sub_nonneg.mpr hC'1) hδ₂0.le) hNR.le) hκre.le]
      have h1 := mul_le_mul_of_nonneg_right hkey hNR.le
      have h2 : C' * δ₂ * (N:ℝ)^2 * L ^ κ.re / L / 2
          = (C' * δ₂ * (N:ℝ)^2 * L ^ κ.re) / (2*L) := by ring
      rw [h2, le_div_iff₀ (by positivity)]
      calc (N:ℝ)/2 * (2*L) = L * (N:ℝ) := by ring
        _ ≤ (C' * δ₂ * (N:ℝ) * L ^ κ.re) * (N:ℝ) := h1
        _ = C' * δ₂ * (N:ℝ)^2 * L ^ κ.re := by ring
    linarith

/-- **Headline**: off the Chowla sector the G₄ window law rests on ONE analytic input. -/
theorem isNormal_G4_of_summatory
    (hSD : ∀ h : ℤ, h ≠ 0 → ¬ ChowlaSector h → RoughSummatory h)
    (hCh : ∀ h : ℤ, h ≠ 0 → ChowlaSector h → WindowDecay h)
    (hSite : SiteDecayFull) : IsNormal 4 (primeLambertAtBase 4) :=
  isNormal_G4_of_parity
    (fun h hh hc => ⟨roughIndependenceAt_two_of_summatory (hSD h hh hc),
      parityDiscrepancy_of_summatory hh hc (hSD h hh hc)⟩) hCh hSite

#print axioms isNormal_G4_of_summatory
#print axioms roughIndependenceAt_two_of_summatory
#print axioms parityDiscrepancy_of_summatory

end NormalNumbers.G4
