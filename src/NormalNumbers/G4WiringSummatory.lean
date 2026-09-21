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
      ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ windowJ N →
        ‖roughPrefixMean N h k
            - c (Finset.Icc 1 k) * ((Real.log N : ℝ) : ℂ) ^ sdExponent h (Finset.Icc 1 k)‖
          ≤ A / Real.log N * Real.log N ^ (sdExponent h (Finset.Icc 1 k)).re
        ∧ ‖roughSiteMean N h k 2 - c {k} * ((Real.log N : ℝ) : ℂ) ^ sdExponent h {k}‖
          ≤ A * ((1:ℝ)/4) ^ k / Real.log N * Real.log N ^ (sdExponent h {k}).re := by
  classical
  obtain ⟨c, B, C, δ, hC, hδ, hcB, hclow, hcone, hev⟩ := hS
  have hBnn : (0:ℝ) ≤ B := le_trans (norm_nonneg _) (hcB ∅)
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  set K : ℝ := 4 * Real.pi * |(h : ℝ)| with hK
  have hKnn : (0:ℝ) ≤ K := by rw [hK]; positivity
  set A : ℝ := 6 * C + 4 * B * K with hA
  have hAnn : (0:ℝ) ≤ A := by rw [hA]; positivity
  refine ⟨c, B, A, δ, hAnn, hδ, hBnn, hcB, hclow, hcone, ?_⟩
  have hdouble : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by show n ≤ 2 * n; omega) tendsto_id
  have hev2 := hdouble.eventually hev
  have hlogK : ∀ᶠ N : ℕ in atTop, max 1 K ≤ Real.log N := by
    have := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop (max 1 K)
  filter_upwards [hev, hev2, hlogK, eventually_gt_atTop 0] with N hN hN2 hNlog hN0
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

end Wiring

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
