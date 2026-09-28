import NormalNumbers.ElliottDivisorTail
import NormalNumbers.ElliottReindex

/-!
# The squarefull expansion of a correlation

Leaf 2, Case B.  `U = u ⋆ Ũ` (`ElliottSquarefullConv.U_eq_sum_divisors`) turns the correlation of
a unimodular **multiplicative** `U₁` against any bounded `g₂` into a `d`-sum of *restricted*
correlations, in which the first function is the unimodular **completely** multiplicative `Ũ₁`
evaluated at `(a₁n+b₁)/d`:

`corr(U₁, g₂) = ∑_{d ≤ Y} u₁(d) · corr_d(Ũ₁, g₂)`,
`corr_d(Ũ₁,g₂) = ∑_{n : d ∣ a₁n+b₁} (1/n) Ũ₁((a₁n+b₁)/d) g₂(a₂n+b₂)`.

Truncating at `D` costs `(a₁+|b₁|)(1+log(Y/L))ε` by `ElliottDivisorTail`, so only the finitely many
`d ≤ D` remain — and on each of those, `ElliottReindex` turns `corr_d` into genuine
`elliottLogWindow` correlations at reduced scale.

## Main results

* `divTerm` — the `d`-th term of the expansion, as a function of the integer affine value.
* `posExt_eq_sum_divTerm` — the pointwise expansion, valid at **every** integer `≤ Y`.
* `elliottLogCorrelation_expand` — the correlation as a `d`-sum.
* `norm_elliottLogCorrelation_le_truncated` — the truncated bound: the head `d ≤ D` plus the
  tail's `ε`-cost.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottExpand

open Erdos67b ArithmeticFunction NormalNumbers.ElliottSquarefullConv

noncomputable section

/-- The `d`-th term of the squarefull expansion, at an integer affine value. -/
def divTerm (f : ℕ → ℂ) (d : ℕ) (m : ℤ) : ℂ :=
  if (d : ℤ) ∣ m then positiveIntExtension f (m / d) else 0

theorem norm_divTerm_le {f : ℕ → ℂ} (hf : ∀ n : ℕ, ‖f n‖ ≤ 1) (d : ℕ) (m : ℤ) :
    ‖divTerm f d m‖ ≤ 1 := by
  rw [divTerm]
  split_ifs with h
  · rw [positiveIntExtension]
    split_ifs with h2
    · exact hf _
    · simp
  · simp

theorem divTerm_eq_zero_of_not_dvd {f : ℕ → ℂ} {d : ℕ} {m : ℤ} (h : ¬ (d : ℤ) ∣ m) :
    divTerm f d m = 0 := by
  rw [divTerm, if_neg h]

/-- **The pointwise expansion.**  Valid at every integer `m ≤ Y`, including `m ≤ 0` (where both
sides vanish). -/
theorem posExt_eq_sum_divTerm {U : ℕ → ℂ} (hone : U 1 = 1) {Y : ℕ} {m : ℤ} (hm : m ≤ (Y : ℤ)) :
    positiveIntExtension U m
      = ∑ d ∈ Finset.Icc 1 Y, squarefullPart U d * divTerm (fun n => cmExt U n) d m := by
  classical
  rcases le_or_gt m 0 with hm0 | hmpos
  · have hL : positiveIntExtension U m = 0 := positiveIntExtension_nonpos hm0
    rw [hL]
    refine (Finset.sum_eq_zero fun d hd => ?_).symm
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have : divTerm (fun n => cmExt U n) d m = 0 := by
      rw [divTerm]
      split_ifs with h
      · refine positiveIntExtension_nonpos ?_
        have hdpos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd1
        have := Int.ediv_le_ediv hdpos hm0
        simpa using this
      · rfl
    rw [this, mul_zero]
  · set t : ℕ := m.toNat with ht
    have hmt : (t : ℤ) = m := Int.toNat_of_nonneg hmpos.le
    have htpos : 0 < t := by omega
    have htY : t ≤ Y := by omega
    have hL : positiveIntExtension U m = U t := by
      rw [← hmt, positiveIntExtension_natCast htpos]
    rw [hL, U_eq_sum_divisors U (by omega : t ≠ 0)]
    have hsub : t.divisors ⊆ Finset.Icc 1 Y := by
      intro d hd
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
      exact Finset.mem_Icc.mpr
        ⟨Nat.pos_of_dvd_of_pos hdvd htpos, le_trans (Nat.le_of_dvd htpos hdvd) htY⟩
    have hzero : ∀ d ∈ Finset.Icc 1 Y, d ∉ t.divisors →
        squarefullPart U d * divTerm (fun n => cmExt U n) d m = 0 := by
      intro d hd hnd
      have hnotdvd : ¬ (d : ℤ) ∣ m := by
        rw [← hmt]
        intro hcon
        exact hnd (Nat.mem_divisors.mpr ⟨Int.ofNat_dvd.mp hcon, by omega⟩)
      rw [divTerm_eq_zero_of_not_dvd hnotdvd, mul_zero]
    rw [← Finset.sum_subset hsub hzero]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    have hd1 : 0 < d := Nat.pos_of_dvd_of_pos hdvd htpos
    have hdvdZ : (d : ℤ) ∣ m := by rw [← hmt]; exact Int.ofNat_dvd.mpr hdvd
    have hquot : m / (d : ℤ) = ((t / d : ℕ) : ℤ) := by
      rw [← hmt]
      exact (Int.natCast_div t d).symm ▸ rfl
    have hqpos : 0 < t / d := Nat.div_pos (Nat.le_of_dvd htpos hdvd) hd1
    rw [divTerm, if_pos hdvdZ, hquot, positiveIntExtension_natCast hqpos]

/-! ## The correlation as a `d`-sum -/

/-- The `d`-th restricted correlation: the first function is the **completely** multiplicative
`Ũ₁ = cmExt U₁`, evaluated at `(a₁n+b₁)/d`, and the sum is restricted to `d ∣ a₁n+b₁`. -/
def restrictedCorr (U₁ : ℕ → ℂ) (g₂ : ℤ → ℂ) (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (X W d : ℕ) : ℂ :=
  ∑ n ∈ elliottLogWindow X W,
    (harmonicWeight n : ℂ) * divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n) *
      g₂ (integerAffine a₂ b₂ n)

theorem elliottLogCorrelation_expand {U₁ : ℕ → ℂ} (hone : U₁ 1 = 1) (g₂ : ℤ → ℂ)
    (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (X W Y : ℕ)
    (hY : ∀ n ∈ elliottLogWindow X W, integerAffine a₁ b₁ n ≤ (Y : ℤ)) :
    elliottLogCorrelation (positiveIntExtension U₁) g₂ a₁ a₂ b₁ b₂ X W
      = ∑ d ∈ Finset.Icc 1 Y, squarefullPart U₁ d * restrictedCorr U₁ g₂ a₁ a₂ b₁ b₂ X W d := by
  classical
  rw [elliottLogCorrelation]
  have hstep : ∀ n ∈ elliottLogWindow X W,
      (harmonicWeight n : ℂ) * positiveIntExtension U₁ (integerAffine a₁ b₁ n) *
          g₂ (integerAffine a₂ b₂ n)
        = ∑ d ∈ Finset.Icc 1 Y, squarefullPart U₁ d *
            ((harmonicWeight n : ℂ) * divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n) *
              g₂ (integerAffine a₂ b₂ n)) := by
    intro n hn
    rw [posExt_eq_sum_divTerm hone (hY n hn)]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [restrictedCorr, Finset.mul_sum]

/-! ## The truncated bound -/

/-- **The truncation.**  Only the `d ≤ D` restricted correlations remain; the rest costs
`(a₁+|b₁|)(1 + log Y − log L) ε`, with `ε` the uniform squarefull tail bound. -/
theorem norm_elliottLogCorrelation_le_truncated {U₁ : ℕ → ℂ} (hone : U₁ 1 = 1)
    (hUp : ∀ p : ℕ, p.Prime → ‖U₁ p‖ = 1) {g₂ : ℤ → ℂ} (h2 : ∀ z : ℤ, ‖g₂ z‖ ≤ 1)
    {a₁ : ℕ} (ha₁ : 0 < a₁) (a₂ : ℕ) (b₁ b₂ : ℤ) (X W : ℕ)
    {L D : ℕ} (hL : 1 ≤ L) (hD : 1 ≤ D) (hDY : D ≤ a₁ * X + b₁.natAbs)
    (hLY : L ≤ a₁ * X + b₁.natAbs) {ε : ℝ} (hε : 0 ≤ ε)
    (hLbd : ∀ n ∈ elliottLogWindow X W, 0 < integerAffine a₁ b₁ n →
      (L : ℤ) ≤ integerAffine a₁ b₁ n)
    (htail : ∑ d ∈ Finset.Icc (D + 1) (a₁ * X + b₁.natAbs),
      ‖squarefullPart U₁ d‖ / (d : ℝ) ≤ ε) :
    ‖elliottLogCorrelation (positiveIntExtension U₁) g₂ a₁ a₂ b₁ b₂ X W‖
      ≤ (∑ d ∈ Finset.Icc 1 D,
            ‖squarefullPart U₁ d‖ * ‖restrictedCorr U₁ g₂ a₁ a₂ b₁ b₂ X W d‖)
        + ((a₁ + b₁.natAbs : ℕ) : ℝ) *
            ((1 + Real.log ((a₁ * X + b₁.natAbs : ℕ) : ℝ) - Real.log (L : ℝ)) * ε) := by
  classical
  set Y : ℕ := a₁ * X + b₁.natAbs with hYdef
  have hYbd : ∀ n ∈ elliottLogWindow X W, integerAffine a₁ b₁ n ≤ (Y : ℤ) := by
    intro n hn
    obtain ⟨-, hnX, -⟩ := mem_elliottLogWindow.mp hn
    rw [integerAffine, hYdef]
    have h1 : (a₁ : ℤ) * n ≤ (a₁ : ℤ) * X := by
      have : (n : ℤ) ≤ (X : ℤ) := by exact_mod_cast hnX
      have ha : (0 : ℤ) ≤ (a₁ : ℤ) := by positivity
      nlinarith
    push_cast
    have hb : b₁ ≤ |b₁| := le_abs_self b₁
    have hbn : (b₁.natAbs : ℤ) = |b₁| := (Int.abs_eq_natAbs b₁).symm
    linarith
  rw [elliottLogCorrelation_expand hone g₂ a₁ a₂ b₁ b₂ X W Y hYbd]
  have hsplit : ∑ d ∈ Finset.Icc 1 Y, squarefullPart U₁ d * restrictedCorr U₁ g₂ a₁ a₂ b₁ b₂ X W d
      = (∑ d ∈ Finset.Icc 1 D, squarefullPart U₁ d * restrictedCorr U₁ g₂ a₁ a₂ b₁ b₂ X W d)
        + ∑ d ∈ Finset.Icc (D + 1) Y,
            squarefullPart U₁ d * restrictedCorr U₁ g₂ a₁ a₂ b₁ b₂ X W d := by
    rw [← Finset.sum_union]
    · congr 1
      ext d
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    · rw [Finset.disjoint_left]
      intro d hd hd'
      rw [Finset.mem_Icc] at hd hd'
      omega
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add ?_ ?_
  · refine le_trans (norm_sum_le _ _) ?_
    exact le_of_eq (Finset.sum_congr rfl fun d _ => norm_mul _ _)
  -- the tail
  · have hswap : ∑ d ∈ Finset.Icc (D + 1) Y,
        squarefullPart U₁ d * restrictedCorr U₁ g₂ a₁ a₂ b₁ b₂ X W d
        = ∑ n ∈ elliottLogWindow X W,
            ((harmonicWeight n : ℂ) *
              (∑ d ∈ Finset.Icc (D + 1) Y, squarefullPart U₁ d *
                divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n)) *
              g₂ (integerAffine a₂ b₂ n)) := by
      simp only [restrictedCorr, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [hswap]
    have hcm : ∀ n : ℕ, ‖(fun k => cmExt U₁ k) n‖ ≤ 1 := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [norm_cmExt hUp hn]
    set F : ℕ → ℝ := fun n =>
      if 0 < integerAffine a₁ b₁ n then
        (n : ℝ)⁻¹ * ∑ d ∈ (Finset.Icc (D + 1) Y).filter
          (fun d => d ∣ (integerAffine a₁ b₁ n).toNat), ‖squarefullPart U₁ d‖
      else 0 with hF
    have hterm : ∀ n ∈ elliottLogWindow X W,
        ‖(harmonicWeight n : ℂ) *
            (∑ d ∈ Finset.Icc (D + 1) Y, squarefullPart U₁ d *
              divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n)) *
            g₂ (integerAffine a₂ b₂ n)‖ ≤ F n := by
      intro n hn
      have hnpos : 0 < n := (mem_elliottLogWindow.mp hn).1
      have hw : ‖((harmonicWeight n : ℝ) : ℂ)‖ = (n : ℝ)⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, harmonicWeight,
          abs_of_nonneg (by positivity)]
      have hwnn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      set S : ℂ := ∑ d ∈ Finset.Icc (D + 1) Y, squarefullPart U₁ d *
        divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n) with hS
      have hnorm : ‖(harmonicWeight n : ℂ) * S * g₂ (integerAffine a₂ b₂ n)‖
          ≤ (n : ℝ)⁻¹ * ‖S‖ := by
        rw [norm_mul, norm_mul, hw]
        calc (n : ℝ)⁻¹ * ‖S‖ * ‖g₂ (integerAffine a₂ b₂ n)‖
            ≤ (n : ℝ)⁻¹ * ‖S‖ * 1 :=
              mul_le_mul_of_nonneg_left (h2 _) (by positivity)
          _ = (n : ℝ)⁻¹ * ‖S‖ := by ring
      refine le_trans hnorm ?_
      rcases lt_or_ge 0 (integerAffine a₁ b₁ n) with hpos | hnp
      · simp only [hF, if_pos hpos]
        refine mul_le_mul_of_nonneg_left ?_ hwnn
        have hcast : ((integerAffine a₁ b₁ n).toNat : ℤ) = integerAffine a₁ b₁ n :=
          Int.toNat_of_nonneg hpos.le
        have hbd : ∀ d ∈ Finset.Icc (D + 1) Y,
            ‖squarefullPart U₁ d * divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n)‖
              ≤ if d ∣ (integerAffine a₁ b₁ n).toNat then ‖squarefullPart U₁ d‖ else 0 := by
          intro d _
          by_cases hdvd : d ∣ (integerAffine a₁ b₁ n).toNat
          · rw [if_pos hdvd, norm_mul]
            calc ‖squarefullPart U₁ d‖ * ‖divTerm (fun k => cmExt U₁ k) d
                  (integerAffine a₁ b₁ n)‖
                ≤ ‖squarefullPart U₁ d‖ * 1 :=
                  mul_le_mul_of_nonneg_left (norm_divTerm_le hcm d _) (norm_nonneg _)
              _ = ‖squarefullPart U₁ d‖ := by ring
          · rw [if_neg hdvd]
            have hnd : ¬ (d : ℤ) ∣ integerAffine a₁ b₁ n := by
              rw [← hcast]
              intro hcon
              exact hdvd (Int.ofNat_dvd.mp hcon)
            rw [divTerm_eq_zero_of_not_dvd hnd, mul_zero, norm_zero]
        calc ‖S‖ ≤ ∑ d ∈ Finset.Icc (D + 1) Y,
              ‖squarefullPart U₁ d * divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ d ∈ Finset.Icc (D + 1) Y,
              (if d ∣ (integerAffine a₁ b₁ n).toNat then ‖squarefullPart U₁ d‖ else 0) :=
            Finset.sum_le_sum hbd
          _ = _ := by rw [Finset.sum_filter]
      · have hzero : S = 0 := by
          rw [hS]
          refine Finset.sum_eq_zero fun d hd => ?_
          have hd1 : 1 ≤ d := by
            have := (Finset.mem_Icc.mp hd).1
            omega
          have : divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n) = 0 := by
            rw [divTerm]
            split_ifs with h
            · refine positiveIntExtension_nonpos ?_
              have hdpos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd1
              have := Int.ediv_le_ediv hdpos hnp
              simpa using this
            · rfl
          rw [this, mul_zero]
        rw [hzero, norm_zero, mul_zero]
        simp only [hF]
        rw [if_neg (by omega)]
    refine le_trans (le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)) ?_
    have hFsum : ∑ n ∈ elliottLogWindow X W, F n
        = ∑ n ∈ (elliottLogWindow X W).filter (fun n => 0 < integerAffine a₁ b₁ n),
            (n : ℝ)⁻¹ * ∑ d ∈ (Finset.Icc (D + 1) Y).filter
              (fun d => d ∣ (integerAffine a₁ b₁ n).toNat), ‖squarefullPart U₁ d‖ := by
      rw [Finset.sum_filter]
    rw [hFsum]
    exact NormalNumbers.ElliottDivisorTail.sum_window_divisor_tail_le ha₁ b₁ X W hL hD hε
      hLY hLbd htail

end

end NormalNumbers.ElliottExpand
