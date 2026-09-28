import NormalNumbers.ElliottExpand

/-!
# The restricted correlation as a sum of genuine correlations

Leaf 2, Case B, the last structural step of stage one.

`ElliottExpand` left the finitely many restricted correlations

`corr_d = ∑_{n ∈ (X/W,X], d ∣ a₁n+b₁} (1/n) Ũ₁((a₁n+b₁)/d) g₂(a₂n+b₂)`.

Splitting the window by the residue `n₀ = n mod d` and substituting `n = dk + n₀` turns each
nonempty class into a **genuine** `elliottLogCorrelation`, because with `q = d`

* `(a₁n+b₁)/d = a₁ k + c`, `c = (a₁n₀+b₁)/d` — the *dilation `a₁` is unchanged*;
* `a₂n+b₂ = (a₂d) k + (a₂n₀+b₂)`;
* the determinant is preserved exactly: `a₁(a₂n₀+b₂) − (a₂d)c = a₁b₂ − a₂b₁`
  (`ElliottProgression.det_progression` with `d₂ = 1`),

and `ElliottReindex.norm_sum_sub_reindexed_le` supplies the window/weight bookkeeping at the cost
of an absolute `4` per class.  Since `d ≤ D` and `D` is fixed before the threshold `A₀`, the total
`4d` is absorbed by taking `A₀` large.

## Main results

* `newShift` — the shift `c = (a₁n₀+b₁)/d` of the substituted form.
* `det_newShift` — the determinant is preserved exactly.
* `norm_restrictedCorr_le` — `‖corr_d‖ ≤ ∑_{n₀ < d} ((1/d)‖corr(Ũ₁, g₂; a₁, a₂d, c, c₂)‖ + 4)`.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottRestricted

open Erdos67b NormalNumbers.ElliottSquarefullConv NormalNumbers.ElliottExpand

noncomputable section

/-- The shift of the substituted first form, `c = (a₁n₀+b₁)/d`. -/
def newShift (a₁ : ℕ) (b₁ : ℤ) (d n₀ : ℕ) : ℤ := ((a₁ : ℤ) * n₀ + b₁) / d

/-- **The determinant is preserved exactly.** -/
theorem det_newShift {a₁ a₂ d n₀ : ℕ} {b₁ b₂ : ℤ} (hd : (d : ℤ) ∣ (a₁ : ℤ) * n₀ + b₁) :
    (a₁ : ℤ) * ((a₂ : ℤ) * n₀ + b₂) - ((a₂ : ℤ) * d) * newShift a₁ b₁ d n₀
      = (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ := by
  have hc : (a₁ : ℤ) * n₀ + b₁ = (d : ℤ) * newShift a₁ b₁ d n₀ := by
    rw [newShift, Int.mul_ediv_cancel' hd]
  linear_combination (a₂ : ℤ) * hc

/-- **The reduction of a restricted correlation.**  Each residue class `n ≡ n₀ (mod d)` becomes a
genuine correlation at the reduced scale, up to an absolute `4`. -/
theorem norm_restrictedCorr_le {U₁ : ℕ → ℂ} (hUp : ∀ p : ℕ, p.Prime → ‖U₁ p‖ = 1)
    {g₂ : ℤ → ℂ} (h2 : ∀ z : ℤ, ‖g₂ z‖ ≤ 1)
    (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) {X W d : ℕ} (hd : 0 < d) (hW : 0 < W) :
    ‖restrictedCorr U₁ g₂ a₁ a₂ b₁ b₂ X W d‖
      ≤ ∑ n₀ ∈ (Finset.range d).filter (fun n₀ : ℕ => (d : ℤ) ∣ (a₁ : ℤ) * (n₀ : ℤ) + b₁),
          ((d : ℝ)⁻¹ * ‖elliottLogCorrelation
              (positiveIntExtension (fun k => cmExt U₁ k)) g₂
              a₁ (a₂ * d) (newShift a₁ b₁ d n₀) ((a₂ : ℤ) * n₀ + b₂)
              (ElliottReindex.progScale X n₀ d)
              (min W (ElliottReindex.progScale X n₀ d))‖ + 4) := by
  classical
  have hcm : ∀ n : ℕ, ‖(fun k => cmExt U₁ k) n‖ ≤ 1 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [norm_cmExt hUp hn]
  have hposcm : ∀ z : ℤ, ‖positiveIntExtension (fun k => cmExt U₁ k) z‖ ≤ 1 := by
    intro z
    rw [positiveIntExtension]
    split_ifs
    · exact hcm _
    · simp
  -- split the window by the residue mod `d`
  have hmaps : ∀ n ∈ elliottLogWindow X W, n % d ∈ Finset.range d := by
    intro n _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hd)
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => (harmonicWeight n : ℂ) * divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n) *
      g₂ (integerAffine a₂ b₂ n))
  rw [restrictedCorr, ← hfiber]
  -- the classes with `d ∤ a₁n₀+b₁` are empty: every term vanishes
  have hvanish : ∀ n₀ ∈ Finset.range d,
      n₀ ∉ (Finset.range d).filter (fun n₀ : ℕ => (d : ℤ) ∣ (a₁ : ℤ) * (n₀ : ℤ) + b₁) →
      ∑ n ∈ (elliottLogWindow X W).filter (fun n => n % d = n₀),
        (harmonicWeight n : ℂ) * divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n) *
          g₂ (integerAffine a₂ b₂ n) = 0 := by
    intro n₀ hn₀ hnf
    have hdvd : ¬ (d : ℤ) ∣ (a₁ : ℤ) * n₀ + b₁ := fun hc =>
      hnf (Finset.mem_filter.mpr ⟨hn₀, hc⟩)
    have hzero : ∀ n ∈ (elliottLogWindow X W).filter (fun n => n % d = n₀),
        (harmonicWeight n : ℂ) * divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n) *
          g₂ (integerAffine a₂ b₂ n) = 0 := by
      intro n hn
      obtain ⟨-, hmod⟩ := Finset.mem_filter.mp hn
      have hsplit : d * (n / d) + n₀ = n := by
        conv_rhs => rw [← Nat.div_add_mod n d, hmod]
      have hnd : ¬ (d : ℤ) ∣ integerAffine a₁ b₁ n := by
        intro hcon
        refine hdvd ?_
        have hcast : (n : ℤ) = (d : ℤ) * ((n / d : ℕ) : ℤ) + (n₀ : ℤ) := by
          exact_mod_cast hsplit.symm
        have hrw : integerAffine a₁ b₁ n
            = (d : ℤ) * ((a₁ : ℤ) * ((n / d : ℕ) : ℤ)) + ((a₁ : ℤ) * n₀ + b₁) := by
          rw [integerAffine, hcast]
          ring
        rw [hrw] at hcon
        exact (dvd_add_right (dvd_mul_right (d : ℤ) ((a₁ : ℤ) * ((n / d : ℕ) : ℤ)))).mp hcon
      rw [divTerm_eq_zero_of_not_dvd hnd, mul_zero, zero_mul]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hvanish]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n₀ hn₀ => ?_)
  obtain ⟨hn₀mem, hdvd⟩ := Finset.mem_filter.mp hn₀
  have hn₀d : n₀ < d := Finset.mem_range.mp hn₀mem
  · -- the class contributes a genuine correlation
    set c : ℤ := newShift a₁ b₁ d n₀ with hc
    have hcmul : (a₁ : ℤ) * n₀ + b₁ = (d : ℤ) * c := by
      rw [hc, newShift, Int.mul_ediv_cancel' hdvd]
    set G : ℕ → ℂ := fun k =>
      positiveIntExtension (fun j => cmExt U₁ j) (integerAffine a₁ c k) *
        g₂ (integerAffine (a₂ * d) ((a₂ : ℤ) * n₀ + b₂) k) with hG
    have hGb : ∀ k, ‖G k‖ ≤ 1 := by
      intro k
      rw [hG, norm_mul]
      calc ‖positiveIntExtension (fun j => cmExt U₁ j) (integerAffine a₁ c k)‖ *
            ‖g₂ (integerAffine (a₂ * d) ((a₂ : ℤ) * n₀ + b₂) k)‖
          ≤ 1 * 1 := mul_le_mul (hposcm _) (h2 _) (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    have hterm : ∀ n ∈ (elliottLogWindow X W).filter (fun n => n % d = n₀),
        (harmonicWeight n : ℂ) * divTerm (fun k => cmExt U₁ k) d (integerAffine a₁ b₁ n) *
            g₂ (integerAffine a₂ b₂ n)
          = ((n : ℝ)⁻¹ : ℂ) * G ((n - n₀) / d) := by
      intro n hn
      obtain ⟨hnw, hmod⟩ := Finset.mem_filter.mp hn
      have hsplit : d * (n / d) + n₀ = n := by
        conv_rhs => rw [← Nat.div_add_mod n d, hmod]
      have hk : (n - n₀) / d = n / d := by
        have hsub : n - n₀ = d * (n / d) := by omega
        rw [hsub, Nat.mul_div_cancel_left _ hd]
      set k : ℕ := n / d with hkdef
      have haff : integerAffine a₁ b₁ n = (d : ℤ) * integerAffine a₁ c k := by
        rw [integerAffine, integerAffine, ← hsplit]
        push_cast
        linear_combination hcmul
      have hdvdn : (d : ℤ) ∣ integerAffine a₁ b₁ n := ⟨_, haff⟩
      have hquot : integerAffine a₁ b₁ n / (d : ℤ) = integerAffine a₁ c k := by
        rw [haff, Int.mul_ediv_cancel_left _ (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0)]
      have haff2 : integerAffine a₂ b₂ n
          = integerAffine (a₂ * d) ((a₂ : ℤ) * n₀ + b₂) k := by
        rw [integerAffine, integerAffine, ← hsplit]
        push_cast
        ring
      rw [divTerm, if_pos hdvdn, hquot, haff2, hk, harmonicWeight, hG]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm]
    have hre := ElliottReindex.norm_sum_sub_reindexed_le (q := d) (n₀ := n₀) (X := X) (W := W)
      hd hn₀d hW G hGb
    have hcorr : ((d : ℝ)⁻¹ : ℂ) * ∑ k ∈ elliottLogWindow (ElliottReindex.progScale X n₀ d)
          (min W (ElliottReindex.progScale X n₀ d)), ((k : ℝ)⁻¹ : ℂ) * G k
        = ((d : ℝ)⁻¹ : ℂ) * elliottLogCorrelation
            (positiveIntExtension (fun k => cmExt U₁ k)) g₂
            a₁ (a₂ * d) c ((a₂ : ℤ) * n₀ + b₂)
            (ElliottReindex.progScale X n₀ d)
            (min W (ElliottReindex.progScale X n₀ d)) := by
      have hinner : ∑ k ∈ elliottLogWindow (ElliottReindex.progScale X n₀ d)
            (min W (ElliottReindex.progScale X n₀ d)), ((k : ℝ)⁻¹ : ℂ) * G k
          = elliottLogCorrelation (positiveIntExtension (fun k => cmExt U₁ k)) g₂
              a₁ (a₂ * d) c ((a₂ : ℤ) * n₀ + b₂)
              (ElliottReindex.progScale X n₀ d)
              (min W (ElliottReindex.progScale X n₀ d)) := by
        rw [elliottLogCorrelation]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hG, harmonicWeight]
        push_cast
        ring
      rw [hinner]
    have hnormsplit : ‖∑ n ∈ (elliottLogWindow X W).filter (fun n => n % d = n₀),
        ((n : ℝ)⁻¹ : ℂ) * G ((n - n₀) / d)‖
        ≤ ‖((d : ℝ)⁻¹ : ℂ) * ∑ k ∈ elliottLogWindow (ElliottReindex.progScale X n₀ d)
            (min W (ElliottReindex.progScale X n₀ d)), ((k : ℝ)⁻¹ : ℂ) * G k‖ + 4 := by
      have := norm_sub_norm_le (∑ n ∈ (elliottLogWindow X W).filter (fun n => n % d = n₀),
        ((n : ℝ)⁻¹ : ℂ) * G ((n - n₀) / d))
        (((d : ℝ)⁻¹ : ℂ) * ∑ k ∈ elliottLogWindow (ElliottReindex.progScale X n₀ d)
          (min W (ElliottReindex.progScale X n₀ d)), ((k : ℝ)⁻¹ : ℂ) * G k)
      linarith [hre, this]
    refine le_trans hnormsplit ?_
    rw [hcorr, norm_mul]
    have hdn : ‖((d : ℝ)⁻¹ : ℂ)‖ = (d : ℝ)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_natCast]
    rw [hdn]
end

end NormalNumbers.ElliottRestricted
