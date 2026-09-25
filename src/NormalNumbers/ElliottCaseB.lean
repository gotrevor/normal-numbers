import NormalNumbers.ElliottStageCost
import NormalNumbers.ElliottThresholdFamily
import NormalNumbers.ElliottZeroExt
import NormalNumbers.ElliottRandomize
import NormalNumbers.ElliottPretentiousTransfer
import NormalNumbers.ElliottMertensIterate
import NormalNumbers.ElliottRankin

/-!
# Case B of leaf 2: the ε-budget assembly

Leaf 2's dichotomy is on the Euler defect `Σ_L(g₁)` at the thin scale.  Case A (defect large) is
`ElliottCaseAThin`; this module is Case B (defect small), the half that consumes
`AffineCMLogElliott`.

## The chain

Start from `g₁, g₂ : ℤ → ℂ`, `1`-bounded and multiplicative on the positive integers, with
`restrictToNat g₁` non-pretentious at level `A` and scale `X`.

0. **Zero-extension** (`ElliottZeroExt.norm_sub_posExt_le`).  Replace `gᵢ` by the zero-extension of
   its natural restriction, at the absolute cost `2(|b₁|+|b₂|)`.
1. **Randomise** (`ElliottRandomize.exists_cover_pair_ge`).  Replace the `1`-bounded `rᵢ` by
   *unimodular multiplicative* covers `uᵢ` with a larger correlation.  The cover lifts `rᵢ` at
   every prime `≤ Y`.
2. **Transfer non-pretentiousness** (`ElliottPretentiousTransfer.mrtNonpretentious_transfer`).
   Deterministic, and it costs `2·Σ_X(g₁)`; the Case-B hypothesis bounds `Σ_L`, and
   `ElliottMertensIterate.reciprocalPrimeInterval_iter` upgrades that to `Σ_X` using the
   hypothesis `X ≤ L^(2^k)` supplied by the truncation.
3. **Expand twice** (`ElliottStageCost.norm_le_cost_first` then `norm_le_cost_second`).  Each
   expansion writes a unimodular multiplicative `u` as `u = uᵇ ⋆ cmExt u` with `uᵇ` supported on
   squarefull numbers, truncates the divisor sum at a `D` chosen **before** `u`
   (`ElliottRankin.exists_squarefull_tail_bound`), and splits each residue class into an
   arithmetic progression.  The two truncation points `D₁, D₂` are chosen **in order**: `D₂` may
   depend on `D₁`, which is what breaks the apparent circularity (the inner cost carries a factor
   `D₁e²` and a coefficient `a₂D₁ + |b₂|` from the substituted data).
4. **Land on the rung** (`ElliottThresholdFamily.memberThreshold_spec`).  The doubly substituted
   pair has determinant *exactly* `a₁b₂ − a₂b₁ ≠ 0` (`det_final`), so `AffineCMLogElliott` applies
   to each of the finitely many members, at the single threshold `familyThreshold`.

## The budget

Writing `P₁ = D₁e²`, `P₂ = D₂e²`, the assembled bound is

`2(|b₁|+|b₂|) + (ε''P₁P₂ + C₂εt₂P₁ + C₁εt₁)·log W + [4D₂P₂P₁ + C₂κ₂εt₂P₁ + 4D₁P₁ + C₁κ₁εt₁]`,

so each of the three `log W` coefficients is made `≤ ε/8` by choosing `εt₁, εt₂, ε''` in that
order, and the bracketed absolute constant is `≤ (ε/2) log W` by taking `W` large.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottCaseB

open Erdos67b NormalNumbers.ElliottSquarefullConv NormalNumbers.ElliottRestricted
open NormalNumbers.ElliottReindex NormalNumbers.ElliottScaleWindow
open NormalNumbers.ElliottStageCost NormalNumbers.ElliottThresholdFamily
open NormalNumbers.ElliottEulerBound NormalNumbers.ElliottCaseA
open NormalNumbers.ElliottMertensIterate NormalNumbers.ElliottScaleDescent
open NormalNumbers.ElliottLadder

noncomputable section

/-! ## Arithmetic of the progression scale -/

theorem progScale_le (X n₀ d : ℕ) : progScale X n₀ d ≤ X :=
  le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)

/-- A lower bound for the progression scale: `S ≤ (X−n₀)/d` as soon as `d(S+1) ≤ X` and `n₀ < d`. -/
theorem le_progScale {X n₀ d S : ℕ} (hd : 0 < d) (hn : n₀ < d) (h : d * (S + 1) ≤ X) :
    S ≤ progScale X n₀ d := by
  rw [progScale, Nat.le_div_iff_mul_le hd]
  have h1 : d * S + d ≤ X := by
    have : d * (S + 1) = d * S + d := by ring
    omega
  have h2 : S * d = d * S := by ring
  omega

/-- The matching upper bound: `X ≤ d·((X−n₀)/d + 2)` when `n₀ < d`. -/
theorem le_mul_progScale_add {X n₀ d : ℕ} (hd : 0 < d) (hn : n₀ < d) :
    X ≤ d * (progScale X n₀ d + 2) := by
  have h1 : X - n₀ < d * ((X - n₀) / d + 1) :=
    NormalNumbers.ElliottCaseAThin.lt_mul_div_add_one hd
  calc X ≤ (X - n₀) + d := by omega
    _ ≤ d * ((X - n₀) / d + 1) + d := by omega
    _ = d * ((X - n₀) / d + 2) := by ring
    _ = d * (progScale X n₀ d + 2) := by rw [progScale]

/-! ## The Case-B sum is the Euler defect -/

/-- The sum appearing in `mrtNonpretentious_transfer` is literally the Euler defect of Case A. -/
theorem sum_primesUpTo_eq_primeDefect (g : ℤ → ℂ) (Z : ℕ) :
    ∑ p ∈ primesUpTo Z, (1 - ‖restrictToNat g p‖) / (p : ℝ)
      = primeDefect (normDivArith g) Z := by
  rw [primeDefect]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpp : p.Prime := by
    have : p ≤ Z ∧ Nat.Prime p := by simpa [Nat.primesLE, Nat.mem_primesBelow] using hp
    exact this.2
  have hp0 : 0 < p := hpp.pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  rw [normDivArith_apply g hp0]
  simp only [restrictToNat]
  field_simp

/-- The affine form is bounded above by `aX + |b|` on the window. -/
theorem integerAffine_le_of_mem {a : ℕ} (b : ℤ) {X W Y : ℕ} (hY : a * X + b.natAbs ≤ Y)
    {n : ℕ} (hn : n ∈ elliottLogWindow X W) : integerAffine a b n ≤ (Y : ℤ) := by
  obtain ⟨-, hnX, -⟩ := mem_elliottLogWindow.mp hn
  have hY' : ((a * X + b.natAbs : ℕ) : ℤ) ≤ (Y : ℤ) := by exact_mod_cast hY
  have h1 : (a : ℤ) * n ≤ (a : ℤ) * X := by
    have : (n : ℤ) ≤ (X : ℤ) := by exact_mod_cast hnX
    have ha : (0 : ℤ) ≤ (a : ℤ) := by positivity
    nlinarith
  have hbn : (b.natAbs : ℤ) = |b| := (Int.abs_eq_natAbs b).symm
  have hb : b ≤ |b| := le_abs_self b
  rw [integerAffine]
  push_cast at hY' ⊢
  linarith

/-! ## The ε-budget, isolated as pure real arithmetic -/

/-- The assembled bound, with the three `log W` coefficients budgeted at `ε/8` each and the
absolute constant at `(ε/2) log W`. -/
theorem budget_assemble {ε LW B P₁ P₂ C₁ C₂ κ₁ κ₂ e0 e1 e2 D₁ D₂ : ℝ}
    (hLW : 0 ≤ LW) (hεnn : 0 ≤ ε)
    (h1 : e0 * P₁ * P₂ ≤ ε / 8)
    (h2 : C₂ * e2 * P₁ ≤ ε / 8)
    (h3 : C₁ * e1 ≤ ε / 8)
    (h4 : 4 * P₂ * P₁ * D₂ + C₂ * κ₂ * e2 * P₁ + 4 * D₁ * P₁ + C₁ * κ₁ * e1 + B
      ≤ ε / 2 * LW) :
    ((e0 * LW + 4 * D₂) * P₂ + C₂ * ((LW + κ₂) * e2) + 4 * D₁) * P₁
        + C₁ * ((LW + κ₁) * e1) + B ≤ ε * LW := by
  have p1 := mul_le_mul_of_nonneg_right h1 hLW
  have p2 := mul_le_mul_of_nonneg_right h2 hLW
  have p3 := mul_le_mul_of_nonneg_right h3 hLW
  nlinarith [p1, p2, p3, h4, mul_nonneg hεnn hLW]

/-! ## Norm bounds for the extensions -/

theorem norm_posExt_le_one {u : ℕ → ℂ} (hu : ∀ n : ℕ, ‖u n‖ = 1) (z : ℤ) :
    ‖positiveIntExtension u z‖ ≤ 1 := by
  rw [positiveIntExtension]
  split_ifs with hz
  · rw [hu]
  · simp

theorem norm_posExt_cmExt_le_one {u : ℕ → ℂ} (hu : ∀ n : ℕ, ‖u n‖ = 1) (z : ℤ) :
    ‖positiveIntExtension (fun kk => cmExt u kk) z‖ ≤ 1 := by
  rw [positiveIntExtension]
  split_ifs with hz
  · rcases Nat.eq_zero_or_pos z.toNat with hz0 | hz0
    · simp [hz0]
    · rw [norm_cmExt (fun p _ => hu p) (by omega)]
  · simp

/-! ## Case B -/

set_option maxHeartbeats 1600000 in
/-- **Case B, all windows.**  If the Euler defect of `g₁` at the thin scale is at most `D₀`, and
the scale gap `X ≤ L^(2^k)` is controlled (which the truncation of `ElliottLeafTwo` provides), then
the correlation is `≤ ε log W` — given `AffineCMLogElliott`. -/
theorem exists_caseB_threshold (h : AffineCMLogElliott)
    {a₁ a₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) {b₁ b₂ : ℤ}
    (hdet : (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0) {ε : ℝ} (hε : 0 < ε) (D₀ : ℝ) (k : ℕ) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
        X ≤ (thinScale a₁ b₁ X W) ^ (2 ^ k) →
        ∀ g₁ g₂ : ℤ → ℂ,
          IsMultiplicativeOnPositiveInt g₁ →
          IsMultiplicativeOnPositiveInt g₂ →
          (∀ n : ℤ, ‖g₁ n‖ ≤ 1) →
          (∀ n : ℤ, ‖g₂ n‖ ≤ 1) →
          (∀ q : ℕ, 0 < q → q ≤ A →
            ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
              |t| ≤ (A : ℝ) * X →
                (A : ℝ) ≤ pretentiousDistSqToTwist (restrictToNat g₁) χ t X) →
          primeDefect (normDivArith g₁) (thinScale a₁ b₁ X W) ≤ D₀ →
          ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖ ≤ ε * Real.log (W : ℝ) := by
  classical
  have hexp2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  -- ### the constants, in dependency order
  set εt₁ : ℝ := ε / (8 * (((a₁ + b₁.natAbs : ℕ) : ℝ) + 1)) with hεt₁def
  have hεt₁pos : 0 < εt₁ := by rw [hεt₁def]; positivity
  obtain ⟨D₁, hD₁one, htail₁⟩ := NormalNumbers.ElliottRankin.exists_squarefull_tail_bound hεt₁pos
  set εt₂ : ℝ := ε / (8 * (((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ) + 1)
      * ((D₁ : ℝ) * Real.exp 2 + 1)) with hεt₂def
  have hεt₂pos : 0 < εt₂ := by rw [hεt₂def]; positivity
  obtain ⟨D₂, hD₂one, htail₂⟩ := NormalNumbers.ElliottRankin.exists_squarefull_tail_bound hεt₂pos
  set ε'' : ℝ := ε / (8 * ((D₁ : ℝ) * Real.exp 2 + 1) * ((D₂ : ℝ) * Real.exp 2 + 1)) with hε''def
  have hε''pos : 0 < ε'' := by rw [hε''def]; positivity
  set T : ℕ := familyThreshold h a₁ a₂ b₁ b₂ hε''pos (max D₁ D₂) with hTdef
  have hT2 : 2 ≤ T := two_le_familyThreshold h a₁ a₂ b₁ b₂ hε''pos (max D₁ D₂)
  set S : ℕ := T + 2 * (D₁ * D₂) + 4 with hSdef
  set Q : ℕ := (D₁ + 1) * ((D₂ + 1) * (S + 1) + 1) with hQdef
  set D₀' : ℝ := D₀ + (k : ℝ) * (Real.log 2 + 2 * Erdos67b.PrimeEstimates.mertensBound)
    with hD₀'def
  set A₁' : ℕ := T + ⌈mrtDescentCost⌉₊ + 1 with hA₁'def
  set Cst : ℝ :=
      4 * ((D₂ : ℝ) * Real.exp 2) * ((D₁ : ℝ) * Real.exp 2) * (D₂ : ℝ)
      + ((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ)
          * logRatioConst (a₂ * D₁) ((a₂ * D₁ + b₂.natAbs : ℕ) : ℤ) * εt₂
          * ((D₁ : ℝ) * Real.exp 2)
      + 4 * (D₁ : ℝ) * ((D₁ : ℝ) * Real.exp 2)
      + ((a₁ + b₁.natAbs : ℕ) : ℝ) * logRatioConst a₁ b₁ * εt₁
      + 2 * ((b₁.natAbs + b₂.natAbs : ℕ) : ℝ) with hCstdef
  refine ⟨max (max 2 (3 * (A₁' + ⌈2 * D₀'⌉₊ + 1)))
    (max Q (⌈Real.exp (2 * Cst / ε)⌉₊ + 1)), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro A X W hA₀A hAW hWX hpow g₁ g₂ hm₁ hm₂ h₁ h₂ hpret hdefect
  -- ### size bookkeeping
  have hA2 : 2 ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA₀A
  have hAtr : 3 * (A₁' + ⌈2 * D₀'⌉₊ + 1) ≤ A :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA₀A
  have hAQ : Q ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA₀A
  have hAexp : ⌈Real.exp (2 * Cst / ε)⌉₊ + 1 ≤ A :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA₀A
  have hW2 : 2 ≤ W := le_trans hA2 hAW
  have hX2 : 2 ≤ X := le_trans hW2 hWX
  have hQX : Q ≤ X := le_trans (le_trans hAQ hAW) hWX
  have hlogWpos : 0 < Real.log (W : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  have hlogWnn : (0 : ℝ) ≤ Real.log (W : ℝ) := hlogWpos.le
  -- ### the Case-B sum at the full scale `X`
  have hmertnn : (0 : ℝ) ≤ Real.log 2 + 2 * Erdos67b.PrimeEstimates.mertensBound := by
    have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h2 := Erdos67b.PrimeEstimates.mertensBound_nonneg
    linarith
  have hSig : ∑ p ∈ primesUpTo X, (1 - ‖restrictToNat g₁ p‖) / (p : ℝ) ≤ D₀' := by
    rw [sum_primesUpTo_eq_primeDefect]
    have hknn : (0 : ℝ) ≤ (k : ℝ) * (Real.log 2 + 2 * Erdos67b.PrimeEstimates.mertensBound) := by
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      exact mul_nonneg this hmertnn
    rcases le_or_gt (thinScale a₁ b₁ X W) X with hLX | hXL
    · have hL2 : 2 ≤ thinScale a₁ b₁ X W := by
        by_contra hc
        push_neg at hc
        have hL1 : thinScale a₁ b₁ X W = 1 := by
          have := one_le_thinScale a₁ b₁ X W
          omega
        rw [hL1, one_pow] at hpow
        omega
      have hstep1 := primeDefect_le_add (g := g₁) h₁ hLX
      have hstep2 := reciprocalPrimeInterval_iter (k := k) hL2 hLX hpow
      rw [hD₀'def]
      linarith
    · have hstep := NormalNumbers.ElliottHall.primeDefect_mono h₁ (le_of_lt hXL)
      rw [hD₀'def]
      linarith
  -- ### the zero extension
  have hr₁b : ∀ n : ℕ, ‖restrictToNat g₁ n‖ ≤ 1 := fun n => h₁ (n : ℤ)
  have hr₂b : ∀ n : ℕ, ‖restrictToNat g₂ n‖ ≤ 1 := fun n => h₂ (n : ℤ)
  have hr₁one : restrictToNat g₁ 1 = 1 := by
    have := hm₁.1
    simpa [restrictToNat] using this
  have hr₂one : restrictToNat g₂ 1 = 1 := by
    have := hm₂.1
    simpa [restrictToNat] using this
  have hstep0 : ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖
      ≤ ‖elliottLogCorrelation (positiveIntExtension (restrictToNat g₁))
          (positiveIntExtension (restrictToNat g₂)) a₁ a₂ b₁ b₂ X W‖
        + 2 * ((b₁.natAbs + b₂.natAbs : ℕ) : ℝ) := by
    have hsub := NormalNumbers.ElliottZeroExt.norm_sub_posExt_le h₁ h₂ ha₁ ha₂ b₁ b₂ X W
    have hsplit : elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W
        = (elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W
            - elliottLogCorrelation (positiveIntExtension (restrictToNat g₁))
              (positiveIntExtension (restrictToNat g₂)) a₁ a₂ b₁ b₂ X W)
          + elliottLogCorrelation (positiveIntExtension (restrictToNat g₁))
              (positiveIntExtension (restrictToNat g₂)) a₁ a₂ b₁ b₂ X W := by ring
    calc ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖
        = ‖(elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W
              - elliottLogCorrelation (positiveIntExtension (restrictToNat g₁))
                (positiveIntExtension (restrictToNat g₂)) a₁ a₂ b₁ b₂ X W)
            + elliottLogCorrelation (positiveIntExtension (restrictToNat g₁))
                (positiveIntExtension (restrictToNat g₂)) a₁ a₂ b₁ b₂ X W‖ := by rw [← hsplit]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by linarith
  -- ### the unimodular cover
  obtain ⟨u₁, u₂, hu₁one, hu₁mul, hu₁norm, hu₂one, hu₂mul, hu₂norm, hlift₁, hlift₂, hcover⟩ :=
    NormalNumbers.ElliottRandomize.exists_cover_pair_ge (restrictToNat g₁) (restrictToNat g₂)
      (a₁ * X + b₁.natAbs + (a₂ * X + b₂.natAbs))
      (NormalNumbers.ElliottZeroExt.coprime_mul_restrictToNat hm₁) hr₁one hr₁b
      (NormalNumbers.ElliottZeroExt.coprime_mul_restrictToNat hm₂) hr₂one hr₂b
      (a₁ := a₁) (a₂ := a₂) (b₁ := b₁) (b₂ := b₂) (X := X) (W := W)
      (fun n hn => integerAffine_le_of_mem b₁ (Nat.le_add_right _ _) hn)
      (fun n hn => integerAffine_le_of_mem b₂ (Nat.le_add_left _ _) hn)
  have hu₁normp : ∀ p : ℕ, p.Prime → ‖u₁ p‖ = 1 := fun p _ => hu₁norm p
  have hu₂normp : ∀ p : ℕ, p.Prime → ‖u₂ p‖ = 1 := fun p _ => hu₂norm p
  -- ### non-pretentiousness passes to the cover
  have hXY : X ≤ a₁ * X + b₁.natAbs + (a₂ * X + b₂.natAbs) := by
    have : X ≤ a₁ * X := Nat.le_mul_of_pos_left _ ha₁
    omega
  have hMRTu₁ : MRTNonpretentious u₁ A₁' X := by
    refine NormalNumbers.ElliottPretentiousTransfer.mrtNonpretentious_transfer
      (g := restrictToNat g₁) (u := u₁) (D₀ := D₀') hr₁b hu₁norm
      (fun p hp hpX => hlift₁ p hp (le_trans hpX hXY)) hSig hpret ?_ ?_
    · omega
    · have h1 : (2 : ℝ) * D₀' ≤ (⌈2 * D₀'⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((3 * (A₁' + ⌈2 * D₀'⌉₊ + 1) : ℕ) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hAtr
      push_cast at h2
      linarith
  -- ### the doubly reduced correlations
  have hgcm₁ : ∀ z : ℤ, ‖positiveIntExtension (fun kk => cmExt u₁ kk) z‖ ≤ 1 :=
    norm_posExt_cmExt_le_one hu₁norm
  have hgu₂ : ∀ z : ℤ, ‖positiveIntExtension u₂ z‖ ≤ 1 := norm_posExt_le_one hu₂norm
  have hkey : ∀ d₁ ∈ Finset.Icc 1 D₁, ∀ n₀₁ < d₁, (d₁ : ℤ) ∣ (a₁ : ℤ) * (n₀₁ : ℤ) + b₁ →
      ‖elliottLogCorrelation (positiveIntExtension (fun kk => cmExt u₁ kk))
          (positiveIntExtension u₂)
          a₁ (a₂ * d₁) (newShift a₁ b₁ d₁ n₀₁) ((a₂ : ℤ) * n₀₁ + b₂)
          (progScale X n₀₁ d₁) (min W (progScale X n₀₁ d₁))‖
        ≤ (ε'' * Real.log (W : ℝ) + 4 * (D₂ : ℝ)) * ((D₂ : ℝ) * Real.exp 2)
          + ((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ)
              * ((Real.log (W : ℝ)
                    + logRatioConst (a₂ * D₁) ((a₂ * D₁ + b₂.natAbs : ℕ) : ℤ)) * εt₂) := by
    intro d₁ hd₁mem n₀₁ hn₀₁ hdvd₁
    obtain ⟨hd₁one, hd₁D₁⟩ := Finset.mem_Icc.mp hd₁mem
    have hd₁pos : 0 < d₁ := hd₁one
    have ha₂d₁ : 0 < a₂ * d₁ := Nat.mul_pos ha₂ hd₁pos
    have hX₁big : (D₂ + 1) * (S + 1) ≤ progScale X n₀₁ d₁ := by
      refine le_progScale hd₁pos hn₀₁ ?_
      calc d₁ * ((D₂ + 1) * (S + 1) + 1)
          ≤ (D₁ + 1) * ((D₂ + 1) * (S + 1) + 1) := Nat.mul_le_mul (by omega) (le_refl _)
        _ = Q := by rw [hQdef]
        _ ≤ X := hQX
    have hSle : S ≤ (D₂ + 1) * (S + 1) := by
      calc S ≤ S + 1 := by omega
        _ = 1 * (S + 1) := by ring
        _ ≤ (D₂ + 1) * (S + 1) := Nat.mul_le_mul (by omega) (le_refl _)
    have hSX₁ : S ≤ progScale X n₀₁ d₁ := le_trans hSle hX₁big
    have hD₂S : D₂ ≤ S := by
      have h1 : D₂ ≤ D₁ * D₂ := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hTS : T ≤ S := by omega
    have h4S : 4 ≤ S := by omega
    set X₁ : ℕ := progScale X n₀₁ d₁ with hX₁def
    set W₁ : ℕ := min W X₁ with hW₁def
    have hX₁X : X₁ ≤ X := progScale_le _ _ _
    have hW₁2 : 2 ≤ W₁ := le_min (by omega) (by omega)
    have hW₁X₁ : W₁ ≤ X₁ := min_le_right _ _
    have hW₁W : W₁ ≤ W := min_le_left _ _
    have hD₂Y : D₂ ≤ a₂ * d₁ * X₁ + ((a₂ : ℤ) * n₀₁ + b₂).natAbs := by
      have h1 : D₂ ≤ X₁ := by omega
      have h2 : X₁ ≤ a₂ * d₁ * X₁ := Nat.le_mul_of_pos_left _ ha₂d₁
      omega
    have hM₂nn : (0 : ℝ) ≤ ε'' * Real.log (W : ℝ) := mul_nonneg hε''pos.le hlogWnn
    refine le_trans (norm_le_cost_second (U := u₂) hu₂one hu₂mul (fun n _ => hu₂norm n)
      hgcm₁ a₁ ha₂d₁ (newShift a₁ b₁ d₁ n₀₁) ((a₂ : ℤ) * n₀₁ + b₂)
      (X := X₁) (W := W₁) (D := D₂) hW₁2 hW₁X₁ hD₂one hD₂Y hεt₂pos.le hM₂nn
      (htail₂ u₂ hu₂one hu₂mul (fun n hn => hu₂norm n) _) ?_) ?_
    · -- the innermost correlations, via the threshold family
      intro d₂ hd₂mem n₀₂ hn₀₂ hdvd₂
      obtain ⟨hd₂one, hd₂D₂⟩ := Finset.mem_Icc.mp hd₂mem
      have hd₂pos : 0 < d₂ := hd₂one
      set X₂ : ℕ := progScale X₁ n₀₂ d₂ with hX₂def
      set W₂ : ℕ := min W₁ X₂ with hW₂def
      have hSX₂ : S ≤ X₂ := by
        refine le_progScale hd₂pos hn₀₂ ?_
        calc d₂ * (S + 1) ≤ (D₂ + 1) * (S + 1) := Nat.mul_le_mul (by omega) (le_refl _)
          _ ≤ X₁ := hX₁big
      have hX₂X₁ : X₂ ≤ X₁ := progScale_le _ _ _
      have hW₂X₂ : W₂ ≤ X₂ := min_le_right _ _
      have hW₂W : W₂ ≤ W := le_trans (min_le_left _ _) hW₁W
      have hA₁'A : A₁' ≤ A := by omega
      have hTW₂ : T ≤ W₂ := by
        refine le_min (le_min ?_ ?_) ?_
        · omega
        · omega
        · omega
      -- the scale gap `X ≤ X₂²`
      have hXX₂ : X ≤ X₂ * X₂ := by
        have hXX₁ : X ≤ d₁ * (X₁ + 2) := le_mul_progScale_add hd₁pos hn₀₁
        have hX₁X₂ : X₁ ≤ d₂ * (X₂ + 2) := le_mul_progScale_add hd₂pos hn₀₂
        have hstep : X ≤ d₁ * (d₂ * (X₂ + 2) + 2) :=
          le_trans hXX₁ (Nat.mul_le_mul (le_refl _) (by omega))
        have hexp : d₁ * (d₂ * (X₂ + 2) + 2) = d₁ * d₂ * X₂ + (2 * (d₁ * d₂) + 2 * d₁) := by ring
        have hdd : d₁ * d₂ ≤ D₁ * D₂ := Nat.mul_le_mul hd₁D₁ hd₂D₂
        have h5 : d₁ * d₂ * X₂ ≤ D₁ * D₂ * X₂ := Nat.mul_le_mul hdd (le_refl _)
        have hd₁DD : d₁ ≤ D₁ * D₂ := le_trans hd₁D₁ (Nat.le_mul_of_pos_right _ (by omega))
        have h7 : 4 * (D₁ * D₂) ≤ D₁ * D₂ * X₂ := by
          calc 4 * (D₁ * D₂) = D₁ * D₂ * 4 := by ring
            _ ≤ D₁ * D₂ * X₂ := Nat.mul_le_mul (le_refl _) (by omega)
        have h8 : 2 * (D₁ * D₂) ≤ X₂ := by omega
        calc X ≤ D₁ * D₂ * X₂ + D₁ * D₂ * X₂ := by omega
          _ = 2 * (D₁ * D₂) * X₂ := by ring
          _ ≤ X₂ * X₂ := Nat.mul_le_mul h8 (le_refl _)
      have hMRT : MRTNonpretentious (fun kk => cmExt u₁ kk) T X₂ := by
        refine mrtNonpretentious_descend_iter (k := 1)
          (fun p hp => le_of_eq (norm_cmExt_eq_one hu₁normp hp.pos))
          (mrtNonpretentious_cmExt hMRTu₁) (by omega) (le_trans hX₂X₁ hX₁X) ?_ (by omega) ?_
        · rw [pow_one, pow_two]; exact hXX₂
        · have h1 : mrtDescentCost ≤ (⌈mrtDescentCost⌉₊ : ℝ) := Nat.le_ceil _
          have h2 : ((A₁' : ℕ) : ℝ) = (T : ℝ) + ((⌈mrtDescentCost⌉₊ : ℕ) : ℝ) + 1 := by
            rw [hA₁'def]; push_cast; ring
          rw [h2]
          push_cast
          linarith
      have hq : ((d₁, n₀₁, d₂, n₀₂) : ℕ × ℕ × ℕ × ℕ) ∈ familyIndex (max D₁ D₂) := by
        refine mem_familyIndex ?_ ?_ ?_ ?_
        · exact le_trans hd₁D₁ (le_max_left _ _)
        · exact le_trans (by omega : n₀₁ ≤ D₁) (le_max_left _ _)
        · exact le_trans hd₂D₂ (le_max_right _ _)
        · exact le_trans (by omega : n₀₂ ≤ D₂) (le_max_right _ _)
      have hTthr := memberThreshold_le_familyThreshold h a₁ a₂ b₁ b₂ hε''pos hq
      rw [← hTdef] at hTthr
      have hdetq : ((finalDil₁ a₁ d₂ : ℕ) : ℤ) * finalShift₂ a₂ b₂ d₁ n₀₁ d₂ n₀₂
          - ((finalDil₂ a₂ d₁ : ℕ) : ℤ) * finalShift₁ a₁ b₁ d₁ n₀₁ n₀₂ ≠ 0 := by
        rw [det_final hdvd₁ hdvd₂]
        exact hdet
      have hspec := memberThreshold_spec h a₁ a₂ b₁ b₂ hε''pos (d₁, n₀₁, d₂, n₀₂)
        (Nat.mul_pos ha₁ hd₂pos) (Nat.mul_pos ha₂ hd₁pos) hdetq T X₂ W₂ hTthr hTW₂ hW₂X₂
        (fun kk => cmExt u₁ kk) (fun kk => cmExt u₂ kk) (isCM_cmExt u₁) (isCM_cmExt u₂)
        (fun n hn => norm_cmExt_eq_one hu₁normp hn) (fun n hn => norm_cmExt_eq_one hu₂normp hn)
        hMRT
      simp only [finalDil₁, finalDil₂, finalShift₁, finalShift₂] at hspec
      refine le_trans hspec ?_
      refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) hε''pos.le
      · have : (0 : ℕ) < W₂ := by omega
        exact_mod_cast this
      · exact_mod_cast hW₂W
    · -- the inner cost is at most the uniform inner cost
      have hc : ((a₂ * d₁ + ((a₂ : ℤ) * n₀₁ + b₂).natAbs : ℕ) : ℝ)
          ≤ ((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ) := by
        have hnat : a₂ * d₁ + ((a₂ : ℤ) * n₀₁ + b₂).natAbs ≤ a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) := by
          have h1 : a₂ * d₁ ≤ a₂ * D₁ := Nat.mul_le_mul (le_refl _) hd₁D₁
          have h2 : ((a₂ : ℤ) * n₀₁ + b₂).natAbs ≤ a₂ * n₀₁ + b₂.natAbs := by
            refine le_trans (Int.natAbs_add_le _ _) ?_
            simp [Int.natAbs_mul]
          have h3 : a₂ * n₀₁ ≤ a₂ * D₁ := Nat.mul_le_mul (le_refl _) (by omega)
          omega
        exact_mod_cast hnat
      have hκ : logRatioConst (a₂ * d₁) ((a₂ : ℤ) * n₀₁ + b₂)
          ≤ logRatioConst (a₂ * D₁) ((a₂ * D₁ + b₂.natAbs : ℕ) : ℤ) := by
        refine logRatioConst_mono (Nat.mul_le_mul (le_refl _) hd₁D₁) ?_
        have h2 : ((a₂ : ℤ) * n₀₁ + b₂).natAbs ≤ a₂ * n₀₁ + b₂.natAbs := by
          refine le_trans (Int.natAbs_add_le _ _) ?_
          simp [Int.natAbs_mul]
        have h3 : a₂ * n₀₁ ≤ a₂ * D₁ := Nat.mul_le_mul (le_refl _) (by omega)
        have h4 : (((a₂ * D₁ + b₂.natAbs : ℕ) : ℤ)).natAbs = a₂ * D₁ + b₂.natAbs := by
          simp only [Int.natAbs_natCast]
        omega
      have hlogW₁ : Real.log (W₁ : ℝ) ≤ Real.log (W : ℝ) := by
        refine Real.log_le_log ?_ ?_
        · have : (0 : ℕ) < W₁ := by omega
          exact_mod_cast this
        · exact_mod_cast hW₁W
      have hκnn : (0 : ℝ) ≤ logRatioConst (a₂ * D₁) ((a₂ * D₁ + b₂.natAbs : ℕ) : ℤ) :=
        logRatioConst_nonneg _ _
      have hκ'nn : (0 : ℝ) ≤ logRatioConst (a₂ * d₁) ((a₂ : ℤ) * n₀₁ + b₂) :=
        logRatioConst_nonneg _ _
      have hinner : (Real.log (W₁ : ℝ) + logRatioConst (a₂ * d₁) ((a₂ : ℤ) * n₀₁ + b₂)) * εt₂
          ≤ (Real.log (W : ℝ)
              + logRatioConst (a₂ * D₁) ((a₂ * D₁ + b₂.natAbs : ℕ) : ℤ)) * εt₂ :=
        mul_le_mul_of_nonneg_right (by linarith) hεt₂pos.le
      have hinnernn : (0 : ℝ) ≤ (Real.log (W₁ : ℝ)
          + logRatioConst (a₂ * d₁) ((a₂ : ℤ) * n₀₁ + b₂)) * εt₂ := by
        have hlogW₁nn : (0 : ℝ) ≤ Real.log (W₁ : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ W₁))
        have := hεt₂pos.le
        nlinarith
      have hCnn : (0 : ℝ) ≤ ((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ) := by positivity
      have := mul_le_mul hc hinner hinnernn hCnn
      linarith
  -- ### the outer expansion and the budget
  have hD₁X : D₁ ≤ a₁ * X + b₁.natAbs := by
    have h1 : D₁ ≤ Q := by
      have : D₁ + 1 ≤ Q := by
        calc D₁ + 1 = (D₁ + 1) * 1 := by ring
          _ ≤ (D₁ + 1) * ((D₂ + 1) * (S + 1) + 1) := Nat.mul_le_mul (le_refl _) (by omega)
          _ = Q := by rw [hQdef]
      omega
    have h2 : X ≤ a₁ * X := Nat.le_mul_of_pos_left _ ha₁
    omega
  have hM₁nn : (0 : ℝ) ≤
      (ε'' * Real.log (W : ℝ) + 4 * (D₂ : ℝ)) * ((D₂ : ℝ) * Real.exp 2)
        + ((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ)
            * ((Real.log (W : ℝ)
                  + logRatioConst (a₂ * D₁) ((a₂ * D₁ + b₂.natAbs : ℕ) : ℤ)) * εt₂) := by
    have e1 : (0 : ℝ) ≤ ε'' * Real.log (W : ℝ) := mul_nonneg hε''pos.le hlogWnn
    have e2 : (0 : ℝ) ≤ (D₂ : ℝ) * Real.exp 2 := by positivity
    have e3 : (0 : ℝ) ≤ ((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ) := by positivity
    have e4 : (0 : ℝ) ≤ (Real.log (W : ℝ)
        + logRatioConst (a₂ * D₁) ((a₂ * D₁ + b₂.natAbs : ℕ) : ℤ)) * εt₂ := by
      have := logRatioConst_nonneg (a₂ * D₁) (((a₂ * D₁ + b₂.natAbs : ℕ) : ℤ))
      have := hεt₂pos.le
      nlinarith
    have e5 : (0 : ℝ) ≤ ε'' * Real.log (W : ℝ) + 4 * (D₂ : ℝ) := by
      have : (0 : ℝ) ≤ (D₂ : ℝ) := by positivity
      linarith
    exact add_nonneg (mul_nonneg e5 e2) (mul_nonneg e3 e4)
  have houter := norm_le_cost_first (U := u₁) hu₁one hu₁mul (fun n _ => hu₁norm n)
    hgu₂ ha₁ a₂ b₁ b₂ (X := X) (W := W) (D := D₁) hW2 hWX hD₁one hD₁X hεt₁pos.le hM₁nn
    (htail₁ u₁ hu₁one hu₁mul (fun n hn => hu₁norm n) _) hkey
  -- the three `log W` budgets
  have hb1 : ε'' * ((D₁ : ℝ) * Real.exp 2) * ((D₂ : ℝ) * Real.exp 2) ≤ ε / 8 := by
    have hP₁ : (0 : ℝ) ≤ (D₁ : ℝ) * Real.exp 2 := by positivity
    have hP₂ : (0 : ℝ) ≤ (D₂ : ℝ) * Real.exp 2 := by positivity
    have hne1 : ((D₁ : ℝ) * Real.exp 2 + 1) ≠ 0 := by positivity
    have hne2 : ((D₂ : ℝ) * Real.exp 2 + 1) ≠ 0 := by positivity
    have hprod : ((D₁ : ℝ) * Real.exp 2) * ((D₂ : ℝ) * Real.exp 2)
        ≤ ((D₁ : ℝ) * Real.exp 2 + 1) * ((D₂ : ℝ) * Real.exp 2 + 1) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod hε''pos.le
    have heq : ε'' * (((D₁ : ℝ) * Real.exp 2 + 1) * ((D₂ : ℝ) * Real.exp 2 + 1)) = ε / 8 := by
      rw [hε''def]; field_simp
    linarith
  have hb2 : ((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ) * εt₂ * ((D₁ : ℝ) * Real.exp 2)
      ≤ ε / 8 := by
    have hP₁ : (0 : ℝ) ≤ (D₁ : ℝ) * Real.exp 2 := by positivity
    have hC : (0 : ℝ) ≤ ((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ) := by positivity
    have hne1 : (((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    have hne2 : ((D₁ : ℝ) * Real.exp 2 + 1) ≠ 0 := by positivity
    have hprod : ((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ) * ((D₁ : ℝ) * Real.exp 2)
        ≤ (((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ) + 1) * ((D₁ : ℝ) * Real.exp 2 + 1) := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod hεt₂pos.le
    have heq : εt₂ * ((((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ) + 1)
        * ((D₁ : ℝ) * Real.exp 2 + 1)) = ε / 8 := by
      rw [hεt₂def]; field_simp
    linarith
  have hb3 : ((a₁ + b₁.natAbs : ℕ) : ℝ) * εt₁ ≤ ε / 8 := by
    have hC : (0 : ℝ) ≤ ((a₁ + b₁.natAbs : ℕ) : ℝ) := by positivity
    have hne1 : (((a₁ + b₁.natAbs : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    have hprod : ((a₁ + b₁.natAbs : ℕ) : ℝ) ≤ (((a₁ + b₁.natAbs : ℕ) : ℝ) + 1) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hprod hεt₁pos.le
    have heq : εt₁ * (((a₁ + b₁.natAbs : ℕ) : ℝ) + 1) = ε / 8 := by
      rw [hεt₁def]; field_simp
    linarith
  -- the absolute constant
  have hb4 : 4 * ((D₂ : ℝ) * Real.exp 2) * ((D₁ : ℝ) * Real.exp 2) * (D₂ : ℝ)
      + ((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ)
          * logRatioConst (a₂ * D₁) ((a₂ * D₁ + b₂.natAbs : ℕ) : ℤ) * εt₂
          * ((D₁ : ℝ) * Real.exp 2)
      + 4 * (D₁ : ℝ) * ((D₁ : ℝ) * Real.exp 2)
      + ((a₁ + b₁.natAbs : ℕ) : ℝ) * logRatioConst a₁ b₁ * εt₁
      + 2 * ((b₁.natAbs + b₂.natAbs : ℕ) : ℝ) ≤ ε / 2 * Real.log (W : ℝ) := by
    rw [← hCstdef]
    have hexpW : Real.exp (2 * Cst / ε) ≤ (W : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast (by omega : ⌈Real.exp (2 * Cst / ε)⌉₊ ≤ W)
    have hlog := Real.log_le_log (Real.exp_pos _) hexpW
    rw [Real.log_exp] at hlog
    have hstep := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ ε / 2)
    rwa [show ε / 2 * (2 * Cst / ε) = Cst by field_simp] at hstep
  have hbud := budget_assemble (LW := Real.log (W : ℝ)) hlogWnn hε.le hb1 hb2 hb3 hb4
  calc ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖
      ≤ ‖elliottLogCorrelation (positiveIntExtension (restrictToNat g₁))
          (positiveIntExtension (restrictToNat g₂)) a₁ a₂ b₁ b₂ X W‖
        + 2 * ((b₁.natAbs + b₂.natAbs : ℕ) : ℝ) := hstep0
    _ ≤ ‖elliottLogCorrelation (positiveIntExtension u₁) (positiveIntExtension u₂)
          a₁ a₂ b₁ b₂ X W‖ + 2 * ((b₁.natAbs + b₂.natAbs : ℕ) : ℝ) := by linarith
    _ ≤ (((ε'' * Real.log (W : ℝ) + 4 * (D₂ : ℝ)) * ((D₂ : ℝ) * Real.exp 2)
            + ((a₂ * D₁ + (a₂ * D₁ + b₂.natAbs) : ℕ) : ℝ)
              * ((Real.log (W : ℝ)
                  + logRatioConst (a₂ * D₁) ((a₂ * D₁ + b₂.natAbs : ℕ) : ℤ)) * εt₂)
            + 4 * (D₁ : ℝ)) * ((D₁ : ℝ) * Real.exp 2)
          + ((a₁ + b₁.natAbs : ℕ) : ℝ)
              * ((Real.log (W : ℝ) + logRatioConst a₁ b₁) * εt₁))
        + 2 * ((b₁.natAbs + b₂.natAbs : ℕ) : ℝ) := by linarith
    _ ≤ ε * Real.log (W : ℝ) := hbud

end

end NormalNumbers.ElliottCaseB
