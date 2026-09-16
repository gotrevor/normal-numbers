/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4OmegaRemainder
import NormalNumbers.G4MediumPrimes
import NormalNumbers.G4FarTail

/-!
# `junkAvgΩ` — the one genuinely new §4D estimate for `Ω`

`Ω`'s retained tail carries one term the `ω`-route does not have: the **valuation junk**
`junk 1 P₀ (m) = ∑_{p} (v_p(m) − v_p(P₀))⁺` restricted to the excess above the frozen depth.
`G4WeightJunk.sum_junk_le` bounds its *sample sum* at a single shift `ρ`; this file pushes that
through a layer block.

The mechanism is the ℓ¹ row budget, applied in the `n`-averaged (not pointwise) form: the junk is
nonnegative, so

  `card⁻¹ ∑_n |blockSum bb G junk n a| ≤ ∑_i |c_i| · (card⁻¹ ∑_n junk(n+ρ_i)) ≤ B · rowL1 bb K`

whenever every shift obeys `card⁻¹ ∑_n junk(n+ρ_i) ≤ B`.  `sampleAvg_abs_blockSum_le_of_shift`
is that step for an arbitrary weight, and `junkAvgΩ_le` is the instance.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-! ### A layer block as a row-coefficient sum -/

/-- `blockSum bb G w n a = ∑_i c_i · w(n + ρ_i)` — the `w`-generic form of the identity
inside `blockSum_omegaOn_eq`. -/
lemma blockSum_eq_sum_rowCoeff (bb : ℕ) (G : GridParams) (w : ℕ → ℝ) (n : ℕ)
    (a : Fin G.K → Fin G.s) :
    blockSum bb G w n a = ∑ i : G.Idx, rowCoeff bb G a i * w (n + shiftAL G.B G.Q G.D₀ i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun jj _ => ?_
  unfold rowCoeff
  ring

/-- **The `n`-averaged ℓ¹ row budget.**  If every shift's sample average of `|w|` is at most `B`,
the sample average of the block is at most `B · rowL1`. -/
theorem sampleAvg_abs_blockSum_le_of_shift (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    {B : ℝ} (hB : 0 ≤ B) (w : ℕ → ℝ) (a : Fin G.K → Fin G.s)
    (hw : ∀ i : G.Idx, ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ *
      ∑ n ∈ apSample X G.P₀ G.b₀, |w (n + shiftAL G.B G.Q G.D₀ i)| ≤ B) :
    ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ *
        ∑ n ∈ apSample X G.P₀ G.b₀, |blockSum bb G w n a| ≤ B * rowL1 bb G.K := by
  classical
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  have hc : (0 : ℝ) ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ := by positivity
  have hstep : ∀ n ∈ apSample X G.P₀ G.b₀, |blockSum bb G w n a|
      ≤ ∑ i : G.Idx, |rowCoeff bb G a i| * |w (n + shiftAL G.B G.Q G.D₀ i)| := by
    intro n _
    rw [blockSum_eq_sum_rowCoeff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => abs_mul _ _
  calc ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ *
        ∑ n ∈ apSample X G.P₀ G.b₀, |blockSum bb G w n a|
      ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
          ∑ i : G.Idx, |rowCoeff bb G a i| * |w (n + shiftAL G.B G.Q G.D₀ i)| :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hc
    _ = ∑ i : G.Idx, |rowCoeff bb G a i| * (((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ *
          ∑ n ∈ apSample X G.P₀ G.b₀, |w (n + shiftAL G.B G.Q G.D₀ i)|) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        ring
    _ ≤ ∑ i : G.Idx, |rowCoeff bb G a i| * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)
    _ = (∑ i : G.Idx, |rowCoeff bb G a i|) * B := by rw [Finset.sum_mul]
    _ ≤ rowL1 bb G.K * B := mul_le_mul_of_nonneg_right (sum_abs_rowCoeff_le bb hbb G a) hB
    _ = B * rowL1 bb G.K := mul_comm _ _

/-! ### The junk at a single shift -/

/-- The closed bound of `sum_junk_le` at `c ≡ 1`, with the shift replaced by a uniform cap. -/
noncomputable def junkShiftBound (P₀ X ρmax : ℕ) : ℝ :=
  (X : ℝ) / P₀ * (∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) + 1)
    + (((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) : ℝ)

lemma junkShiftBound_nonneg (P₀ X ρmax : ℕ) : 0 ≤ junkShiftBound P₀ X ρmax := by
  unfold junkShiftBound
  have h1 : (0 : ℝ) ≤ ∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) := by
    refine Finset.sum_nonneg fun p hp => ?_
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  positivity

/-- The sample sum of the valuation junk at any shift `1 ≤ ρ ≤ ρmax`. -/
theorem sum_junk_one_le {X P₀ b₀ ρ ρmax : ℕ} (hP₀ : 0 < P₀) (hρ : 1 ≤ ρ) (hρm : ρ ≤ ρmax) :
    ∑ n ∈ apSample X P₀ b₀, junk (fun _ => (1 : ℕ)) P₀ (n + ρ) ≤ junkShiftBound P₀ X ρmax := by
  have h := sum_junk_le (fun _ => (1 : ℕ)) (C := 1) (fun _ => by norm_num) (X := X) (b₀ := b₀) hP₀ hρ
  refine h.trans ?_
  rw [one_mul]
  unfold junkShiftBound
  have hmono : ((Nat.sqrt (X + ρ) + 1) * Nat.log 2 (X + ρ) : ℕ)
      ≤ ((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) :=
    Nat.mul_le_mul (by
        have := Nat.sqrt_le_sqrt (show X + ρ ≤ X + ρmax by omega)
        omega)
      (Nat.log_mono_right (by omega))
  have : (((Nat.sqrt (X + ρ) + 1) * Nat.log 2 (X + ρ) : ℕ) : ℝ)
      ≤ (((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) : ℝ) := by exact_mod_cast hmono
  linarith

/-! ### `junkAvgΩ` -/

/-- **The valuation-junk block average.** -/
theorem junkAvgΩ_le (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀) {ρmax : ℕ}
    (hρm : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ ρmax) :
    junkAvgΩ bb G X
      ≤ (junkShiftBound G.P₀ X ρmax / ((apSample X G.P₀ G.b₀).card : ℝ)) * rowL1 bb G.K := by
  classical
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  set P := apSample X G.P₀ G.b₀ with hP
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  set B : ℝ := junkShiftBound G.P₀ X ρmax / (P.card : ℝ) with hBdef
  have hB0 : 0 ≤ B := div_nonneg (junkShiftBound_nonneg _ _ _) hc.le
  have hjunk0 : ∀ m : ℕ, 0 ≤ junk (fun _ => (1 : ℕ)) G.P₀ m := by
    intro m
    unfold junk
    exact Finset.sum_nonneg fun p _ => by positivity
  have hshift : ∀ i : G.Idx, (P.card : ℝ)⁻¹ *
      ∑ n ∈ P, |junk (fun _ => (1 : ℕ)) G.P₀ (n + shiftAL G.B G.Q G.D₀ i)| ≤ B := by
    intro i
    have habs : ∑ n ∈ P, |junk (fun _ => (1 : ℕ)) G.P₀ (n + shiftAL G.B G.Q G.D₀ i)|
        = ∑ n ∈ P, junk (fun _ => (1 : ℕ)) G.P₀ (n + shiftAL G.B G.Q G.D₀ i) :=
      Finset.sum_congr rfl fun n _ => abs_of_nonneg (hjunk0 _)
    rw [habs, hP]
    have := sum_junk_one_le (b₀ := G.b₀) (X := X) hP₀ (shiftAL_pos G i) (hρm i)
    rw [hBdef, ← hP, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hrow : ∀ ν : Fin G.rDim, (P.card : ℝ)⁻¹ *
      ∑ n ∈ P, |blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)|
      ≤ B * rowL1 bb G.K := fun ν =>
    sampleAvg_abs_blockSum_le_of_shift bb hbb G X hB0 _ (G.rowEquiv.symm ν) hshift
  unfold junkAvgΩ
  rw [← hP]
  have hswap : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)|
      = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
        |blockSum bb G (junk (fun _ => (1 : ℕ)) G.P₀) n (G.rowEquiv.symm ν)| := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hswap]
  have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
  rw [← hr]
  exact avg_le_of_forall_le _ _ (mul_nonneg hB0 (rowL1_nonneg hbr G.K)) fun ν _ => hrow ν

/-! ### `bigAvgΩ`: literally the `ω` estimate -/

lemma bigAvgΩ_eq_bigAvg (bb : ℕ) (G : GridParams) (X R : ℕ) :
    bigAvgΩ bb G X R = bigAvg bb G X R := rfl

/-- **`bigAvgΩ` in closed form** — the same RHS as `bigAvg_le'`: the large-prime block of `Ω`
*is* the large-prime block of `ω` (the valuation excess was split off into the junk). -/
theorem bigAvgΩ_le' (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X R Y : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty)
    (hK : 0 < G.K) (hR : 2 ≤ R) (hRY : R ≤ Y) {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    (hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx) :
    bigAvgΩ bb G X R
      ≤ Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) * rowL2 bb G.K
          + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
        + (Real.log Mx / Real.log Y) * rowL1 bb G.K := by
  rw [bigAvgΩ_eq_bigAvg]
  exact bigAvg_le' bb hbb G X R Y hne hK hR hRY hMx1 hMx

/-! ### The AP-mean of `Ω` — the far-tail input

`Ω` is **not** controlled by `log d(m)` (the inequality `2^{Ω} ≥ d` goes the wrong way), and the
pointwise bound `Ω(m) ≤ log₂ m` costs a `log X` the schedule cannot pay.  The working route is the
same split as §4D: `Ω = ω + frozenExcess + junk`, where the frozen part is bounded by `Ω(P₀)` and
the junk by `junkShiftBound`. -/

/-- The frozen excess at `c ≡ 1` never exceeds `Ω(P₀)`. -/
lemma frozenExcess_one_le {P₀ : ℕ} (hP₀ : P₀ ≠ 0) (m : ℕ) :
    frozenExcess (fun _ => (1 : ℕ)) P₀ m ≤ ((Ω P₀ : ℕ) : ℝ) := by
  classical
  have hsum : ((Ω P₀ : ℕ) : ℝ) = ∑ p ∈ P₀.primeFactors, ((P₀.factorization p : ℕ) : ℝ) := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum,
      Nat.support_factorization]
    push_cast
    rfl
  rw [hsum]
  unfold frozenExcess
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Nat.cast_one, one_mul]
  have : (min (m.factorization p) (P₀.factorization p) - 1 : ℕ) ≤ P₀.factorization p := by
    omega
  exact_mod_cast this

/-- **The AP-mean of `Ω` at layer `j`** — the `ω` bound plus the two `Ω`-specific costs. -/
theorem sum_cardFactors_shiftG_le (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (α : G.Atom) {j : ℕ} (hj : 1 ≤ j) :
    ∑ n ∈ apSample X G.P₀ G.b₀,
        ((Ω (n + shiftG G.B G.Q G.D₀ α j) : ℕ) : ℝ)
      ≤ (apSample X G.P₀ G.b₀).card *
            ((farC G X Dm + 2 * j) / Real.log 2
              + ((Ω G.P₀ : ℕ) : ℝ))
          + junkShiftBound G.P₀ X (j * Dm) := by
  classical
  set P := apSample X G.P₀ G.b₀ with hP
  set ρ := shiftG G.B G.Q G.D₀ α j with hρ
  have hρ1 : 1 ≤ ρ := shiftG_pos G α hj
  have hρle : ρ ≤ j * Dm := by
    rw [hρ]; unfold shiftG
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_left j (hDm α))
  have hP₀' : G.P₀ ≠ 0 := hP₀.ne'
  -- pointwise: Ω = ω + frozen + junk
  have hpt : ∀ n, ((Ω (n + ρ) : ℕ) : ℝ)
      = omegaR (n + ρ) + frozenExcess (fun _ => (1 : ℕ)) G.P₀ (n + ρ)
        + junk (fun _ => (1 : ℕ)) G.P₀ (n + ρ) := by
    intro n
    rw [cardFactors_eq_omegaR_add_excess,
      excess_eq_frozen_add_junk (fun _ => (1 : ℕ)) hP₀' (show n + ρ ≠ 0 by omega)]
    ring
  calc ∑ n ∈ P, ((Ω (n + ρ) : ℕ) : ℝ)
      = ∑ n ∈ P, omegaR (n + ρ) + ∑ n ∈ P, frozenExcess (fun _ => (1 : ℕ)) G.P₀ (n + ρ)
          + ∑ n ∈ P, junk (fun _ => (1 : ℕ)) G.P₀ (n + ρ) := by
        simp_rw [hpt]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ (P.card * ((farC G X Dm + 2 * j) / Real.log 2)
          + P.card * ((Ω G.P₀ : ℕ) : ℝ)) + junkShiftBound G.P₀ X (j * Dm) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · rw [hP, hρ]
          exact sum_omegaR_shiftG_le G X hne hDm α hj
        · calc ∑ n ∈ P, frozenExcess (fun _ => (1 : ℕ)) G.P₀ (n + ρ)
              ≤ ∑ _n ∈ P, ((Ω G.P₀ : ℕ) : ℝ) :=
                Finset.sum_le_sum fun n _ => frozenExcess_one_le hP₀' _
            _ = P.card * ((Ω G.P₀ : ℕ) : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        · rw [hP]
          exact sum_junk_one_le hP₀ hρ1 hρle
    _ = _ := by ring

/-! ### The far tail for `Ω`

Summing the AP-mean against `bb^{-j}` over `j > J`.  The `ω` piece is `farBound` verbatim; the
frozen piece is a bare geometric series; the junk piece needs an envelope, because
`junkShiftBound P₀ X (j·Dm)` grows in `j`.  Using `X + jDm ≤ (X+Dm)·j` and `(j+1)² ≤ 4·2^j`, the
growth is at most `2^j`, which is summable against `bb^{-j}` for `bb ≥ 3` (and only for `bb ≥ 3`
— the same wall as the row masses). -/

/-- The `j`-free part of the junk envelope. -/
noncomputable def junkA (P₀ X : ℕ) : ℝ :=
  (X : ℝ) / P₀ * (∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) + 1)

/-- The `2^j`-coefficient of the junk envelope. -/
noncomputable def junkB (X Dm : ℕ) : ℝ :=
  4 * (Real.sqrt ((X + Dm : ℕ) : ℝ) + 1) * (Real.log ((X + Dm : ℕ) : ℝ) / Real.log 2 + 1)

lemma junkA_nonneg (P₀ X : ℕ) : 0 ≤ junkA P₀ X := by
  unfold junkA
  have h1 : (0 : ℝ) ≤ ∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) := by
    refine Finset.sum_nonneg fun p hp => ?_
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  positivity

lemma junkB_nonneg (X Dm : ℕ) : 0 ≤ junkB X Dm := by
  unfold junkB
  have hlog : 0 ≤ Real.log ((X + Dm : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (X + Dm) with h | h
    · rw [h]; norm_num
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : 0 ≤ Real.log ((X + Dm : ℕ) : ℝ) / Real.log 2 := by positivity
  have hs : 0 ≤ Real.sqrt ((X + Dm : ℕ) : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- `(j+1)² ≤ 4·2^j`. -/
lemma sq_succ_le_four_mul_two_pow (j : ℕ) : (j + 1) ^ 2 ≤ 4 * 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ k ih =>
      have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      nlinarith [ih, hk]

/-- **The junk envelope at layer `j`.** -/
theorem junkShiftBound_layer_le (P₀ X Dm : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    junkShiftBound P₀ X (j * Dm) ≤ junkA P₀ X + junkB X Dm * 2 ^ j := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set M : ℕ := X + Dm with hM
  set Nj : ℕ := X + j * Dm with hNj
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hNjM : Nj ≤ M * j := by
    have : X ≤ j * X := Nat.le_mul_of_pos_left X (by omega)
    rw [hNj, hM]; nlinarith [this]
  have hNjMr : ((Nj : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) * (j : ℝ) := by exact_mod_cast hNjM
  have hM0 : (0 : ℝ) ≤ ((M : ℕ) : ℝ) := by positivity
  set L : ℝ := Real.log ((M : ℕ) : ℝ) / Real.log 2 with hL
  have hLlog : 0 ≤ Real.log ((M : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h]; norm_num
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  -- the square root piece
  have hsq : ((Nat.sqrt Nj : ℕ) : ℝ) ≤ Real.sqrt ((M : ℕ) : ℝ) * (j : ℝ) := by
    have h1 : ((Nat.sqrt Nj : ℕ) : ℝ) ≤ Real.sqrt ((Nj : ℕ) : ℝ) := by
      rw [show ((Nat.sqrt Nj : ℕ) : ℝ) = Real.sqrt (((Nat.sqrt Nj : ℕ) : ℝ) ^ 2) by
        rw [Real.sqrt_sq (by positivity)]]
      refine Real.sqrt_le_sqrt ?_
      have h0 : Nat.sqrt Nj ^ 2 ≤ Nj := Nat.sqrt_le' Nj
      have h0' : ((Nat.sqrt Nj : ℕ) : ℝ) ^ 2 ≤ ((Nj : ℕ) : ℝ) := by exact_mod_cast h0
      nlinarith [h0']
    refine h1.trans ?_
    calc Real.sqrt ((Nj : ℕ) : ℝ) ≤ Real.sqrt (((M : ℕ) : ℝ) * (j : ℝ)) :=
          Real.sqrt_le_sqrt hNjMr
      _ = Real.sqrt ((M : ℕ) : ℝ) * Real.sqrt (j : ℝ) :=
          Real.sqrt_mul hM0 _
      _ ≤ Real.sqrt ((M : ℕ) : ℝ) * (j : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          have : Real.sqrt (j : ℝ) ≤ Real.sqrt ((j : ℝ) ^ 2) := by
            refine Real.sqrt_le_sqrt ?_; nlinarith
          rwa [Real.sqrt_sq (by linarith)] at this
  -- the logarithm piece
  have hlogj : Real.log (j : ℝ) ≤ (j : ℝ) * Real.log 2 := by
    have h2 : (j : ℝ) ≤ (2 : ℝ) ^ j := by
      have : (j : ℕ) < 2 ^ j := Nat.lt_two_pow_self
      exact_mod_cast this.le
    calc Real.log (j : ℝ) ≤ Real.log ((2 : ℝ) ^ j) := Real.log_le_log (by linarith) h2
      _ = (j : ℝ) * Real.log 2 := by rw [Real.log_pow]
  have hlg : ((Nat.log 2 Nj : ℕ) : ℝ) ≤ L + (j : ℝ) := by
    rcases Nat.eq_zero_or_pos Nj with h | h
    · rw [h]
      simp only [Nat.log_zero_right, Nat.cast_zero]
      positivity
    · have hpow : (2 : ℕ) ^ (Nat.log 2 Nj) ≤ Nj := Nat.pow_log_le_self 2 (by omega)
      have hpowr : (2 : ℝ) ^ (Nat.log 2 Nj) ≤ ((Nj : ℕ) : ℝ) := by exact_mod_cast hpow
      have hNj0 : (0 : ℝ) < ((Nj : ℕ) : ℝ) := by exact_mod_cast h
      have hle : ((Nat.log 2 Nj : ℕ) : ℝ) * Real.log 2 ≤ Real.log ((Nj : ℕ) : ℝ) := by
        have := Real.log_le_log (by positivity) hpowr
        rwa [Real.log_pow] at this
      have hlogNj : Real.log ((Nj : ℕ) : ℝ) ≤ Real.log ((M : ℕ) : ℝ) + Real.log (j : ℝ) := by
        have hMpos : (0 : ℝ) < ((M : ℕ) : ℝ) := by
          rcases Nat.eq_zero_or_pos M with h' | h'
          · exfalso; rw [h'] at hNjM; omega
          · exact_mod_cast h'
        calc Real.log ((Nj : ℕ) : ℝ) ≤ Real.log (((M : ℕ) : ℝ) * (j : ℝ)) :=
              Real.log_le_log hNj0 hNjMr
          _ = Real.log ((M : ℕ) : ℝ) + Real.log (j : ℝ) :=
              Real.log_mul hMpos.ne' (by linarith)
      rw [hL, div_add' _ _ _ hlog2.ne', le_div_iff₀ hlog2]
      linarith
  -- assemble
  have hsq0 : 0 ≤ Real.sqrt ((M : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hquad : ((j : ℝ) + 1) ^ 2 ≤ 4 * 2 ^ j := by
    have := sq_succ_le_four_mul_two_pow j
    exact_mod_cast this
  have hmain : (((Nat.sqrt Nj + 1) * Nat.log 2 Nj : ℕ) : ℝ) ≤ junkB X Dm * 2 ^ j := by
    have hcast : (((Nat.sqrt Nj + 1) * Nat.log 2 Nj : ℕ) : ℝ)
        = (((Nat.sqrt Nj : ℕ) : ℝ) + 1) * ((Nat.log 2 Nj : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    have h1 : (((Nat.sqrt Nj : ℕ) : ℝ) + 1) ≤ (Real.sqrt ((M : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) := by
      nlinarith [hsq, hjr, hsq0]
    have h2 : ((Nat.log 2 Nj : ℕ) : ℝ) ≤ (L + 1) * ((j : ℝ) + 1) := by nlinarith [hlg, hL0, hjr]
    have h3 : (0 : ℝ) ≤ ((Nat.log 2 Nj : ℕ) : ℝ) := by positivity
    have h4 : (0 : ℝ) ≤ (((Nat.sqrt Nj : ℕ) : ℝ) + 1) := by positivity
    have hstep : (((Nat.sqrt Nj : ℕ) : ℝ) + 1) * ((Nat.log 2 Nj : ℕ) : ℝ)
        ≤ ((Real.sqrt ((M : ℕ) : ℝ) + 1) * ((j : ℝ) + 1)) * ((L + 1) * ((j : ℝ) + 1)) :=
      mul_le_mul h1 h2 h3 (by nlinarith [hjr, hsq0])
    refine hstep.trans ?_
    unfold junkB
    rw [show X + Dm = M from hM.symm, ← hL]
    nlinarith [hquad, hsq0, hL0, (by positivity : (0:ℝ) ≤ (Real.sqrt ((M : ℕ) : ℝ) + 1) * (L + 1))]
  unfold junkShiftBound junkA
  linarith [hmain]

/-- The closed form of the far junk series in base `bb ≥ 3`. -/
noncomputable def farJunkBound (bb : ℝ) (J : ℕ) (A B : ℝ) : ℝ :=
  A * (1 / bb) ^ (J + 1) * (bb / (bb - 1)) + B * (2 / bb) ^ (J + 1) * (bb / (bb - 2))

lemma hasSum_farJunkBound {bb : ℝ} (hb : 3 ≤ bb) (A B : ℝ) (J : ℕ) :
    HasSum (fun i : ℕ => (A + B * 2 ^ (J + i + 1)) * (1 / bb) ^ (J + i + 1))
      (farJunkBound bb J A B) := by
  have hbpos : (0 : ℝ) < bb := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / bb := by positivity
  have hr1 : (1 / bb : ℝ) < 1 := by rw [div_lt_one hbpos]; linarith
  have hs0 : (0 : ℝ) ≤ 2 / bb := by positivity
  have hs1 : (2 / bb : ℝ) < 1 := by rw [div_lt_one hbpos]; linarith
  have h1 := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (A * (1 / bb) ^ (J + 1))
  have h2 := (hasSum_geometric_of_lt_one hs0 hs1).mul_left (B * (2 / bb) ^ (J + 1))
  have h := h1.add h2
  have hfun : (fun i : ℕ => (A + B * 2 ^ (J + i + 1)) * (1 / bb) ^ (J + i + 1))
      = fun i : ℕ => A * (1 / bb) ^ (J + 1) * (1 / bb) ^ i
          + B * (2 / bb) ^ (J + 1) * (2 / bb) ^ i := by
    funext i
    have hbne : (bb : ℝ) ≠ 0 := hbpos.ne'
    rw [show J + i + 1 = (J + 1) + i by omega]
    simp only [pow_add, div_pow, one_pow]
    field_simp
  rw [hfun]
  have hclosed : farJunkBound bb J A B
      = A * (1 / bb) ^ (J + 1) * (1 - 1 / bb)⁻¹ + B * (2 / bb) ^ (J + 1) * (1 - 2 / bb)⁻¹ := by
    unfold farJunkBound
    have hb1 : (bb : ℝ) - 1 ≠ 0 := by linarith
    have hb2 : (bb : ℝ) - 2 ≠ 0 := by linarith
    have hb0 : (bb : ℝ) ≠ 0 := hbpos.ne'
    have e1 : (1 - 1 / bb : ℝ)⁻¹ = bb / (bb - 1) := by field_simp
    have e2 : (1 - 2 / bb : ℝ)⁻¹ = bb / (bb - 2) := by field_simp
    rw [e1, e2]
  rw [hclosed]
  exact h

/-! ### The far tail of `Ω`, assembled -/

/-- The far layers of one atom are summable for any `TWeight`. -/
lemma summable_farW (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) {X n : ℕ}
    (hn : n ∈ apSample X G.P₀ G.b₀) (α : G.Atom) :
    Summable (fun i : ℕ => (W.wN (n + shiftG G.B G.Q G.D₀ α (G.K + G.N + i + 1)) : ℝ)
      / (bb : ℝ) ^ (G.K + G.N + i + 1)) := by
  obtain ⟨k, hk1, -⟩ := G.exists_mult_mul hn α
  have hsum : Summable
      (fun j : ℕ => (W.wN (n + shiftG G.B G.Q G.D₀ α (j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1)) := by
    refine (W.summable_dilatedTailB (b := bb) hbb (G.d α) k (G.d_pos α).ne').congr (fun j => ?_)
    rw [hk1]
    show (W.wN (G.d α * (k + j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1)
      = (W.wN (offset G.B G.Q α + mult G.B G.Q G.D₀ α * k
          + shiftG G.B G.Q G.D₀ α (j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1)
    rw [add_shiftG_eq G.B G.Q G.D₀ α (G.hD α) (by omega)]
    show (W.wN (G.d α * (k + j + 1)) : ℝ) / (bb : ℝ) ^ (j + 1)
      = (W.wN (G.d α * (k + (j + 1))) : ℝ) / (bb : ℝ) ^ (j + 1)
    rw [show k + j + 1 = k + (j + 1) by omega]
  refine ((summable_nat_add_iff (G.K + G.N)).2 hsum).congr (fun i => ?_)
  rw [show i + (G.K + G.N) = G.K + G.N + i from by omega]

/-- **The `Ω` far tail of one row, summed over the sample.**  Three pieces: the `ω` tail
(`farBound`), the frozen excess (a bare geometric series) and the valuation junk
(`farJunkBound`).  Base `≥ 3` is used by the junk piece. -/
theorem sum_abs_farPartΩ_le (bb : ℕ) (hbb : 3 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (a : Fin G.K → Fin G.s) :
    ∑ n ∈ apSample X G.P₀ G.b₀, |farPartW TWeight.cardFactors bb G n a|
      ≤ (2 : ℝ) ^ G.K *
          ((apSample X G.P₀ G.b₀).card *
              (farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
                + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
            + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)) := by
  have hbr : (3 : ℝ) ≤ bb := by exact_mod_cast hbb
  have hbr2 : (2 : ℝ) ≤ bb := by linarith
  have hbb2 : 2 ≤ bb := by omega
  set P := apSample X G.P₀ G.b₀ with hP
  set J := G.K + G.N with hJ
  set C := farC G X Dm with hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  set f : G.Atom → ℕ → ℕ → ℝ := fun α n i =>
    ((Ω (n + shiftG G.B G.Q G.D₀ α (J + i + 1)) : ℕ) : ℝ) / (bb : ℝ) ^ (J + i + 1) with hf
  have hf0 : ∀ α n i, 0 ≤ f α n i := fun α n i => by
    simp only [hf]; positivity
  have hfs : ∀ α, ∀ n ∈ P, Summable (f α n) := fun α n hn =>
    summable_farW TWeight.cardFactors bb hbb2 G hn α
  have hpt : ∀ n ∈ P, |farPartW TWeight.cardFactors bb G n a|
      ≤ ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * ∑' i, f α n i := by
    intro n hn
    unfold farPartW
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (abs_nonneg _)
    exact abs_of_nonneg (tsum_nonneg fun i => hf0 α n i)
  -- the per-layer AP-mean
  have hlayer : ∀ α i, ∑ n ∈ P, f α n i
      ≤ ((P.card : ℝ) / Real.log 2 * (C + 2 * ((J : ℝ) + i + 1))
          + (P.card : ℝ) * ((Ω G.P₀ : ℕ) : ℝ)
          + (junkA G.P₀ X + junkB X Dm * 2 ^ (J + i + 1))) * (1 / (bb : ℝ)) ^ (J + i + 1) := by
    intro α i
    simp only [hf]
    rw [← Finset.sum_div]
    have h1 := sum_cardFactors_shiftG_le G X hne hP₀ hDm α
      (j := J + i + 1) (by omega)
    have h2 := junkShiftBound_layer_le G.P₀ X Dm (j := J + i + 1) (by omega)
    have hbpos : (0 : ℝ) < (bb : ℝ) := by linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (bb : ℝ) ^ (J + i + 1))]
    rw [← hP, ← hC] at h1
    refine (h1.trans (add_le_add le_rfl h2)).trans (le_of_eq ?_)
    rw [one_div_pow]
    field_simp
    push_cast
    ring
  -- the three summable pieces
  have hgeo := hasSum_farJunkBound hbr ((P.card : ℝ) * ((Ω G.P₀ : ℕ) : ℝ)) 0 J
  have hjk := hasSum_farJunkBound hbr (junkA G.P₀ X) (junkB X Dm) J
  have hom := (hasSum_farBound hbr2 C J).mul_left ((P.card : ℝ) / Real.log 2)
  have hsum3 := (hom.add hgeo).add hjk
  have hfun : (fun i : ℕ => (P.card : ℝ) / Real.log 2 * ((C + 2 * ((J : ℝ) + i + 1))
          * (1 / (bb : ℝ)) ^ (J + i + 1))
        + ((P.card : ℝ) * ((Ω G.P₀ : ℕ) : ℝ) + 0 * 2 ^ (J + i + 1))
            * (1 / (bb : ℝ)) ^ (J + i + 1)
        + (junkA G.P₀ X + junkB X Dm * 2 ^ (J + i + 1)) * (1 / (bb : ℝ)) ^ (J + i + 1))
      = fun i : ℕ => ((P.card : ℝ) / Real.log 2 * (C + 2 * ((J : ℝ) + i + 1))
          + (P.card : ℝ) * ((Ω G.P₀ : ℕ) : ℝ)
          + (junkA G.P₀ X + junkB X Dm * 2 ^ (J + i + 1))) * (1 / (bb : ℝ)) ^ (J + i + 1) := by
    funext i; ring
  rw [hfun] at hsum3
  set T : ℝ := (P.card : ℝ) / Real.log 2 * farBound bb J C
      + farJunkBound bb J ((P.card : ℝ) * ((Ω G.P₀ : ℕ) : ℝ)) 0
      + farJunkBound bb J (junkA G.P₀ X) (junkB X Dm) with hT
  calc ∑ n ∈ P, |farPartW TWeight.cardFactors bb G n a|
      ≤ ∑ n ∈ P, ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * ∑' i, f α n i :=
        Finset.sum_le_sum hpt
    _ = ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * ∑' i, ∑ n ∈ P, f α n i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← Finset.mul_sum, Summable.tsum_finsetSum (hfs α)]
    _ ≤ ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * T := by
        refine Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [← hsum3.tsum_eq]
        refine Summable.tsum_le_tsum (hlayer α) ?_ hsum3.summable
        exact summable_sum fun n hn => hfs α n hn
    _ = (2 : ℝ) ^ G.K * T := by
        rw [← Finset.sum_mul, sum_abs_kronPow_diffZ]
    _ = _ := by
        rw [hT]
        unfold farJunkBound
        ring

lemma farJunkBound_nonneg {bb : ℝ} (hb : 3 ≤ bb) (J : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ farJunkBound bb J A B := by
  unfold farJunkBound
  have h1 : (0 : ℝ) < bb - 1 := by linarith
  have h2 : (0 : ℝ) < bb - 2 := by linarith
  have h3 : (0 : ℝ) ≤ 1 / bb := by positivity
  have h4 : (0 : ℝ) ≤ 2 / bb := by positivity
  positivity

/-- **`farAvgΩ` in closed form.**  The `ω` far bound, plus the frozen geometric term, plus the
junk term normalised by the sample size (where the `√X / |P| → 0` saving lives). -/
theorem farAvgΩ_le (bb : ℕ) (hbb : 3 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) :
    farAvgΩ bb G X
      ≤ (2 : ℝ) ^ G.K *
          ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
              + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
            + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
                / ((apSample X G.P₀ G.b₀).card : ℝ)) := by
  have hbr : (3 : ℝ) ≤ bb := by exact_mod_cast hbb
  have hbr2 : (2 : ℝ) ≤ bb := by linarith
  set P := apSample X G.P₀ G.b₀ with hP
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  set Bd : ℝ := (2 : ℝ) ^ G.K *
      ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
          + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
        + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm) / (P.card : ℝ)) with hBd
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCn := farC_nonneg G X hne Dm
  have hfb := farBound_nonneg hbr2 (G.K + G.N) hCn
  have hfj := farJunkBound_nonneg hbr (G.K + G.N) (junkA_nonneg G.P₀ X) (junkB_nonneg X Dm)
  have hgeo : (0 : ℝ) ≤ ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))) := by
    have h1 : (0 : ℝ) < bb - 1 := by linarith
    have h2 : (0 : ℝ) ≤ 1 / (bb : ℝ) := by positivity
    positivity
  have hBd0 : 0 ≤ Bd := by
    rw [hBd]
    have : (0 : ℝ) ≤ farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm) / (P.card : ℝ) :=
      div_nonneg hfj hc.le
    have h5 : (0 : ℝ) ≤ farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2 :=
      div_nonneg hfb hlog2.le
    positivity
  have hrow : ∀ ν : Fin G.rDim,
      (P.card : ℝ)⁻¹ * ∑ n ∈ P, |farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν)|
        ≤ Bd := by
    intro ν
    have h := sum_abs_farPartΩ_le bb hbb G X hne hP₀ hDm (G.rowEquiv.symm ν)
    rw [← hP] at h
    calc (P.card : ℝ)⁻¹ * ∑ n ∈ P, |farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν)|
        ≤ (P.card : ℝ)⁻¹ * ((2 : ℝ) ^ G.K *
            ((P.card : ℝ) * (farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
                + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
              + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Bd := by rw [hBd]; field_simp
  unfold farAvgΩ
  rw [← hP]
  have hswap : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν)|
      = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
        |farPartW TWeight.cardFactors bb G n (G.rowEquiv.symm ν)| := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hswap]
  have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
  rw [← hr]
  exact avg_le_of_forall_le _ _ hBd0 fun ν _ => hrow ν

end NormalNumbers.G4
