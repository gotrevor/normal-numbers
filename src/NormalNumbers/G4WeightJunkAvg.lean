/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightRemainder
import NormalNumbers.G4OmegaJunk

/-!
# The three §4D estimates for `w_c`

The `Ω` estimates of `G4OmegaJunk` at a general bounded coefficient vector `c ≤ C`.  Writing
`κ = max C 1`:

* `bigAvgC = bigAvg` — the large-prime block never sees the weight;
* `junkAvgC ≤ C · (junkShiftBound / |P|) · rowL1` — one factor `C` from
  `G4WeightJunk.sum_junk_le`;
* `farAvgC ≤ κ · (the Ω far bound)` — from the pointwise domination
  `w_c(m) ≤ κ · Ω(m)` (`weightW_le_kappa_mul_cardFactors`).

So the whole `C`-dependence of §4D is a single factor `κ` in front of the `Ω` budget, which the
schedule pays by enlarging `K` (the deltas are fixed fractions of `ε·η = 2^{-k₄}/K`).
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert GridParams

variable (c : ℕ → ℕ) (C : ℕ) (hC : ∀ p, c p ≤ C)

include hC

/-- **Pointwise domination**: `w_c(m) ≤ max(C,1) · Ω(m)`. -/
theorem weightW_le_kappa_mul_cardFactors (m : ℕ) :
    weightW c m ≤ ((max C 1 : ℕ) : ℝ) * ((Ω m : ℕ) : ℝ) := by
  have hN : m.primeFactors.card ≤ Ω m := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum,
      Nat.support_factorization]
    calc m.primeFactors.card = ∑ _p ∈ m.primeFactors, 1 := by simp
      _ ≤ ∑ p ∈ m.primeFactors, m.factorization p := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp' := Nat.mem_primeFactors.1 hp
          exact hp'.1.factorization_pos_of_dvd hp'.2.2 hp'.2.1
  have homega : omegaR m ≤ ((Ω m : ℕ) : ℝ) := by
    rw [omegaR_eq]
    exact_mod_cast hN
  have hex : excess c m ≤ (C : ℝ) * (((Ω m : ℕ) : ℝ) - omegaR m) :=
    excess_le (C := (C : ℝ)) (fun p => by exact_mod_cast hC p) m
  have hCk : (C : ℝ) ≤ ((max C 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left C 1
  have h1k : (1 : ℝ) ≤ ((max C 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right C 1
  have hdiff : (0 : ℝ) ≤ ((Ω m : ℕ) : ℝ) - omegaR m := by linarith
  have hom0 : (0 : ℝ) ≤ omegaR m := omegaR_nonneg m
  unfold weightW
  nlinarith

/-! ### `junkAvgC` -/

/-- The sample sum of the `c`-junk at any shift `1 ≤ ρ ≤ ρmax`. -/
theorem sum_junk_C_le {X P₀ b₀ ρ ρmax : ℕ} (hP₀ : 0 < P₀) (hρ : 1 ≤ ρ) (hρm : ρ ≤ ρmax) :
    ∑ n ∈ apSample X P₀ b₀, junk c P₀ (n + ρ) ≤ (C : ℝ) * junkShiftBound P₀ X ρmax := by
  have h := sum_junk_le c (C := (C : ℝ)) (fun p => by exact_mod_cast hC p)
    (X := X) (b₀ := b₀) hP₀ hρ
  refine h.trans ?_
  unfold junkShiftBound
  have hmono : ((Nat.sqrt (X + ρ) + 1) * Nat.log 2 (X + ρ) : ℕ)
      ≤ ((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) :=
    Nat.mul_le_mul (by
        have := Nat.sqrt_le_sqrt (show X + ρ ≤ X + ρmax by omega)
        omega)
      (Nat.log_mono_right (by omega))
  have hm : (((Nat.sqrt (X + ρ) + 1) * Nat.log 2 (X + ρ) : ℕ) : ℝ)
      ≤ (((Nat.sqrt (X + ρmax) + 1) * Nat.log 2 (X + ρmax) : ℕ) : ℝ) := by exact_mod_cast hmono
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := by positivity
  nlinarith

/-- **The valuation-junk block average for `w_c`.** -/
theorem junkAvgC_le (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀) {ρmax : ℕ}
    (hρm : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ ρmax) :
    junkAvgC c bb G X
      ≤ ((C : ℝ) * junkShiftBound G.P₀ X ρmax / ((apSample X G.P₀ G.b₀).card : ℝ))
          * rowL1 bb G.K := by
  classical
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := by positivity
  set P := apSample X G.P₀ G.b₀ with hP
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  set B : ℝ := (C : ℝ) * junkShiftBound G.P₀ X ρmax / (P.card : ℝ) with hBdef
  have hB0 : 0 ≤ B :=
    div_nonneg (mul_nonneg hC0 (junkShiftBound_nonneg _ _ _)) hc.le
  have hjunk0 : ∀ m : ℕ, 0 ≤ junk c G.P₀ m := by
    intro m
    unfold junk
    exact Finset.sum_nonneg fun p _ => by positivity
  have hshift : ∀ i : G.Idx, (P.card : ℝ)⁻¹ *
      ∑ n ∈ P, |junk c G.P₀ (n + shiftAL G.B G.Q G.D₀ i)| ≤ B := by
    intro i
    have habs : ∑ n ∈ P, |junk c G.P₀ (n + shiftAL G.B G.Q G.D₀ i)|
        = ∑ n ∈ P, junk c G.P₀ (n + shiftAL G.B G.Q G.D₀ i) :=
      Finset.sum_congr rfl fun n _ => abs_of_nonneg (hjunk0 _)
    rw [habs, hP]
    have := sum_junk_C_le c C hC (b₀ := G.b₀) (X := X) hP₀ (shiftAL_pos G i) (hρm i)
    rw [hBdef, ← hP, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hrow : ∀ ν : Fin G.rDim, (P.card : ℝ)⁻¹ *
      ∑ n ∈ P, |blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)|
      ≤ B * rowL1 bb G.K := fun ν =>
    sampleAvg_abs_blockSum_le_of_shift bb hbb G X hB0 _ (G.rowEquiv.symm ν) hshift
  unfold junkAvgC
  rw [← hP]
  have hswap : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)|
      = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
        |blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)| := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hswap]
  have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
  rw [← hr]
  exact avg_le_of_forall_le _ _ (mul_nonneg hB0 (rowL1_nonneg hbr G.K)) fun ν _ => hrow ν

/-! ### `bigAvgC`: the `ω` estimate verbatim -/

omit hC in
lemma bigAvgC_eq_bigAvg (bb : ℕ) (G : GridParams) (X R : ℕ) :
    bigAvgC bb G X R = bigAvg bb G X R := rfl

omit hC in
theorem bigAvgC_le' (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X R Y : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty)
    (hK : 0 < G.K) (hR : 2 ≤ R) (hRY : R ≤ Y) {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    (hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx) :
    bigAvgC bb G X R
      ≤ Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) * rowL2 bb G.K
          + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
        + (Real.log Mx / Real.log Y) * rowL1 bb G.K := by
  rw [bigAvgC_eq_bigAvg]
  exact bigAvg_le' bb hbb G X R Y hne hK hR hRY hMx1 hMx

/-! ### The far tail for `w_c` -/

theorem sum_abs_farPartC_le (bb : ℕ) (hbb : 3 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (a : Fin G.K → Fin G.s) :
    ∑ n ∈ apSample X G.P₀ G.b₀, |farPartW (TWeight.weight c C hC) bb G n a|
      ≤ ((max C 1 : ℕ) : ℝ) * ((2 : ℝ) ^ G.K *
          ((apSample X G.P₀ G.b₀).card *
              (farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
                + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
            + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm))) := by
  have hκ0 : (0 : ℝ) ≤ ((max C 1 : ℕ) : ℝ) := by positivity
  have hbr : (3 : ℝ) ≤ bb := by exact_mod_cast hbb
  have hbr2 : (2 : ℝ) ≤ bb := by linarith
  have hbb2 : 2 ≤ bb := by omega
  set P := apSample X G.P₀ G.b₀ with hP
  set J := G.K + G.N with hJ
  set Cf := farC G X Dm with hCf
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  set κ : ℝ := ((max C 1 : ℕ) : ℝ) with hκ
  set f : G.Atom → ℕ → ℕ → ℝ := fun α n i =>
    (((TWeight.weight c C hC).wN (n + shiftG G.B G.Q G.D₀ α (J + i + 1)) : ℕ) : ℝ)
      / (bb : ℝ) ^ (J + i + 1) with hf
  have hf0 : ∀ α n i, 0 ≤ f α n i := fun α n i => by
    simp only [hf]; positivity
  have hfs : ∀ α, ∀ n ∈ P, Summable (f α n) := fun α n hn =>
    summable_farW (TWeight.weight c C hC) bb hbb2 G hn α
  have hpt : ∀ n ∈ P, |farPartW (TWeight.weight c C hC) bb G n a|
      ≤ ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * ∑' i, f α n i := by
    intro n hn
    unfold farPartW
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (abs_nonneg _)
    exact abs_of_nonneg (tsum_nonneg fun i => hf0 α n i)
  -- the per-layer AP-mean
  have hlayer : ∀ α i, ∑ n ∈ P, f α n i
      ≤ (κ * (P.card : ℝ) / Real.log 2 * (Cf + 2 * ((J : ℝ) + i + 1))
          + κ * (P.card : ℝ) * ((Ω G.P₀ : ℕ) : ℝ)
          + (κ * junkA G.P₀ X + κ * junkB X Dm * 2 ^ (J + i + 1)))
        * (1 / (bb : ℝ)) ^ (J + i + 1) := by
    intro α i
    simp only [hf]
    rw [← Finset.sum_div]
    have h1 := sum_cardFactors_shiftG_le G X hne hP₀ hDm α
      (j := J + i + 1) (by omega)
    have h2 := junkShiftBound_layer_le G.P₀ X Dm (j := J + i + 1) (by omega)
    have hdom : ∑ n ∈ P, (((TWeight.weight c C hC).wN
          (n + shiftG G.B G.Q G.D₀ α (J + i + 1)) : ℕ) : ℝ)
        ≤ κ * ∑ n ∈ P, ((Ω (n + shiftG G.B G.Q G.D₀ α (J + i + 1)) : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n _ => ?_
      have := weightW_le_kappa_mul_cardFactors c C hC (n + shiftG G.B G.Q G.D₀ α (J + i + 1))
      rwa [TWeight.weight_wN c C hC]
    have hbpos : (0 : ℝ) < (bb : ℝ) := by linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (bb : ℝ) ^ (J + i + 1))]
    rw [← hP, ← hCf] at h1
    have h3 : ∑ n ∈ P, (((TWeight.weight c C hC).wN
          (n + shiftG G.B G.Q G.D₀ α (J + i + 1)) : ℕ) : ℝ)
        ≤ κ * ((P.card : ℝ) * ((Cf + 2 * ((J : ℝ) + i + 1)) / Real.log 2
              + ((Ω G.P₀ : ℕ) : ℝ))
            + (junkA G.P₀ X + junkB X Dm * 2 ^ (J + i + 1))) := by
      refine hdom.trans ?_
      have := (h1.trans (add_le_add le_rfl h2))
      have hκ0' : (0 : ℝ) ≤ κ := by rw [hκ]; positivity
      push_cast at this ⊢
      nlinarith [this]
    refine h3.trans (le_of_eq ?_)
    rw [one_div_pow]
    field_simp
  -- the three summable pieces
  have hgeo := hasSum_farJunkBound hbr (κ * (P.card : ℝ) * ((Ω G.P₀ : ℕ) : ℝ)) 0 J
  have hjk := hasSum_farJunkBound hbr (κ * junkA G.P₀ X) (κ * junkB X Dm) J
  have hom := (hasSum_farBound hbr2 Cf J).mul_left (κ * (P.card : ℝ) / Real.log 2)
  have hsum3 := (hom.add hgeo).add hjk
  have hfun : (fun i : ℕ => κ * (P.card : ℝ) / Real.log 2 * ((Cf + 2 * ((J : ℝ) + i + 1))
          * (1 / (bb : ℝ)) ^ (J + i + 1))
        + (κ * (P.card : ℝ) * ((Ω G.P₀ : ℕ) : ℝ) + 0 * 2 ^ (J + i + 1))
            * (1 / (bb : ℝ)) ^ (J + i + 1)
        + (κ * junkA G.P₀ X + κ * junkB X Dm * 2 ^ (J + i + 1))
            * (1 / (bb : ℝ)) ^ (J + i + 1))
      = fun i : ℕ => (κ * (P.card : ℝ) / Real.log 2 * (Cf + 2 * ((J : ℝ) + i + 1))
          + κ * (P.card : ℝ) * ((Ω G.P₀ : ℕ) : ℝ)
          + (κ * junkA G.P₀ X + κ * junkB X Dm * 2 ^ (J + i + 1)))
        * (1 / (bb : ℝ)) ^ (J + i + 1) := by
    funext i; ring
  rw [hfun] at hsum3
  set T : ℝ := κ * (P.card : ℝ) / Real.log 2 * farBound bb J Cf
      + farJunkBound bb J (κ * (P.card : ℝ) * ((Ω G.P₀ : ℕ) : ℝ)) 0
      + farJunkBound bb J (κ * junkA G.P₀ X) (κ * junkB X Dm) with hT
  calc ∑ n ∈ P, |farPartW (TWeight.weight c C hC) bb G n a|
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


theorem farAvgC_le (bb : ℕ) (hbb : 3 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) :
    farAvgC c C hC bb G X
      ≤ ((max C 1 : ℕ) : ℝ) * ((2 : ℝ) ^ G.K *
          ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
              + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
            + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
                / ((apSample X G.P₀ G.b₀).card : ℝ))) := by
  have hbr : (3 : ℝ) ≤ bb := by exact_mod_cast hbb
  have hbr2 : (2 : ℝ) ≤ bb := by linarith
  set P := apSample X G.P₀ G.b₀ with hP
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  set κ : ℝ := ((max C 1 : ℕ) : ℝ) with hκ
  have hκ0 : (0 : ℝ) ≤ κ := by rw [hκ]; positivity
  set Bd : ℝ := κ * ((2 : ℝ) ^ G.K *
      ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
          + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
        + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm) / (P.card : ℝ))) with hBd
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
      (P.card : ℝ)⁻¹ * ∑ n ∈ P, |farPartW (TWeight.weight c C hC) bb G n (G.rowEquiv.symm ν)|
        ≤ Bd := by
    intro ν
    have h := sum_abs_farPartC_le c C hC bb hbb G X hne hP₀ hDm (G.rowEquiv.symm ν)
    rw [← hP] at h
    calc (P.card : ℝ)⁻¹ * ∑ n ∈ P, |farPartW (TWeight.weight c C hC) bb G n (G.rowEquiv.symm ν)|
        ≤ (P.card : ℝ)⁻¹ * (κ * ((2 : ℝ) ^ G.K *
            ((P.card : ℝ) * (farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
                + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
              + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Bd := by rw [hBd]; field_simp
  unfold farAvgC
  rw [← hP]
  have hswap : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |farPartW (TWeight.weight c C hC) bb G n (G.rowEquiv.symm ν)|
      = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
        |farPartW (TWeight.weight c C hC) bb G n (G.rowEquiv.symm ν)| := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hswap]
  have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
  rw [← hr]
  exact avg_le_of_forall_le _ _ hBd0 fun ν _ => hrow ν


/-! ### `PropD` for `w_c` from the three closed forms -/

/-- **`PropD` for the `w_c`-frame from three closed-form bounds.**  Compared with the `Ω`
version, the junk budget carries a factor `C` and the far budget a factor `max C 1`. -/
theorem gridFrameW_weightC_propD_of_bounds (bb : ℕ) (hbb : 3 ≤ bb) (G : GridParams)
    (X R Y : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    (hK : 0 < G.K) (hR : 2 ≤ R) (hRY : R ≤ Y) {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    (hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) {ρmax : ℕ}
    (hρm : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ ρmax)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {δbig δjunk δfar : ℝ}
    (hbig : Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R)) * rowL2 bb G.K
          + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
        + (Real.log Mx / Real.log Y) * rowL1 bb G.K ≤ δbig * (ε * η))
    (hjunk : ((C : ℝ) * junkShiftBound G.P₀ X ρmax / ((apSample X G.P₀ G.b₀).card : ℝ))
        * rowL1 bb G.K ≤ δjunk * (ε * η))
    (hfar : ((max C 1 : ℕ) : ℝ) * ((2 : ℝ) ^ G.K *
        ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
            + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
          + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
              / ((apSample X G.P₀ G.b₀).card : ℝ))) ≤ δfar * (ε * η)) :
    (gridFrameW (TWeight.weight c C hC) bb (by omega) G X hne (smallPrimes R G.P₀)
      (frozenGammaC c bb G) hη hε D).PropD (δbig + δjunk + δfar) :=
  gridFrameW_weightC_propD c C hC bb (by omega) G X hne R hη hε D
    ((bigAvgC_le' bb (by omega) G X R Y hne hK hR hRY hMx1 hMx).trans hbig)
    ((junkAvgC_le c C hC bb (by omega) G X hne hP₀ hρm).trans hjunk)
    ((farAvgC_le c C hC bb hbb G X hne hP₀ hDm).trans hfar)


end NormalNumbers.G4
