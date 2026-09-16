/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4FrameA
import NormalNumbers.G4WeightA
import NormalNumbers.G4SubsetCFrame

/-!
# §4D for the master additive weight `w_{a,c}` on the `a`-weighted frame

`G4SubsetCFrame` proves `PropD` for the merged weight `w_{c,S}` on `gridFrameW`, whose retained
small-prime vector is the *indicator* `Sval` on `(smallPrimes R P₀).filter S`.  For a general
bounded multiplier `a` the retained vector is `SvalA` (`G4PhaseA`) and the frame is `gridFrameWA`
(`G4FrameA`).  This module ports the §4D chain, term by term:

    w_{a,c}(m) = [ ω_a(m ∧ P₀) + frozenExcess_c(m) ]   (frozen → γ)
               + ω_a(m ∧ smallPrimes R P₀)             (retained vector, `SvalA`)
               + ω_{a,big}(m)                          (large-prime junk)
               + junk_c(m)                             (valuation junk)

The one genuinely new estimate is the large-prime average.  `bigAvgS_le'` is **uniform in the
prime set `S`**, so the layer-cake decomposition

    ω_{a,big} = ∑_{k=1}^{Ca} ω_{S_k,big},   S_k = {p : k ≤ a_p}

turns the `a`-weighted large-prime average into `Ca` copies of the subset one: the cost of a
general bounded `a` in the far/large-prime field is the *multiplicative* constant `Ca`, exactly
as in the far tail (`farAvgW_le_of_layer` at `g = Ca · weightW c`, legitimate because
`w_{a,c} ≤ Ca · w_c` pointwise for `1 ≤ Ca`).

At `a = 1` every statement here is the campaign-B one, and at `a = 1_S` it is `G4SubsetCFrame`'s.
-/

open Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-! ### The `a`-weighted large-prime count, and the three-way split of `ω_a` -/

/-- The `a`-weighted large-prime count. -/
def omegaBigA (a : ℕ → ℕ) (R P₀ m : ℕ) : ℕ :=
  ∑ p ∈ m.primeFactors.filter (fun p => ¬ p ∣ P₀ ∧ R < p), a p

lemma omegaOnA_primeFactors_eq (a : ℕ → ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    omegaOnA a P₀.primeFactors m = ∑ p ∈ m.primeFactors.filter (fun p => p ∣ P₀), a p := by
  classical
  unfold omegaOnA
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨⟨h1, h3, hm⟩, h2⟩
  · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨⟨h1, h3, hP₀⟩, h2⟩

lemma omegaOnA_smallPrimes_eq (a : ℕ → ℕ) {R P₀ m : ℕ} (hm : m ≠ 0) :
    omegaOnA a (smallPrimes R P₀) m
      = ∑ p ∈ m.primeFactors.filter (fun p => ¬ p ∣ P₀ ∧ p ≤ R), a p := by
  classical
  unfold omegaOnA
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, mem_smallPrimes]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨h1, h4, hm⟩, h3, h2⟩
  · rintro ⟨⟨h1, h2, -⟩, h3, h4⟩; exact ⟨⟨h1, h4, h3⟩, h2⟩

/-- **The frozen / small / large partition of `ω_a`.** -/
theorem omegaWN_split (a : ℕ → ℕ) (R : ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    ∑ p ∈ m.primeFactors, a p
      = omegaOnA a P₀.primeFactors m + omegaOnA a (smallPrimes R P₀) m
        + omegaBigA a R P₀ m := by
  classical
  rw [omegaOnA_primeFactors_eq a hP₀ hm, omegaOnA_smallPrimes_eq a hm]
  unfold omegaBigA
  have e1 : m.primeFactors.filter (fun p => ¬ p ∣ P₀ ∧ p ≤ R)
      = (m.primeFactors.filter (fun p => ¬ p ∣ P₀)).filter (fun p => p ≤ R) := by
    rw [Finset.filter_filter]
  have e2 : m.primeFactors.filter (fun p => ¬ p ∣ P₀ ∧ R < p)
      = (m.primeFactors.filter (fun p => ¬ p ∣ P₀)).filter (fun p => ¬ p ≤ R) := by
    rw [Finset.filter_filter]
    ext p
    simp only [Finset.mem_filter, not_le]
  rw [e1, e2, add_assoc, Finset.sum_filter_add_sum_filter_not, Finset.sum_filter_add_sum_filter_not]

/-- The real form of the `ω_a` split. -/
lemma omegaW_split (a : ℕ → ℕ) (R : ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    omegaW a m = (omegaOnA a P₀.primeFactors m : ℝ) + (omegaOnA a (smallPrimes R P₀) m : ℝ)
      + (omegaBigA a R P₀ m : ℝ) := by
  have h : ((∑ p ∈ m.primeFactors, a p : ℕ) : ℝ)
      = ((omegaOnA a P₀.primeFactors m + omegaOnA a (smallPrimes R P₀) m
          + omegaBigA a R P₀ m : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (omegaWN_split a R hP₀ hm)
  unfold omegaW
  push_cast at h ⊢
  linarith

/-! ### The four-way split of `w_{a,c}` -/

variable (a c : ℕ → ℕ)

/-- **The four-way split of `w_{a,c}`.** -/
theorem weightAC_split (R : ℕ) {P₀ m : ℕ} (hP₀ : P₀ ≠ 0) (hm : m ≠ 0) :
    weightAW a c m
      = ((omegaOnA a P₀.primeFactors m : ℕ) : ℝ) + frozenExcess c P₀ m
        + ((omegaOnA a (smallPrimes R P₀) m : ℕ) : ℝ)
        + ((omegaBigA a R P₀ m : ℕ) : ℝ) + junk c P₀ m := by
  have h3 := excess_eq_frozen_add_junk c hP₀ hm
  rw [weightAW, h3, omegaW_split a R hP₀ hm]
  push_cast
  ring

/-! ### The frozen translate -/

/-- The weight the modulus freezes for `w_{a,c}`. -/
noncomputable def frozenWeightAC (P₀ m : ℕ) : ℝ :=
  ((omegaOnA a P₀.primeFactors m : ℕ) : ℝ) + frozenExcess c P₀ m

/-- The `a`-weighted frozen translate. -/
noncomputable def frozenTranslateAC (bb : ℕ) (G : GridParams) (ν : Fin G.rDim) : ℝ :=
  blockSum bb G (frozenWeightAC a c G.P₀) G.b₀ (G.rowEquiv.symm ν)

/-- The `a`-weighted frozen translate as a point of the torus. -/
noncomputable def frozenGammaAC (bb : ℕ) (G : GridParams) : Torus G.rDim :=
  fun ν => ((frozenTranslateAC a c bb G ν : ℝ) : UnitAddCircle)

lemma omegaOnA_primeFactors_congr {P₀ n m ρ : ℕ} (h : n % P₀ = m % P₀) :
    omegaOnA a P₀.primeFactors (n + ρ) = omegaOnA a P₀.primeFactors (m + ρ) := by
  classical
  unfold omegaOnA
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_congr fun p hp => ?_
  have hpP : p ∣ P₀ := (Nat.mem_primeFactors.1 hp).2.1
  have hnm : n ≡ m [MOD p] := Nat.ModEq.of_dvd hpP h
  constructor
  · intro hd
    exact (Nat.modEq_zero_iff_dvd).1 (((hnm.add_right ρ).symm).trans
      ((Nat.modEq_zero_iff_dvd).2 hd))
  · intro hd
    exact (Nat.modEq_zero_iff_dvd).1 ((hnm.add_right ρ).trans ((Nat.modEq_zero_iff_dvd).2 hd))

lemma blockSum_frozenAC_eq (bb : ℕ) (G : GridParams) {X n : ℕ}
    (hn : n ∈ apSample X G.P₀ G.b₀) (u : Fin G.K → Fin G.s) :
    blockSum bb G (frozenWeightAC a c G.P₀) n u
      = blockSum bb G (frozenWeightAC a c G.P₀) G.b₀ u := by
  refine blockSum_congr bb G u fun α jj => ?_
  have h1 : n % G.P₀ = G.b₀ := (Finset.mem_filter.1 hn).2
  have h2 : G.b₀ % G.P₀ = G.b₀ := Nat.mod_eq_of_lt G.b₀_lt_P₀
  have hρ : 0 < shiftAL G.B G.Q G.D₀ (α, jj) := shiftAL_pos G (α, jj)
  unfold frozenWeightAC
  rw [omegaOnA_primeFactors_congr a (h1.trans h2.symm),
    frozenExcess_congr c (h1.trans h2.symm) (by omega) (by omega)]

/-! ### The block split -/

lemma SvalA_eq_blockSum (bb : ℕ) (G : GridParams) (sm : Finset ℕ) (n : ℕ)
    (u : Fin G.K → Fin G.s) :
    SvalA bb a sm (shiftAL G.B G.Q G.D₀ (N := G.N)) n u
      = blockSum bb G (fun m => ((omegaOnA a sm m : ℕ) : ℝ)) n u := rfl

/-- **The exact remainder decomposition for `w_{a,c}`.** -/
theorem blockSum_weightAC_split (bb : ℕ) (G : GridParams) (R : ℕ) (n : ℕ)
    (u : Fin G.K → Fin G.s) :
    blockSum bb G (fun m => weightAW a c m) n u
      = blockSum bb G (frozenWeightAC a c G.P₀) n u
        + SvalA bb a (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n u
        + blockSum bb G (fun m => ((omegaBigA a R G.P₀ m : ℕ) : ℝ)) n u
        + blockSum bb G (junk c G.P₀) n u := by
  rw [SvalA_eq_blockSum, ← blockSum_add, ← blockSum_add, ← blockSum_add]
  refine blockSum_congr bb G u fun α jj => ?_
  have hρ : 0 < shiftAL G.B G.Q G.D₀ (α, jj) := shiftAL_pos G (α, jj)
  have h := weightAC_split a c R (P₀ := G.P₀) (m := n + shiftAL G.B G.Q G.D₀ (α, jj))
    G.P₀_pos.ne' (by omega)
  rw [h]
  unfold frozenWeightAC
  ring

/-! ### Dropping the inactive primes from the retained vector -/

lemma omegaOnA_filter_active (s : Finset ℕ) (m : ℕ) :
    omegaOnA a (s.filter (fun p => 1 ≤ a p)) m = omegaOnA a s m := by
  classical
  unfold omegaOnA
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1,
      (Finset.mem_filter.1 hp).2⟩
  · intro p hp hnp
    by_contra h
    exact hnp (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hp).1,
      Nat.one_le_iff_ne_zero.2 h⟩, (Finset.mem_filter.1 hp).2⟩)

lemma SvalA_filter_active (bb : ℕ) (G : GridParams) (s : Finset ℕ) (n : ℕ)
    (u : Fin G.K → Fin G.s) :
    SvalA bb a (s.filter (fun p => 1 ≤ a p)) (shiftAL G.B G.Q G.D₀ (N := G.N)) n u
      = SvalA bb a s (shiftAL G.B G.Q G.D₀ (N := G.N)) n u := by
  unfold SvalA
  exact Finset.sum_congr rfl fun α _ => congrArg _ (Finset.sum_congr rfl fun jj _ => by
    rw [omegaOnA_filter_active])

/-! ### `Ffull`, fully decomposed -/

lemma gridFrameWA_Ffull (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrameWA W a bb hbb G X hne sm γ hη hε D).Ffull
      = (gridFrameW W bb hbb G X hne sm γ hη hε D).Ffull := rfl

theorem gridFrameWA_weightAC_Ffull_decomp (W : TWeight)
    (hW : ∀ m : ℕ, ((W.wN m : ℕ) : ℝ) = weightAW a c m) (bb : ℕ)
    (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (R : ℕ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (ν : Fin G.rDim) :
    (gridFrameWA W a bb hbb G X hne ((smallPrimes R G.P₀).filter (fun p => 1 ≤ a p))
        (frozenGammaAC a c bb G) hη hε D).Ffull n ν
      = (((SvalA bb a ((smallPrimes R G.P₀).filter (fun p => 1 ≤ a p))
            (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν)
          + blockSum bb G (fun m => ((omegaBigA a R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
          + blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)
          + farPartW W bb G n (G.rowEquiv.symm ν) : ℝ)) : UnitAddCircle) := by
  have hw : (fun m => ((W).wN m : ℝ)) = fun m => weightAW a c m := funext fun m => hW m
  rw [gridFrameWA_Ffull a W bb hbb G X hne _ _ hη hε D,
    gridFrameW_Ffull_eq W bb hbb G X hne _ _ hη hε D hn ν,
    tailFrom_splitW W bb hbb G X hne _ _ hη hε D hn ν, hw,
    blockSum_weightAC_split a c bb G R n (G.rowEquiv.symm ν),
    blockSum_frozenAC_eq a c bb G hn (G.rowEquiv.symm ν),
    SvalA_filter_active a bb G (smallPrimes R G.P₀) n (G.rowEquiv.symm ν)]
  show (((frozenTranslateAC a c bb G ν
      + SvalA bb a (smallPrimes R G.P₀) (shiftAL G.B G.Q G.D₀ (N := G.N)) n
          (G.rowEquiv.symm ν)
      + blockSum bb G (fun m => ((omegaBigA a R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
      + blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)
      + farPartW W bb G n (G.rowEquiv.symm ν) : ℝ)) : UnitAddCircle)
      - ((frozenTranslateAC a c bb G ν : ℝ) : UnitAddCircle) = _
  rw [← QuotientAddGroup.mk_sub]
  congr 1
  ring

/-! ### `PropD`, reduced to three sample averages -/

/-- The `a`-weighted large-prime block average. -/
noncomputable def bigAvgA (a : ℕ → ℕ) (bb : ℕ) (G : GridParams) (X R : ℕ) : ℝ :=
  ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
    (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
      |blockSum bb G (fun m => ((omegaBigA a R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|

/-- **`PropD` for the master weight**, reduced to the three arithmetic estimates. -/
theorem gridFrameWA_weightAC_propD (W : TWeight)
    (hW : ∀ m : ℕ, ((W.wN m : ℕ) : ℝ) = weightAW a c m) (bb : ℕ)
    (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (R : ℕ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {δbig δjunk δfar : ℝ}
    (hbig : bigAvgA a bb G X R ≤ δbig * (ε * η))
    (hjunk : junkAvgC c bb G X ≤ δjunk * (ε * η))
    (hfar : farAvgW W bb G X ≤ δfar * (ε * η)) :
    (gridFrameWA W a bb hbb G X hne ((smallPrimes R G.P₀).filter (fun p => 1 ≤ a p))
      (frozenGammaAC a c bb G) hη hε D).PropD (δbig + δjunk + δfar) := by
  classical
  set fr := gridFrameWA W a bb hbb G X hne ((smallPrimes R G.P₀).filter (fun p => 1 ≤ a p))
    (frozenGammaAC a c bb G) hη hε D with hfr
  have hcard : (0 : ℝ) ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ := by positivity
  have hstep : ∀ n ∈ apSample X G.P₀ G.b₀, dAv (fr.S n) (fr.Ffull n)
      ≤ (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum bb G (fun m => ((omegaBigA a R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
        + ((G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)|
          + (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
            |farPartW W bb G n (G.rowEquiv.symm ν)|) := by
    intro n hn
    have hpt : ∀ ν : Fin G.rDim, dist (fr.S n ν) (fr.Ffull n ν)
        ≤ |blockSum bb G (fun m => ((omegaBigA a R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
          + (|blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)|
            + |farPartW W bb G n (G.rowEquiv.symm ν)|) := by
      intro ν
      rw [gridFrameWA_weightAC_Ffull_decomp a c W hW bb hbb G X hne R hη hε D hn ν]
      refine (dist_coe_le' _ _).trans ?_
      have hrw : SvalA bb a ((smallPrimes R G.P₀).filter (fun p => 1 ≤ a p))
              (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν)
          - (SvalA bb a ((smallPrimes R G.P₀).filter (fun p => 1 ≤ a p))
              (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν)
            + blockSum bb G (fun m => ((omegaBigA a R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
            + blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)
            + farPartW W bb G n (G.rowEquiv.symm ν))
          = -(blockSum bb G (fun m => ((omegaBigA a R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)
              + (blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)
                + farPartW W bb G n (G.rowEquiv.symm ν))) := by ring
      rw [hrw, abs_neg]
      exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    calc dAv (fr.S n) (fr.Ffull n)
        = (∑ ν : Fin G.rDim, dist (fr.S n ν) (fr.Ffull n ν)) / (G.rDim : ℝ) := rfl
      _ ≤ (∑ ν : Fin G.rDim,
            (|blockSum bb G (fun m => ((omegaBigA a R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
              + (|blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)|
                + |farPartW W bb G n (G.rowEquiv.symm ν)|)))
            / (G.rDim : ℝ) := by
            gcongr with ν
            exact hpt ν
      _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            ring
  show ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
      dAv (fr.S n) (fr.Ffull n) ≤ (δbig + δjunk + δfar) * fr.res
  have hres : fr.res = ε * η := rfl
  rw [hres]
  calc ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
        dAv (fr.S n) (fr.Ffull n)
      ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
          ((G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
              |blockSum bb G (fun m => ((omegaBigA a R G.P₀ m : ℕ) : ℝ)) n (G.rowEquiv.symm ν)|
            + ((G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
                |blockSum bb G (junk c G.P₀) n (G.rowEquiv.symm ν)|
              + (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
                |farPartW W bb G n (G.rowEquiv.symm ν)|)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hcard
    _ = bigAvgA a bb G X R + (junkAvgC c bb G X + farAvgW W bb G X) := by
        unfold bigAvgA junkAvgC farAvgW
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        ring
    _ ≤ δbig * (ε * η) + (δjunk * (ε * η) + δfar * (ε * η)) :=
        add_le_add hbig (add_le_add hjunk hfar)
    _ = (δbig + δjunk + δfar) * (ε * η) := by ring

/-! ### The layer cake: the `a`-weighted large-prime average -/

lemma blockSum_sum {ι : Type*} (T : Finset ι) (bb : ℕ) (G : GridParams) (w : ι → ℕ → ℝ) (n : ℕ)
    (u : Fin G.K → Fin G.s) :
    blockSum bb G (fun m => ∑ k ∈ T, w k m) n u = ∑ k ∈ T, blockSum bb G (w k) n u := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [blockSum]
  | insert k T hk ih =>
      rw [Finset.sum_insert hk]
      have hfun : (fun m => ∑ j ∈ insert k T, w j m) = fun m => w k m + ∑ j ∈ T, w j m := by
        funext m
        rw [Finset.sum_insert hk]
      rw [hfun, blockSum_add, ih]

/-- **The layer cake for the `a`-weighted large-prime count**: `a_p = #{k ∈ [1,Ca] : k ≤ a_p}`,
so `ω_{a,big}` is the sum of the `Ca` subset counts at `S_k = {p : k ≤ a_p}`. -/
lemma omegaBigA_layer_cake {Ca : ℕ} (hCa : ∀ p, a p ≤ Ca) (R P₀ m : ℕ) :
    omegaBigA a R P₀ m
      = ∑ k ∈ Finset.Icc 1 Ca, omegaBigS (fun p => k ≤ a p) R P₀ m := by
  classical
  unfold omegaBigA omegaBigS
  simp only [Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hQ : ¬ p ∣ P₀ ∧ R < p
  · rw [if_pos hQ]
    have hterm : ∀ k : ℕ, (if k ≤ a p ∧ ¬ p ∣ P₀ ∧ R < p then 1 else 0)
        = (if k ≤ a p then 1 else 0) := by
      intro k
      by_cases hk : k ≤ a p
      · rw [if_pos ⟨hk, hQ⟩, if_pos hk]
      · rw [if_neg (by tauto), if_neg hk]
    rw [Finset.sum_congr rfl fun k _ => hterm k]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, smul_eq_mul, mul_one, add_zero]
    have hset : (Finset.Icc 1 Ca).filter (fun k => k ≤ a p) = Finset.Icc 1 (a p) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans (hCa p)⟩, h2⟩
    rw [hset, Nat.card_Icc]
    omega
  · rw [if_neg hQ]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [if_neg (by tauto)]

/-- The `a`-weighted large-prime average is at most the sum of the `Ca` subset averages. -/
theorem bigAvgA_le_sum {Ca : ℕ} (hCa : ∀ p, a p ≤ Ca) (bb : ℕ) (G : GridParams) (X R : ℕ) :
    bigAvgA a bb G X R ≤ ∑ k ∈ Finset.Icc 1 Ca, bigAvgS (fun p => k ≤ a p) bb G X R := by
  classical
  have hb : ∀ (n : ℕ) (u : Fin G.K → Fin G.s),
      blockSum bb G (fun m => ((omegaBigA a R G.P₀ m : ℕ) : ℝ)) n u
        = ∑ k ∈ Finset.Icc 1 Ca,
            blockSum bb G (fun m => ((omegaBigS (fun p => k ≤ a p) R G.P₀ m : ℕ) : ℝ)) n u := by
    intro n u
    rw [← blockSum_sum]
    refine blockSum_congr bb G u fun α jj => ?_
    rw [omegaBigA_layer_cake a hCa]
    push_cast
    rfl
  have hswap : ∑ k ∈ Finset.Icc 1 Ca, bigAvgS (fun p => k ≤ a p) bb G X R
      = ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
          (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, ∑ k ∈ Finset.Icc 1 Ca,
            |blockSum bb G (fun m => ((omegaBigS (fun p => k ≤ a p) R G.P₀ m : ℕ) : ℝ)) n
              (G.rowEquiv.symm ν)| := by
    unfold bigAvgS
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_comm
  rw [hswap]
  unfold bigAvgA
  have hcard : (0 : ℝ) ≤ ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ := by positivity
  have hrd : (0 : ℝ) ≤ (G.rDim : ℝ)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) hcard
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ν _ => ?_) hrd
  rw [hb n (G.rowEquiv.symm ν)]
  exact Finset.abs_sum_le_sum_abs _ _

/-- **`bigAvgA` in closed form**: the subset bound, times `Ca`. -/
theorem bigAvgA_le' {Ca : ℕ} (hCa : ∀ p, a p ≤ Ca) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams)
    (X R Y : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty)
    (hK : 0 < G.K) (hR : 2 ≤ R) (hRY : R ≤ Y) {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    (hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx) :
    bigAvgA a bb G X R
      ≤ (Ca : ℝ) * (Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R))
            * rowL2 bb G.K
          + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
        + (Real.log Mx / Real.log Y) * rowL1 bb G.K) := by
  classical
  refine (bigAvgA_le_sum a hCa bb G X R).trans ?_
  calc ∑ k ∈ Finset.Icc 1 Ca, bigAvgS (fun p => k ≤ a p) bb G X R
      ≤ ∑ _k ∈ Finset.Icc 1 Ca, (Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y)
              - Real.log (Nat.log 2 R)) * rowL2 bb G.K
            + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
          + (Real.log Mx / Real.log Y) * rowL1 bb G.K) :=
        Finset.sum_le_sum fun k _ =>
          bigAvgS_le' (fun p => k ≤ a p) bb hbb G X R Y hne hK hR hRY hMx1 hMx
    _ = _ := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num

/-! ### The far tail at a scaled dominating weight -/

/-- `w_{a,c} ≤ Ca · w_c` pointwise, for `1 ≤ Ca`. -/
lemma weightAW_le_smul {Ca : ℕ} (hCa : ∀ p, a p ≤ Ca) (h1 : 1 ≤ Ca) (m : ℕ) :
    weightAW a c m ≤ (Ca : ℝ) * weightW c m := by
  have hom : omegaW a m ≤ (Ca : ℝ) * omegaR m := by
    unfold omegaW omegaR
    rw [cardDistinctFactors_eq_card_primeFactors]
    calc ∑ p ∈ m.primeFactors, (a p : ℝ)
        ≤ ∑ _p ∈ m.primeFactors, (Ca : ℝ) :=
          Finset.sum_le_sum fun p _ => by exact_mod_cast hCa p
      _ = (m.primeFactors.card : ℝ) * (Ca : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Ca : ℝ) * (m.primeFactors.card : ℝ) := by ring
  have hex : (0 : ℝ) ≤ excess c m := excess_nonneg m
  have hCa1 : (1 : ℝ) ≤ (Ca : ℝ) := by exact_mod_cast h1
  unfold weightAW weightW
  nlinarith

/-- **The far average at a scaled dominating weight** — `farAvgW_le_effC` with `weightW c`
replaced by `Ka · weightW c`, which is what a general bounded `a` needs. -/
theorem farAvgW_le_effC_smul (c : ℕ → ℕ) {A : ℝ} (hT : Tame c A) (bb : ℕ) (hbb : 3 ≤ bb)
    (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    (hΩ : (1 : ℝ) ≤ ((Ω G.P₀ : ℕ) : ℝ)) {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (W : TWeight)
    {Ka : ℝ} (hKa : 0 ≤ Ka) (hW : ∀ m : ℕ, ((W.wN m : ℕ) : ℝ) ≤ Ka * weightW c m) :
    farAvgW W bb G X
      ≤ (Ka * effC c G.P₀ A) * ((2 : ℝ) ^ G.K *
          ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
              + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
            + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
                / ((apSample X G.P₀ G.b₀).card : ℝ))) := by
  have heff : (0 : ℝ) ≤ effC c G.P₀ A := effC_nonneg (c := c) hT.one_le G.P₀
  refine farAvgW_le_of_layer W (fun m => Ka * weightW c m) hW bb hbb G X hne hP₀ hDm
    (by positivity) (fun α j hj => ?_)
  have h := sum_weightW_shiftG_le_effC c hT G X hne hP₀ hΩ hDm α hj
  rw [← Finset.mul_sum]
  calc Ka * ∑ n ∈ apSample X G.P₀ G.b₀, weightW c (n + shiftG G.B G.Q G.D₀ α j)
      ≤ Ka * (effC c G.P₀ A * ((apSample X G.P₀ G.b₀).card
            * ((farC G X Dm + 2 * j) / Real.log 2 + ((Ω G.P₀ : ℕ) : ℝ))
          + junkShiftBound G.P₀ X (j * Dm))) := by gcongr
    _ = _ := by ring

/-! ### §4D for the master weight from the closed-form bounds -/

/-- **§4D for `w_{a,c}` at the effective constant** — the `a`-weighted analogue of
`gridFrameW_weightSU_propD_of_bounds`.  The general bounded `a` costs a factor `Ca` in the
large-prime and far fields, and nothing at all in the valuation junk. -/
theorem gridFrameWA_weightA_propD_of_bounds {Ca : ℕ} (hCa : ∀ p, a p ≤ Ca) (h1 : 1 ≤ Ca)
    {A : ℝ} (hT : Tame c A)
    (bb : ℕ) (hbb : 3 ≤ bb) (G : GridParams)
    (X R Y : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (hP₀ : 0 < G.P₀)
    (hΩ : (1 : ℝ) ≤ ((Ω G.P₀ : ℕ) : ℝ))
    (hK : 0 < G.K) (hR : 2 ≤ R) (hRY : R ≤ Y) {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    (hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) {ρmax : ℕ}
    (hρm : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ ρmax)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {δbig δjunk δfar : ℝ}
    (hbig : (Ca : ℝ) * (Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R))
            * rowL2 bb G.K
          + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
        + (Real.log Mx / Real.log Y) * rowL1 bb G.K) ≤ δbig * (ε * η))
    (hjunk : (effC c G.P₀ A * junkShiftBound G.P₀ X ρmax
          / ((apSample X G.P₀ G.b₀).card : ℝ)) * rowL1 bb G.K ≤ δjunk * (ε * η))
    (hfar : ((Ca : ℝ) * effC c G.P₀ A) * ((2 : ℝ) ^ G.K *
        ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
            + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
          + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
              / ((apSample X G.P₀ G.b₀).card : ℝ))) ≤ δfar * (ε * η)) :
    (gridFrameWA (TWeight.weightA a c hCa hT) a bb (by omega) G X hne
      ((smallPrimes R G.P₀).filter (fun p => 1 ≤ a p))
      (frozenGammaAC a c bb G) hη hε D).PropD (δbig + δjunk + δfar) := by
  refine gridFrameWA_weightAC_propD a c (TWeight.weightA a c hCa hT)
    (TWeight.weightA_wN a c hCa hT) bb (by omega) G X hne R hη hε D
    ((bigAvgA_le' a hCa bb (by omega) G X R Y hne hK hR hRY hMx1 hMx).trans hbig) ?_ ?_
  · refine (junkAvgC_le' c bb (by omega) G X hne hP₀ hρm).trans (le_trans ?_ hjunk)
    have h := junkShiftBoundC_le_effC hT G.P₀ X ρmax
    have hrow : 0 ≤ rowL1 bb G.K :=
      rowL1_nonneg (by exact_mod_cast (show 2 ≤ bb by omega) : (2:ℝ) ≤ bb) G.K
    have hc : (0 : ℝ) < ((apSample X G.P₀ G.b₀).card : ℝ) := by
      exact_mod_cast hne.card_pos
    gcongr
  · refine (farAvgW_le_effC_smul c hT bb hbb G X hne hP₀ hΩ hDm (TWeight.weightA a c hCa hT)
      (by positivity) (fun m => ?_)).trans hfar
    rw [TWeight.weightA_wN a c hCa hT]
    exact weightAW_le_smul a c hCa h1 m

end NormalNumbers.G4
