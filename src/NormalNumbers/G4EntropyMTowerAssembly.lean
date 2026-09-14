/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyMTowerDown

/-!
# The marched ladder, step 5: **`entropy_E1_march`** and the scale gap closed

The assembly.  `entropy_E1_down`'s proof, verbatim, with the marched parameters
`R ↦ Rm K j`, `Y ↦ Ym K j`, `Mc ↦ Mcm K j`, and the outer scale `X'` anywhere in the marched
window `[Xlom K j, Xm K j]`.  Its three inputs are the ported ones:

* `hbig_small_down_m` and `hfar_small_down_m` (`G4EntropyMTowerDown`);
* `smallPrime_term_tiny_down_m` (`G4EntropyMTowerBudget`).

Everything else in the E1 cone is literally `R`/`Y`/`Mc`-free — the cover term, the Jackson
term, `PropC`'s combinatorics and the budget arithmetic — so it is reused unchanged.

The endpoint is `entropy_E1_tile`: the E1 conclusion at **every** outer scale in
`[Xlo K, Xlo (K+4)]`, i.e. the outer-scale gap of `G4EntropyScaleGap` closed unconditionally by
the two-dimensional `(K, j)` ladder.
-/

open Finset Real MeasureTheory
open scoped BigOperators Nat

namespace NormalNumbers.G4

namespace Sched

open NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

set_option maxHeartbeats 4000000 in
/-- **The E1 chain at the marched parameters `(K, j)`.**  `entropy_E1_down` is the `j = 0`
instance (`entropy_E1_march_zero` below). -/
theorem entropy_E1_march {K k₄ j X' : ℕ} (hK4 : K = 4 * k₄) (hK : 160000 ≤ K)
    (hj : j ≤ jstar K) (hlo : Xlom K j ≤ X') (hhi : X' ≤ Xm K j)
    (hb : (gridOf K (N K) (show 1 ≤ K by omega)).b₀ < X') :
    (k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
        - 50 * Real.sqrt K * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
      < (jointLaw (gridOf K (N K) (show 1 ≤ K by omega)) hb k₄ (primeLambertAtBase 4)).H₂ := by
  have hK100 : 100 ≤ K := by omega
  have hK1 : 1 ≤ K := by omega
  have hk : 25 ≤ k₄ := by omega
  have hKr : (160000 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hS0 : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.2 hKpos
  have hSsq : Real.sqrt K * Real.sqrt K = (K : ℝ) := Real.mul_self_sqrt (by positivity)
  have hS400 : (400 : ℝ) ≤ Real.sqrt K := by
    have h : Real.sqrt (160000 : ℝ) ≤ Real.sqrt K := Real.sqrt_le_sqrt hKr
    have he : Real.sqrt (160000 : ℝ) = 400 := by
      rw [show (160000 : ℝ) = 400 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [he ▸ h]
  set δ : ℝ := 200 / Real.sqrt K with hδdef
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ hS0 (by norm_num)]
    linarith
  have hδ1 : δ < 1 := by linarith
  set G := gridOf K (N K) hK1 with hGdef
  set η : ℝ := (1 / 2 : ℝ) ^ k₄ with hηdef
  have hη : (0 : ℝ) < η := by rw [hηdef]; positivity
  set ε : ℝ := 1 / (K : ℝ) with hεdef
  have hε : (0 : ℝ) < ε := by rw [hεdef]; positivity
  set hne := NormalNumbers.G4Entropy.apSample_nonempty G hb with hnedef
  set fr := gridFrame 4 (by norm_num) G X' hne (smallPrimes (Rm K j) G.P₀)
    (frozenGamma 4 G) hη hε (DjE K k₄) with hfrdef
  choose θr hθr using fun ν => QuotientAddGroup.mk_surjective (fr.θ ν)
  choose γr hγr using fun ν => QuotientAddGroup.mk_surjective (fr.γ ν)
  set M : ℝ := (k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ) with hMdef
  have hHcast : (0 : ℝ) < (((K ^ 2 + 1) ^ K : ℕ) : ℝ) := by
    have : 0 < (K ^ 2 + 1) ^ K := Nat.pow_pos (by positivity)
    exact_mod_cast this
  have hk₄pos : (0 : ℝ) < (k₄ : ℝ) := by exact_mod_cast (show 0 < k₄ by omega)
  have hMpos : (0 : ℝ) < M := by rw [hMdef]; positivity
  -- (1) the cover term
  have hcover : (2 : ℝ) ^ ((1 - δ / 2) * M)
      * (∑ G' ∈ fr.goodSets, η ^ G'.card * (volume (fr.pieceCube G')).toReal)
      ≤ (1 / 8 : ℝ) / 2 ^ K := by
    refine entropy_cover_sum_le 4 (by norm_num) G X' hne _ _ hη hε (DjE K k₄)
      (Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K))
      (by rw [hεdef, div_lt_one (by linarith)]; linarith)
      (Nat.one_le_pow _ _ (show 0 < K ^ 2 by positivity)) ?_ (by positivity) (by positivity) ?_
    · have h := log_det_one_add_tensorGram_le' (K := K) hK1
      show Real.log (1 + tensorGram G.K G.s).det
        ≤ (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)
      push_cast
      exact h
    · intro g hglo hghi
      have h := entropy_cover_bound (K := K) (m := k₄) (g := g) (η := η)
        (Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)) (δ := δ)
        (by omega) ?_ hδ0.le hδ1.le ?_ hη ?_ le_rfl ?_ ?_
      · refine h.trans_eq ?_
        show (1 / 8 : ℝ) / 2 ^ (K + (K ^ 2) ^ K) = (1 / 8 : ℝ) / 2 ^ K / 2 ^ G.rDim
        rw [show G.rDim = (K ^ 2) ^ K from rfl, pow_add]
        field_simp
      · rw [hK4]; push_cast; ring_nf; rfl
      · have hl2 : (0.6931 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        have hδK : δ * (K : ℝ) = 200 * Real.sqrt K := by
          rw [hδdef, div_mul_eq_mul_div, eq_comm, eq_div_iff hS0.ne']
          rw [mul_assoc, hSsq]
        rw [hδK]
        nlinarith [hS400, hl2, hS0]
      · rw [hηdef, ← pow_mul, hK4, mul_comm]
      · exact hglo
      · exact hghi
  -- (2) the Jackson term
  have hjack : 2 * (1 / (fr.res * Real.sqrt ((DjE K k₄ : ℕ) + 1))) ≤ 1 / (8 * K) := by
    have h := jackson_term_small (K := K) (k₄ := k₄) hK1
    have hres : fr.res = (1 / (K : ℝ)) * (1 / 2 : ℝ) ^ k₄ := by rw [hfrdef]; rfl
    rw [hres]
    exact h
  -- (3) `PropD`
  have hD : fr.PropD ((1 / 2 : ℝ) ^ k₄ + (1 / 2 : ℝ) ^ k₄) := by
    refine gridFrame_propD_of_bounds 4 (by norm_num) G X' (Rm K j) (Ym K j) hne
      (show 0 < K from hK1) (Rm_ge_two K j) (Rm_le_Ym K j)
      (Mx := ((X' + J K * gridDm K (N K) : ℕ) : ℝ)) ?_ ?_
      (Dm := gridDm K (N K)) (gridOf.d_le hK1) hη hε (DjE K k₄) ?_ ?_
    · have : 1 ≤ X' := by have := Xlom_pos K j; omega
      exact_mod_cast le_add_right this
    · exact fun n hn i => by exact_mod_cast gridOf.add_shiftAL_le hK1 hn i
    · have h := hbig_small_down_m hK4 hK100 hlo hhi
      simp only [Nat.cast_ofNat, rowL1_four, rowL2_four, hεdef, hηdef,
        show G.K = K from rfl, show G.b₀ = (gridOf K (N K) hK1).b₀ from rfl]
      ring_nf
      ring_nf at h
      linarith
    · have h := hfar_small_down_m hK4 hK100 hj hlo hhi
      simp only [Nat.cast_ofNat, farBound_four, hεdef, hηdef,
        show G.K = K from rfl, show G.N = N K from rfl]
      exact h
  -- (4) `PropC` and the small-prime term
  set δ₃ : ℝ := smallPrimeBound (smallPrimes (Rm K j) G.P₀) (Fintype.card G.Idx) (Rm K j)
    (Mcm K j) (apSample X' G.P₀ G.b₀).card (Real.exp 1) (13 / 2)
    (1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ G.K) with hδ₃def
  have hC : fr.PropC δ₃ :=
    gridFrame_propC_four G X' hne _ _ hη hε (R := Rm K j)
      (fun p hp => (mem_smallPrimes.1 hp).1) (fun p hp => (mem_smallPrimes.1 hp).2.2)
      (by have := Rm_ge_two K j; omega) (fun p hp => (mem_smallPrimes.1 hp).2.1)
      (by
        show 1 + Nat.clog 4 (2 ^ K * DjE K k₄) ≤ N K
        have h := (Nat.clog_le_iff_le_pow (by norm_num)).2 (two_pow_mul_DjE_le hK4 hK100)
        have hN : 1 ≤ N K := N_pos hK1
        omega)
      (Mcm_pos hK1 j) (Real.one_le_exp zero_le_one) (by norm_num)
  have hδ₃nn : (0 : ℝ) ≤ δ₃ :=
    smallPrimeBound_nonneg _ _ _ _ _ (by positivity) (by norm_num)
  have hsmall : (((2 * DjE K k₄ + 1) ^ G.rDim : ℕ) : ℝ) * δ₃ ≤ (1 / 8 : ℝ) / 2 ^ K := by
    have h := smallPrime_term_tiny_down_m hK4 hK100 hj hlo
    have hcard : Fintype.card G.Idx = T K := gridOf.card_Idx hK1
    rw [hδ₃def, hcard]
    exact h
  -- ### assemble
  have hmη : ((2 : ℝ)⁻¹) ^ k₄ ≤ η := by rw [hηdef]; norm_num
  have hmain := NormalNumbers.G4Entropy.entropy_gt_of_budget G X' hb (by norm_num)
    (smallPrimes (Rm K j) G.P₀) (frozenGamma 4 G) hη hε (DjE K k₄) k₄ θr γr hθr hγr hmη
    (δ := δ) (M := M) hδ0 hδ1 hMpos hD hC hδ₃nn ?_
  · have he : (1 - δ) * M
        = (k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
          - 50 * Real.sqrt K * (((K ^ 2 + 1) ^ K : ℕ) : ℝ) := by
      have hk4 : (k₄ : ℝ) = (K : ℝ) / 4 := by rw [hK4]; push_cast; ring
      rw [hMdef, hδdef, hk4]
      field_simp
      nlinarith [hSsq, hS0, hHcast]
    rw [he] at hmain
    exact hmain
  · have h2K : (K : ℝ) ≤ (2 : ℝ) ^ K := by
      have : K < 2 ^ K := Nat.lt_two_pow_self
      exact_mod_cast this.le
    have hk₄2 : (k₄ : ℝ) ≤ (2 : ℝ) ^ k₄ := by
      have : k₄ < 2 ^ k₄ := Nat.lt_two_pow_self
      exact_mod_cast this.le
    have e1 : (1 / 8 : ℝ) / 2 ^ K ≤ 5 / (K : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hKpos]
      nlinarith [h2K, hKpos]
    have ehalf : (1 / 2 : ℝ) ^ k₄ ≤ 5 / (K : ℝ) := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ k₄ := by positivity
      have he : (1 / 2 : ℝ) ^ k₄ = 1 / (2 : ℝ) ^ k₄ := by rw [one_div_pow]
      rw [he, div_le_div_iff₀ hpos hKpos]
      have hKk : (K : ℝ) = 4 * (k₄ : ℝ) := by rw [hK4]; push_cast; ring
      nlinarith [hk₄2, hpos]
    have e2 : 2 * (1 / (fr.res * Real.sqrt ((DjE K k₄ : ℕ) + 1))) ≤ 5 / (K : ℝ) := by
      refine hjack.trans ?_
      rw [div_le_div_iff₀ (by positivity) hKpos]
      linarith
    have h2d : (0 : ℝ) < 2 - δ := by linarith
    have hRHS : (100 : ℝ) / Real.sqrt K ≤ δ / (2 - δ) := by
      have hmono : δ / 2 ≤ δ / (2 - δ) :=
        div_le_div_of_nonneg_left hδ0.le h2d (by linarith)
      have hδ2 : δ / 2 = 100 / Real.sqrt K := by rw [hδdef]; ring
      linarith [hmono, hδ2.le, hδ2.ge]
    set B : ℝ := 5 / (K : ℝ) with hBdef
    have h25 : 5 * B < 100 / Real.sqrt K := by
      rw [hBdef, show (5 : ℝ) * (5 / (K : ℝ)) = 25 / (K : ℝ) by ring,
        div_lt_div_iff₀ hKpos hS0]
      nlinarith [hS400, hS0, hSsq]
    clear_value B
    have hfreq : gridFrame 4 (by norm_num) G X'
        (NormalNumbers.G4Entropy.apSample_nonempty G hb) (smallPrimes (Rm K j) G.P₀)
        (frozenGamma 4 G) hη hε (DjE K k₄) = fr := rfl
    rw [hfreq]
    refine lt_of_le_of_lt (b := 5 * B) ?_ (lt_of_lt_of_le h25 hRHS)
    have t1 := hcover.trans e1
    have t2 := hsmall.trans e1
    set C : ℝ := (2 : ℝ) ^ ((1 - δ / 2) * M)
      * ∑ G' ∈ fr.goodSets, η ^ G'.card * (volume (fr.pieceCube G')).toReal with hCdef
    set S : ℝ := (((2 * DjE K k₄ + 1) ^ G.rDim : ℕ) : ℝ) * δ₃ with hSdef
    set J : ℝ := 2 * (1 / (fr.res * Real.sqrt ((DjE K k₄ : ℕ) + 1))) with hJdef
    set h₂ : ℝ := (1 / 2 : ℝ) ^ k₄ with hh₂def
    clear_value C S J h₂
    linarith only [t1, t2, e2, ehalf]

set_option maxHeartbeats 1000000 in
/-- The `j = 0` instance of `entropy_E1_march` **is** `entropy_E1_down` — a check that the
marched definitions line up with the implemented schedule. -/
theorem entropy_E1_march_zero {K k₄ X' : ℕ} (hK4 : K = 4 * k₄) (hK : 160000 ≤ K)
    (hlo : Xlom K 0 ≤ X') (hhi : X' ≤ Xm K 0)
    (hb : (gridOf K (N K) (show 1 ≤ K by omega)).b₀ < X') :
    (k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
        - 50 * Real.sqrt K * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
      < (jointLaw (gridOf K (N K) (show 1 ≤ K by omega)) hb k₄ (primeLambertAtBase 4)).H₂ :=
  entropy_E1_down hK4 hK (by rw [← Xlom_zero]; exact hlo) (by rw [← Xm_zero]; exact hhi)

set_option maxHeartbeats 1000000 in
/-- **THE ENDPOINT — the scale gap closed.**  `entropy_E1_down`'s conclusion at **every** outer
scale in `[Xlo K, Xlo (K+4)]`: the two rungs' certified ranges now meet.  Contrast
`G4EntropyScaleGap.ScheduleWitness.X_lt_Xlo_step`, which shows the *one-dimensional* ladder's
rung `K` reaches only `Xhi K k₄ < Xlo (K+4)`. -/
theorem entropy_E1_tile {K k₄ X' : ℕ} (hK4 : K = 4 * k₄) (hK : 160000 ≤ K)
    (hlo : Xlo K ≤ X') (hhi : X' ≤ Xlo (K + 4))
    (hb : (gridOf K (N K) (show 1 ≤ K by omega)).b₀ < X') :
    (k₄ : ℝ) * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
        - 50 * Real.sqrt K * (((K ^ 2 + 1) ^ K : ℕ) : ℝ)
      < (jointLaw (gridOf K (N K) (show 1 ≤ K by omega)) hb k₄ (primeLambertAtBase 4)).H₂ := by
  obtain ⟨j, hj, hj1, hj2⟩ := exists_tile (show 100 ≤ K by omega) hlo hhi
  exact entropy_E1_march hK4 hK hj hj1 hj2 hb

end Sched

end NormalNumbers.G4
