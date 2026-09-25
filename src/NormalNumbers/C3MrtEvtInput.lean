/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtDepthInput

/-!
# The open input at all LARGE `K` only

Lap 94 cut the open statement down to one explicit sequence, but the headline still asked it
at **every** `K`:

    conjC3_of_geom_input_depth : (∀ b ≥ 3, ∀ h' primitive, ∀ K, KPointNoExcDepth …) → ConjC3

The chain only ever evaluates the input at `K = KN N = max 1 (depthSlow b N - v)`, and
`KN N → ∞`.  So each fixed `K` is consulted at only finitely many `N`, and a `Tendsto … (𝓝 0)`
conclusion cannot see finitely many `N`.  Hence the input is needed only **eventually in `K`**:

    conjC3_of_geom_input_evt :
      (∀ b ≥ 3, ∀ h' : ℤ, ¬ (b:ℤ) ∣ h' → ∀ᶠ K in atTop,
          KPointNoExcDepth b h' (cKgeom c₀ θ b) (CstKdeg m) K) → ConjC3     (0 < θ < 1)

This is a genuine narrowing on the ledger: the small-`K` rungs — in particular `K = 2`, the only
rung anywhere near the literature — are no longer assumed at all.  The open statement is purely
asymptotic in the number of correlation points.

The mechanism is one line: in `depthAvg_gen_tendsto_of_unif_depth` the input is applied inside a
`filter_upwards`, so `hKNtop.eventually hin` joins that list.  Everything else is lap 94
verbatim with `hKNtop : Tendsto KN atTop atTop` threaded through;
`tendsto_KNslow_atTop` supplies it at the one `KN` the chain uses.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- The diagonal level schedule `KN N = max 1 (depthSlow b N - v)` tends to infinity. -/
theorem tendsto_KNslow_atTop {b : ℕ} (hb : 2 ≤ b) (v : ℕ) :
    Tendsto (fun N : ℕ => max 1 (depthSlow b N - v)) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun c => ?_
  obtain ⟨N₀, hN₀⟩ := (tendsto_atTop_atTop.1 (tendsto_depthSlow hb)) (v + c)
  exact ⟨N₀, fun N hN => le_trans (by have := hN₀ N hN; omega) (le_max_right _ _)⟩

/-- **The `depthAvg` diagonal from the input at LARGE `K` only.**  Lap 94's
`depthAvg_gen_tendsto_of_unif_depth` with `∀ K` weakened to `∀ᶠ K in atTop`. -/
theorem depthAvg_gen_tendsto_of_unif_evt {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    {cK CstK : ℕ → ℝ} (hc : ∀ K, 0 < cK K) (hC : ∀ K, 0 < CstK K)
    (KN : ℕ → ℕ) (hKN : ∀ N, 0 < KN N) (hKNtop : Tendsto KN atTop atTop)
    (hin : ∀ᶠ K in atTop, KPointNoExcDepth b hh cK CstK K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b hh 0)) X L)
    (Athr : ℕ → ℕ) (hA2 : ∀ K, 2 ≤ Athr K)
    (hAthr : ∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * cK K))
    (k₀ : ℕ → ℕ)
    (hsched : Tendsto (fun N : ℕ =>
        windowPhi cK CstK κ (KN N) (Q * primorial P)
            (Athr (KN N)) (N / 2 ^ k₀ N)
          + (1 / 2 : ℝ) ^ k₀ N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh (KN N) N) atTop (𝓝 0) := by
  classical
  have hM0 : 0 < Q * primorial P := Nat.mul_pos hQ (primorial_pos P)
  set M₀ : ℕ := Q * primorial P with hM₀def
  set Ψ : ℕ → ℝ := fun N =>
    windowPhi cK CstK κ (KN N) M₀ (Athr (KN N))
        (N / 2 ^ k₀ N)
      + (1 / 2 : ℝ) ^ k₀ N with hΨdef
  have hT1 : Tendsto (fun N : ℕ => (M₀ : ℝ) * (((M₀ : ℝ) + 2)) / (N : ℝ)) atTop (𝓝 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul ((M₀ : ℝ) * ((M₀ : ℝ) + 2))
    rw [mul_zero] at this
    exact this.congr fun N => by ring
  have hT2 : Tendsto
      (fun N : ℕ => (M₀ : ℝ) * (((Nat.log 2 (N + M₀) + 1 : ℕ) : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
    have := (tendsto_natLog_shift_div M₀).const_mul ((M₀ : ℝ))
    rwa [mul_zero] at this
  have hone : Tendsto (fun N : ℕ => 1 + (M₀ : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul ((M₀ : ℝ))
    rw [mul_zero] at this
    have h2 : Tendsto (fun N : ℕ => (M₀ : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      this.congr fun N => by ring
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add h2
  have hT3 : Tendsto (fun N : ℕ => (M₀ : ℝ) * Ψ N * (1 + (M₀ : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
    have hΨ0 : Tendsto Ψ atTop (𝓝 0) := hsched
    have := ((hΨ0.const_mul ((M₀ : ℝ))).mul hone)
    simpa using this
  have hmaj : Tendsto (fun N : ℕ =>
      (M₀ : ℝ) * (((M₀ : ℝ) + 2)) / (N : ℝ)
        + (M₀ : ℝ) * (((Nat.log 2 (N + M₀) + 1 : ℕ) : ℝ) / (N : ℝ))
        + (M₀ : ℝ) * Ψ N * (1 + (M₀ : ℝ) / (N : ℝ))) atTop (𝓝 0) := by
    simpa using (hT1.add hT2).add hT3
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [Filter.eventually_ge_atTop (M₀ + 1), hKNtop.eventually hin] with N hN hinN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hstep := depthAvg_le_depth hQ P j hh (hKN N) (hc _) (hC _) hinN
    hκ hκ1 hnp (hA2 _) (hAthr _) (show M₀ < N by omega) (k₀ N)
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  ring

set_option maxHeartbeats 1600000 in
/-- Lap 94's `depthAvg_gen_tendsto_of_geom_slow_depth` at large `K` only. -/
theorem depthAvg_gen_tendsto_of_geom_slow_evt {b Q : ℕ} (hb : 2 ≤ b) (hQ : 0 < Q)
    (P j : ℕ) (hh : ℤ)
    {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (KN : ℕ → ℕ) (hKN : ∀ N, 0 < KN N) (hKNtop : Tendsto KN atTop atTop)
    (hKle : ∀ᶠ N : ℕ in atTop, KN N ≤ depthSlow b N)
    (hin : ∀ᶠ K in atTop, KPointNoExcDepth b hh (cKgeom c₀ θ b) (CstKdeg m) K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b hh 0)) X L)
    (Athr : ℕ → ℕ) (hA2 : ∀ K, 2 ≤ Athr K)
    (hAthr : ∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * cKgeom c₀ θ b K))
    (hAle : ∀ᶠ N : ℕ in atTop, Athr (KN N) ≤ N / 2 ^ (Nat.log 2 (Nat.log 2 N))) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh (KN N) N) atTop (𝓝 0) := by
  have hb0 : 0 < b := by omega
  have hk₀ : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop :=
    (PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
      (PairDecouple.tendsto_natLog_atTop 2 le_rfl)
  have hbase : ∀ᶠ N : ℕ in atTop,
      0 < 2 * Real.log ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ) := by
    filter_upwards [tendsto_cut_atTop.eventually_ge_atTop 2] with N hN
    have h2 : (2 : ℝ) ≤ ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ) := by exact_mod_cast hN
    have hlog : 0 < Real.log ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ) :=
      Real.log_pos (by linarith)
    linarith
  have hrate := rate_tendsto_of_exponent (cK := cKgeom c₀ θ b) (CstK := CstKdeg m)
    (fun K => CstKdeg_pos m K) (κ := κ) (M₀ := Q * primorial P) KN
    (fun N => N / 2 ^ (Nat.log 2 (Nat.log 2 N))) hbase
    (exponent_tendsto_atBot_of_geom_slow hb hc₀ hθ0 hθ hκ m KN hKle)
  have hΦ := windowPhi_diag_tendsto (cK := cKgeom c₀ θ b) (CstK := CstKdeg m) (κ := κ)
    (M₀ := Q * primorial P) KN (fun N => Athr (KN N))
    (fun N => N / 2 ^ (Nat.log 2 (Nat.log 2 N)))
    (fun N => hA2 _) (fun K => (CstKdeg_pos m K).le) hAle hrate
  have hhalf : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ (Nat.log 2 (Nat.log 2 N))) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hk₀
  refine depthAvg_gen_tendsto_of_unif_evt hQ P j hh (fun K => cKgeom_pos hc₀ hb0 K)
    (fun K => CstKdeg_pos m K) KN hKN hKNtop hin hκ hκ1 hnp Athr hA2 hAthr
    (fun N => Nat.log 2 (Nat.log 2 N)) ?_
  simpa using hΦ.add hhalf

/-- **`DepthDiagonalSlow b` from the input at LARGE `K` only.** -/
theorem depthDiagonalSlow_of_geom_evt {b : ℕ} (hb : 2 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∀ᶠ K in atTop, KPointNoExcDepth b h' (cKgeom c₀ θ b) (CstKdeg m) K)
    (hthr : ∀ P Q : ℕ, 0 < Q → KPointThresholdSlow b Q P (cKgeom c₀ θ b)) :
    DepthDiagonalSlow b := by
  intro P Q j hh hQ hj0 hjQ
  have hb0 : 0 < b := by omega
  rcases eq_or_ne hh 0 with rfl | hne
  · exact depthAvg_zero_tendsto b P Q j hj0 hjQ
  obtain ⟨v, h', hfac, hnd⟩ := exists_pow_mul_not_dvd hb hh hne
  subst hfac
  set z : ℂ := depthRoot b h' 0 with hzdef
  have hznorm : ‖z‖ = 1 := norm_ee_real _
  have hz1 : z ≠ 1 := depthRoot_ne_one_of_not_dvd hb0 hnd
  set κ : ℝ := ttExponent z with hκdef
  have hκ : 0 < κ := ttExponent_pos hznorm hz1
  have hκ1 : κ ≤ 1 := ttExponent_le_one hznorm
  have hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b h' 0)) X L :=
    ttNonPretentious_zOmegaNat hznorm hz1 le_rfl
  obtain ⟨Athr, hA2, hAthr, hAcut⟩ := hthr P Q hQ κ hκ hκ1
  set KN : ℕ → ℕ := fun N => max 1 (depthSlow b N - v) with hKNdef
  have hKN : ∀ N, 0 < KN N := fun N => lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hKNtop : Tendsto KN atTop atTop := tendsto_KNslow_atTop hb v
  have hvN := (tendsto_depthSlow hb).eventually_ge_atTop (v + 1)
  have hKle : ∀ᶠ N : ℕ in atTop, KN N ≤ depthSlow b N := by
    filter_upwards [hvN] with N hN
    rw [hKNdef]; simp only; omega
  have hKeq : ∀ᶠ N : ℕ in atTop, KN N = depthSlow b N - v := by
    filter_upwards [hvN] with N hN
    rw [hKNdef]; simp only; omega
  have hAle : ∀ᶠ N : ℕ in atTop,
      Athr (KN N) ≤ N / 2 ^ (Nat.log 2 (Nat.log 2 N)) := by
    filter_upwards [hAcut, hKle] with N hcut hle
    exact hcut _ hle
  have hgen := depthAvg_gen_tendsto_of_geom_slow_evt hb hQ P j h' hc₀ hθ0 hθ m KN hKN hKNtop hKle
    (hin h' hnd) hκ hκ1 hnp Athr hA2 hAthr hAle
  have hprim : Tendsto (fun N : ℕ =>
      depthAvg b P Q j h' (depthSlow b N - v) N) atTop (𝓝 0) := by
    refine hgen.congr' ?_
    filter_upwards [hKeq] with N hN
    rw [hN]
  exact depthAvg_dvd_tendsto_of_primitive_sched hb P Q j h' v (depthSlow b)
    (tendsto_depthSlow hb) hprim

/-- **THE C3 CRUX FROM THE INPUT AT LARGE `K` ONLY.** -/
theorem weylLambertTwist_of_geom_input_evt {b : ℕ} (hb : 3 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∀ᶠ K in atTop, KPointNoExcDepth b h' (cKgeom c₀ θ b) (CstKdeg m) K) :
    WeylLambertTwist b :=
  weylLambertTwist_of_depthDiagonalSlow hb
    (depthDiagonalSlow_of_geom_evt (by omega) hc₀ hθ0 hθ m hin
      fun P Q _ => kPointThresholdSlow_of_geom (by omega) Q P hc₀ hθ0 hθ)

/-- **`ConjC3` FROM THE INPUT AT LARGE `K` ONLY.**  No small-`K` rung is assumed — in
particular `K = 2`, the only rung near the literature, is not used.  The open statement is
asymptotic in the number of correlation points. -/
theorem conjC3_of_geom_input_evt {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ b : ℕ, 3 ≤ b → ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∀ᶠ K in atTop, KPointNoExcDepth b h' (cKgeom c₀ θ b) (CstKdeg m) K) :
    ConjC3 :=
  conjC3_of_weylLambertTwist fun b hb =>
    weylLambertTwist_of_geom_input_evt hb hc₀ hθ0 hθ m (hin b hb)

/-- Nothing is given up: the lap-94 input implies the lap-95 one. -/
theorem conjC3_of_geom_input_depth' {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ b : ℕ, 3 ≤ b → ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∀ K, KPointNoExcDepth b h' (cKgeom c₀ θ b) (CstKdeg m) K) :
    ConjC3 :=
  conjC3_of_geom_input_evt hc₀ hθ0 hθ m
    fun b hb h' hh' => Filter.Eventually.of_forall (hin b hb h' hh')

#print axioms NormalNumbers.CastingOut.tendsto_KNslow_atTop
#print axioms NormalNumbers.CastingOut.depthAvg_gen_tendsto_of_unif_evt
#print axioms NormalNumbers.CastingOut.depthDiagonalSlow_of_geom_evt
#print axioms NormalNumbers.CastingOut.weylLambertTwist_of_geom_input_evt
#print axioms NormalNumbers.CastingOut.conjC3_of_geom_input_evt
#print axioms NormalNumbers.CastingOut.conjC3_of_geom_input_depth'

end CastingOut

end NormalNumbers
