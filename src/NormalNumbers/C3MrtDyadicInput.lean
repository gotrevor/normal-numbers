/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtEvtInput

/-!
# The open input as ONE EXPLICIT INEQUALITY

Laps 90–95 narrowed the single open statement five times, but `KPointNoExcDepth` still carries
machinery inherited from TT Thm 3.1: a free scale `X`, a free cutoff `L`, the range
`√X ≤ N ≤ X`, and the archimedean hypothesis `∃ i, TTNonPretentious (zOmegaNat (z i)) X L`.
The consumer determines **all** of it: `dyadic_window_bound_at` always takes `X = N²`,
`L = (2 log N)^κ` with `κ = ttExponent (depthRoot b h' 0)`, and always discharges the
non-pretentiousness hypothesis itself at `i = 0` via the unconditional
`ttNonPretentious_zOmegaNat`.

So all of it can be peeled.  `DepthDyadicBound b h' κ cK CstK K` is what remains:

    ‖ ∑_{N < n ≤ 2N, n ≡ r (M)} ∏_{i<K} e(h'/b^{i+1})^{ω(n+i+1)} ‖
        ≤ CstK K · (2 log N)^{-κ·cK K} · N / M

for every `N ≥ 2` past the threshold and every modulus `M` below it.  There is no quantification
over analytic objects left at all: no multiplicative function, no Dirichlet character, no
pretentiousness, no auxiliary scale.  It is an explicit exponential-sum bound, indexed by
`(b, h', K)`.  `depthDyadicBound_of_depth` is exactly `dyadic_window_bound_at`, so the lap-94
input still implies this one; `conjC3_of_geom_input_evt'` recovers lap 95's headline.

Headline of this file:

    conjC3_of_dyadic_input :
      (∀ b ≥ 3, ∀ h' : ℤ, ¬ (b:ℤ) ∣ h' → ∀ᶠ K in atTop,
          DepthDyadicBound b h' (ttExponent (depthRoot b h' 0))
            (cKgeom c₀ θ b) (CstKdeg m) K) → ConjC3          (0 < θ < 1)

The `κ` in the exponent is no longer a free parameter either: it is the `ttExponent` of the
LEADING depth root, the one quantity lap 92 showed cannot be shared across the factors.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- **The open input as one explicit inequality on one explicit exponential sum.**
`κ` is the archimedean saving exponent; `cK`, `CstK` the per-`K` profile. -/
def DepthDyadicBound (b : ℕ) (h' : ℤ) (κ : ℝ) (cK CstK : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ N : ℕ, 2 ≤ N → max 2 ((K : ℝ) + 1) ≤ (2 * Real.log N) ^ (κ * cK K) →
    ∀ M r : ℕ, 0 < M → (M : ℝ) ≤ (2 * Real.log N) ^ (κ * cK K) →
      ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
          ∏ i : Fin K, depthRoot b h' i ^ omegaNat (n + (i : ℕ) + 1)‖
        ≤ CstK K * (2 * Real.log N) ^ (-(κ * cK K)) * (N : ℝ) / (M : ℝ)

/-- Nothing is lost: the lap-94 input implies the explicit inequality.  This IS
`dyadic_window_bound_at`, which is where every one of the peeled quantities was being chosen. -/
theorem depthDyadicBound_of_depth {K : ℕ} (hK : 0 < K) {cK CstK : ℕ → ℝ} {b : ℕ} {h' : ℤ}
    (hin : KPointNoExcDepth b h' cK CstK K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b h' 0)) X L) :
    DepthDyadicBound b h' κ cK CstK K :=
  fun _N hN2 hthr _M r hM hML =>
    dyadic_window_bound_at hK (depthRoot b h') (fun i => by rw [depthRoot]; exact norm_ee_real _)
      hin hκ hκ1 hnp hN2 hthr hM r hML

open scoped Classical in
/-- `DepthDyadicBound` supplies `windowPhi`'s analytic branch. -/
theorem windowPhi_hwin_dy {K : ℕ} {cK CstK : ℕ → ℝ} (hc : 0 < cK K) {b : ℕ} {h' : ℤ}
    {κ : ℝ} (hκ : 0 < κ) (h : DepthDyadicBound b h' κ cK CstK K)
    {M A : ℕ} (hM : 0 < M) (hA2 : 2 ≤ A)
    (hAthr : max (max 2 ((K : ℝ) + 1)) (M : ℝ) ≤ (2 * Real.log A) ^ (κ * cK K))
    (r : ℕ) {a : ℕ} (haA : A ≤ a) :
    ‖∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M),
        ∏ i ∈ range K, depthRoot b h' i ^ omegaNat (n + i + 1)‖
      ≤ CstK K * (2 * Real.log a) ^ (-(κ * cK K)) * (a : ℝ) / (M : ℝ) := by
  classical
  have ha2 : 2 ≤ a := le_trans hA2 haA
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA2
  have hAa : (A : ℝ) ≤ (a : ℝ) := by exact_mod_cast haA
  have hlogA : Real.log 2 ≤ Real.log A := Real.log_le_log (by norm_num) hAR
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogAa : Real.log A ≤ Real.log a := Real.log_le_log (by linarith) hAa
  have hmono : (2 * Real.log A) ^ (κ * cK K) ≤ (2 * Real.log a) ^ (κ * cK K) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (mul_pos hκ hc).le
  have hthr : max 2 ((K : ℝ) + 1) ≤ (2 * Real.log a) ^ (κ * cK K) :=
    le_trans (le_trans (le_max_left _ _) hAthr) hmono
  have hML : (M : ℝ) ≤ (2 * Real.log a) ^ (κ * cK K) :=
    le_trans (le_trans (le_max_right _ _) hAthr) hmono
  have hrw : ∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M),
        ∏ i ∈ range K, depthRoot b h' i ^ omegaNat (n + i + 1)
      = ∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M),
        ∏ i : Fin K, depthRoot b h' i ^ omegaNat (n + (i : ℕ) + 1) :=
    Finset.sum_congr rfl fun n _ =>
      (Fin.prod_univ_eq_prod_range (fun i => depthRoot b h' i ^ omegaNat (n + i + 1)) K).symm
  rw [hrw]
  exact h a ha2 hthr M r hM hML

open scoped Classical in
/-- **The explicit `depthAvg` majorant from the explicit inequality.**  No archimedean
hypothesis appears: it was fully consumed in producing `DepthDyadicBound`. -/
theorem depthAvg_le_dy {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ) {K : ℕ}
    {cK CstK : ℕ → ℝ} (hc : 0 < cK K) (hC : 0 < CstK K)
    {κ : ℝ} (hκ : 0 < κ) (hin : DepthDyadicBound b hh κ cK CstK K)
    {A : ℕ} (hA2 : 2 ≤ A)
    (hAthr : max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log A) ^ (κ * cK K))
    {N : ℕ} (hN : Q * primorial P < N) (k₀ : ℕ) :
    ‖depthAvg b P Q j hh K N‖
      ≤ ((Q * primorial P : ℕ) : ℝ)
          * ((((Q * primorial P : ℕ) : ℝ) + 2)
              + ((Nat.log 2 (N + Q * primorial P) + 1 : ℕ) : ℝ)
            + (windowPhi cK CstK κ K (Q * primorial P) A (N / 2 ^ k₀) + (1 / 2) ^ k₀)
                * ((N : ℝ) + ((Q * primorial P : ℕ) : ℝ)))
        / (N : ℝ) := by
  classical
  have hM0 : 0 < Q * primorial P := Nat.mul_pos hQ (primorial_pos P)
  have hz : ∀ i, ‖depthRoot b hh i‖ = 1 := fun i => by rw [depthRoot]; exact norm_ee_real _
  have hf : ∀ n : ℕ, ‖∏ i ∈ range K, depthRoot b hh i ^ omegaNat (n + i + 1)‖ ≤ 1 := by
    intro n
    simp only [norm_prod, norm_pow]
    have hone : ∀ i ∈ range K, ‖depthRoot b hh i‖ ^ omegaNat (n + i + 1) = 1 := by
      intro i _
      rw [hz i, one_pow]
    rw [Finset.prod_congr rfl hone, Finset.prod_const_one]
  refine depthAvg_le_of_window hQ P j hh
    (windowPhi_nonneg hA2 hC.le)
    (fun a => windowPhi_le_one cK CstK κ K (Q * primorial P) A a)
    (fun {x y} hxy => windowPhi_antitone hA2 hC.le (mul_pos hκ hc).le hxy)
    (fun r a => windowPhi_window_bound hf
      (fun a' ha' => windowPhi_hwin_dy hc hκ hin hM0 hA2 hAthr r ha') a)
    hN k₀

theorem depthAvg_gen_tendsto_of_unif_dy {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    {cK CstK : ℕ → ℝ} (hc : ∀ K, 0 < cK K) (hC : ∀ K, 0 < CstK K)
    (KN : ℕ → ℕ) (hKNtop : Tendsto KN atTop atTop)
    {κ : ℝ} (hκ : 0 < κ)
    (hin : ∀ᶠ K in atTop, DepthDyadicBound b hh κ cK CstK K)
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
  have hstep := depthAvg_le_dy hQ P j hh (hc _) (hC _) hκ hinN
    (hA2 _) (hAthr _) (show M₀ < N by omega) (k₀ N)
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  ring

set_option maxHeartbeats 1600000 in
theorem depthAvg_gen_tendsto_of_geom_slow_dy {b Q : ℕ} (hb : 2 ≤ b) (hQ : 0 < Q)
    (P j : ℕ) (hh : ℤ)
    {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (KN : ℕ → ℕ) (hKNtop : Tendsto KN atTop atTop)
    (hKle : ∀ᶠ N : ℕ in atTop, KN N ≤ depthSlow b N)
    {κ : ℝ} (hκ : 0 < κ)
    (hin : ∀ᶠ K in atTop, DepthDyadicBound b hh κ (cKgeom c₀ θ b) (CstKdeg m) K)
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
  refine depthAvg_gen_tendsto_of_unif_dy hQ P j hh (fun K => cKgeom_pos hc₀ hb0 K)
    (fun K => CstKdeg_pos m K) KN hKNtop hκ hin Athr hA2 hAthr
    (fun N => Nat.log 2 (Nat.log 2 N)) ?_
  simpa using hΦ.add hhalf

/-- **`DepthDiagonalSlow b` from the explicit inequality alone.** -/
theorem depthDiagonalSlow_of_dyadic {b : ℕ} (hb : 2 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∀ᶠ K in atTop, DepthDyadicBound b h' (ttExponent (depthRoot b h' 0))
        (cKgeom c₀ θ b) (CstKdeg m) K)
    (hthr : ∀ P Q : ℕ, 0 < Q → KPointThresholdSlow b Q P (cKgeom c₀ θ b)) :
    DepthDiagonalSlow b := by
  intro P Q j hh hQ hj0 hjQ
  have hb0 : 0 < b := by omega
  rcases eq_or_ne hh 0 with rfl | hne
  · exact depthAvg_zero_tendsto b P Q j hj0 hjQ
  obtain ⟨v, h', hfac, hnd⟩ := exists_pow_mul_not_dvd hb hh hne
  subst hfac
  have hznorm : ‖depthRoot b h' 0‖ = 1 := norm_ee_real _
  have hz1 : depthRoot b h' 0 ≠ 1 := depthRoot_ne_one_of_not_dvd hb0 hnd
  set κ : ℝ := ttExponent (depthRoot b h' 0) with hκdef
  have hκ : 0 < κ := ttExponent_pos hznorm hz1
  have hκ1 : κ ≤ 1 := ttExponent_le_one hznorm
  obtain ⟨Athr, hA2, hAthr, hAcut⟩ := hthr P Q hQ κ hκ hκ1
  set KN : ℕ → ℕ := fun N => max 1 (depthSlow b N - v) with hKNdef
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
  have hgen := depthAvg_gen_tendsto_of_geom_slow_dy hb hQ P j h' hc₀ hθ0 hθ m KN hKNtop hKle
    hκ (hin h' hnd) Athr hA2 hAthr hAle
  have hprim : Tendsto (fun N : ℕ =>
      depthAvg b P Q j h' (depthSlow b N - v) N) atTop (𝓝 0) := by
    refine hgen.congr' ?_
    filter_upwards [hKeq] with N hN
    rw [hN]
  exact depthAvg_dvd_tendsto_of_primitive_sched hb P Q j h' v (depthSlow b)
    (tendsto_depthSlow hb) hprim

/-- **THE C3 CRUX FROM THE EXPLICIT INEQUALITY ALONE.** -/
theorem weylLambertTwist_of_dyadic_input {b : ℕ} (hb : 3 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∀ᶠ K in atTop, DepthDyadicBound b h' (ttExponent (depthRoot b h' 0))
        (cKgeom c₀ θ b) (CstKdeg m) K) :
    WeylLambertTwist b :=
  weylLambertTwist_of_depthDiagonalSlow hb
    (depthDiagonalSlow_of_dyadic (by omega) hc₀ hθ0 hθ m hin
      fun P Q _ => kPointThresholdSlow_of_geom (by omega) Q P hc₀ hθ0 hθ)

/-- **`ConjC3` FROM ONE EXPLICIT EXPONENTIAL-SUM BOUND.**  No quantification over
multiplicative functions, characters, pretentiousness or auxiliary scales survives: the whole
headline rests on the displayed inequality for the sums
`∑_{N<n≤2N, n≡r (M)} ∏_{i<K} e(h'/b^{i+1})^{ω(n+i+1)}`, at large `K`, for primitive `h'`. -/
theorem conjC3_of_dyadic_input {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ b : ℕ, 3 ≤ b → ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∀ᶠ K in atTop, DepthDyadicBound b h' (ttExponent (depthRoot b h' 0))
        (cKgeom c₀ θ b) (CstKdeg m) K) :
    ConjC3 :=
  conjC3_of_weylLambertTwist fun b hb =>
    weylLambertTwist_of_dyadic_input hb hc₀ hθ0 hθ m (hin b hb)

/-- Nothing is given up: the lap-95 input implies the lap-96 one. -/
theorem conjC3_of_geom_input_evt' {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ b : ℕ, 3 ≤ b → ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∀ᶠ K in atTop, KPointNoExcDepth b h' (cKgeom c₀ θ b) (CstKdeg m) K) :
    ConjC3 := by
  refine conjC3_of_dyadic_input hc₀ hθ0 hθ m fun b hb h' hh' => ?_
  have hb0 : 0 < b := by omega
  have hznorm : ‖depthRoot b h' 0‖ = 1 := norm_ee_real _
  have hz1 : depthRoot b h' 0 ≠ 1 := depthRoot_ne_one_of_not_dvd hb0 hh'
  filter_upwards [hin b hb h' hh', Filter.eventually_gt_atTop 0] with K hK hKpos
  exact depthDyadicBound_of_depth hKpos hK (ttExponent_pos hznorm hz1)
    (ttExponent_le_one hznorm) (ttNonPretentious_zOmegaNat hznorm hz1 le_rfl)

#print axioms NormalNumbers.CastingOut.depthDyadicBound_of_depth
#print axioms NormalNumbers.CastingOut.windowPhi_hwin_dy
#print axioms NormalNumbers.CastingOut.depthAvg_le_dy
#print axioms NormalNumbers.CastingOut.depthDiagonalSlow_of_dyadic
#print axioms NormalNumbers.CastingOut.weylLambertTwist_of_dyadic_input
#print axioms NormalNumbers.CastingOut.conjC3_of_dyadic_input
#print axioms NormalNumbers.CastingOut.conjC3_of_geom_input_evt'

end CastingOut

end NormalNumbers
