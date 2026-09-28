/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtNoExcAll

/-!
# Restricting the open input to the family the C3 chain actually uses

`KPointNoExcWith cK CstK K` quantifies over **every** family `g : Fin K → ℕ → ℂ` of
coprime-multiplicative, bounded functions and over **every** injective shift vector
`hsh : Fin K → ℕ`.  The C3 chain uses far less: its factors are always
`g i = zOmegaNat (z i)` for unimodular `z i` (indeed `z i = depthRoot b h' i`), and its shifts
are always `hsh i = i + 1`.

`KPointNoExcRoots cK CstK K` is that restriction — the same bound, asked only for
`ω`-powers of unimodular numbers at consecutive shifts.  It is a strictly weaker `Prop`
(`kPointNoExcRoots_of_with`), and this file rethreads the whole chain onto it, ending at

    conjC3_of_geom_input_roots :
      (∀ b ≥ 3, ∀ K, KPointNoExcRoots (cKgeom c₀ θ b) (CstKdeg m) K) → ConjC3    (0 < θ < 1)

**Why this is the right narrowing, where the `∀ i` one (`C3MrtNoExcAll`) was not.**  The `∀ i`
attempt failed for a quantitative reason — `ttExponent (depthRoot b h' i) → 0`, so no shared
cutoff `L` certifies every factor.  Restricting the *family* costs nothing of the kind: the
consumer already only ever instantiates at `zOmegaNat ∘ z`, so no hypothesis has to be
discharged that was not being discharged before.  The gain is on the ledger: the open statement
is no longer "the `K`-point Elliott bound for arbitrary bounded multiplicative functions" but
"…for the one-parameter family `n ↦ z^{ω(n)}`, `|z| = 1`, at consecutive shifts".

Everything below is `C3MrtUnifK` / `C3MrtSlowSched` verbatim with `KPointNoExcWith` replaced by
`KPointNoExcRoots`; only `dyadic_window_bound_roots` differs in its proof, and only in the single
line that applies the input.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- **The `K`-point input, restricted to `ω`-powers of unimodular numbers at consecutive
shifts.**  Strictly weaker than `KPointNoExcWith`; everything the C3 chain ever asks for. -/
def KPointNoExcRoots (cK CstK : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ z : ℕ → ℂ, (∀ i, ‖z i‖ = 1) →
    ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X →
      (∃ i : Fin K, TTNonPretentious (zOmegaNat (z i)) X L) →
        ∀ N : ℕ, Real.sqrt X ≤ (N : ℝ) → (N : ℝ) ≤ X →
          ∀ W r : ℕ, 0 < W → (W : ℝ) ≤ L ^ cK K → ((K : ℝ) + 1 ≤ L ^ cK K) →
            ‖((W : ℝ) / (N : ℝ) : ℝ) •
                ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = r % W),
                  ∏ i : Fin K, zOmegaNat (z i) (n + ((i : ℕ) + 1))‖
              ≤ CstK K * L ^ (-(cK K))

/-- Nothing is lost: the unrestricted input implies the restricted one. -/
theorem kPointNoExcRoots_of_with {cK CstK : ℕ → ℝ} {K : ℕ}
    (h : KPointNoExcWith cK CstK K) : KPointNoExcRoots cK CstK K := by
  intro z hz X L hX hL hLlog hnp N hNl hNu W r hW hWL hKL
  refine h (fun i => zOmegaNat (z i)) (fun i => isCoprimeMultiplicativeNat_zOmegaNat _)
    (fun i n => norm_zOmegaNat_le_one (hz i) n) X L hX hL hLlog hnp N hNl hNu W r
    (fun i => (i : ℕ) + 1) hW hWL ?_ ?_
  · intro i
    have hi : ((i : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_of_lt i.isLt)
    push_cast
    linarith
  · intro i j hij
    have h' : (i : ℕ) + 1 = (j : ℕ) + 1 := hij
    exact Fin.ext (by omega)

theorem dyadic_window_bound_roots {K : ℕ} (hK : 0 < K) {cK CstK : ℕ → ℝ}
    (h : KPointNoExcRoots cK CstK K)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (z 0)) X L)
    {N : ℕ} (hN2 : 2 ≤ N)
    (hthr : max 2 ((K : ℝ) + 1) ≤ (2 * Real.log N) ^ (κ * cK K))
    {M : ℕ} (hM : 0 < M) (r : ℕ) (hML : (M : ℝ) ≤ (2 * Real.log N) ^ (κ * cK K)) :
    ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
        ∏ i : Fin K, z i ^ omegaNat (n + (i : ℕ) + 1)‖
      ≤ CstK K * (2 * Real.log N) ^ (-(κ * cK K)) * (N : ℝ) / (M : ℝ) := by
  have h2L : (2 : ℝ) ≤ (2 * Real.log N) ^ (κ * cK K) := le_trans (le_max_left _ _) hthr
  have hKL : (K : ℝ) + 1 ≤ (2 * Real.log N) ^ (κ * cK K) := le_trans (le_max_right _ _) hthr
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  set X : ℝ := (N : ℝ) ^ 2 with hX
  have hlogX : Real.log X = 2 * Real.log N := by rw [hX, Real.log_pow]; push_cast; ring
  have hX3 : 3 ≤ X := by rw [hX]; nlinarith
  have hbase : (1 : ℝ) ≤ 2 * Real.log N := by linarith
  have hbase0 : (0 : ℝ) ≤ 2 * Real.log N := by linarith
  set L : ℝ := (2 * Real.log N) ^ κ with hLdef
  have hpow : ∀ s : ℝ, L ^ s = (2 * Real.log N) ^ (κ * s) := by
    intro s; rw [hLdef, ← Real.rpow_mul hbase0]
  have hL1 : (1 : ℝ) ≤ L := Real.one_le_rpow hbase hκ.le
  have hLlog : L ≤ Real.log X := by
    rw [hlogX, hLdef]
    calc (2 * Real.log N) ^ κ ≤ (2 * Real.log N) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase hκ1
      _ = 2 * Real.log N := Real.rpow_one _
  have hLκ : L ≤ Real.log X ^ κ := by rw [hlogX]
  have hsqrt : Real.sqrt X = (N : ℝ) := by rw [hX, Real.sqrt_sq hNpos.le]
  have hNX : (N : ℝ) ≤ X := by rw [hX]; nlinarith
  have hspec := h z hz X L (by linarith) hL1 hLlog
    ⟨⟨0, hK⟩, hnp X L hX3 hL1 hLκ⟩
    N (by rw [hsqrt]) hNX M r hM (by rw [hpow]; exact hML) (by rw [hpow]; exact hKL)
  rw [hpow, mul_neg] at hspec
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hspec
  set S : ℂ := ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
      ∏ i : Fin K, zOmegaNat (z i) (n + ((i : ℕ) + 1)) with hS
  have hSrw : (∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
      ∏ i : Fin K, z i ^ omegaNat (n + (i : ℕ) + 1)) = S := by
    rw [hS]
    refine Finset.sum_congr rfl fun n _ => Finset.prod_congr rfl fun i _ => ?_
    simp [zOmegaNat, ← add_assoc]
  rw [hSrw]
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [div_mul_eq_mul_div, div_le_iff₀ hNpos] at hspec
  rw [le_div_iff₀ hMpos]
  nlinarith [hspec, norm_nonneg S, hNpos.le, hMpos.le]

open scoped Classical in
/-- **`dyadic_window_bound_roots` supplies `windowPhi`'s analytic branch.**  One threshold
condition at the single scale `A` propagates to every `a ≥ A`, because `a ↦ (2 log a)^(κ·cK K)`
is increasing.  `A` may — and along the diagonal must — depend on `K`. -/
theorem windowPhi_hwin_roots {K : ℕ} (hK : 0 < K) {cK CstK : ℕ → ℝ} (hc : 0 < cK K)
    (h : KPointNoExcRoots cK CstK K)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (z 0)) X L)
    {M A : ℕ} (hM : 0 < M) (hA2 : 2 ≤ A)
    (hAthr : max (max 2 ((K : ℝ) + 1)) (M : ℝ) ≤ (2 * Real.log A) ^ (κ * cK K))
    (r : ℕ) {a : ℕ} (haA : A ≤ a) :
    ‖∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M),
        ∏ i ∈ range K, z i ^ omegaNat (n + i + 1)‖
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
        ∏ i ∈ range K, z i ^ omegaNat (n + i + 1)
      = ∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M),
        ∏ i : Fin K, z i ^ omegaNat (n + (i : ℕ) + 1) :=
    Finset.sum_congr rfl fun n _ =>
      (Fin.prod_univ_eq_prod_range (fun i => z i ^ omegaNat (n + i + 1)) K).symm
  rw [hrw]
  exact dyadic_window_bound_roots hK h z hz hκ hκ1 hnp ha2 hthr hM r hML

open scoped Classical in
/-- **The explicit `depthAvg` majorant from the named input, constants and all.**
Everything of laps 84–87 in one statement: the `K`-point input with named constants, the
archimedean certificate, the window profile, the halving stack cut at `k₀`, the `M₀` residue
classes and the `1/N`.  Only three quantities move with `K`: `cK K`, `CstK K` and the threshold
scale `A`.  That is exactly the data the diagonal `K = depthLL b N` needs. -/
theorem depthAvg_le_roots {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ) {K : ℕ} (hK : 0 < K)
    {cK CstK : ℕ → ℝ} (hc : 0 < cK K) (hC : 0 < CstK K)
    (hin : KPointNoExcRoots cK CstK K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b hh 0)) X L)
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
      (fun a' ha' => windowPhi_hwin_roots hK hc hin (fun i => depthRoot b hh i) hz hκ hκ1 hnp
        hM0 hA2 hAthr r ha') a)
    hN k₀

theorem depthAvg_gen_tendsto_of_unif_roots {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    {cK CstK : ℕ → ℝ} (hc : ∀ K, 0 < cK K) (hC : ∀ K, 0 < CstK K)
    (KN : ℕ → ℕ) (hKN : ∀ N, 0 < KN N)
    (hin : ∀ K, KPointNoExcRoots cK CstK K)
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
  -- the three pieces of the majorant
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
  filter_upwards [Filter.eventually_ge_atTop (M₀ + 1)] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hstep := depthAvg_le_roots hQ P j hh (hKN N) (hc _) (hC _) (hin _)
    hκ hκ1 hnp (hA2 _) (hAthr _) (show M₀ < N by omega) (k₀ N)
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  ring

set_option maxHeartbeats 1600000 in
/-- **The diagonal at any level below the SLOW schedule, from the geometric input, `θ < 1`.**
Verbatim `C3MrtUnifK.depthAvg_gen_tendsto_of_geom` with the exponent estimate swapped for
`exponent_tendsto_atBot_of_geom_slow`; nothing else in that assembly cares which schedule the
levels sit under. -/
theorem depthAvg_gen_tendsto_of_geom_slow_roots {b Q : ℕ} (hb : 2 ≤ b) (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (KN : ℕ → ℕ) (hKN : ∀ N, 0 < KN N)
    (hKle : ∀ᶠ N : ℕ in atTop, KN N ≤ depthSlow b N)
    (hin : ∀ K, KPointNoExcRoots (cKgeom c₀ θ b) (CstKdeg m) K)
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
  refine depthAvg_gen_tendsto_of_unif_roots hQ P j hh (fun K => cKgeom_pos hc₀ hb0 K)
    (fun K => CstKdeg_pos m K) KN hKN hin hκ hκ1 hnp Athr hA2 hAthr
    (fun N => Nat.log 2 (Nat.log 2 N)) ?_
  simpa using hΦ.add hhalf

/-- **`DepthDiagonalSlow b` FROM THE GEOMETRICALLY DEGRADING INPUT AT `θ < 1`.**  All twist
levels, exactly as in `C3MrtUnifK.depthDiagonal_of_geom`. -/
theorem depthDiagonalSlow_of_geom_roots {b : ℕ} (hb : 2 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcRoots (cKgeom c₀ θ b) (CstKdeg m) K)
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
  have hgen := depthAvg_gen_tendsto_of_geom_slow_roots hb hQ P j h' hc₀ hθ0 hθ m KN hKN hKle hin
    hκ hκ1 hnp Athr hA2 hAthr hAle
  have hprim : Tendsto (fun N : ℕ =>
      depthAvg b P Q j h' (depthSlow b N - v) N) atTop (𝓝 0) := by
    refine hgen.congr' ?_
    filter_upwards [hKeq] with N hN
    rw [hN]
  exact depthAvg_dvd_tendsto_of_primitive_sched hb P Q j h' v (depthSlow b)
    (tendsto_depthSlow hb) hprim

/-- **THE C3 CRUX FROM THE GEOMETRIC `K`-POINT INPUT, `θ < 1`.**  This supersedes
`C3MrtUnifK.weylLambertTwist_of_geom`: the admissible decay rate for the `K`-point saving is
widened from `θ < 1/2` to `θ < 1` — i.e. the input may lose a full factor `b^{-1}` per extra
correlation point, near the `V^{-0.49J'}` shape TT Thm 3.3 actually produces — at the cost of
slowing the depth schedule to `b^{D_N} ≍ log log N · log log log N`, which is the minimum the
mean-phase discard permits. -/
theorem weylLambertTwist_of_geom_slow_roots {b : ℕ} (hb : 3 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcRoots (cKgeom c₀ θ b) (CstKdeg m) K)
    (hthr : ∀ P Q : ℕ, 0 < Q → KPointThresholdSlow b Q P (cKgeom c₀ θ b)) :
    WeylLambertTwist b :=
  weylLambertTwist_of_depthDiagonalSlow hb
    (depthDiagonalSlow_of_geom_roots (by omega) hc₀ hθ0 hθ m hin hthr)

/-- **THE C3 CRUX FROM THE `K`-POINT INPUT ALONE.**  No threshold hypothesis: it is discharged
by `kPointThresholdSlow_of_geom`.  Everything the crux still needs is the one open analytic
statement `KPointNoExcRoots (cKgeom c₀ θ b) (CstKdeg m) K`. -/
theorem weylLambertTwist_of_geom_input_roots {b : ℕ} (hb : 3 ≤ b) {c₀ θ : ℝ} (hc₀ : 0 < c₀)
    (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ K, KPointNoExcRoots (cKgeom c₀ θ b) (CstKdeg m) K) :
    WeylLambertTwist b :=
  weylLambertTwist_of_geom_slow_roots hb hc₀ hθ0 hθ m hin
    fun P Q _ => kPointThresholdSlow_of_geom (by omega) Q P hc₀ hθ0 hθ

/-- **`ConjC3` FROM THE `K`-POINT INPUT ALONE**, for every geometric decay rate `θ < 1`. -/
theorem conjC3_of_geom_input_roots {c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1) (m : ℕ)
    (hin : ∀ b : ℕ, 3 ≤ b → ∀ K, KPointNoExcRoots (cKgeom c₀ θ b) (CstKdeg m) K) :
    ConjC3 :=
  conjC3_of_weylLambertTwist fun b hb =>
    weylLambertTwist_of_geom_input_roots hb hc₀ hθ0 hθ m (hin b hb)

#print axioms NormalNumbers.CastingOut.kPointNoExcRoots_of_with
#print axioms NormalNumbers.CastingOut.dyadic_window_bound_roots
#print axioms NormalNumbers.CastingOut.depthAvg_le_roots
#print axioms NormalNumbers.CastingOut.depthAvg_gen_tendsto_of_unif_roots
#print axioms NormalNumbers.CastingOut.depthDiagonalSlow_of_geom_roots
#print axioms NormalNumbers.CastingOut.weylLambertTwist_of_geom_input_roots
#print axioms NormalNumbers.CastingOut.conjC3_of_geom_input_roots

end CastingOut

end NormalNumbers
