/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Rotation
import NormalNumbers.SwingC3Weyl

/-!
# The rotation route on CONTINUOUS test functions, and the `…_of_H` conditional

`SwingC3Rotation.isRich_of_rotationRoute` runs the covering argument with the *indicator* of an
arc.  That is the wrong test class for a Weyl reduction: for a signed weight the trapezoid
squeeze costs `(1/N)∑ (trapUp − trapLo)(u_k)`, whose control is equidistribution of the `L_P`
orbit itself — i.e. normality, which is what we are trying to prove.  **The fix is to move the
glue, not the leaf.**

`density_lower_of_decouple` only ever uses a *lower* bound on the class counts, so the arc
indicator may be replaced by any continuous `g` with `0 ≤ g ≤ 1` supported in the arc, provided
the covering still delivers mass `1` at every point.  It does: Leaf A
(`SwingC3Cover.exists_rotationCover_core`) produces a net at *any* scale, so run the covering on
the middle quarter of the arc, where `g = 1`.

The payoff is `isRich_of_weylHypothesis`: `IsRich b G_b` from a single, precise, purely
analytic hypothesis about exponential sums — the `…_of_H` conditional the swing kickoff names as
its main target, with `H` exactly the quantity the B4 probe measured
(`probes/swingc3_b4_fourier.py`: it decays like `(log N)^{−1.86}`, one power of `log` better
than the global mean's `(log N)^{Re e(1/b) − 1}`).
-/

open Filter Topology Finset

namespace NormalNumbers

/-! ### The plateau of the lower trapezoid -/

/-- `trapLo a c δ` is identically `1` on the arc shrunk by `δ`. -/
lemma trapLo_eq_one_inside (a c δ x : ℝ) (hδ : 0 < δ)
    (hx : |x - (a + c) / 2| ≤ (c - a) / 2 - δ) (hhalf : |x - (a + c) / 2| ≤ 1 / 2) :
    trapLo a c δ ((x : ℝ) : AddCircle (1 : ℝ)) = 1 := by
  rw [trapLo_apply_of_close a c δ x hhalf]
  have hge : (1 : ℝ) ≤ ((c - a) / 2 - |x - (a + c) / 2|) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  rw [max_eq_right (by linarith), min_eq_left hge]

/-- The circle projection only sees the fractional part. -/
lemma coe_eq_coe_fract (z : ℝ) :
    ((z : ℝ) : AddCircle (1 : ℝ)) = ((Int.fract z : ℝ) : AddCircle (1 : ℝ)) :=
  (AddCircle.coe_fract z).symm

/-! ### Leaf B on continuous test functions -/

namespace CastingOut

open PrimeLambert

/-- **Leaf B′.**  The continuous-test-function form of `TailLargeDecouple`: the class weight
`1_{n ≡ r (Q)} − 1/Q` annihilates every continuous function of the orbit, in Cesàro mean.
No arcs, hence no squeeze, hence no equidistribution needed. -/
def TailLargeDecoupleC (b P Q : ℕ) : Prop :=
  ∀ (r : ℕ) (θ : ℝ) (g : C(AddCircle (1 : ℝ), ℝ)),
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N,
        classWeight r Q n * g (((θ + tailLarge P b n : ℝ)) : AddCircle (1 : ℝ))) / N)
      atTop (𝓝 0)

/-- **The reduction.**  Leaf B′ follows from the single exponential-sum hypothesis.  This is
`wgood_real` applied to the class weight; `h = 0` is included and is the elementary statement
`#{n < N : n ≡ r (Q)}/N → 1/Q`. -/
theorem tailLargeDecoupleC_of_weyl (b P Q : ℕ)
    (H : ∀ (r : ℕ) (θ : ℝ) (h : ℤ),
        Tendsto (wFourierMean (fun n => θ + tailLarge P b n) (classWeight r Q) h)
          atTop (𝓝 0)) :
    TailLargeDecoupleC b P Q :=
  fun r θ g => wgood_real (fun n => θ + tailLarge P b n) (classWeight r Q)
    (abs_classWeight_le r Q) (H r θ) g

/-! ### The counting core, real-valued -/

lemma density_lower_of_decoupleR {Q M : ℕ} (hQ : 0 < Q) (A B : ℕ → ℕ → ℝ) (C : ℕ → ℕ)
    (hdec : ∀ k, k < M →
      Tendsto (fun N : ℕ => ((A k N - B k N / Q) / N)) atTop (𝓝 0))
    (hcov : ∀ N : ℕ, (N : ℝ) ≤ ∑ k ∈ range M, B k N)
    (hdisj : ∀ N, ∑ k ∈ range M, A k N ≤ (C N : ℝ)) :
    ∀ᶠ N in atTop, (1 / (2 * (Q : ℝ))) * N ≤ (C N : ℝ) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hg : Tendsto (fun N : ℕ => ∑ k ∈ range M, ((A k N - B k N / Q) / N))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (range M) (fun k hk => hdec k (mem_range.1 hk))
    simpa using this
  have hneg : -(1 / (2 * (Q : ℝ))) < 0 := by
    have : (0 : ℝ) < 1 / (2 * Q) := by positivity
    linarith
  have hev := Filter.Tendsto.eventually_const_lt hneg hg
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hQ' : (Q : ℝ) ≠ 0 := ne_of_gt hQR
  have hN' : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hsplit : ∑ k ∈ range M, ((A k N - B k N / Q) / N)
      = (∑ k ∈ range M, A k N) / N - (∑ k ∈ range M, B k N) / (Q * N) := by
    have hterm : ∀ k : ℕ, ((A k N - B k N / Q) / N)
        = A k N / N - B k N / (Q * N) := by
      intro k; field_simp
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  rw [hsplit] at hN
  have hBd : (1 : ℝ) / Q ≤ (∑ k ∈ range M, B k N) / (Q * N) := by
    rw [div_le_div_iff₀ hQR (by positivity)]
    nlinarith [hcov N]
  have hhalf : (1 : ℝ) / (2 * Q) + 1 / (2 * Q) = 1 / Q := by field_simp; ring
  have hA : (1 : ℝ) / (2 * Q) ≤ (∑ k ∈ range M, A k N) / N := by linarith
  have := (le_div_iff₀ hNR).1 hA
  linarith [hdisj N]

/-! ### The continuous route -/

/-- The two leaves, with Leaf B replaced by its continuous-test-function form. -/
def RotationRouteC (b : ℕ) : Prop :=
  ∀ α len : ℝ, 0 ≤ α → 0 < len → α + len ≤ 1 →
    ∃ (P Q M : ℕ) (a : ℕ → ℕ), 0 < Q ∧ 0 < M ∧
      (∀ p, p ≤ P → p.Prime → p ∣ Q) ∧
      (∀ k, k < M → ∀ k', k' < M → a k ≡ a k' [MOD Q] → k = k') ∧
      RotationCover b P M a α len ∧ TailLargeDecoupleC b P Q

/-- **`IsRich` from the continuous route.**  The covering argument again, but tested against a
continuous bump instead of an arc indicator: the net is run on the middle quarter of the arc,
where the bump is `1`, and the bump vanishes off the arc so every counted point is still an
occurrence. -/
theorem isRich_of_rotationRouteC {b : ℕ} (hb : 2 ≤ b) (H : RotationRouteC b) :
    IsRich b (primeLambertAtBase b) := by
  classical
  intro w hw
  have hb0 : 0 < b := by omega
  have hbR : (0 : ℝ) < (b : ℝ) ^ w.length := by
    have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb0
    positivity
  have hVlt : blockNatVal b w < b ^ w.length := blockNatVal_lt b w hw
  set V : ℕ := blockNatVal b w with hV
  set α : ℝ := (V : ℝ) / (b : ℝ) ^ w.length with hα
  set len : ℝ := 1 / (b : ℝ) ^ w.length with hlen
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hlen0 : 0 < len := by rw [hlen]; positivity
  have hsum : α + len = ((V : ℝ) + 1) / (b : ℝ) ^ w.length := by rw [hα, hlen]; ring
  have hαlen : α + len ≤ 1 := by
    rw [hsum, div_le_one hbR]
    have : (V : ℝ) + 1 ≤ ((b ^ w.length : ℕ) : ℝ) := by exact_mod_cast hVlt
    simpa using this
  set δ : ℝ := len / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set g : C(AddCircle (1 : ℝ), ℝ) := trapLo α (α + len) δ with hg
  obtain ⟨P, Q, M, a, hQ0, hM0, hQP, hinj, hcov, hdec⟩ :=
    H (α + δ) δ (by linarith) hδ0 (by rw [hδ]; linarith)
  set θ : ℕ → ℝ := fun k => tailSmall P b (a k) with hθ
  set G : ℕ → ℕ → ℝ := fun k n =>
    g (((θ k + tailLarge P b n : ℝ)) : AddCircle (1 : ℝ)) with hG
  have hG0 : ∀ k n, 0 ≤ G k n := fun k n => trapLo_nonneg _ _ _ _
  have hG1 : ∀ k n, G k n ≤ 1 := fun k n => trapLo_le_one _ _ _ _
  have hGfr : ∀ k n, G k n
      = g (((Int.fract (θ k + tailLarge P b n) : ℝ)) : AddCircle (1 : ℝ)) := by
    intro k n; rw [hG]; exact congrArg _ (coe_eq_coe_fract _)
  -- the bump vanishes off the arc
  have hGzero : ∀ k n, ¬ (Int.fract (θ k + tailLarge P b n) ∈ Set.Ico α (α + len)) →
      G k n = 0 := by
    intro k n hn
    rw [hGfr k n, hg]
    exact trapLo_eq_zero_outside α (α + len) δ _ hα0 (by linarith) hαlen
      (Int.fract_nonneg _) (Int.fract_lt_one _) (by simpa [Set.mem_Ico] using hn) hδ0
  -- the bump is `1` on the middle quarter
  have hGone : ∀ k n, Int.fract (θ k + tailLarge P b n) ∈ Set.Ico (α + δ) ((α + δ) + δ) →
      G k n = 1 := by
    intro k n hn
    obtain ⟨h1, h2⟩ := hn
    rw [hGfr k n, hg]
    have hmid : (α + (α + len)) / 2 = α + 2 * δ := by rw [hδ]; ring
    have habs : |Int.fract (θ k + tailLarge P b n) - (α + (α + len)) / 2| ≤ δ := by
      rw [hmid, abs_le]; constructor <;> linarith
    refine trapLo_eq_one_inside α (α + len) δ _ hδ0 ?_ ?_
    · have : ((α + len) - α) / 2 - δ = δ := by rw [hδ]; ring
      rw [this]; exact habs
    · refine habs.trans ?_
      rw [hδ]; linarith
  set A : ℕ → ℕ → ℝ := fun k N =>
    ∑ n ∈ (range N).filter (fun n => n ≡ a k [MOD Q]), G k n with hA
  set B : ℕ → ℕ → ℝ := fun k N => ∑ n ∈ range N, G k n with hB
  set Cc : ℕ → ℕ := fun N =>
    ((range N).filter (fun n => OccursAt b (primeLambertAtBase b) w n)).card with hCc
  -- decoupling
  have hdecA : ∀ k, k < M → Tendsto (fun N : ℕ => ((A k N - B k N / Q) / N)) atTop (𝓝 0) := by
    intro k _
    have hrw : ∀ N : ℕ, A k N - B k N / Q
        = ∑ n ∈ range N, classWeight (a k) Q n * G k n := by
      intro N
      rw [hA, hB]
      simp only [classWeight, sub_mul, Finset.sum_sub_distrib, Finset.sum_filter,
        ite_mul, one_mul, zero_mul, div_eq_mul_inv, ← Finset.sum_mul]
      congr 1
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => mul_comm _ _
    simp only [hrw]
    exact hdec (a k) (θ k) g
  -- covering
  have hcovN : ∀ N : ℕ, (N : ℝ) ≤ ∑ k ∈ range M, B k N := by
    intro N
    have hswap : ∑ k ∈ range M, B k N = ∑ n ∈ range N, ∑ k ∈ range M, G k n := by
      rw [hB]; exact Finset.sum_comm
    rw [hswap]
    have hone : ∀ n ∈ range N, (1 : ℝ) ≤ ∑ k ∈ range M, G k n := by
      intro n _
      obtain ⟨k, hkM, hk⟩ := hcov (tailLarge P b n)
      have := Finset.single_le_sum (f := fun k => G k n)
        (fun k _ => hG0 k n) (mem_range.2 hkM)
      rwa [hGone k n hk] at this
    calc (N : ℝ) = ∑ _n ∈ range N, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum hone
  -- disjointness
  have hdisjN : ∀ N, ∑ k ∈ range M, A k N ≤ (Cc N : ℝ) := by
    intro N
    set D : ℕ → ℕ := fun k =>
      ((range N).filter (fun n => n ≡ a k [MOD Q] ∧
        Int.fract (θ k + tailLarge P b n) ∈ Set.Ico α (α + len))).card with hD
    have hAD : ∀ k, A k N ≤ (D k : ℝ) := by
      intro k
      rw [hA, hD]
      have hstep : ∀ n ∈ (range N).filter (fun n => n ≡ a k [MOD Q]),
          G k n ≤ (if Int.fract (θ k + tailLarge P b n) ∈ Set.Ico α (α + len) then
            (1 : ℝ) else 0) := by
        intro n _
        by_cases h : Int.fract (θ k + tailLarge P b n) ∈ Set.Ico α (α + len)
        · rw [if_pos h]; exact hG1 k n
        · rw [if_neg h, hGzero k n h]
      refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
      rw [← Finset.sum_filter, Finset.filter_filter]
      simp
    have hDC : ∑ k ∈ range M, D k ≤ Cc N := by
      rw [hD, hCc]
      rw [← Finset.card_biUnion]
      · refine Finset.card_le_card fun n hn => ?_
        rw [Finset.mem_biUnion] at hn
        obtain ⟨k, -, hk⟩ := hn
        rw [mem_filter] at hk ⊢
        refine ⟨hk.1, ?_⟩
        rw [occursAt_iff_orbit_mem b hb _ w hw n,
          orbit_eq_rotation hb hQP hk.2.1, ← hV, ← hα, ← hsum]
        exact hk.2.2
      · intro k hk k' hk' hne
        refine Finset.disjoint_left.2 fun n hn hn' => ?_
        rw [mem_filter] at hn hn'
        exact hne (hinj k (mem_range.1 hk) k' (mem_range.1 hk') (hn.2.1.symm.trans hn'.2.1))
    calc ∑ k ∈ range M, A k N ≤ ∑ k ∈ range M, (D k : ℝ) := Finset.sum_le_sum fun k _ => hAD k
      _ = ((∑ k ∈ range M, D k : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Cc N : ℝ) := by exact_mod_cast hDC
  refine ⟨1 / (2 * (Q : ℝ)), by positivity, ?_⟩
  exact density_lower_of_decoupleR hQ0 A B Cc hdecA hcovN hdisjN

/-! ### The named hypothesis, and the conditional headline -/

/-- **`H`, the swing's named hypothesis.**  For every prime cut `P`, every modulus `Q`, every
class `r`, every rotation `θ` and every frequency `h` (`h = 0` included, where it is the
elementary `#{n<N : n ≡ r (Q)}/N → 1/Q`), the class-weighted exponential sum of the large-prime
tail vanishes in Cesàro mean:

`(1/N) ∑_{n<N} (1_{n ≡ r (Q)} − 1/Q) · e(h·(θ + tailLarge P b n)) → 0`.

This is a precise, literature-checkable statement about a multiplicative function twisted by an
additive character; the `j`-slot expansion turns it into `∑_{t≤x} χ(t) z^{ω(t)}` with
`z = e(h/b)`, i.e. Selberg–Delange with characters.  The B4 probe
(`probes/swingc3_b4_fourier.py`) measured the left side decaying like `(log N)^{−1.86}` for
`b = 4, h = 1`. -/
def WeylTailHypothesis (b : ℕ) : Prop :=
  ∀ (P Q r : ℕ) (θ : ℝ) (h : ℤ), 0 < Q →
    Tendsto (wFourierMean (fun n => θ + tailLarge P b n) (classWeight r Q) h) atTop (𝓝 0)

theorem rotationRouteC_of_weyl {b : ℕ} (hb : 2 ≤ b) (H : WeylTailHypothesis b) :
    RotationRouteC b := by
  intro α len hα hlen hαlen
  obtain ⟨P, Q, M, a, hQ0, hM0, hQP, hPQ, hinj, hcov⟩ :=
    exists_rotationCover_core hb α len hα hlen hαlen
  exact ⟨P, Q, M, a, hQ0, hM0, hQP, hinj, hcov,
    tailLargeDecoupleC_of_weyl b P Q (fun r θ h => H P Q r θ h hQ0)⟩

/-- **The `…_of_H` conditional the swing kickoff names as its main target.**  `G_b` is rich,
given only the exponential-sum hypothesis `H`.  Leaf A is proved, the covering glue is proved,
the Weyl reduction is proved; `H` is the whole remaining content. -/
theorem isRich_of_weylHypothesis {b : ℕ} (hb : 2 ≤ b) (H : WeylTailHypothesis b) :
    IsRich b (primeLambertAtBase b) :=
  isRich_of_rotationRouteC hb (rotationRouteC_of_weyl hb H)

/-- `ConjC3`, conditional on `H`. -/
theorem conjC3_of_weylHypothesis (H : ∀ b, 3 ≤ b → WeylTailHypothesis b) : ConjC3 :=
  fun b hb => isRich_of_weylHypothesis (by omega) (H b hb)

end CastingOut

end NormalNumbers
