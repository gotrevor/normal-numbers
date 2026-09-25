/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3ContGlue

/-!
# Rung 0 of the C3 depth ladder: bad SCALES, and the richness that survives them

The C3 crux `WeylTailHypothesis` asks for the twisted mean to vanish **for every `N`**.  What the
literature actually supplies (Pilatte 2025's decoupling inequality, in the form of
Tao–Teräväinen 2025 Theorem 3.1, `papers/tao-teravainen-2025-quantitative-correlations.txt`) is
the same bound for every `N` **outside an exceptional set `E` of small logarithmic density**.  The
two are not the same statement, and the gap is exactly a set of scales.

This file is the re-plumb.  It records the *structural* reason the C3 consumer tolerates bad
scales while the C1 consumer does not, and cashes that reason out as a theorem:

* `IsRich` (`CastingOut.lean`) is a **lower** bound on the **monotone** count
  `C N = #{n < N : word occurs at n}`.  So a single good scale `N ≤ M` already bounds `C M` from
  below: `C M ≥ C N ≥ c·N`.  Bad scales cost only the ratio `N/M`.
* `ConjC1`'s `CastLaw` is a two-sided density **limit** with no monotonicity; it does not absorb
  `E` at all.  That asymmetry is why the C3 leaf is the one to re-plumb.

`ScalesDense ε S` says the good scales are dense enough that every large `M` has a good
`N ∈ [M^{1−ε}, M]` — which is what an exceptional set of logarithmic density `≪ L^{−c}` gives,
since a gap fully inside `E` has logarithmic length `≪ L^{−c} log M`.  The absorption lemma then
yields `C M ≥ c·M^{1−ε}` for every `ε > 0`: the new rung

`IsRichSubpoly` — *every word occurs at `≥ N^{1−o(1)}` positions below `N`* —

strictly between the proved `isDisjunctive_base` (every word occurs at least once) and `ConjC3`
(positive lower density).  `isRich_implies` and `isDisjunctive_of_isRichSubpoly` pin it between
the two.
-/

open Filter Topology Finset

namespace NormalNumbers

open PrimeLambert

/-! ### The signed-weight Weyl criterion along an arbitrary filter of scales

`SwingC3Weyl.wgood_all` is stated for `atTop` and its proof goes through `Metric.tendsto_atTop`.
Only the *eventual* half of the `ε/2 + ε/2` split is filter-sensitive (the approximation half is a
uniform-in-`N` bound, `norm_wMean_le`), so the criterion holds verbatim along any filter.  These
are the filter-relative copies. -/

/-- `WGood` along a filter of scales. -/
def WGoodAt (l : Filter ℕ) (u w : ℕ → ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) : Prop :=
  Tendsto (wMean u w f) l (𝓝 0)

lemma wgoodAt_fourier (l : Filter ℕ) (u w : ℕ → ℝ) (h : ℤ)
    (hW : ∀ h : ℤ, Tendsto (wFourierMean u w h) l (𝓝 0)) :
    WGoodAt l u w (fourier h) := by
  rw [WGoodAt, show wMean u w (fourier h) = wFourierMean u w h from
    funext fun n => wMean_eq_wFourierMean u w h n]
  exact hW h

lemma wgoodAt_span (l : Filter ℕ) (u w : ℕ → ℝ)
    (hW : ∀ h : ℤ, Tendsto (wFourierMean u w h) l (𝓝 0))
    {f : C(AddCircle (1 : ℝ), ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) : WGoodAt l u w f := by
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨h, rfl⟩ := hx; exact wgoodAt_fourier l u w h hW
  | zero =>
      have h0 : wMean u w (0 : C(AddCircle (1 : ℝ), ℂ)) = fun _ => (0 : ℂ) := by
        funext n; simp [wMean]
      rw [WGoodAt, h0]
      exact tendsto_const_nhds
  | add x y _ _ hx hy =>
      have hxy : wMean u w (x + y) = fun n => wMean u w x n + wMean u w y n :=
        funext fun n => wMean_add u w x y n
      rw [WGoodAt, hxy]
      simpa using hx.add hy
  | smul a x _ hx =>
      have hax : wMean u w (a • x) = fun n => a * wMean u w x n :=
        funext fun n => wMean_smul u w a x n
      rw [WGoodAt, hax]
      simpa using hx.const_mul a

/-- **The signed-weight Weyl criterion along a filter.** -/
theorem wgoodAt_all {W : ℝ} (l : Filter ℕ) (u w : ℕ → ℝ) (hw : ∀ k, |w k| ≤ W)
    (hW : ∀ h : ℤ, Tendsto (wFourierMean u w h) l (𝓝 0))
    (f : C(AddCircle (1 : ℝ), ℂ)) : WGoodAt l u w f := by
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hw 0)
  rw [WGoodAt, Metric.tendsto_nhds]
  intro ε hε
  have hWpos : 0 < W + 1 := by linarith
  have hdense : f ∈ closure (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) : Set _) := by
    have hspan := span_fourier_closure_eq_top (T := (1 : ℝ))
    have hmem : f ∈ (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure := by
      rw [hspan]; trivial
    rw [← Submodule.topologicalClosure_coe]
    exact hmem
  obtain ⟨P, hPmem, hP⟩ :=
    Metric.mem_closure_iff.mp hdense (ε / (2 * (W + 1))) (by positivity)
  have hPgood := wgoodAt_span l u w hW hPmem
  rw [WGoodAt, Metric.tendsto_nhds] at hPgood
  have hnorm : ‖f - P‖ < ε / (2 * (W + 1)) := by rwa [← dist_eq_norm]
  filter_upwards [hPgood (ε / 2) (by linarith)] with n h2
  have h1 : ‖wMean u w f n - wMean u w P n‖ < ε / 2 := by
    have hsub : wMean u w f n - wMean u w P n = wMean u w (f - P) n := by
      simp only [wMean, ContinuousMap.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_div]
    rw [hsub]
    calc ‖wMean u w (f - P) n‖ ≤ W * ‖f - P‖ := norm_wMean_le u w hw _ n
      _ ≤ (W + 1) * ‖f - P‖ := by nlinarith [norm_nonneg (f - P)]
      _ < (W + 1) * (ε / (2 * (W + 1))) := mul_lt_mul_of_pos_left hnorm hWpos
      _ = ε / 2 := by field_simp
  rw [dist_eq_norm, sub_zero] at h2 ⊢
  calc ‖wMean u w f n‖ = ‖(wMean u w f n - wMean u w P n) + wMean u w P n‖ := by ring_nf
    _ ≤ ‖wMean u w f n - wMean u w P n‖ + ‖wMean u w P n‖ := norm_add_le _ _
    _ < ε := by linarith

/-- Real-valued form of `wgoodAt_all`. -/
theorem wgoodAt_real {W : ℝ} (l : Filter ℕ) (u w : ℕ → ℝ) (hw : ∀ k, |w k| ≤ W)
    (hW : ∀ h : ℤ, Tendsto (wFourierMean u w h) l (𝓝 0))
    (g : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range n, w k * g ((u k : ℝ) : AddCircle (1 : ℝ))) / n)
      l (𝓝 0) := by
  set f : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun y => ((g y : ℝ) : ℂ), Complex.continuous_ofReal.comp g.continuous⟩ with hf
  have hmean : ∀ n : ℕ, (wMean u w f n).re
      = (∑ k ∈ Finset.range n, w k * g ((u k : ℝ) : AddCircle (1 : ℝ))) / n := by
    intro n
    rw [wMean]
    have hs : (∑ k ∈ Finset.range n, (w k : ℂ) * f ((u k : ℝ) : AddCircle (1 : ℝ)))
        = ((∑ k ∈ Finset.range n, w k * g ((u k : ℝ) : AddCircle (1 : ℝ)) : ℝ) : ℂ) := by
      push_cast [hf]; rfl
    rw [hs, ← Complex.ofReal_natCast n, ← Complex.ofReal_div, Complex.ofReal_re]
  have hcont := (Complex.continuous_re.tendsto (0 : ℂ)).comp (wgoodAt_all l u w hw hW f)
  simp only [Function.comp_def, hmean, Complex.zero_re] at hcont
  exact hcont

namespace CastingOut

/-! ### Dense sets of good scales -/

/-- `ScalesDense ε S`: every large `M` has a member of `S` in `[M^{1−ε}, M]`.  This is the shape
an exceptional set of small logarithmic density leaves behind: a maximal gap of `S` inside
`[1, M]` has logarithmic length `≤ ε·log M`. -/
def ScalesDense (ε : ℝ) (S : Set ℕ) : Prop :=
  ∀ᶠ M : ℕ in atTop, ∃ N ∈ S, ((M : ℝ) ^ (1 - ε) ≤ (N : ℝ) ∧ N ≤ M)

/-- Shrinking `S` by a finite initial segment does not affect density of scales, as long as
`ε < 1` (so that `M^{1−ε} → ∞`). -/
theorem ScalesDense.inter_Ici {ε : ℝ} (hε : ε < 1) {S : Set ℕ} (hS : ScalesDense ε S) (M₀ : ℕ) :
    ScalesDense ε (S ∩ {N | M₀ ≤ N}) := by
  have hpow : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 - ε)) atTop atTop := by
    have h1 : (0 : ℝ) < 1 - ε := by linarith
    exact (tendsto_rpow_atTop h1).comp tendsto_natCast_atTop_atTop
  filter_upwards [hS, hpow.eventually_ge_atTop (M₀ : ℝ)] with M hM hM₀
  obtain ⟨N, hNS, hlow, hhigh⟩ := hM
  refine ⟨N, ⟨hNS, ?_⟩, hlow, hhigh⟩
  have : (M₀ : ℝ) ≤ (N : ℝ) := hM₀.trans hlow
  exact_mod_cast this

/-- **The absorption lemma.**  A *monotone* count that is large at a dense set of scales is large
at *every* large scale, with the loss exactly the scale ratio.  This is the structural fact that
makes the C3 consumer tolerant of an exceptional set of scales. -/
theorem lower_of_monotone_of_scalesDense {C : ℕ → ℝ} (hmono : Monotone C) {c ε : ℝ} (hc : 0 ≤ c)
    {S : Set ℕ} (hS : ScalesDense ε S) (hgood : ∀ N ∈ S, c * (N : ℝ) ≤ C N) :
    ∀ᶠ M : ℕ in atTop, c * (M : ℝ) ^ (1 - ε) ≤ C M := by
  filter_upwards [hS] with M hM
  obtain ⟨N, hNS, hlow, hhigh⟩ := hM
  calc c * (M : ℝ) ^ (1 - ε) ≤ c * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlow hc
    _ ≤ C N := hgood N hNS
    _ ≤ C M := hmono hhigh

/-! ### The new rung -/

/-- The occurrence count of the word `w` below `N`. -/
noncomputable def occCount (b : ℕ) (x : ℝ) (w : List ℕ) (N : ℕ) : ℕ :=
  open Classical in ((range N).filter (fun n => OccursAt b x w n)).card

theorem monotone_occCount (b : ℕ) (x : ℝ) (w : List ℕ) :
    Monotone (fun N : ℕ => (occCount b x w N : ℝ)) := by
  classical
  intro M N hMN
  show ((occCount b x w M : ℝ)) ≤ ((occCount b x w N : ℝ))
  have : occCount b x w M ≤ occCount b x w N := by
    rw [occCount, occCount]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hMN))
  exact_mod_cast this

/-- **`IsRichSubpoly`** — the rung strictly between disjunctivity and `IsRich`: every admissible
word occurs at `≥ N^{1−o(1)}` positions below `N`. -/
def IsRichSubpoly (b : ℕ) (x : ℝ) : Prop :=
  ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ (1 - ε) ≤ (occCount b x w N : ℝ)

theorem isRichSubpoly_of_isRich {b : ℕ} {x : ℝ} (h : IsRich b x) : IsRichSubpoly b x := by
  classical
  intro w hw ε hε
  obtain ⟨c, hc, hev⟩ := h w hw
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hle : (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) := by
    calc (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
      _ = (N : ℝ) := Real.rpow_one _
  exact (mul_le_mul_of_nonneg_left hle hc.le).trans (by simpa [occCount] using hN)

/-- `IsRichSubpoly` is strictly above disjunctivity: it forces every word to occur. -/
theorem isDisjunctive_of_isRichSubpoly {b : ℕ} (hb : 2 ≤ b) (x : ℝ) (hx : IsRichSubpoly b x) :
    IsDisjunctive b x := by
  classical
  rw [isDisjunctive_iff_forall_occursAt b hb x]
  intro w hw
  obtain ⟨c, hc, hev⟩ := hx w hw (1 / 2) (by norm_num)
  obtain ⟨N, hN, hN0⟩ := (hev.and (eventually_gt_atTop (0:ℕ))).exists
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hpow : (0 : ℝ) < (N : ℝ) ^ (1 - 1 / 2 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hposc : (0 : ℝ) < (occCount b x w N : ℝ) := lt_of_lt_of_le (by positivity) hN
  have hcard : 0 < occCount b x w N := by exact_mod_cast hposc
  rw [occCount] at hcard
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hcard
  exact ⟨n, (Finset.mem_filter.mp hn).2⟩

/-! ### The chain, run along a filter of scales

Everything between the exponential-sum hypothesis and the occurrence count is *pointwise* in `N`
(the covering and disjointness inputs of `density_lower_of_decoupleR` are `∀ N`); the only place
the scale filter enters is the decoupling limit.  So the whole route generalises verbatim from
`atTop` to any filter `l ≤ atTop`, and that is what lets an exceptional set of scales be carried
through to the end and then absorbed.
-/

/-- Leaf B′ along a filter of scales. -/
def TailLargeDecoupleCAt (l : Filter ℕ) (b P Q : ℕ) : Prop :=
  ∀ (r : ℕ) (θ : ℝ) (g : C(AddCircle (1 : ℝ), ℝ)),
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N,
        classWeight r Q n * g (((θ + tailLarge P b n : ℝ)) : AddCircle (1 : ℝ))) / N)
      l (𝓝 0)

/-- The counting core along a filter.  Verbatim `density_lower_of_decoupleR` with `atTop`
replaced by `l`; positivity of `N` is inherited through `l ≤ atTop`. -/
lemma density_lower_of_decoupleR_at {l : Filter ℕ} (hl : l ≤ atTop) {Q M : ℕ} (hQ : 0 < Q)
    (A B : ℕ → ℕ → ℝ) (C : ℕ → ℕ)
    (hdec : ∀ k, k < M → Tendsto (fun N : ℕ => ((A k N - B k N / Q) / N)) l (𝓝 0))
    (hcov : ∀ N : ℕ, (N : ℝ) ≤ ∑ k ∈ range M, B k N)
    (hdisj : ∀ N, ∑ k ∈ range M, A k N ≤ (C N : ℝ)) :
    ∀ᶠ N in l, (1 / (2 * (Q : ℝ))) * N ≤ (C N : ℝ) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hg : Tendsto (fun N : ℕ => ∑ k ∈ range M, ((A k N - B k N / Q) / N)) l (𝓝 0) := by
    have := tendsto_finsetSum (range M) (fun k hk => hdec k (mem_range.1 hk))
    simpa using this
  have hneg : -(1 / (2 * (Q : ℝ))) < 0 := by
    have : (0 : ℝ) < 1 / (2 * Q) := by positivity
    linarith
  have hev := Filter.Tendsto.eventually_const_lt hneg hg
  filter_upwards [hev, (eventually_gt_atTop 0).filter_mono hl] with N hN hN0
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hQ' : (Q : ℝ) ≠ 0 := ne_of_gt hQR
  have hN' : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hsplit : ∑ k ∈ range M, ((A k N - B k N / Q) / N)
      = (∑ k ∈ range M, A k N) / N - (∑ k ∈ range M, B k N) / (Q * N) := by
    have hterm : ∀ k : ℕ, ((A k N - B k N / Q) / N) = A k N / N - B k N / (Q * N) := by
      intro k; field_simp
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  rw [hsplit] at hN
  have hBd : (1 : ℝ) / Q ≤ (∑ k ∈ range M, B k N) / (Q * N) := by
    rw [div_le_div_iff₀ hQR (by positivity)]
    nlinarith [hcov N]
  have hA : (1 : ℝ) / (2 * Q) ≤ (∑ k ∈ range M, A k N) / N := by
    have hhalf : (1 : ℝ) / (2 * Q) + 1 / (2 * Q) = 1 / Q := by field_simp; ring
    linarith
  have := (le_div_iff₀ hNR).1 hA
  linarith [hdisj N]

/-- The rotation route along a filter of scales. -/
def RotationRouteCAt (l : Filter ℕ) (b : ℕ) : Prop :=
  ∀ α len : ℝ, 0 ≤ α → 0 < len → α + len ≤ 1 →
    ∃ (P Q M : ℕ) (a : ℕ → ℕ), 0 < Q ∧ 0 < M ∧
      (∀ p, p ≤ P → p.Prime → p ∣ Q) ∧
      (∀ k, k < M → ∀ k', k' < M → a k ≡ a k' [MOD Q] → k = k') ∧
      RotationCover b P M a α len ∧ TailLargeDecoupleCAt l b P Q

/-- **Richness along a filter of scales.**  This is `isRich_of_rotationRouteC` with the scale
filter as a parameter: the covering and disjointness steps are unchanged (they hold for every
`N`), and the conclusion is a lower bound on the occurrence count at the scales of `l`. -/
theorem occCount_lower_of_rotationRouteCAt {l : Filter ℕ} (hl : l ≤ atTop) {b : ℕ} (hb : 2 ≤ b)
    (H : RotationRouteCAt l b) (w : List ℕ) (hw : ∀ d ∈ w, d < b) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in l,
      c * N ≤ (occCount b (primeLambertAtBase b) w N : ℝ) := by
  classical
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
  have hGzero : ∀ k n, ¬ (Int.fract (θ k + tailLarge P b n) ∈ Set.Ico α (α + len)) →
      G k n = 0 := by
    intro k n hn
    rw [hGfr k n, hg]
    exact trapLo_eq_zero_outside α (α + len) δ _ hα0 (by linarith) hαlen
      (Int.fract_nonneg _) (Int.fract_lt_one _) (by simpa [Set.mem_Ico] using hn) hδ0
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
  set Cc : ℕ → ℕ := fun N => occCount b (primeLambertAtBase b) w N with hCc
  have hdecA : ∀ k, k < M → Tendsto (fun N : ℕ => ((A k N - B k N / Q) / N)) l (𝓝 0) := by
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
      show _ ≤ occCount b (primeLambertAtBase b) w N
      rw [occCount]
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
  exact density_lower_of_decoupleR_at hl hQ0 A B Cc hdecA hcovN hdisjN

/-! ### The re-plumbed hypothesis, and the theorem it buys -/

/-- **`WeylTailAlong l b`** — the C3 crux restricted to the scales of `l`. -/
def WeylTailAlong (l : Filter ℕ) (b : ℕ) : Prop :=
  ∀ (P Q r : ℕ) (θ : ℝ) (h : ℤ), 0 < Q →
    Tendsto (wFourierMean (fun n => θ + tailLarge P b n) (classWeight r Q) h) l (𝓝 0)

theorem tailLargeDecoupleCAt_of_weylAlong {l : Filter ℕ} {b : ℕ} (P Q : ℕ) (hQ : 0 < Q)
    (H : WeylTailAlong l b) : TailLargeDecoupleCAt l b P Q :=
  fun r θ g => wgoodAt_real l (fun n => θ + tailLarge P b n) (classWeight r Q)
    (abs_classWeight_le r Q) (fun h => H P Q r θ h hQ) g

theorem rotationRouteCAt_of_weylAlong {l : Filter ℕ} {b : ℕ} (hb : 2 ≤ b)
    (H : WeylTailAlong l b) : RotationRouteCAt l b := by
  intro α len hα hlen hαlen
  obtain ⟨P, Q, M, a, hQ0, hM0, hQP, hPQ, hinj, hcov⟩ :=
    exists_rotationCover_core hb α len hα hlen hαlen
  exact ⟨P, Q, M, a, hQ0, hM0, hQP, hinj, hcov,
    tailLargeDecoupleCAt_of_weylAlong P Q hQ0 H⟩

/-- **`WeylTailAlmostAll b`** — the form of the C3 crux that Pilatte 2025 / Tao–Teräväinen 2025
Theorem 3.1 actually supplies: for every `ε > 0` the twisted mean vanishes along a set of scales
whose gaps are shorter than `M^{1-ε}`.  (Theorem 3.1 gives an exceptional set `E` of logarithmic
density `≪ L^{−c}` with `L` free, so a maximal gap has logarithmic length `≤ ε log M` for every
fixed `ε > 0` once `L` is a large enough power of log.)  This is *strictly weaker* than
`WeylTailHypothesis b`, which is the `S = univ` case. -/
def WeylTailAlmostAll (b : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ S : Set ℕ, ScalesDense ε S ∧ WeylTailAlong (atTop ⊓ 𝓟 S) b

theorem weylTailAlmostAll_of_weylTailHypothesis {b : ℕ} (H : WeylTailHypothesis b) :
    WeylTailAlmostAll b := by
  intro ε hε
  refine ⟨Set.univ, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with M hM
    refine ⟨M, Set.mem_univ _, ?_, le_rfl⟩
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    calc (M : ℝ) ^ (1 - ε) ≤ (M : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      _ = (M : ℝ) := Real.rpow_one _
  · intro P Q r θ h hQ
    exact (H P Q r θ h hQ).mono_left inf_le_left

/-- **Rung 0.**  From the almost-all-scales form of the C3 crux, `G_b` is *subpolynomially rich*:
every word occurs at `≥ N^{1−ε}` positions below `N`, for every `ε > 0`.  The bad scales are
absorbed by monotonicity of the occurrence count — the step that `ConjC1`'s two-sided `CastLaw`
cannot perform. -/
theorem isRichSubpoly_of_weylTailAlmostAll {b : ℕ} (hb : 2 ≤ b) (H : WeylTailAlmostAll b) :
    IsRichSubpoly b (primeLambertAtBase b) := by
  classical
  intro w hw ε hε
  set ε' : ℝ := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε'le : ε' ≤ ε := min_le_left _ _
  obtain ⟨S, hS, HW⟩ := H ε' hε'0
  obtain ⟨c, hc, hev⟩ := occCount_lower_of_rotationRouteCAt (l := atTop ⊓ 𝓟 S) inf_le_left hb
    (rotationRouteCAt_of_weylAlong hb HW) w hw
  rw [Filter.eventually_inf_principal] at hev
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hev
  have hgood : ∀ N ∈ S ∩ {N | M₀ ≤ N},
      c * (N : ℝ) ≤ (occCount b (primeLambertAtBase b) w N : ℝ) := by
    intro N hN
    exact hM₀ N hN.2 hN.1
  have habs := lower_of_monotone_of_scalesDense
    (monotone_occCount b (primeLambertAtBase b) w) hc.le (hS.inter_Ici hε'1 M₀) hgood
  refine ⟨c, hc, ?_⟩
  filter_upwards [habs, eventually_ge_atTop 1] with N hN hN1
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hmono : (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) ^ (1 - ε') :=
    Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
  exact (mul_le_mul_of_nonneg_left hmono hc.le).trans hN

end CastingOut

end NormalNumbers
