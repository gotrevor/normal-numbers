/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitSquareNonNormal
import NormalNumbers.PowerBaseReal
import NormalNumbers.Wall
import NormalNumbers.WeylCriterion
import NormalNumbers.DecayAeNormal

/-!
# Levin's rate in base 2, normal in every odd base

Audit: `docs/LEVIN-SPARSE-AUDIT-2026-10-03.md` (sweep `docs/OPEN-PROBLEMS-SWEEP-2026-10-03b.md` §3).

**Target.**  A real `x` normal in base 2 (hence in every `2^k`) and in every odd base `r ≥ 3`,
whose base-2 star discrepancy is `D*_N(2ⁿx) = O((log N)²/N)`, Levin's one-base rate.  For
normality in more than one base, the best published rate is `O(N^{-1/2})` in every base
(Aistleitner–Becher–Scheerer–Slaman, arXiv 1707.02628, who call `N^{-1/2}` "a kind of barrier";
Manai 2508.09319 §1 still calls lower discrepancy "a very difficult … problem").  The target
beats the barrier in one base while keeping normality in the odd bases.

**Mechanism.**  `x = α + y`.  `α` is Levin's base-2 number (`Literature.Levin1999`).  `y` is a
random point of Becher–Lew Deveali's sparse Cantor set `C(S)` (2607.06773): binary digits are
`0` off a sparse set `S`, fair coins on it.
* **Base 2, every `y ∈ C(S)` at once.**  `{2ⁿy}` is below `2/N` except when an element of `S`
  lies in `(n, n + log₂N + 1]`; there are at most `(log₂N + 2)·#(S ∩ [1, 2N])` such `n`
  (`fract_bldPoint_small`).  Moving all but those points by at most `2/N` costs
  `2D + 2/N + #B/N` (`discLe_fract_add`).  With `#(S ∩ [1,N]) = O(log N)`, which BLD's own
  example `{⌈e^{j/100}⌉}` has (`sIcc_expSet_le`), the total is `O((log N)²/N)`.
* **Odd bases, `μ_S`-a.e. `y`.**  BLD's second-moment bound (proof of Lemma 7) bounds the cosine
  double sum `N⁻² Σ_{p,q} Π_{k∈S} |cos(π h(rᵖ − r^q)/2ᵏ)|` (`bld_doubleSum_le`, from the cited
  Lemma 5).  The second moment of the **translate** `α + y` is bounded by the same double sum
  (`secondMoment_translate_le`: translation multiplies each Fourier coefficient by a unimodular
  phase).  Davenport–Erdős–LeVeque (`del_ae_tendsto`) then gives Weyl's criterion a.s.

**Why even bases are blocked** (not claimed): for `r = 2ᵃm`, `a ≥ 1`, `m > 1` odd, the frequency
`h(rᵖ − r^q)` is divisible by `2^{aq}`, so only the positions of `S` in `(aq, O(p)]` matter.  A
sparse `S` with `#(S ∩ [1,N]) = O(log N)` has `O(1)` points there, so the cosine product does not
tend to `0` and the second-moment route gives nothing; BLD Theorem 2 even puts base-6 non-normal
points in `C(S)`.  Base `4 = 2²` is fine: it follows from base 2 (`PowerBase.isNormal_pow`).

**Known-false siblings** (the mechanism must refuse them, and does):
* dense digits (`S = {k ≥ 1}`): the base-2 perturbation budget is `≥ 1`
  (`perturbBudget_dense_ge_one`, proved), and indeed some `y` in the dense set makes `α + y`
  non-normal in base 2 (`exists_not_isNormal_two_dense`), so the "every `y`" base-2 claim needs
  sparsity;
* the base-2 bound for `y` alone (`α = 0`): every `y ∈ C(S)` has digit-1 frequency `0`, so it is
  not normal in base 2; the content is in the `α` + sparse-`y` split.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.LevinSparse

open DecayAeNormal ExplicitSquare

/-! ## Definitions -/

/-- **Star discrepancy bound**: `D*_N(u) ≤ D`, with `D*_N(u) = sup_{c∈[0,1]} |#{n<N : u n ∈ [0,c)}/N − c|`
(Levin 1999 eq. (1), up to the endpoint `c = 0`, where the term is `0`). -/
def DiscLe (u : ℕ → ℝ) (N : ℕ) (D : ℝ) : Prop :=
  ∀ c ∈ Set.Icc (0 : ℝ) 1, |(visitCount u 0 c N : ℝ) / N - c| ≤ D

theorem DiscLe.mono {u : ℕ → ℝ} {N : ℕ} {D D' : ℝ} (h : DiscLe u N D) (hD : D ≤ D') :
    DiscLe u N D' := fun c hc => (h c hc).trans hD

/-- BLD's `S(a, c) = #(S ∩ [a, c])` (inclusive). -/
noncomputable def sIcc (S : Set ℕ) (a c : ℕ) : ℕ := by
  classical exact ((Finset.Icc a c).filter (· ∈ S)).card

/-- **Sparse set** (Becher–Lew Deveali 2607.06773, Definition "Sparse set"), in a form that
implies theirs: `S ⊆ ℤ_{>0}`, density zero, and a sparsity exponent `ρ > 0` with
`S(a, a+k) ≥ (1+ε)·30 log k` for all large `k` and all `0 ≤ a ≤ k^ρ`.  Theirs is
`liminf_k min_{0≤a≤k^ρ} S(a,a+k)/(30 log k) > 1`, which is equivalent to the existence of such
an `ε`.  (Taking the margin explicitly keeps every cited Prop quantified over `Sparse` no
stronger than BLD's lemma.) -/
def Sparse (S : Set ℕ) (ρ : ℝ) : Prop :=
  0 ∉ S ∧ Tendsto (fun n : ℕ => (sIcc S 1 n : ℝ) / n) atTop (𝓝 0) ∧ 0 < ρ ∧
    ∃ ε : ℝ, 0 < ε ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → ∀ a : ℕ, (a : ℝ) ≤ (k : ℝ) ^ ρ →
      (1 + ε) * (30 * Real.log k) ≤ sIcc S a (a + k)

/-- **The point of `C(S)` coded by `ω`**: binary digit `k` (weight `2^{-k}`, `k ≥ 1`) is `ω k`
for `k ∈ S` and `0` otherwise (BLD Definition "Sparse Cantor set").  Under fair coins its law is
BLD's measure `μ(S)`. -/
noncomputable def bldPoint (S : Set ℕ) (ω : ℕ → Bool) : ℝ := by
  classical exact ∑' k : ℕ, (if k ∈ S ∧ ω k = true then (1 : ℝ) else 0) / 2 ^ k

/-- **The Riesz tail** `Π_{k∈S, k>a} |cos(π t / 2^{k-a})|`, as the infimum of its partial
products (which decrease in `M`, every factor lying in `[0,1]`), so it is the infinite product
with no junk value.  `|μ̂_S(t)| = rieszTail S 0 t` (BLD §2). -/
noncomputable def rieszTail (S : Set ℕ) (a : ℕ) (t : ℝ) : ℝ := by
  classical exact ⨅ M : ℕ,
    ∏ k ∈ (Finset.Ioc a M).filter (· ∈ S), |Real.cos (Real.pi * t / 2 ^ (k - a))|

/-- BLD's own example of a sparse set (2607.06773 §1: "Also `{⌈e^{j/100}⌉ : j ≥ 1}` is sparse"). -/
def expSet : Set ℕ := {k | ∃ j : ℕ, 1 ≤ j ∧ k = ⌈Real.exp ((j : ℝ) / 100)⌉₊}

/-! ## Cited inputs -/

namespace Literature

/-- **Levin 1999.**  M. B. Levin, *On the discrepancy estimate of normal numbers*, Acta Arith. 88
(1999) 99–111, **Theorem 2** (base `q = 2` here): the explicit
`α = Σ_{m≥1} q^{-n_m} Σ_{0≤n<q^{2^m}} q^{-n2^m} Σ_{i=1}^{2^m} d_i(n) q^{-i}`
(`d_i(n)` from Pascal's triangle mod 2 applied to the base-`q` digits of `n`) is normal to base
`q` with `D(N, {αqⁿ}) = O(N⁻¹ log² N)`, `D` the star discrepancy of eq. (1).  An `O` for
`N → ∞` with a fixed constant covers all `N ≥ 2` after enlarging the constant (each `D ≤ 1`,
`log² N / N > 0`).  Faithful-or-weaker: existential in `α`, star discrepancy, base 2 only.
Quoted the same way in ABSS 1707.02628 §1 and Alvarez–Becher 1510.02004 §1. -/
def Levin1999 : Prop :=
  ∃ α C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → DiscLe (orbit 2 α) N (C * Real.log N ^ 2 / N)

/-- **Becher–Lew Deveali, Lemma 5** (2607.06773v1, §2, p. 8), with the threshold of Lemmas 1,
3, 4 made explicit.  For sparse `S` with exponent `ρ`, integers `a ≥ 0`, odd `r ≥ 3`, odd
`ℓ > 0` and `N ≥ δ₄(a)`:
`Σ_{n<N} Π_{k∈S,k>a} |cos(πℓrⁿ/2^{k−a})| ≤ 2^{ν₂(r²−1)+2} N/(log N)^{1.005}`.
Their threshold: `δ₄(a) = 2^{δ₃(a)}`, `δ₃(a) = max(δ₁(a), 10³⁰)`, `δ₁(a) = (a^{1/ρ}+1)K_S`
(Lemma 1, `K_S ≥ 2` depending only on `S`).  Here the threshold is
`2^{K(a+1)^{1/ρ} + 10³⁰}`, which is `≥ δ₄(a)` for `K = 3K_S` (so this Prop is implied by
theirs, possibly-ceiling'd `δ₁` included).  `Sparse` implies their sparsity, so the Prop is
faithful-or-weaker. -/
def BLDLemma5 : Prop :=
  ∀ (S : Set ℕ) (ρ : ℝ), Sparse S ρ → ∃ K : ℝ, 0 < K ∧
    ∀ a ℓ r N : ℕ, Odd ℓ → Odd r → 3 ≤ r →
      (2 : ℝ) ^ (K * ((a : ℝ) + 1) ^ (1 / ρ) + 10 ^ 30) ≤ N →
        ∑ n ∈ Finset.range N, rieszTail S a ((ℓ : ℝ) * (r : ℝ) ^ n) ≤
          (2 : ℝ) ^ (padicValNat 2 (r ^ 2 - 1) + 2) * N / Real.log N ^ (1.005 : ℝ)

end Literature

/-! ## Base 2: the sparse perturbation barely moves the discrepancy -/

theorem visitCount_zero_eq (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Set.Ico (0 : ℝ) 1) (c : ℝ) (N : ℕ) :
    visitCount u 0 c N = ((Finset.range N).filter fun n => u n < c).card := by
  unfold visitCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Set.mem_Ico]
  constructor
  · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (hu n).1, h2⟩

/-- **Shift lemma.**  Moving all points outside `B` up by at most `η` (mod 1) costs at most
`2D + η + #B/N` in star discrepancy.

Confidence 92%.  Proof: for `n ∉ B`, `v_n := fract(u_n + δ_n)` satisfies
`u_n < c − η ⇒ v_n < c` and `v_n < c ⇒ u_n < c ∨ u_n ≥ 1 − η` (wrap-around).  So
`#{v < c} ≥ N(c − η − D) − #B` and `#{v < c} ≤ N(c + D) + N(η + D) + #B`, using
`#{u ≥ 1−η} = N − #{u < 1−η} ≤ N(η + D)`.  Edge cases `c < η`, `η ≥ 1`, `N = 0` are trivial
(`DiscLe u 0 D` forces `D ≥ 1`). -/
theorem discLe_fract_add (u δ : ℕ → ℝ) (N : ℕ) (D η : ℝ) (B : Finset ℕ)
    (hu : ∀ n, u n ∈ Set.Ico (0 : ℝ) 1) (hδ0 : ∀ n, 0 ≤ δ n) (hη : 0 ≤ η)
    (hδ : ∀ n < N, n ∉ B → δ n ≤ η) (hD : DiscLe u N D) :
    DiscLe (fun n => Int.fract (u n + δ n)) N (2 * D + η + B.card / N) := by
  intro c hc
  set v : ℕ → ℝ := fun n => Int.fract (u n + δ n) with hv
  have hvI : ∀ n, v n ∈ Set.Ico (0 : ℝ) 1 := fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 := hD 1 ⟨zero_le_one, le_rfl⟩
    simp at h1 ⊢
    rw [abs_of_nonneg hc.1]
    nlinarith [hc.2, abs_nonneg D]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0 ⟨le_rfl, zero_le_one⟩)
  set U : ℝ → ℕ := fun c => ((Finset.range N).filter fun n => u n < c).card with hUdef
  have hUb : ∀ c ∈ Set.Icc (0 : ℝ) 1, N * (c - D) ≤ U c ∧ (U c : ℝ) ≤ N * (c + D) := by
    intro c hc
    have := hD c hc
    rw [visitCount_zero_eq u hu] at this
    rw [abs_le] at this
    obtain ⟨h1, h2⟩ := this
    constructor
    · have := (le_div_iff₀ hNR).1 (by linarith : c - D ≤ (U c : ℝ) / N); linarith
    · have := (div_le_iff₀ hNR).1 (by linarith : (U c : ℝ) / N ≤ c + D); linarith
  set V := ((Finset.range N).filter fun n => v n < c).card with hVdef
  have hBc : (((Finset.range N).filter fun n => n ∈ B).card : ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_le_card (fun n hn => (Finset.mem_filter.1 hn).2)
  -- lower bound
  have hlow : (N : ℝ) * (c - η - D) ≤ V + B.card := by
    by_cases hce : 0 ≤ c - η
    · have hsub : (Finset.range N).filter (fun n => u n < c - η) ⊆
          ((Finset.range N).filter fun n => v n < c) ∪ (Finset.range N).filter fun n => n ∈ B := by
        intro n hn
        obtain ⟨hnN, hun⟩ := Finset.mem_filter.1 hn
        by_cases hnB : n ∈ B
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hnN, hnB⟩)
        · refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hnN, ?_⟩)
          have := hδ n (Finset.mem_range.1 hnN) hnB
          have hlt : u n + δ n < 1 := by linarith [hc.2]
          simp only [hv]
          rw [Int.fract_eq_self.2 ⟨by linarith [(hu n).1, hδ0 n], hlt⟩]
          linarith
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le ((Finset.range N).filter fun n => v n < c)
        ((Finset.range N).filter fun n => n ∈ B)
      have h3 : (U (c - η) : ℝ) ≤ V + B.card := by
        have : U (c - η) ≤ V + ((Finset.range N).filter fun n => n ∈ B).card := h1.trans h2
        have : (U (c - η) : ℝ) ≤ V + (((Finset.range N).filter fun n => n ∈ B).card : ℝ) := by
          exact_mod_cast this
        linarith
      have := (hUb (c - η) ⟨hce, by linarith [hc.2]⟩).1
      linarith
    · push Not at hce
      have : (N : ℝ) * (c - η - D) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hNR.le (by linarith)
      have : (0 : ℝ) ≤ V + B.card := by positivity
      linarith
  -- upper bound
  have hup : (V : ℝ) ≤ B.card + N * (c + D) + N * (η + D) := by
    by_cases hη1 : η ≤ 1
    · have hsub : (Finset.range N).filter (fun n => v n < c) ⊆
          (((Finset.range N).filter fun n => n ∈ B) ∪ (Finset.range N).filter fun n => u n < c) ∪
            (Finset.range N).filter fun n => ¬ u n < 1 - η := by
        intro n hn
        obtain ⟨hnN, hvn⟩ := Finset.mem_filter.1 hn
        by_cases hnB : n ∈ B
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hnN, hnB⟩))
        by_cases hu1 : u n < 1 - η
        · refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hnN, ?_⟩))
          have := hδ n (Finset.mem_range.1 hnN) hnB
          have hlt : u n + δ n < 1 := by linarith
          simp only [hv] at hvn
          rw [Int.fract_eq_self.2 ⟨by linarith [(hu n).1, hδ0 n], hlt⟩] at hvn
          linarith [hδ0 n]
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hnN, hu1⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (((Finset.range N).filter fun n => n ∈ B) ∪
        (Finset.range N).filter fun n => u n < c) ((Finset.range N).filter fun n => ¬ u n < 1 - η)
      have h3 := Finset.card_union_le ((Finset.range N).filter fun n => n ∈ B)
        ((Finset.range N).filter fun n => u n < c)
      have h4 := Finset.card_filter_add_card_filter_not (s := Finset.range N)
        (p := fun n => u n < 1 - η)
      rw [Finset.card_range] at h4
      have hU1 := (hUb (1 - η) ⟨by linarith, by linarith⟩).1
      have hUc := (hUb c hc).2
      have h5 : (V : ℝ) ≤ ((Finset.range N).filter fun n => n ∈ B).card + U c +
          ((Finset.range N).filter fun n => ¬ u n < 1 - η).card := by
        exact_mod_cast h1.trans (h2.trans (Nat.add_le_add_right h3 _))
      have h6 : (((Finset.range N).filter fun n => ¬ u n < 1 - η).card : ℝ) = N - U (1 - η) := by
        have : (U (1 - η) : ℝ) + ((Finset.range N).filter fun n => ¬ u n < 1 - η).card = N := by
          exact_mod_cast h4
        linarith
      linarith
    · have : V ≤ N := by
        simpa using Finset.card_filter_le (Finset.range N) (fun n => v n < c)
      have : (V : ℝ) ≤ N := by exact_mod_cast this
      push Not at hη1
      have : (N : ℝ) ≤ N * (η + D) := by nlinarith
      have : 0 ≤ (N : ℝ) * (c + D) := by nlinarith [hc.1]
      have : (0 : ℝ) ≤ B.card := by positivity
      linarith
  rw [visitCount_zero_eq v hvI, ← hVdef, abs_le]
  have hBN : (B.card : ℝ) / N * N = B.card := div_mul_cancel₀ _ hNR.ne'
  have hVN : (V : ℝ) / N * N = V := div_mul_cancel₀ _ hNR.ne'
  constructor
  · refine le_of_mul_le_mul_right ?_ hNR
    nlinarith
  · refine le_of_mul_le_mul_right ?_ hNR
    nlinarith

theorem not_isNormal_two_zero_aux : ¬ IsNormal 2 0 := by
  intro h
  have hcount : ∀ l : List ℕ, (∀ d ∈ l, d = 0) → countOccurrences [1] l = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      have ha : a = 0 := hl a (List.mem_cons_self ..)
      have ih' := ih fun d hd => hl d (List.mem_cons_of_mem _ hd)
      unfold countOccurrences at ih' ⊢
      rw [List.tails_cons, List.countP_cons, ih', ha]
      rfl
  have hdig : ∀ i, digitOf 2 (Int.fract (0 : ℝ)) i = 0 := by
    intro i; simp [digitOf]
  have ht := h [1] (by simp) (by simp)
  have h0 : (fun n : ℕ => (countOccurrences [1] ((List.range n).map
      (digitOf 2 (Int.fract (0 : ℝ)))) : ℝ) / n) = fun _ => 0 := by
    funext n
    rw [hcount _ (fun d hd => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hd; exact hdig i)]
    simp
  rw [h0] at ht
  have := tendsto_nhds_unique ht tendsto_const_nhds
  norm_num at this

/-- Binary expansion: `z ∈ [0,1)` is the sum of its digits. -/

theorem hasSum_digitOf_two (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun i => (digitOf 2 z i : ℝ) / 2 ^ (i + 1)) z := by
  set F : ℕ → ℤ := fun n => ⌊z * 2 ^ n⌋ with hF
  have hstep : ∀ n, (digitOf 2 z n : ℝ) = F (n + 1) - 2 * F n := by
    intro n
    have h1 : (2 : ℝ) * F n ≤ z * 2 ^ (n + 1) := by
      have := Int.floor_le (z * 2 ^ n); rw [pow_succ]; simp only [hF]; linarith
    have h2 : z * 2 ^ (n + 1) < 2 * F n + 2 := by
      have := Int.lt_floor_add_one (z * 2 ^ n); rw [pow_succ]; simp only [hF]; linarith
    have hlo : 2 * F n ≤ F (n + 1) := by
      simp only [hF]; rw [Int.le_floor]; push_cast; simpa [hF] using h1
    have hhi : F (n + 1) < 2 * F n + 2 := by
      simp only [hF]; rw [Int.floor_lt]; push_cast; simpa [hF] using h2
    have hF0 : 0 ≤ F n := by simp only [hF]; exact Int.floor_nonneg.2 (by positivity)
    unfold digitOf
    have : (⌊z * ((2 : ℕ) : ℝ) ^ (n + 1)⌋) = F (n + 1) := by simp [hF]
    rw [this]
    rcases (show F (n + 1) = 2 * F n ∨ F (n + 1) = 2 * F n + 1 by omega) with h | h
    · rw [h]
      have : (2 * F n).toNat % 2 = 0 := by omega
      rw [this]; push_cast; ring
    · rw [h]
      have : (2 * F n + 1).toNat % 2 = 1 := by omega
      rw [this]; push_cast; ring
  have hpart : ∀ n, ∑ i ∈ Finset.range n, (digitOf 2 z i : ℝ) / 2 ^ (i + 1) = F n / 2 ^ n := by
    intro n
    induction n with
    | zero => simp [hF, Int.floor_eq_zero_iff.2 ⟨hz0, hz1⟩]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hstep, pow_succ]
      field_simp
      ring
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity)]
  simp_rw [hpart]
  have hlo : ∀ n : ℕ, z - (1 / 2) ^ n ≤ (F n : ℝ) / 2 ^ n := by
    intro n
    have := Int.lt_floor_add_one (z * 2 ^ n)
    rw [one_div_pow, le_div_iff₀ (by positivity), sub_mul, div_mul_cancel₀ _ (by positivity)]
    simp only [hF]; linarith
  have hhi : ∀ n : ℕ, (F n : ℝ) / 2 ^ n ≤ z := by
    intro n
    rw [div_le_iff₀ (by positivity)]; exact Int.floor_le _
  have hg : Tendsto (fun n : ℕ => z - (1 / 2 : ℝ) ^ n) atTop (𝓝 z) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ))
      (by norm_num) (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg tendsto_const_nhds hlo hhi

/-- **Digit tail of a sparse point.**  `{2ⁿy} ≤ 2/N` except for at most
`(log₂N + 2)·S(1, N + log₂N + 2)` indices `n < N`.

Confidence 92%.  Proof: `B = {n < N : ∃ k ∈ S, n < k ≤ n + L}`, `L = Nat.log 2 N + 1`.  Each
`k ∈ S ∩ [1, N+L]` puts at most `L` indices `n ∈ [k−L, k)` in `B`.  For `n ∉ B` the binary digits
of `y` at positions `n+1, …, n+L` vanish, so `{2ⁿy} = Σ_{k∈S, k>n+L} b_k 2^{n−k} ≤ 2^{−L} < 1/N`
(the digits `k ≤ n` contribute integers, and the tail is `< 1`). -/
theorem fract_bldPoint_small (S : Set ℕ) (hS0 : 0 ∉ S) (ω : ℕ → Bool) (N : ℕ) (hN : 2 ≤ N) :
    ∃ B : Finset ℕ, (B.card : ℝ) ≤ (Nat.log 2 N + 2) * sIcc S 1 (N + Nat.log 2 N + 2) ∧
      ∀ n < N, n ∉ B → Int.fract (bldPoint S ω * 2 ^ n) ≤ 2 / N := by
  classical
  set L := Nat.log 2 N + 1 with hL
  set c : ℕ → ℝ := fun k => if k ∈ S ∧ ω k = true then 1 else 0 with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => by simp only [hc]; split_ifs <;> norm_num
  have hc1 : ∀ k, c k ≤ 1 := fun k => by simp only [hc]; split_ifs <;> norm_num
  have hy : bldPoint S ω = ∑' k, c k / 2 ^ k := by
    unfold bldPoint; simp only [hc]
  set B := (Finset.range N).filter (fun n => ∃ k ∈ S, n < k ∧ k ≤ n + L) with hB
  refine ⟨B, ?_, ?_⟩
  · set T := (Finset.Icc 1 (N + Nat.log 2 N + 2)).filter (· ∈ S) with hT
    have hsub : B ⊆ T.biUnion (fun k => Finset.Ico (k - L) k) := by
      intro n hn
      simp only [hB, Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨hnN, k, hkS, hnk, hkn⟩ := hn
      simp only [Finset.mem_biUnion, hT, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      exact ⟨k, ⟨⟨by omega, by omega⟩, hkS⟩, by omega, hnk⟩
    have hcard : B.card ≤ T.card * L := by
      refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
      rw [Finset.card_eq_sum_ones T, Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      simp; omega
    have hTs : sIcc S 1 (N + Nat.log 2 N + 2) = T.card := by
      unfold sIcc; simp only [hT]
    rw [hTs]
    have : (B.card : ℝ) ≤ (T.card : ℝ) * L := by exact_mod_cast hcard
    have hL2 : (L : ℝ) ≤ Nat.log 2 N + 2 := by simp only [hL]; push_cast; linarith
    nlinarith [(Nat.cast_nonneg T.card : (0:ℝ) ≤ _)]
  · intro n hn hnB
    have hgap : ∀ k, n < k → k ≤ n + L → c k = 0 := by
      intro k h1 h2
      simp only [hc]
      rw [if_neg]
      rintro ⟨hkS, -⟩
      exact hnB (by simp only [hB, Finset.mem_filter, Finset.mem_range]; exact ⟨hn, k, hkS, h1, h2⟩)
    have hgs : Summable fun k => c k / (2 : ℝ) ^ k := by
      refine Summable.of_nonneg_of_le (fun k => by have := hc0 k; positivity) (fun k => ?_)
        (summable_geometric_two)
      rw [one_div_pow]; exact div_le_div_of_nonneg_right (hc1 k) (by positivity)
    set m := n + 1 with hm
    have hsplit := (hgs.sum_add_tsum_nat_add (m + L)).symm
    set t : ℝ := (∑' k, c (k + (m + L)) / (2 : ℝ) ^ (k + (m + L))) * 2 ^ n with ht
    have hmid : ∑ k ∈ Finset.range (m + L), c k / (2 : ℝ) ^ k = ∑ k ∈ Finset.range m, c k / 2 ^ k := by
      rw [Finset.sum_range_add, add_eq_left]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [hgap (m + j) (by omega) (by omega), zero_div]
    set I : ℕ := ∑ k ∈ Finset.range m, (if k ∈ S ∧ ω k = true then 2 ^ (n - k) else 0) with hI
    have hhead : (∑ k ∈ Finset.range m, c k / (2 : ℝ) ^ k) * 2 ^ n = (I : ℝ) := by
      rw [Finset.sum_mul, hI]; push_cast
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp only [hc]
      split_ifs
      · rw [show (2 : ℝ) ^ n = 2 ^ (n - k) * 2 ^ k by rw [← pow_add]; congr 1; omega]
        field_simp
      · simp
    have hyn : bldPoint S ω * 2 ^ n = t + I := by
      rw [hy, hsplit, hmid, add_mul, hhead, ht]; ring
    have ht0 : 0 ≤ t := by
      rw [ht]; exact mul_nonneg (tsum_nonneg fun k => by have := hc0 (k + (m + L)); positivity) (by positivity)
    have hgeo : Summable fun k : ℕ => (1 / 2 : ℝ) ^ (k + (m + L)) :=
      (summable_nat_add_iff (f := fun k : ℕ => (1 / 2 : ℝ) ^ k) (m + L)).2 summable_geometric_two
    have ht1 : t ≤ (1 / 2 : ℝ) ^ L := by
      have hle : ∑' k, c (k + (m + L)) / (2 : ℝ) ^ (k + (m + L)) ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ (k + (m + L)) := by
        refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff (f := fun k => c k / (2 : ℝ) ^ k) (m + L)).2 hgs) hgeo
        rw [one_div_pow]; exact div_le_div_of_nonneg_right (hc1 _) (by positivity)
      have heq : (∑' k : ℕ, (1 / 2 : ℝ) ^ (k + (m + L))) * 2 ^ n = (1 / 2) ^ L := by
        simp_rw [pow_add]
        rw [tsum_mul_right, tsum_geometric_two, hm, pow_add, pow_add]
        ring_nf
        have h1 : (1/2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
        linear_combination ((1 / 2 : ℝ) ^ Nat.log 2 N * (1 / 2)) * h1
      rw [ht, ← heq]
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    have hLN : (N : ℝ) < 2 ^ L := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) N
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hpow : (1 / 2 : ℝ) ^ L ≤ 2 / N := by
      rw [one_div_pow, div_le_div_iff₀ (by positivity) hNpos]; linarith
    have hlt : t < 1 := by
      have : (2 : ℝ) / N ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast hN
      have : (1 / 2 : ℝ) ^ L < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      linarith
    rw [hyn, Int.fract_add_natCast, Int.fract_eq_self.2 ⟨ht0, hlt⟩]
    linarith

theorem bldPoint_nonneg (S : Set ℕ) (ω : ℕ → Bool) : 0 ≤ bldPoint S ω := by
  unfold bldPoint
  exact tsum_nonneg fun k => by split_ifs <;> positivity

/-- **Base-2 transfer** (wiring): every point of `C(S)` moves Levin's discrepancy by at most the
perturbation budget. -/
theorem discLe_add_bldPoint (S : Set ℕ) (hS0 : 0 ∉ S) (ω : ℕ → Bool) (α : ℝ) (N : ℕ)
    (hN : 2 ≤ N) {D : ℝ} (hD : DiscLe (orbit 2 α) N D) :
    DiscLe (orbit 2 (α + bldPoint S ω)) N
      (2 * D + 2 / N + (Nat.log 2 N + 2) * sIcc S 1 (N + Nat.log 2 N + 2) / N) := by
  obtain ⟨B, hBc, hB⟩ := fract_bldPoint_small S hS0 ω N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have key := discLe_fract_add (orbit 2 α) (fun n => Int.fract (bldPoint S ω * 2 ^ n)) N D (2 / N)
    B (fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) (fun n => Int.fract_nonneg _)
    (by positivity) (fun n hn hnB => by simpa using hB n hn hnB) hD
  have heq : (fun n => Int.fract (orbit 2 α n + Int.fract (bldPoint S ω * 2 ^ n)))
      = orbit 2 (α + bldPoint S ω) := by
    funext n
    simp only [orbit]
    rw [Int.fract_eq_fract]
    refine ⟨-⌊α * (2 : ℝ) ^ n⌋ - ⌊bldPoint S ω * 2 ^ n⌋, ?_⟩
    push_cast
    rw [Int.fract, Int.fract]
    ring
  rw [heq] at key
  refine key.mono ?_
  have : (B.card : ℝ) / N ≤ (Nat.log 2 N + 2) * sIcc S 1 (N + Nat.log 2 N + 2) / N :=
    div_le_div_of_nonneg_right hBc hNpos.le
  linarith

/-- **Discrepancy → normality** (any base): a star-discrepancy bound tending to `0` gives
equidistribution of the orbit, hence normality by Wall.

Confidence 95%.  Proof: `visitCount u a c N = visitCount u 0 c N − visitCount u 0 a N` for
`0 ≤ a ≤ c` (orbit values are in `[0,1)`), so each interval frequency is within `2ε N` of
`c − a`; then `isNormal_iff_equidistributed_orbit`. -/
theorem isNormal_of_discLe (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ N : ℕ, 2 ≤ N → DiscLe (orbit b x) N (ε N)) :
    IsNormal b x := by
  rw [isNormal_iff_equidistributed_orbit b hb]
  have hu : ∀ n, orbit b x n ∈ Set.Ico (0 : ℝ) 1 := fun n =>
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  intro a c ha hac hc1
  have hsplit : ∀ N, (visitCount (orbit b x) a c N : ℝ) =
      visitCount (orbit b x) 0 c N - visitCount (orbit b x) 0 a N := by
    intro N
    rw [eq_sub_iff_add_eq]
    norm_cast
    unfold visitCount
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext n; simp only [Finset.mem_union, Finset.mem_filter, Set.mem_Ico]
      constructor
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> exact ⟨h1, by linarith, by linarith⟩
      · rintro ⟨h1, h2, h3⟩
        by_cases hna : a ≤ orbit b x n
        · exact Or.inl ⟨h1, hna, h3⟩
        · push Not at hna; exact Or.inr ⟨h1, h2, hna⟩
    · rw [Finset.disjoint_left]
      intro n h1 h2
      simp only [Finset.mem_filter, Set.mem_Ico] at h1 h2
      linarith [h1.2.1, h2.2.2]
  rw [Metric.tendsto_atTop]
  intro e he
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hε (e / 3) (by positivity)
  refine ⟨max K 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  have hεN := hK N (le_of_max_le_left hN)
  rw [Real.dist_eq, sub_zero] at hεN
  have h1 := h N hN2 c ⟨by linarith, hc1⟩
  have h2 := h N hN2 a ⟨ha, by linarith⟩
  rw [Real.dist_eq, hsplit, sub_div]
  have := abs_sub_le ((visitCount (orbit b x) 0 c N : ℝ) / N - c) 0
    ((visitCount (orbit b x) 0 a N : ℝ) / N - a)
  rw [show (visitCount (orbit b x) 0 c N : ℝ) / N - visitCount (orbit b x) 0 a N / N - (c - a)
    = ((visitCount (orbit b x) 0 c N : ℝ) / N - c) - ((visitCount (orbit b x) 0 a N : ℝ) / N - a)
    by ring]
  have := abs_sub ((visitCount (orbit b x) 0 c N : ℝ) / N - c)
    ((visitCount (orbit b x) 0 a N : ℝ) / N - a)
  have := le_abs_self (ε N)
  linarith

/-! ## Odd bases: BLD's second moment survives translation -/

/-- Deterministic core of Davenport–Erdős–LeVeque: unit-bounded summands with
`Σ_N ‖A_N‖²/N < ∞` have means `A_N → 0` (a mean `≥ ε` at `M` persists on `[M, M + εM/2]`,
contributing `≥ ε³/64` to the series). -/
theorem tendsto_of_summable_sq_div (z : ℕ → ℂ) (hz : ∀ k, ‖z k‖ ≤ 1)
    (hs : Summable fun N : ℕ => ‖(∑ k ∈ Finset.range N, z k) / (N : ℂ)‖ ^ 2 / N) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, z k) / (N : ℂ)) atTop (𝓝 0) := by
  set S : ℕ → ℂ := fun N => ∑ k ∈ Finset.range N, z k with hS
  have hdiff : ∀ M N, M ≤ N → ‖S N - S M‖ ≤ (N - M : ℕ) := by
    intro M N hMN
    have : S N - S M = ∑ k ∈ Finset.Ico M N, z k := by
      simp only [S]; rw [Finset.sum_range_sub_sum_range hMN]
      congr 1; ext k; simp [Finset.mem_Ico]; omega
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hz k).trans ?_
    simp
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e : ℝ := min ε 1 with he
  have he0 : 0 < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  obtain ⟨s, hsv⟩ := (summable_iff_vanishing_norm.1 hs) (e ^ 3 / 64) (by positivity)
  refine ⟨s.sup id + 1, fun M hM => ?_⟩
  rw [dist_zero_right]
  by_contra hcon
  push Not at hcon
  have hMe : e ≤ ‖S M / (M : ℂ)‖ := (min_le_left _ _).trans hcon
  have hM1 : 1 ≤ M := by omega
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMpos : (0 : ℝ) < M := by linarith
  have hSM : e * M ≤ ‖S M‖ := by
    rw [norm_div, Complex.norm_natCast, le_div_iff₀ hMpos] at hMe; exact hMe
  set j : ℕ := ⌊e * M / 2⌋₊ with hj
  have hjle : (j : ℝ) ≤ e * M / 2 := Nat.floor_le (by positivity)
  have hjgt : e * M / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  set t := Finset.Icc M (M + j) with ht
  have hdisj : Disjoint t s := by
    rw [Finset.disjoint_left]
    intro n hn hns
    have h1 : n ≤ s.sup id := Finset.le_sup (f := id) hns
    have : M ≤ n := (Finset.mem_Icc.1 hn).1
    omega
  have hsmall := hsv t hdisj
  have hlow : ∀ n ∈ t, e ^ 2 / (32 * M) ≤ ‖S n / (n : ℂ)‖ ^ 2 / n := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have hnR : (M : ℝ) ≤ n := by exact_mod_cast h1
    have hn2 : (n : ℝ) ≤ M + j := by exact_mod_cast h2
    have hnpos : (0 : ℝ) < n := by linarith
    have hd := hdiff M n h1
    have hcast : ((n - M : ℕ) : ℝ) = n - M := by push_cast [h1]; ring
    rw [hcast] at hd
    have hSn : e * M / 2 ≤ ‖S n‖ := by
      have := norm_sub_norm_le (S M) (S n)
      rw [norm_sub_rev] at hd
      linarith
    have hn2M : (n : ℝ) ≤ 2 * M := by nlinarith
    rw [norm_div, Complex.norm_natCast, div_pow, div_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (e * M / 2) ^ 2 ≤ ‖S n‖ ^ 2 := pow_le_pow_left₀ (by positivity) hSn 2
    have hn3 : (n : ℝ) ^ 2 * n ≤ 8 * M ^ 3 := by
      have := pow_le_pow_left₀ hnpos.le hn2M 3
      nlinarith
    nlinarith [sq_nonneg (e : ℝ), mul_pos hMpos hMpos]
  have hsum : e ^ 3 / 64 ≤ ∑ n ∈ t, ‖S n / (n : ℂ)‖ ^ 2 / n := by
    calc e ^ 3 / 64 ≤ ((j : ℝ) + 1) * (e ^ 2 / (32 * M)) := by
          rw [mul_div_assoc', le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg e]
      _ = ∑ n ∈ t, e ^ 2 / (32 * M) := by
          rw [Finset.sum_const, ht, Nat.card_Icc, nsmul_eq_mul, show M + j + 1 - M = j + 1 by omega]
          push_cast; ring
      _ ≤ _ := Finset.sum_le_sum hlow
  have hnn : 0 ≤ ∑ n ∈ t, ‖S n / (n : ℂ)‖ ^ 2 / n :=
    Finset.sum_nonneg fun n _ => by positivity
  rw [Real.norm_of_nonneg hnn] at hsmall
  linarith

/-- **Davenport–Erdős–LeVeque** (Michigan Math. J. 10 (1963) 311–314, Theorem 1), for
unit-bounded measurable functions on a probability space: `Σ_N N⁻¹ 𝔼|A_N|² < ∞` forces
`A_N → 0` a.s., `A_N = N⁻¹ Σ_{n<N} f_n`.

Confidence 95% (classical).  Proof: the series condition gives `N_k ↑` with `N_{k+1}/N_k → 1`
and `Σ_k 𝔼|A_{N_k}|² < ∞` (pick `N_k` minimizing `𝔼|A_N|²` on `[(1+1/k)^?…]` blocks, or the
standard dyadic-refinement argument of DEL); Borel–Cantelli / monotone convergence gives
`A_{N_k} → 0` a.s.; unit bounds interpolate (`|A_N − A_{N_k}| ≤ 2(N − N_k)/N`). -/
theorem del_ae_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℂ) (hf : ∀ n, Measurable (f n)) (hb : ∀ n ω, ‖f n ω‖ ≤ 1)
    (hs : Summable fun N : ℕ =>
      (∫ ω, ‖(∑ n ∈ Finset.range N, f n ω) / (N : ℂ)‖ ^ 2 ∂μ) / N) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n ω) / (N : ℂ)) atTop (𝓝 0) := by
  set g : ℕ → Ω → ℝ := fun N ω => ‖(∑ n ∈ Finset.range N, f n ω) / (N : ℂ)‖ ^ 2 / N with hg
  have hg0 : ∀ N ω, 0 ≤ g N ω := fun N ω => by positivity
  have hgm : ∀ N, Measurable (g N) := fun N =>
    (((Finset.measurable_sum _ fun n _ => hf n).div_const _).norm.pow_const 2).div_const _
  have hA1 : ∀ N ω, ‖(∑ n ∈ Finset.range N, f n ω) / (N : ℂ)‖ ≤ 1 := by
    intro N ω
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    rw [norm_div, Complex.norm_natCast, div_le_one (by exact_mod_cast hN)]
    exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum fun n (_ : n ∈ Finset.range N) => hb n ω)
  have hgi : ∀ N, Integrable (g N) μ := fun N =>
    Integrable.of_bound (hgm N).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hg0 N ω)]
      simp only [hg]
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      rw [div_le_one (by linarith)]
      have := pow_le_one₀ (norm_nonneg _) (hA1 N ω) (n := 2)
      linarith)
  have hgI : ∀ N, ∫ ω, g N ω ∂μ =
      (∫ ω, ‖(∑ n ∈ Finset.range N, f n ω) / (N : ℂ)‖ ^ 2 ∂μ) / N := fun N => integral_div _ _
  have hlin : ∫⁻ ω, ∑' N, ENNReal.ofReal (g N ω) ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun N => (hgm N).ennreal_ofReal.aemeasurable]
    have hs' : Summable fun N => ∫ ω, g N ω ∂μ := by simpa [hgI] using hs
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' N, ∫ ω, g N ω ∂μ)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun N => integral_nonneg (hg0 N)) hs']
    refine ENNReal.tsum_le_tsum fun N => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hgi N) (Eventually.of_forall (hg0 N))]
  have hae := ae_lt_top' (AEMeasurable.tsum fun N =>
    (hgm N).ennreal_ofReal.aemeasurable) hlin
  filter_upwards [hae] with ω hω
  refine tendsto_of_summable_sq_div (fun n => f n ω) (fun n => hb n ω) ?_
  have := ENNReal.summable_toReal hω.ne
  refine this.congr fun N => ?_
  rw [ENNReal.toReal_ofReal (hg0 _ ω)]

/-- The `k`-th term of `bldPoint`. -/
noncomputable def bldTerm (S : Set ℕ) (ω : ℕ → Bool) (k : ℕ) : ℝ := by
  classical exact (if k ∈ S ∧ ω k = true then (1 : ℝ) else 0) / 2 ^ k

theorem bldPoint_eq_tsum (S : Set ℕ) (ω : ℕ → Bool) :
    bldPoint S ω = ∑' k, bldTerm S ω k := by
  unfold bldPoint bldTerm; rfl

theorem bldTerm_nonneg (S : Set ℕ) (ω : ℕ → Bool) (k : ℕ) : 0 ≤ bldTerm S ω k := by
  unfold bldTerm; split_ifs <;> positivity

theorem bldTerm_le (S : Set ℕ) (ω : ℕ → Bool) (k : ℕ) : bldTerm S ω k ≤ (1 / 2) ^ k := by
  unfold bldTerm
  rw [one_div_pow]
  split_ifs <;> simp

theorem summable_bldTerm (S : Set ℕ) (ω : ℕ → Bool) : Summable (bldTerm S ω) :=
  Summable.of_nonneg_of_le (bldTerm_nonneg S ω) (bldTerm_le S ω)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem measurable_bldPoint (S : Set ℕ) : Measurable (bldPoint S) := by
  classical
  have : bldPoint S = fun ω => ∑' k, bldTerm S ω k := funext (bldPoint_eq_tsum S)
  rw [this]
  refine Measurable.tsum fun k => ?_
  unfold bldTerm
  refine Measurable.div_const ?_ _
  exact (measurable_of_countable (fun b : Bool => if k ∈ S ∧ b = true then (1 : ℝ) else 0)).comp
    (measurable_pi_apply k)

/-- Flip coin `k`. -/
def flipAt (k : ℕ) (ω : ℕ → Bool) : ℕ → Bool := Function.update ω k (!ω k)

theorem flipAt_eq (k : ℕ) (ω : ℕ → Bool) :
    flipAt k ω = fun i => (if i = k then (fun b : Bool => !b) else id) (ω i) := by
  funext i
  unfold flipAt
  by_cases h : i = k
  · subst h; simp
  · simp [Function.update_of_ne h, h]

theorem measurePreserving_flipAt (k : ℕ) : MeasurePreserving (flipAt k) coinMeasure coinMeasure := by
  have hm : ∀ i, Measurable ((if i = k then (fun b : Bool => !b) else id) : Bool → Bool) :=
    fun i => measurable_of_countable _
  have hf : flipAt k = fun ω i => (if i = k then (fun b : Bool => !b) else id) (ω i) :=
    funext (flipAt_eq k)
  refine ⟨by rw [hf]; exact measurable_pi_lambda _ fun i => (hm i).comp (measurable_pi_apply i), ?_⟩
  rw [hf]
  unfold coinMeasure
  rw [Measure.infinitePi_map_pi _ hm]
  congr 1
  funext i
  split_ifs
  · ext A hA
    rw [Measure.map_apply (measurable_of_countable _) hA]
    classical
    rw [PMF.toMeasure_apply_fintype, PMF.toMeasure_apply_fintype]
    simp [Set.indicator, PMF.uniformOfFintype_apply, Fintype.card_bool]
    by_cases h1 : true ∈ A <;> by_cases h2 : false ∈ A <;> simp [h1, h2, add_comm]
  · exact Measure.map_id

theorem bldPoint_split (T : Set ℕ) (k : ℕ) (hk : k ∈ T) (ω : ℕ → Bool) :
    bldPoint T ω = bldPoint (T \ {k}) ω + (if ω k = true then (1 : ℝ) else 0) / 2 ^ k := by
  classical
  rw [bldPoint_eq_tsum, bldPoint_eq_tsum]
  have h : bldTerm T ω = fun j => bldTerm (T \ {k}) ω j +
      if j = k then (if ω k = true then (1 : ℝ) else 0) / 2 ^ k else 0 := by
    funext j
    unfold bldTerm
    by_cases hj : j = k
    · subst hj; by_cases hw : ω j = true <;> simp [hk, hw]
    · simp [hj]
  rw [h, Summable.tsum_add (summable_bldTerm _ _) (summable_of_ne_finset_zero
    (s := {k}) (fun j hj => by simp at hj; simp [hj])), tsum_ite_eq]

theorem bldPoint_flipAt (T : Set ℕ) (k : ℕ) (ω : ℕ → Bool) :
    bldPoint (T \ {k}) (flipAt k ω) = bldPoint (T \ {k}) ω := by
  classical
  rw [bldPoint_eq_tsum, bldPoint_eq_tsum]
  congr 1; funext j
  unfold bldTerm
  by_cases hj : j = k
  · subst hj; simp
  · simp [flipAt, Function.update_of_ne hj]

theorem integrable_ee_comp {f : (ℕ → Bool) → ℝ} (hf : Measurable f) :
    Integrable (fun ω => ee (f ω)) coinMeasure :=
  Integrable.of_bound ((measurable_ee.comp hf).aestronglyMeasurable) 1
    (Eventually.of_forall fun ω => (norm_ee _).le)

/-- One coin integrated out. -/

theorem integral_ee_step (T : Set ℕ) (k : ℕ) (hk : k ∈ T) (t : ℝ) :
    ∫ ω, ee (t * bldPoint T ω) ∂coinMeasure =
      (∫ ω, ee (t * bldPoint (T \ {k}) ω) ∂coinMeasure) * ((1 + ee (t / 2 ^ k)) / 2) := by
  set g : (ℕ → Bool) → ℂ := fun ω => ee (t * bldPoint T ω)
  have hgm : Measurable (fun ω => t * bldPoint T ω) := (measurable_bldPoint T).const_mul t
  have hgM : Measurable g := measurable_ee.comp hgm
  have hpres := measurePreserving_flipAt k
  have h1 : ∫ ω, g (flipAt k ω) ∂coinMeasure = ∫ ω, g ω ∂coinMeasure := by
    rw [← integral_map hpres.measurable.aemeasurable hgM.aestronglyMeasurable, hpres.map_eq]
  have hpt : ∀ ω, g ω + g (flipAt k ω) =
      ee (t * bldPoint (T \ {k}) ω) * (1 + ee (t / 2 ^ k)) := by
    intro ω
    simp only [g]
    rw [bldPoint_split T k hk ω, bldPoint_split T k hk (flipAt k ω), bldPoint_flipAt]
    have hfk : flipAt k ω k = !ω k := by simp [flipAt]
    rw [hfk]
    rw [mul_add, mul_add, ee_add, ee_add]
    cases ω k <;> simp [ee] <;> ring_nf
  have hint : Integrable g coinMeasure := integrable_ee_comp hgm
  have hint2 : Integrable (fun ω => g (flipAt k ω)) coinMeasure :=
    integrable_ee_comp (hgm.comp hpres.measurable)
  have h2 : 2 * ∫ ω, g ω ∂coinMeasure =
      ∫ ω, ee (t * bldPoint (T \ {k}) ω) * (1 + ee (t / 2 ^ k)) ∂coinMeasure := by
    simp_rw [← hpt]
    rw [integral_add hint hint2, h1]; ring
  rw [integral_mul_const] at h2
  change ∫ ω, g ω ∂coinMeasure = _
  linear_combination h2 / 2

theorem integral_ee_finset (t : ℝ) (F : Finset ℕ) : ∀ T : Set ℕ, (↑F : Set ℕ) ⊆ T →
    ∫ ω, ee (t * bldPoint T ω) ∂coinMeasure =
      (∫ ω, ee (t * bldPoint (T \ ↑F) ω) ∂coinMeasure) *
        ∏ k ∈ F, ((1 + ee (t / 2 ^ k)) / 2) := by
  classical
  induction F using Finset.induction_on with
  | empty => intro T _; simp
  | insert k F hkF ih =>
    intro T hT
    have hFT : (↑F : Set ℕ) ⊆ T := fun x hx => hT (by simp [hx])
    have hk : k ∈ T \ ↑F := ⟨hT (by simp), by simpa using hkF⟩
    rw [ih T hFT, integral_ee_step (T \ ↑F) k hk t, Finset.prod_insert hkF,
      show (T \ (F : Set ℕ)) \ {k} = T \ ((insert k F : Finset ℕ) : Set ℕ) by
        ext x; simp; tauto]
    ring

theorem norm_one_add_ee_div_two (s : ℝ) : ‖(1 + ee s) / 2‖ = |Real.cos (Real.pi * s)| := by
  have h : (1 + ee s) / 2 = ee (s / 2) * (Real.cos (Real.pi * s) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    unfold ee
    rw [mul_div_assoc', mul_add, ← Complex.exp_add, ← Complex.exp_add,
      show 2 * (Real.pi : ℂ) * Complex.I * ((s / 2 : ℝ) : ℂ) + ((Real.pi * s : ℝ) : ℂ) * Complex.I
        = 2 * Real.pi * Complex.I * (s : ℂ) by push_cast; ring,
      show 2 * (Real.pi : ℂ) * Complex.I * ((s / 2 : ℝ) : ℂ) + -((Real.pi * s : ℝ) : ℂ) * Complex.I
        = 0 by push_cast; ring, Complex.exp_zero, add_comm]
  rw [h, norm_mul, norm_ee, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_integral_ee_bldPoint_le (S : Set ℕ) (t : ℝ) :
    ‖∫ ω, ee (t * bldPoint S ω) ∂coinMeasure‖ ≤ rieszTail S 0 t := by
  classical
  unfold rieszTail
  refine le_ciInf fun M => ?_
  set F := (Finset.Ioc 0 M).filter (· ∈ S)
  have hF : (↑F : Set ℕ) ⊆ S := fun x hx => (Finset.mem_filter.1 hx).2
  rw [integral_ee_finset t F S hF, norm_mul, norm_prod]
  have h1 : ‖∫ ω, ee (t * bldPoint (S \ ↑F) ω) ∂coinMeasure‖ ≤ 1 :=
    (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun ω => (norm_ee _).le)).trans
      (by simp)
  have h2 : ∏ k ∈ F, ‖(1 + ee (t / 2 ^ k)) / 2‖ =
      ∏ k ∈ F, |Real.cos (Real.pi * t / 2 ^ (k - 0))| := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_one_add_ee_div_two, Nat.sub_zero, mul_div_assoc]
  rw [h2]
  have h0 : 0 ≤ ∏ k ∈ F, |Real.cos (Real.pi * t / 2 ^ (k - 0))| :=
    Finset.prod_nonneg fun _ _ => abs_nonneg _
  nlinarith [norm_nonneg (∫ ω, ee (t * bldPoint (S \ ↑F) ω) ∂coinMeasure)]

/-- **Translation invariance of the second moment bound.**  For any `α`,
`𝔼|N⁻¹Σ_{j<N} e(h rʲ(α + y))|² ≤ N⁻² Σ_{p,q<N} |μ̂_S(h(rᵖ − r^q))|`, and
`|μ̂_S(t)| = Π_{k∈S} |cos(πt/2ᵏ)| = rieszTail S 0 t` (BLD §2).

Confidence 88% (truth 98%).  Proof: expand the square;
`𝔼 e(t(α+y)) = e(tα) μ̂_S(t)` and `μ̂_S(t) = Π_{k∈S} (1 + e(t/2ᵏ))/2` (independent coins, the
product converging since `Σ_k t²/4ᵏ < ∞`); `|(1 + e(s))/2| = |cos(πs)|`; then the triangle
inequality.  The partial products decrease to the infimum. -/
theorem secondMoment_translate_le (S : Set ℕ) (hS0 : 0 ∉ S) (α : ℝ) (h : ℤ) (r N : ℕ) :
    ∫ ω, ‖(∑ j ∈ Finset.range N, ee (h * (r : ℝ) ^ j * (α + bldPoint S ω))) / (N : ℂ)‖ ^ 2
        ∂coinMeasure ≤
      (∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N,
        rieszTail S 0 ((h : ℝ) * ((r : ℝ) ^ p - (r : ℝ) ^ q))) / (N : ℝ) ^ 2 := by
  have hym : Measurable (fun ω => α + bldPoint S ω) := (measurable_bldPoint S).const_add α
  have hint : ∀ u : ℝ, Integrable (fun ω => ee (u * (α + bldPoint S ω))) coinMeasure :=
    fun u => integrable_ee_comp (hym.const_mul u)
  have hnd : ∀ ω, ‖(∑ j ∈ Finset.range N, ee (h * (r : ℝ) ^ j * (α + bldPoint S ω))) / (N : ℂ)‖ ^ 2
      = ‖∑ j ∈ Finset.range N, ee (h * (r : ℝ) ^ j * (α + bldPoint S ω))‖ ^ 2 / (N : ℝ) ^ 2 := by
    intro ω; rw [norm_div, Complex.norm_natCast, div_pow]
  simp_rw [hnd]
  rw [integral_div]
  gcongr
  have hexp : ∀ ω, ((‖∑ j ∈ Finset.range N, ee (h * (r : ℝ) ^ j * (α + bldPoint S ω))‖ ^ 2 : ℝ)
      : ℂ) = ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N,
        ee (((h : ℝ) * ((r : ℝ) ^ p - (r : ℝ) ^ q)) * (α + bldPoint S ω)) := by
    intro ω
    rw [sq_norm_sum_ee (fun j => h * (r : ℝ) ^ j * (α + bldPoint S ω))]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ j ∈ Finset.range N, ee (h * (r : ℝ) ^ j * (α + bldPoint S ω))‖ ^ 2
      ∂coinMeasure : ℝ) : ℂ) = ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N,
        ∫ ω, ee (((h : ℝ) * ((r : ℝ) ^ p - (r : ℝ) ^ q)) * (α + bldPoint S ω)) ∂coinMeasure := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_finsetSum _ fun q _ => hint _]
  have hterm : ∀ u : ℝ, ‖∫ ω, ee (u * (α + bldPoint S ω)) ∂coinMeasure‖ ≤ rieszTail S 0 u := by
    intro u
    have : (fun ω => ee (u * (α + bldPoint S ω))) =
        fun ω => ee (u * α) * ee (u * bldPoint S ω) := by
      funext ω; rw [mul_add, ee_add]
    rw [this, integral_const_mul, norm_mul, norm_ee, one_mul]
    exact norm_integral_ee_bldPoint_le S u
  have := congrArg Complex.re hI
  rw [Complex.ofReal_re] at this
  rw [this]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  refine Finset.sum_le_sum fun p _ => (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun q _ => hterm _

/-- **BLD Lemma 7, cosine form.**  The double sum decays like `(log N)^{-1.005}`.  This is the
inequality BLD's proof of Lemma 7 actually establishes (2607.06773 pp. 9–11, "Combining the
estimates"), before they bound the integral by it.

Confidence 85%.  Proof (BLD): diagonal `p = q` gives `N`.  For `p > q`, `g = p − q`,
`d(g) = ν₂(r^g − 1)`: `h(rᵖ − r^q) = 2^{ν₂(h)+d(g)} ℓ_g r^q` with `ℓ_g` odd, so
`rieszTail S 0 (h(rᵖ−r^q)) = rieszTail S (ν₂(h)+d(g)) (ℓ_g r^q)` (factors `k ≤ a` are `|±1|`).
Small valuations `d(g) ≤ B = ⌊2 log₂ log N⌋`: Lemma 5 with `a = ν₂(h)+d(g) ≤ 3 log₂ log N`
(threshold `2^{K(a+1)^{1/ρ}+10³⁰} ≤ N` for large `N`) and Lemma 6
(`#{g ≤ N : d(g) = d} ≤ 2^{ν₂(r²−1)−1} N/2ᵈ`, Lifting-the-Exponent).  Large valuations: at most
`2^{ν₂(r²−1)−1}N/2^B ≤ 2^{ν₂(r²−1)}N/(log N)²` values of `g`, each inner sum `≤ N`.  Total
`≤ 2^{2ν₂(r²−1)+4}/(log N)^{1.005}` after dividing by `N²`. -/
theorem bld_doubleSum_le (hL5 : Literature.BLDLemma5) {S : Set ℕ} {ρ : ℝ} (hS : Sparse S ρ)
    (r : ℕ) (hr : Odd r) (hr3 : 3 ≤ r) (h : ℤ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N,
          rieszTail S 0 ((h : ℝ) * ((r : ℝ) ^ p - (r : ℝ) ^ q))) / (N : ℝ) ^ 2 ≤
        C / Real.log N ^ (1.005 : ℝ) := by
  sorry

theorem summable_inv_mul_log_rpow {p : ℝ} (hp : 1 < p) :
    Summable fun N : ℕ => 1 / ((N : ℝ) * Real.log N ^ p) := by
  set g : ℕ → ℝ := fun n => 1 / ((max n 3 : ℕ) * Real.log (max n 3 : ℕ) ^ p) with hg
  have hlogpos : ∀ n : ℕ, 3 ≤ n → 0 < Real.log n := fun n hn =>
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    have := hlogpos (max n 3) (le_max_right _ _)
    simp only [hg]; positivity
  have hmono : ∀ ⦃m n⦄, 0 < m → m ≤ n → g n ≤ g m := by
    intro m n _ hmn
    have h3 : max m 3 ≤ max n 3 := max_le_max hmn le_rfl
    have hm := hlogpos (max m 3) (le_max_right _ _)
    have hR : ((max m 3 : ℕ) : ℝ) ≤ (max n 3 : ℕ) := by exact_mod_cast h3
    have hm0 : (0 : ℝ) < (max m 3 : ℕ) := by
      have : 0 < max m 3 := by omega
      exact_mod_cast this
    have hl : Real.log (max m 3 : ℕ) ≤ Real.log (max n 3 : ℕ) := Real.log_le_log hm0 hR
    simp only [hg]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have hcond : Summable fun k : ℕ => (2 : ℝ) ^ k * g (2 ^ k) := by
    rw [← summable_nat_add_iff 2]
    have hb : Summable fun k : ℕ => (Real.log 2 ^ p)⁻¹ * ((k : ℝ) + 2) ^ (-p) := by
      refine Summable.mul_left _ ?_
      have := (summable_nat_add_iff 2).2 (Real.summable_nat_rpow.2 (by linarith : -p < -1))
      simpa using this
    refine hb.congr fun k => ?_
    have hmax : max (2 ^ (k + 2)) 3 = 2 ^ (k + 2) := by
      have : 4 ≤ 2 ^ (k + 2) := by
        rw [pow_add]; have := Nat.one_le_two_pow (n := k); omega
      omega
    simp only [hg, hmax]
    push_cast
    rw [Real.log_pow, Real.mul_rpow (by positivity) (Real.log_nonneg (by norm_num)),
      Real.rpow_neg (by positivity)]
    push_cast
    field_simp
  have hgs := (summable_condensed_iff_of_nonneg hg0 hmono).1 hcond
  rw [← summable_nat_add_iff 3] at hgs ⊢
  refine hgs.congr fun n => ?_
  simp only [hg, show max (n + 3) 3 = n + 3 by omega]

theorem fourierMean_orbit (r : ℕ) (x : ℝ) (h : ℤ) (N : ℕ) :
    fourierMean (orbit r x) h N = (∑ k ∈ Finset.range N, ee (h * (r : ℝ) ^ k * x)) / N := by
  unfold fourierMean
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have := ee_int_mul_fract h (x * (r : ℝ) ^ k)
  unfold ee at this
  unfold orbit
  push_cast at this ⊢
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * ((Int.fract (x * (r : ℝ) ^ k) : ℝ) : ℂ)
      = 2 * Real.pi * Complex.I * ((h : ℂ) * ((Int.fract (x * (r : ℝ) ^ k) : ℝ) : ℂ)) by ring, this]
  unfold ee; push_cast; ring_nf

/-- **Odd-base normality of every translate**, `μ_S`-almost surely.

Confidence 85%.  Proof: for each odd `r ≥ 3` and `h ≠ 0` (countably many), `del_ae_tendsto`
with `f_j(ω) = e(h rʲ(α + bldPoint S ω))`: measurability of `bldPoint` (a `tsum` of measurable
coordinate functions), summability from `secondMoment_translate_le` + `bld_doubleSum_le`
(`Σ_N C/(N (log N)^{1.005}) < ∞`, integral test).  Then Weyl (`equidistributed_of_weyl`, the
Weyl mean of `orbit r x` equals the raw mean as in `fourierMean_orbit_two`) and Wall
(`isNormal_iff_equidistributed_orbit`). -/
theorem ae_isNormal_odd_add (hL5 : Literature.BLDLemma5) {S : Set ℕ} {ρ : ℝ} (hS : Sparse S ρ)
    (α : ℝ) :
    ∀ᵐ ω ∂coinMeasure, ∀ r : ℕ, 3 ≤ r → Odd r → IsNormal r (α + bldPoint S ω) := by
  have hS0 : 0 ∉ S := hS.1
  have hone : ∀ r : ℕ, 3 ≤ r → Odd r → ∀ h : ℤ, h ≠ 0 → ∀ᵐ ω ∂coinMeasure, Tendsto
      (fun N : ℕ => (∑ j ∈ Finset.range N, ee (h * (r : ℝ) ^ j * (α + bldPoint S ω))) / (N : ℂ))
      atTop (𝓝 0) := by
    intro r hr3 hr h hh
    obtain ⟨C, hC, N₀, hN₀⟩ := bld_doubleSum_le hL5 hS r hr hr3 h hh
    refine del_ae_tendsto coinMeasure _ (fun j => measurable_ee.comp
      (((measurable_bldPoint S).const_add α).const_mul _)) (fun _ _ => (norm_ee _).le) ?_
    refine Summable.of_norm_bounded_eventually
      ((summable_inv_mul_log_rpow (p := 1.005) (by norm_num)).mul_left C) ?_
    rw [Nat.cofinite_eq_atTop, eventually_atTop]
    refine ⟨max N₀ 2, fun N hN => ?_⟩
    have hN2 : 2 ≤ N := le_of_max_le_right hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hI0 : 0 ≤ ∫ ω, ‖(∑ j ∈ Finset.range N, ee (h * (r : ℝ) ^ j * (α + bldPoint S ω)))
        / (N : ℂ)‖ ^ 2 ∂coinMeasure := integral_nonneg fun _ => by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 := (secondMoment_translate_le S hS0 α h r N).trans (hN₀ N (le_of_max_le_left hN))
    calc _ ≤ (C / Real.log N ^ (1.005 : ℝ)) / N := by gcongr
      _ = C * (1 / ((N : ℝ) * Real.log N ^ (1.005 : ℝ))) := by field_simp
  have hall : ∀ᵐ ω ∂coinMeasure, ∀ r : ℕ, ∀ h : ℤ, 3 ≤ r → Odd r → h ≠ 0 → Tendsto
      (fun N : ℕ => (∑ j ∈ Finset.range N, ee (h * (r : ℝ) ^ j * (α + bldPoint S ω))) / (N : ℂ))
      atTop (𝓝 0) := by
    rw [ae_all_iff]; intro r
    rw [ae_all_iff]; intro h
    by_cases hr : 3 ≤ r ∧ Odd r ∧ h ≠ 0
    · filter_upwards [hone r hr.1 hr.2.1 h hr.2.2] with ω hω _ _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hr
  filter_upwards [hall] with ω hω r hr3 hr
  rw [isNormal_iff_equidistributed_orbit r (by omega)]
  refine equidistributed_of_weyl _ (fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) ?_
  intro h hh
  refine (hω r h hr3 hr hh).congr fun N => ?_
  rw [fourierMean_orbit]

/-! ## The sparse set -/

theorem zero_not_mem_expSet : 0 ∉ expSet := by
  rintro ⟨j, hj, h0⟩
  have hpos : 0 < Real.exp ((j : ℝ) / 100) := Real.exp_pos _
  have : (0 : ℝ) < ⌈Real.exp ((j : ℝ) / 100)⌉₊ := by
    exact_mod_cast Nat.ceil_pos.2 hpos
  rw [← h0] at this
  simp at this

/-- Logarithmic count: `#(expSet ∩ [1, N]) ≤ 100 log N + 1`.

Confidence 97%.  Proof: `⌈e^{j/100}⌉ ≤ N` forces `j ≤ 100 log N`, and the map `j ↦ ⌈e^{j/100}⌉`
covers the set. -/
theorem sIcc_expSet_le (N : ℕ) (hN : 1 ≤ N) :
    (sIcc expSet 1 N : ℝ) ≤ 100 * Real.log N + 1 := by
  classical
  set J := ⌊100 * Real.log N⌋₊
  have hsub : (Finset.Icc 1 N).filter (· ∈ expSet) ⊆
      (Finset.Icc 1 J).image fun j : ℕ => ⌈Real.exp ((j : ℝ) / 100)⌉₊ := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨_, hkN⟩, j, hj, rfl⟩ := hk
    refine Finset.mem_image.2 ⟨j, Finset.mem_Icc.2 ⟨hj, ?_⟩, rfl⟩
    apply Nat.le_floor
    have h1 : Real.exp ((j : ℝ) / 100) ≤ N :=
      (Nat.le_ceil _).trans (by exact_mod_cast hkN)
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    linarith
  have hc : sIcc expSet 1 N ≤ J := by
    unfold sIcc
    refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
    simp
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc (sIcc expSet 1 N : ℝ) ≤ J := by exact_mod_cast hc
    _ ≤ 100 * Real.log N := Nat.floor_le (by positivity)
    _ ≤ _ := by linarith

/-- BLD's example is sparse (their §1 claim; they give no proof).

Confidence 85%.  Proof: `⌈e^{j/100}⌉ ∈ [a, a+k]` iff `e^{j/100} ∈ (a−1, a+k]`.  For `a ≥ 101`
consecutive values differ by `> 1`, so they are distinct and the count is
`≥ 100 log((a+k)/(a−1)) − 1 ≥ 100(1 − ρ) log k − O(1)` for `a ≤ k^ρ`; with `ρ = 1/2` this is
`≥ 50 log k − O(1) ≥ 1.5 · 30 log k` for large `k`.  For `a ≤ 100` every integer in `[2, 100]`
is hit and the count is `≥ 100 log((a+k)/101) − 1`.  Density zero: `sIcc_expSet_le`. -/
theorem sparse_expSet : Sparse expSet (1 / 2) := by
  classical
  refine ⟨zero_not_mem_expSet, ?_, by norm_num, 1 / 2, by norm_num, ⌈Real.exp 101⌉₊, ?_⟩
  · have h0 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun n : ℕ => 100 * (Real.log n / n) + 1 / (n : ℝ)) atTop (𝓝 0) := by
      have := (h0.const_mul 100).add (tendsto_const_div_atTop_nhds_zero_nat 1)
      simpa [Function.comp_def] using this
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ h1
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hnp]
    have := sIcc_expSet_le n hn
    calc (sIcc expSet 1 n : ℝ) ≤ 100 * Real.log n + 1 := this
      _ = _ := by field_simp
  · intro k hk a ha
    have hkR : Real.exp 101 ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    have hkpos : (0 : ℝ) < k := (Real.exp_pos _).trans_le hkR
    set u := Real.log k with hu
    have hu101 : 101 ≤ u := by
      have := Real.log_le_log (Real.exp_pos _) hkR; rwa [Real.log_exp] at this
    have hek : Real.exp u = k := Real.exp_log hkpos
    have hsq : (k : ℝ) ^ (1 / 2 : ℝ) = Real.exp (u / 2) := by
      rw [← hek, ← Real.exp_mul]; ring_nf
    rw [hsq] at ha
    set j0 := ⌈50 * u + 500⌉₊
    set j1 := ⌊100 * u⌋₊
    set f : ℕ → ℕ := fun j => ⌈Real.exp ((j : ℝ) / 100)⌉₊
    have he5 : (100 : ℝ) ≤ Real.exp 5 := by
      have h := Real.exp_one_gt_d9
      have : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) (show (2.7:ℝ) ≤ Real.exp 1 by linarith) 5]
    have hlo : ∀ j ∈ Finset.Icc j0 j1, Real.exp (u / 2) * 100 ≤ Real.exp ((j : ℝ) / 100) := by
      intro j hj
      have : (j0 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
      have : 50 * u + 500 ≤ (j : ℝ) := (Nat.le_ceil _).trans this
      calc Real.exp (u / 2) * 100 ≤ Real.exp (u / 2) * Real.exp 5 := by gcongr
        _ = Real.exp (u / 2 + 5) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.2 (by linarith)
    have hhi : ∀ j ∈ Finset.Icc j0 j1, Real.exp ((j : ℝ) / 100) ≤ k := by
      intro j hj
      have : (j : ℝ) ≤ j1 := by exact_mod_cast (Finset.mem_Icc.1 hj).2
      have : (j : ℝ) ≤ 100 * u := this.trans (Nat.floor_le (by linarith))
      rw [← hek]; exact Real.exp_le_exp.2 (by linarith)
    have hinj : Set.InjOn f (Finset.Icc j0 j1 : Set ℕ) := by
      intro i hi j hj hij
      by_contra hne
      have key : ∀ i j, i ∈ Finset.Icc j0 j1 → j ∈ Finset.Icc j0 j1 → i < j → f i ≠ f j := by
        intro i j hi hj hlt heq
        have hx := hlo i hi
        have hx1 : (100 : ℝ) ≤ Real.exp ((i : ℝ) / 100) :=
          le_trans (by nlinarith [Real.one_le_exp (show 0 ≤ u / 2 by linarith)]) hx
        have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
        have hy : Real.exp ((i : ℝ) / 100) * Real.exp (1 / 100) ≤ Real.exp ((j : ℝ) / 100) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
        have h01 : 1 + 1 / 100 ≤ Real.exp (1 / 100) := by
          have := Real.add_one_le_exp (1 / 100 : ℝ); linarith
        have hgap : Real.exp ((i : ℝ) / 100) + 1 ≤ Real.exp ((j : ℝ) / 100) := by nlinarith
        have c1 : (f i : ℝ) < Real.exp ((i : ℝ) / 100) + 1 := Nat.ceil_lt_add_one (by positivity)
        have c2 : Real.exp ((j : ℝ) / 100) ≤ f j := Nat.le_ceil _
        rw [heq] at c1
        linarith
      rcases lt_or_gt_of_ne hne with h | h
      · exact key i j hi hj h hij
      · exact key j i hj hi h hij.symm
    have hsub : (Finset.Icc j0 j1).image f ⊆ (Finset.Icc a (a + k)).filter (· ∈ expSet) := by
      intro m hm
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hm
      have hjpos : 1 ≤ j := by
        have : (j0 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
        have : (1 : ℝ) ≤ j := by
          have := (Nat.le_ceil (50 * u + 500)).trans this; linarith
        exact_mod_cast this
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, j, hjpos, rfl⟩
      · have h1 : (a : ℝ) ≤ Real.exp ((j : ℝ) / 100) := by
          have := hlo j hj; nlinarith [Real.exp_pos (u / 2)]
        exact_mod_cast h1.trans (Nat.le_ceil _)
      · have := Nat.ceil_mono (hhi j hj)
        rw [Nat.ceil_natCast] at this
        simp only [f]
        omega
    have hcard : (Finset.Icc j0 j1).card ≤ sIcc expSet a (a + k) := by
      unfold sIcc
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card hsub
    have hj0 : (j0 : ℝ) < 50 * u + 501 := by
      have := Nat.ceil_lt_add_one (show 0 ≤ 50 * u + 500 by linarith); linarith
    have hj1 : 100 * u - 1 < (j1 : ℝ) := by
      have := Nat.lt_floor_add_one (100 * u); linarith
    have hle : j0 ≤ j1 + 1 := by
      have : (j0 : ℝ) ≤ j1 + 1 := by linarith
      exact_mod_cast this
    have hc : ((Finset.Icc j0 j1).card : ℝ) = j1 + 1 - j0 := by
      rw [Nat.card_Icc]; push_cast [hle]; ring
    calc (1 + 1 / 2) * (30 * u) ≤ (j1 : ℝ) + 1 - j0 := by linarith
      _ = _ := hc.symm
      _ ≤ _ := by exact_mod_cast hcard

/-- **Rate arithmetic** for the headline.

Confidence 99%.  Proof: for `N ≥ 2`, `Nat.log 2 N + 2 ≤ 3 log N / log 2 ≤ 5 log N`,
`log(N + Nat.log 2 N + 2) ≤ log (3N) ≤ 3 log N`, `2 ≤ 5 log² N`. -/
theorem rate_arith (C : ℝ) (hC : 0 < C) (N : ℕ) (hN : 2 ≤ N) :
    2 * (C * Real.log N ^ 2 / N) + 2 / N +
        (Nat.log 2 N + 2) * (100 * Real.log ((N + Nat.log 2 N + 2 : ℕ) : ℝ) + 1) / N ≤
      (2 * C + 2000) * Real.log N ^ 2 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set l := Real.log N with hl
  set a : ℝ := (Nat.log 2 N : ℝ)
  set b := Real.log ((N + Nat.log 2 N + 2 : ℕ) : ℝ)
  have hl2 : Real.log 2 ≤ l := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlog2 := Real.log_two_gt_d9
  have ha : a * Real.log 2 ≤ l := by
    have h1 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
    have : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ l :=
      Real.log_le_log (by positivity) (by exact_mod_cast h1)
    rwa [Real.log_pow] at this
  have ha0 : 0 ≤ a := by positivity
  have hb : b ≤ 2 + l := by
    have hlt : Nat.log 2 N < N := Nat.log_lt_self 2 (by omega)
    have hM : ((N + Nat.log 2 N + 2 : ℕ) : ℝ) ≤ 3 * N := by
      have : N + Nat.log 2 N + 2 ≤ 3 * N := by omega
      exact_mod_cast this
    have hMp : (0 : ℝ) < ((N + Nat.log 2 N + 2 : ℕ) : ℝ) := by positivity
    have := Real.log_le_log hMp hM
    rw [Real.log_mul (by norm_num) hNpos.ne'] at this
    have h3 : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hb0 : 0 ≤ b := Real.log_nonneg (by
    have : (1 : ℕ) ≤ N + Nat.log 2 N + 2 := by omega
    exact_mod_cast this)
  have key : 2 + (a + 2) * (100 * b + 1) ≤ 2000 * l ^ 2 := by
    have hal : a ≤ 1.45 * l := by nlinarith
    have h1 : a + 2 ≤ 4.4 * l := by nlinarith
    have h2 : 100 * b + 1 ≤ 392 * l := by nlinarith
    have : (a + 2) * (100 * b + 1) ≤ (4.4 * l) * (392 * l) :=
      mul_le_mul h1 h2 (by positivity) (by nlinarith)
    nlinarith
  have e : 2 * (C * l ^ 2 / N) + 2 / N + (a + 2) * (100 * b + 1) / N =
      (2 * C * l ^ 2 + (2 + (a + 2) * (100 * b + 1))) / N := by ring
  rw [e]
  apply div_le_div_of_nonneg_right _ hNpos.le
  nlinarith

/-! ## Headline -/

/-- **Headline.**  There is a real `x` normal in every odd base `≥ 3` and every power-of-two base,
whose base-2 star discrepancy is `O((log N)²/N)`: Levin's one-base rate, far below the `N^{-1/2}`
"barrier" of ABSS 1707.02628 for numbers normal in several bases.

Wiring (proved from the leaves): `x = α + bldPoint expSet ω` with `α` from `Levin1999` and `ω`
from the full-measure set of `ae_isNormal_odd_add`. -/
theorem exists_levinRate_oddNormal (hL : Literature.Levin1999) (hB : Literature.BLDLemma5) :
    ∃ x : ℝ, (∀ b : ℕ, 2 ≤ b → (Odd b ∨ ∃ k : ℕ, b = 2 ^ k) → IsNormal b x) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → DiscLe (orbit 2 x) N (C * Real.log N ^ 2 / N) := by
  obtain ⟨α, C, hC, hα⟩ := hL
  obtain ⟨ω, hω⟩ := (ae_isNormal_odd_add hB sparse_expSet α).exists
  set x := α + bldPoint expSet ω with hx
  have hrate : ∀ N : ℕ, 2 ≤ N →
      DiscLe (orbit 2 x) N ((2 * C + 2000) * Real.log N ^ 2 / N) := by
    intro N hN
    refine (discLe_add_bldPoint expSet zero_not_mem_expSet ω α N hN (hα N hN)).mono ?_
    refine le_trans ?_ (rate_arith C hC N hN)
    have hcnt := sIcc_expSet_le (N + Nat.log 2 N + 2) (by omega)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hL0 : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) + 2 := by positivity
    have : (Nat.log 2 N + 2 : ℝ) * (sIcc expSet 1 (N + Nat.log 2 N + 2) : ℝ) / N ≤
        (Nat.log 2 N + 2) * (100 * Real.log ((N + Nat.log 2 N + 2 : ℕ) : ℝ) + 1) / N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcnt hL0) hNpos.le
    linarith
  have h2 : IsNormal 2 x := by
    refine isNormal_of_discLe 2 le_rfl x (fun N => (2 * C + 2000) * Real.log N ^ 2 / N) ?_ hrate
    have h0 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    have := h0.const_mul (2 * C + 2000)
    simp only [mul_zero] at this
    refine this.congr fun N => ?_
    simp only [Function.comp_apply, one_mul, add_zero]
    ring
  refine ⟨x, ?_, 2 * C + 2000, by positivity, hrate⟩
  intro b hb hcase
  rcases hcase with hodd | ⟨k, rfl⟩
  · exact hω b (by
      rcases hodd with ⟨m, rfl⟩
      omega) hodd
  · have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hb
      · exact hk
    exact PowerBase.isNormal_pow (b := 2) (by norm_num) hk h2

/-! ## Known-false siblings and the open upgrade -/

/-- The full binary set `{k ≥ 1}` (dense digits). -/
def denseSet : Set ℕ := {k | 1 ≤ k}

/-- **The mechanism refuses dense digits**: with `S = {k ≥ 1}` the base-2 perturbation budget
`(log₂N + 2)·S(1, N + log₂N + 2)/N` is at least `1`, so `discLe_add_bldPoint` says nothing. -/
theorem perturbBudget_dense_ge_one (N : ℕ) (hN : 1 ≤ N) :
    (1 : ℝ) ≤ (Nat.log 2 N + 2) * sIcc denseSet 1 (N + Nat.log 2 N + 2) / N := by
  have hc : sIcc denseSet 1 (N + Nat.log 2 N + 2) = N + Nat.log 2 N + 2 := by
    classical
    unfold sIcc
    rw [show ((Finset.Icc 1 (N + Nat.log 2 N + 2)).filter (· ∈ denseSet)) =
        Finset.Icc 1 (N + Nat.log 2 N + 2) by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h.1⟩]
    simp
  rw [hc]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNpos]
  push_cast
  nlinarith [(Nat.cast_nonneg (Nat.log 2 N) : (0 : ℝ) ≤ _)]

/-- **Dense digits really fail "for every `y`"**: for every `α` some point of the dense set makes
`α + y` an integer, hence not normal in base 2.

Confidence 92%.  Proof: take `ω` the binary digits of `fract(−α)` (shifted to positions `k ≥ 1`);
then `bldPoint denseSet ω = fract(−α)` (proper expansion, `Bridge.digitOf_realOfDigits`-style),
`α + fract(−α) ∈ ℤ`, all base-2 digits of `fract 0 = 0` are `0`. -/
theorem exists_not_isNormal_two_dense (α : ℝ) :
    ∃ ω : ℕ → Bool, ¬ IsNormal 2 (α + bldPoint denseSet ω) := by
  classical
  set z := Int.fract (-α) with hz
  refine ⟨fun k => decide (1 ≤ k ∧ digitOf 2 z (k - 1) = 1), ?_⟩
  have hd : ∀ i, digitOf 2 z i < 2 := fun i => Nat.mod_lt _ (by norm_num)
  have hsum : HasSum (fun k : ℕ => (if k ∈ denseSet ∧ decide (1 ≤ k ∧ digitOf 2 z (k - 1) = 1) = true
      then (1 : ℝ) else 0) / 2 ^ k) z := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, pow_zero, div_one]
    have h0 : ¬ (0 ∈ denseSet) := by simp [denseSet]
    simp only [h0, false_and, if_false, sub_zero]
    refine (hasSum_digitOf_two z (Int.fract_nonneg _) (Int.fract_lt_one _)).congr_fun fun i => ?_
    have hm : i + 1 ∈ denseSet := by simp [denseSet]
    simp only [hm, true_and, Nat.add_sub_cancel, decide_eq_true_eq]
    have := hd i
    by_cases h1 : digitOf 2 z i = 1
    · simp [h1]
    · have h0 : digitOf 2 z i = 0 := by omega
      simp [h0]
  have hb : bldPoint denseSet (fun k => decide (1 ≤ k ∧ digitOf 2 z (k - 1) = 1)) = z := by
    unfold bldPoint; exact hsum.tsum_eq
  rw [hb]
  intro h
  apply not_isNormal_two_zero_aux
  have : Int.fract (α + z) = Int.fract (0 : ℝ) := by
    rw [Int.fract_zero, hz, show α + Int.fract (-α) = ((-⌊-α⌋ : ℤ) : ℝ) by
      rw [Int.fract]; push_cast; ring, Int.fract_intCast]
  unfold IsNormal at h ⊢
  rwa [this] at h

/-- **Open upgrade (not claimed; 20%).**  An absolutely normal `x` with base-2 star discrepancy
`o(N^{-1/2})`.  Route: a denser sparse set (BLD exponent `1 < ρ < 2`, e.g. the primes, with
`#(S ∩ [1,N]) ≈ N^{1−1/ρ}`) keeps the base-2 budget at `O(N^{-1/ρ} log² N) = o(N^{-1/2})`, but the
odd/even-base decay for bases `2ᵃm` (`a ≥ 1`) needs Schmidt's 1960 tools on windows of length
`≫ log N` at shifts `≍ N`, which BLD only assert ("Applying Schmidt's specialized tools from [18]
it can be extended to all bases multiplicatively independent of 2") and do not prove. -/
theorem exists_absNormal_base2_fast :
    ∃ x : ℝ, (∀ b : ℕ, 2 ≤ b → IsNormal b x) ∧ ∃ C θ : ℝ, 0 < C ∧ 1 / 2 < θ ∧
      ∀ N : ℕ, 2 ≤ N → DiscLe (orbit 2 x) N (C / (N : ℝ) ^ θ) := by
  sorry

/-- **Derandomization stretch (65%).**  For computable `α ∈ [0,1)` (Levin's `α` is an explicit
digit concatenation), a computable coin sequence `e` with `α + bldPoint expSet e` normal in every
odd base.  Route: BLD Theorem 3's algorithm (Becher–Figueira reformulation of Sierpiński, bad
sets defined by exponential-sum averages, choices only at positions in `S`), with the bad-set
measure bounds coming from `secondMoment_translate_le` + `bld_doubleSum_le` by Chebyshev, which
are translation-invariant. -/
theorem exists_computable_bld_odd_add (hL5 : Literature.BLDLemma5) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : Computable fun n : ℕ => ⌊α * 2 ^ n⌋₊) :
    ∃ e : ℕ → Bool, Computable e ∧
      ∀ r : ℕ, 3 ≤ r → Odd r → IsNormal r (α + bldPoint expSet e) := by
  sorry

end NormalNumbers.LevinSparse
