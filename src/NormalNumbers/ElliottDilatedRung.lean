import NormalNumbers.ElliottDilatedSlice
import NormalNumbers.ElliottDilatedGrouped
import NormalNumbers.ElliottDilatedFourier
import NormalNumbers.ElliottDilatedSelectMirror

/-!
# The live crux route: `DilatedCMLogElliott` from the `a`-dilated graph stack

This file carries the crux rung `NormalNumbers.ElliottLadder.DilatedCMLogElliott` on the route the
campaign is actually pursuing — the **`a`-dilated prime graph** of
`ElliottDilatedUpper` / `ElliottGenericGraph*` / `ElliottDilatedBridge` /
`ElliottDilatedCorrelation` — and not on the refuted *dilation-slice* route of
`NormalNumbers.ElliottDilatedSlice`.

## Why the slice route is dead

`NormalNumbers.ElliottDilatedSlice` reduces the common dilation to a divisibility `a ∣ m` at
residue `0`, by an exact identity.  The reduction itself is fine and stays proved
(`dilatedCM_of_slice`, `sliceCM_one`, `dilatedSlice_of_ge`).  What is dead is its *remaining leaf*:
centring the graph edge on `f₁` translates by `p·c₁`, turning `a ∣ m` into `a ∣ n - p c₁`, a
condition on `p mod a` that does **not** factor out of the prime sum, so the indicator cannot be
carried as a fixed periodic block factor.  See `PENDING_WORK.md` (lap 16).

## The live decomposition

The dilated stack works directly with `NormalNumbers.ElliottLadder.pairObservable`, i.e. with the
pair of forms `(a n + c₁, a n + c₂)`, and the graph step `n ↦ p n` dilates **both** shifts.  Its
correlation-transfer rung
`NormalNumbers.ElliottDilatedCorrelation.norm_logProb_dilatedGraph_sub_correlation_le` is stated for
`c₁ : ℕ` and `c₂ = c₁ + h` with `h : ℕ`.  This file supplies the (free) passage from arbitrary
integer shifts to that shape, so that the remaining obligations have exactly the signature the
graph stack produces:

* `norm_window_translate_sub_le` — translating the harmonic window by `k` costs `3k`.  Proved.
* `elliottLogCorrelation_translate` — translating the window index by `k` translates **both**
  shifts by `a·k`.  Proved, exactly (no error): it is a reindexing of the observable.
* `elliottLogCorrelation_swap` — the correlation is symmetric under swapping `(f₁,c₁) ↔ (f₂,c₂)`.
  Proved.
* `dilatedCM_of_natShift` — `DilatedNatShiftCMLogElliott → DilatedNatShiftCMLogElliottMirror →
  DilatedCMLogElliott`.  **Proved**: pick `k` with `c₁ + a k ≥ 0` and `c₂ + a k ≥ 0` (possible for
  any `a ≥ 1` with `k = |c₁| + |c₂|`), pay `3k`, which
  `Erdos67b.elliottExists_finalThreshold` absorbs into `(ε/2) log W`; the sign of `c₂ - c₁` chooses
  the orientation.
* `dilatedNatShiftCMLogElliott`, `dilatedNatShiftCMLogElliottMirror` — **the two open leaves**, the
  only remaining analytic obligations of the crux.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottDilatedRung

open Erdos67b
open NormalNumbers.ElliottLadder
open NormalNumbers.ElliottTwoShift
open Erdos67b.FiniteEntropy
open NormalNumbers.ElliottLadder

noncomputable section

/-! ## Translating the harmonic window -/

/-- **Translating the index of a harmonic window sum by `k` costs `3k`.**

The same three-way split as `NormalNumbers.ElliottTwoShift.norm_twoShift_le_shiftedPair_add`: the
weight discrepancy telescopes to `≤ k`, and the two boundary blocks contribute `≤ k` each. -/
theorem norm_window_translate_sub_le {G : ℕ → ℂ} (hG : ∀ n : ℕ, 0 < n → ‖G n‖ ≤ 1)
    (k : ℕ) {X W : ℕ} (hW : 0 < W) :
    ‖(∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * G n) -
        ∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * G (n + k)‖ ≤ 3 * (k : ℝ) := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : ℕ, elliottLogWindow X W = Finset.Ioc L X :=
    ⟨X / W, elliottLogWindow_eq_Ioc hW⟩
  have hmem : ∀ m : ℕ, m ∈ elliottLogWindow X W ↔ (L < m ∧ m ≤ X) := by
    intro m; rw [hL, Finset.mem_Ioc]
  set J : Finset ℕ := (elliottLogWindow X W).image (fun m ↦ m + k) with hJdef
  have hre : ∑ j ∈ J, (harmonicWeight j : ℂ) * G j
      = ∑ n ∈ elliottLogWindow X W, (harmonicWeight (n + k) : ℂ) * G (n + k) := by
    rw [hJdef, Finset.sum_image (fun x _ y _ hxy ↦ by omega)]
  -- the telescoping weight discrepancy
  have hweight : ∑ n ∈ elliottLogWindow X W, (k : ℝ) / ((n : ℝ) * (n + k : ℝ)) ≤ (k : ℝ) := by
    have heq : ∀ n ∈ elliottLogWindow X W, (k : ℝ) / ((n : ℝ) * (n + k : ℝ))
        = harmonicWeight n - harmonicWeight (n + k) := fun n hn ↦
      (harmonicWeight_sub_shift (mem_elliottLogWindow.mp hn).1).symm
    rw [Finset.sum_congr rfl heq]
    exact sum_harmonicWeight_shift_diff_le (elliottLogWindow_subset_range X W)
  have h1 : ‖(∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * G (n + k)) -
      ∑ j ∈ J, (harmonicWeight j : ℂ) * G j‖ ≤ (k : ℝ) := by
    rw [hre]
    refine (norm_sum_harmonic_shift_sub_le (elliottLogWindow X W) G k
      (fun n hn ↦ (mem_elliottLogWindow.mp hn).1)
      (fun n hn ↦ hG (n + k) (by have := (mem_elliottLogWindow.mp hn).1; omega))).trans hweight
  have hJpos : ∀ j ∈ J, 0 < j := by
    intro j hj
    rw [hJdef, Finset.mem_image] at hj
    obtain ⟨m, hm, rfl⟩ := hj
    have := (mem_elliottLogWindow.mp hm).1; omega
  have hcard1 : (J \ elliottLogWindow X W).card ≤ k := by
    have hsub : J \ elliottLogWindow X W ⊆ Finset.Ioc X (X + k) := by
      intro j hj
      rw [Finset.mem_sdiff, hJdef, Finset.mem_image] at hj
      obtain ⟨⟨m, hm, rfl⟩, hnot⟩ := hj
      have hmw := (hmem m).mp hm
      rw [Finset.mem_Ioc]
      refine ⟨?_, by omega⟩
      by_contra hle
      exact hnot ((hmem (m + k)).mpr ⟨by omega, by omega⟩)
    refine (Finset.card_le_card hsub).trans ?_
    rw [Nat.card_Ioc]; omega
  have hcard2 : (elliottLogWindow X W \ J).card ≤ k := by
    have hsub : elliottLogWindow X W \ J ⊆ Finset.Ioc L (L + k) := by
      intro j hj
      rw [Finset.mem_sdiff] at hj
      obtain ⟨hjw, hnot⟩ := hj
      have hjm := (hmem j).mp hjw
      rw [Finset.mem_Ioc]
      refine ⟨hjm.1, ?_⟩
      by_contra hgt
      apply hnot
      rw [hJdef, Finset.mem_image]
      exact ⟨j - k, (hmem (j - k)).mpr ⟨by omega, by omega⟩, by omega⟩
    refine (Finset.card_le_card hsub).trans ?_
    rw [Nat.card_Ioc]; omega
  have h2 := norm_sum_window_sub_le (J := J) (G := G) (X := X) (W := W) (r := k)
    hG hJpos hcard1 hcard2
  have hsplit : (∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * G n) -
      ∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * G (n + k) =
      -(((∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * G (n + k)) -
          ∑ j ∈ J, (harmonicWeight j : ℂ) * G j) +
        ((∑ j ∈ J, (harmonicWeight j : ℂ) * G j) -
          ∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * G n)) := by abel
  rw [hsplit, norm_neg]
  have := norm_add_le
    ((∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * G (n + k)) -
      ∑ j ∈ J, (harmonicWeight j : ℂ) * G j)
    ((∑ j ∈ J, (harmonicWeight j : ℂ) * G j) -
      ∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * G n)
  linarith

/-! ## Translating both shifts -/

/-- Translating the window index by `k` translates **both** shifts by `a·k`.  Exact, no error. -/
theorem pairObservable_translate (f₁ f₂ : ℕ → ℂ) (a : ℕ) (c₁ c₂ : ℤ) (k n : ℕ) :
    pairObservable f₁ f₂ a c₁ c₂ (n + k) =
      pairObservable f₁ f₂ a (c₁ + (a : ℤ) * k) (c₂ + (a : ℤ) * k) n := by
  unfold pairObservable integerAffine
  push_cast
  ring_nf

/-- The correlation is symmetric under swapping the function/shift pairs. -/
theorem elliottLogCorrelation_swap (F₁ F₂ : ℤ → ℂ) (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (X W : ℕ) :
    elliottLogCorrelation F₁ F₂ a₁ a₂ b₁ b₂ X W =
      elliottLogCorrelation F₂ F₁ a₂ a₁ b₂ b₁ X W := by
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [mul_assoc, mul_assoc, mul_comm (F₁ _) (F₂ _)]

/-- **The translation estimate for the common-dilation correlation.** -/
theorem norm_elliottLogCorrelation_le_translate {f₁ f₂ : ℕ → ℂ}
    (h₁ : ∀ n : ℕ, 0 < n → ‖f₁ n‖ ≤ 1) (h₂ : ∀ n : ℕ, 0 < n → ‖f₂ n‖ ≤ 1)
    (a : ℕ) (c₁ c₂ : ℤ) (k : ℕ) {X W : ℕ} (hW : 0 < W) :
    ‖elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂) a a c₁ c₂ X W‖ ≤
      ‖elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂) a a
          (c₁ + (a : ℤ) * k) (c₂ + (a : ℤ) * k) X W‖ + 3 * (k : ℝ) := by
  have hG : ∀ n : ℕ, 0 < n → ‖pairObservable f₁ f₂ a c₁ c₂ n‖ ≤ 1 := fun n _ ↦
    norm_pairObservable_le_one h₁ h₂ a c₁ c₂ n
  have hkey := norm_window_translate_sub_le (G := pairObservable f₁ f₂ a c₁ c₂) hG k (X := X) hW
  set A : ℂ := ∑ n ∈ elliottLogWindow X W,
    (harmonicWeight n : ℂ) * pairObservable f₁ f₂ a c₁ c₂ n with hA
  set B : ℂ := ∑ n ∈ elliottLogWindow X W,
    (harmonicWeight n : ℂ) * pairObservable f₁ f₂ a c₁ c₂ (n + k) with hB
  have e0 : elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂)
      a a c₁ c₂ X W = A := elliottLogCorrelation_eq_pairObservable f₁ f₂ a c₁ c₂ X W
  have e1 : elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂) a a
      (c₁ + (a : ℤ) * k) (c₂ + (a : ℤ) * k) X W = B := by
    rw [elliottLogCorrelation_eq_pairObservable, hB]
    exact (Finset.sum_congr rfl fun n _ ↦ by rw [pairObservable_translate]).symm
  rw [e0, e1]
  have hsplit : A = B + (A - B) := by abel
  calc ‖A‖ = ‖B + (A - B)‖ := by rw [← hsplit]
    _ ≤ ‖B‖ + ‖A - B‖ := norm_add_le _ _
    _ ≤ ‖B‖ + 3 * (k : ℝ) := by linarith

/-! ## The two open leaves -/

/-- **The dilated rung at natural shifts.**  Two independent completely multiplicative unimodular
functions against the forms `a n + c₁`, `a n + c₁ + h` with `h ≥ 1`, non-pretentiousness on the
function carrying the **smaller** shift.

This is exactly the shape the `a`-dilated graph stack produces: compare
`NormalNumbers.ElliottDilatedCorrelation.norm_logProb_dilatedGraph_sub_correlation_le`, whose
correlation is `affineLogCorrelation L U f₁ f₂ a c₁ (c₁ + h)`. -/
def DilatedNatShiftCMLogElliott : Prop :=
  ∀ (a c₁ h : ℕ), 0 < a → 0 < h →
    ∀ ε : ℝ, 0 < ε →
      ∃ A₀ : ℕ, 2 ≤ A₀ ∧
        ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
          ∀ f₁ f₂ : ℕ → ℂ,
            IsCompletelyMultiplicativeOnPositive f₁ →
            IsCompletelyMultiplicativeOnPositive f₂ →
            (∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) →
            (∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1) →
            MRTNonpretentious f₁ A X →
            ‖elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂)
                a a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) X W‖ ≤ ε * Real.log W

/-- **The mirrored dilated rung.**  Same forms, but the non-pretentious function carries the
**larger** shift.  Compare `NormalNumbers.ElliottTwistedGraph.shiftCMLogElliottMirror`, the
`a = 1`, `c₁ = 0` case. -/
def DilatedNatShiftCMLogElliottMirror : Prop :=
  ∀ (a c₁ h : ℕ), 0 < a → 0 < h →
    ∀ ε : ℝ, 0 < ε →
      ∃ A₀ : ℕ, 2 ≤ A₀ ∧
        ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
          ∀ f₁ f₂ : ℕ → ℂ,
            IsCompletelyMultiplicativeOnPositive f₁ →
            IsCompletelyMultiplicativeOnPositive f₂ →
            (∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) →
            (∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1) →
            MRTNonpretentious f₂ A X →
            ‖elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂)
                a a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) X W‖ ≤ ε * Real.log W

/-! ## Arbitrary integer shifts are free over the natural-shift rungs -/

/-- **Proved.**  Both integer shifts are free: translating the window index by
`k = |c₁| + |c₂|` translates both shifts by `a k ≥ k`, which makes both nonnegative, and costs
`3k` — absorbed by `Erdos67b.elliottExists_finalThreshold` into `(ε/2) log W`.  The sign of
`c₂ - c₁` chooses the orientation. -/
theorem dilatedCM_of_natShift (hfwd : DilatedNatShiftCMLogElliott)
    (hmir : DilatedNatShiftCMLogElliottMirror) : DilatedCMLogElliott := by
  intro a c₁ c₂ ha hne ε hε
  obtain ⟨k, hk₁, hk₂⟩ : ∃ k : ℕ, -c₁ ≤ (k : ℤ) ∧ -c₂ ≤ (k : ℤ) :=
    ⟨c₁.natAbs + c₂.natAbs, by omega, by omega⟩
  have hak : (k : ℤ) ≤ (a : ℤ) * k := by
    have h1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    nlinarith [Int.natCast_nonneg k]
  have hd₁ : 0 ≤ c₁ + (a : ℤ) * k := by linarith
  have hd₂ : 0 ≤ c₂ + (a : ℤ) * k := by linarith
  set d₁ : ℕ := (c₁ + (a : ℤ) * k).toNat with hd₁def
  set d₂ : ℕ := (c₂ + (a : ℤ) * k).toNat with hd₂def
  have he₁ : ((d₁ : ℕ) : ℤ) = c₁ + (a : ℤ) * k := Int.toNat_of_nonneg hd₁
  have he₂ : ((d₂ : ℕ) : ℤ) = c₂ + (a : ℤ) * k := Int.toNat_of_nonneg hd₂
  have hdne : d₁ ≠ d₂ := by
    intro hEq
    apply hne
    have : ((d₁ : ℕ) : ℤ) = ((d₂ : ℕ) : ℤ) := by rw [hEq]
    omega
  obtain ⟨A₂, hA₂4, -, -, hthr⟩ := elliottExists_finalThreshold (3 * k) 0 0 hε
  rcases Nat.lt_or_ge d₁ d₂ with hlt | hge
  · -- the non-pretentious function carries the smaller shift
    obtain ⟨A₁, hA₁, hmain⟩ := hfwd a d₁ (d₂ - d₁) ha (by omega) (ε / 2) (by positivity)
    refine ⟨max A₁ A₂, hA₁.trans (le_max_left _ _), ?_⟩
    intro A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
    have hA₂W : A₂ ≤ W := (le_max_right A₁ A₂).trans (hA.trans hAW)
    have hW : 0 < W := by omega
    have hres := hmain A X W ((le_max_left A₁ A₂).trans hA) hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
    have hrw : ((d₁ + (d₂ - d₁) : ℕ) : ℤ) = c₂ + (a : ℤ) * k := by
      rw [show d₁ + (d₂ - d₁) = d₂ by omega]; exact he₂
    rw [hrw, he₁] at hres
    have hest := norm_elliottLogCorrelation_le_translate
      (fun n hn ↦ (hu₁ n hn).le) (fun n hn ↦ (hu₂ n hn).le) a c₁ c₂ k (X := X) hW
    obtain ⟨-, -, herr⟩ := hthr W hA₂W
    have herr' : 3 * (k : ℝ) ≤ ε / 2 * Real.log W := by push_cast at herr; linarith
    linarith
  · -- the non-pretentious function carries the larger shift: the mirrored rung
    have hlt : d₂ < d₁ := by omega
    obtain ⟨A₁, hA₁, hmain⟩ := hmir a d₂ (d₁ - d₂) ha (by omega) (ε / 2) (by positivity)
    refine ⟨max A₁ A₂, hA₁.trans (le_max_left _ _), ?_⟩
    intro A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
    have hA₂W : A₂ ≤ W := (le_max_right A₁ A₂).trans (hA.trans hAW)
    have hW : 0 < W := by omega
    have hres := hmain A X W ((le_max_left A₁ A₂).trans hA) hAW hWX f₂ f₁ hm₂ hm₁ hu₂ hu₁ hpret
    have hrw : ((d₂ + (d₁ - d₂) : ℕ) : ℤ) = c₁ + (a : ℤ) * k := by
      rw [show d₂ + (d₁ - d₂) = d₁ by omega]; exact he₁
    rw [hrw, he₂, ← elliottLogCorrelation_swap] at hres
    have hest := norm_elliottLogCorrelation_le_translate
      (fun n hn ↦ (hu₁ n hn).le) (fun n hn ↦ (hu₂ n hn).le) a c₁ c₂ k (X := X) hW
    obtain ⟨-, -, herr⟩ := hthr W hA₂W
    have herr' : 3 * (k : ℝ) ≤ ε / 2 * Real.log W := by push_cast at herr; linarith
    linarith

/-! ## The remaining analytic obligations -/

/-- **Open leaf 1 of the crux.**  The `a`-dilated, two-function, natural-shift rung, with
non-pretentiousness on the function at the smaller shift.

Every rung of the `a`-dilated graph argument needed for this is already a proved, axiom-clean
statement in `src/`:

* upper — `NormalNumbers.ElliottDilatedUpper.exists_dilatedPairTwistedMean_small_of_fourier_first_moment`;
* generic CRT / concentration — `NormalNumbers.ElliottGenericGraph.exists_gen_exponential_tail`;
* entropy decoupling — `NormalNumbers.ElliottGenericGraph.exists_logProb_gen_decoupling`;
* the join — `NormalNumbers.ElliottDilatedBridge.genMeanCRT_dilatedEdgeReindexed`;
* correlation transfer —
  `NormalNumbers.ElliottDilatedCorrelation.norm_logProb_dilatedGraph_sub_correlation_le`.

What is left is the assembly, in three steps (see `PENDING_WORK.md`):
1. trade the CRT sum for the mean (`exists_logProb_gen_decoupling` at `Δ m = crtShift`);
2. a lower bound on `dilatedCorrelationWeight` (function-free counting: for `p` dyadic in `(P, 2P]`
   with `2 p h < H` the count is `≥ H/(2a)`);
3. the entropy-selected dyadic scale and the contradiction against the upper bound — the
   `NormalNumbers.ElliottTwistedGraph.exists_pairLogCorrelation_small_of_fourier_first_moments`
   collision verbatim — then the MRT parameter choreography of
   `NormalNumbers.ElliottTwistedGraph.shiftCMLogElliott`. -/
theorem elliottLogCorrelation_eq_window_sum (f₁ f₂ : ℕ → ℂ) (a : ℕ) (c₁ c₂ : ℤ) (X W : ℕ) :
    elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂) a a c₁ c₂ X W =
      ∑ n ∈ elliottLogWindow X W, (n : ℝ)⁻¹ • pairObservable f₁ f₂ a c₁ c₂ n := by
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp only [pairObservable, harmonicWeight, Complex.real_smul, mul_assoc]

/-- **Leaf 1 of the crux, PROVED.**  The `a`-dilated, two-function, natural-shift rung.

Assembly (the MRT choreography of `NormalNumbers.ElliottTwistedGraph.shiftCMLogElliott`, with the
dilated ingredients substituted):

* the graph criterion is
  `NormalNumbers.ElliottDilatedSelect.exists_affineLogCorrelation_small_of_fourier_first_moments`;
* its Fourier hypothesis is supplied by
  `NormalNumbers.ElliottDilatedFourier.logProb_fourier_firstMoment_affineBlock_of_MRT`, i.e. MRT
  applied at the stretched scale `X' = aX + a` over the window `W' = min (2W) X'`, with
  non-pretentiousness transported by
  `NormalNumbers.ElliottDilatedFourier.MRTNonpretentious_of_le` at the reduced threshold
  `A' = A/(2a)` (the frequency range `A'X' ≤ AX` is what forces the reduction);
* the window trimming is the dependency's function-agnostic `Erdos67b.norm_elliottWindow_trim_error`
  applied to `pairObservable`.

All dilation losses are constant multiples of `a`, which is fixed before `ε`. -/
theorem dilatedNatShiftCMLogElliott : DilatedNatShiftCMLogElliott := by
  classical
  intro a c₁ h ha hh ε hε
  have har : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  set η : ℝ := ε / 4 with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  obtain ⟨ζ, hζ, hgraph⟩ :=
    NormalNumbers.ElliottDilatedSelect.exists_affineLogCorrelation_small_of_fourier_first_moments
      ha c₁ hh hη
  set δ : ℝ := ζ / (8 * a) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨Hmin, hHmin, hmrt⟩ := mrtModulatedShortIntervalUnrestricted δ hδ
  obtain ⟨H₀, J, L₀, W₀, hH₀min, hH₀, hH₀a, hJ, hL₀, hW₀, hgraphMain⟩ := hgraph Hmin
  set Hmax : ℕ := max H₀ (a * ((Finset.range J).sup (entropyScale H₀))) with hHmaxdef
  have hHmaxmin : Hmin ≤ Hmax := hH₀min.trans (le_max_left _ _)
  obtain ⟨N, hN, hmrtMain⟩ := hmrt Hmax hHmaxmin
  set L₁ : ℕ := max L₀ 2 with hL₁def
  obtain ⟨A₀, hA₀4, hA₀N, hA₀L, hthreshold⟩ := elliottExists_finalThreshold L₁ N W₀ hε
  refine ⟨2 * a * A₀ + 2 * a * N + 4, by omega, ?_⟩
  intro A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
  have h2a : 0 < 2 * a := by omega
  have hA₀A : A₀ ≤ A := by
    have : A₀ ≤ 2 * a * A₀ := Nat.le_mul_of_pos_left A₀ h2a
    omega
  have hA₀W : A₀ ≤ W := hA₀A.trans hAW
  have hW4 : 4 ≤ W := hA₀4.trans hA₀W
  have hW : 0 < W := by omega
  obtain ⟨hlog, hmassThreshold, herror⟩ := hthreshold W hA₀W
  obtain ⟨hLpos, hLL₁, hLX⟩ := elliottTrimmedLower_geometry hW4 hWX
    (hA₀L.trans (hA₀W.trans hWX))
  obtain ⟨hMlo, hMhi⟩ := elliottTrimmedMass_bounds (L₀ := L₁) hW hWX hlog
  set L := elliottTrimmedLower X W L₁ with hLdef
  have hM : 0 < (logProbMassNN L X : ℝ) := by
    exact_mod_cast logProbMassNN_pos hLpos (by omega : L ≤ X)
  have hL2 : 2 ≤ L := (le_max_right L₀ 2).trans hLL₁
  have hL₀L : L₀ ≤ L := (le_max_left L₀ 2).trans hLL₁
  have hX1 : 1 ≤ X := by omega
  -- the rescaled MRT data
  set A' := A / (2 * a) with hA'def
  set X' := a * X + a with hX'def
  set W' := min (2 * W) X' with hW'def
  have hA'A : A' ≤ A := Nat.div_le_self _ _
  have hXX' : X ≤ X' := by
    have : X ≤ a * X := Nat.le_mul_of_pos_left X ha
    omega
  have hX'pos : 0 < X' := by omega
  have hA'N : N ≤ A' := by
    rw [hA'def]
    refine (Nat.le_div_iff_mul_le h2a).mpr ?_
    calc N * (2 * a) = 2 * a * N := by ring
      _ ≤ A := by omega
  have hprod : (A' : ℝ) * X' ≤ (A : ℝ) * X := by
    have h1 : (A' : ℝ) ≤ (A : ℝ) / (2 * a) := by
      rw [hA'def]
      have := Nat.cast_div_le (α := ℝ) (m := A) (n := 2 * a)
      push_cast at this ⊢
      linarith
    have h2 : (X' : ℝ) ≤ 2 * a * X := by
      rw [hX'def]
      have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX1
      push_cast
      nlinarith
    have hApos : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hX'nn : (0 : ℝ) ≤ X' := Nat.cast_nonneg X'
    have hA'nn : (0 : ℝ) ≤ A' := Nat.cast_nonneg A'
    calc (A' : ℝ) * X' ≤ ((A : ℝ) / (2 * a)) * (2 * a * X) := by
          apply mul_le_mul h1 h2 hX'nn (by positivity)
      _ = (A : ℝ) * X := by field_simp
  have hpret' : MRTNonpretentious f₁ A' X' :=
    NormalNumbers.ElliottDilatedFourier.MRTNonpretentious_of_le hu₁ hpret hA'A hXX' hprod
  have hA'W' : A' ≤ W' := by
    refine le_min ?_ ?_
    · omega
    · exact hA'A.trans ((hAW.trans hWX).trans hXX')
  have hW'X' : W' ≤ X' := min_le_right _ _
  have hlogW : 0 < Real.log W := by
    have : (1 : ℝ) < W := by exact_mod_cast (by omega : 1 < W)
    exact Real.log_pos this
  have hlogW' : Real.log W' ≤ 2 * Real.log W := by
    have hmono : Real.log W' ≤ Real.log (2 * W : ℕ) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < W'))
      exact_mod_cast (min_le_left (2 * W) X')
    have hcast : ((2 * W : ℕ) : ℝ) = 2 * (W : ℝ) := by push_cast; ring
    have hsplit : Real.log (2 * W : ℕ) = Real.log 2 + Real.log W := by
      rw [hcast, Real.log_mul (by norm_num) (by positivity)]
    have hlog2 : Real.log 2 ≤ Real.log W :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ W))
    linarith [hmono, hsplit]
  -- the inclusion of dilated base points in the stretched window
  have hincl : ∀ n ∈ Finset.Icc L X, a * (n + 1) - 1 ∈ elliottLogWindow X' W' := by
    intro n hn
    obtain ⟨hnL, hnX⟩ := Finset.mem_Icc.mp hn
    have hn2 : 2 ≤ n := hL2.trans hnL
    have haL : a * L ≤ a * (n + 1) - 1 := by
      have h1 : a * L ≤ a * n := Nat.mul_le_mul_left a (by omega)
      have h2 : a * n + a = a * (n + 1) := by ring
      have h3 : 1 ≤ a := ha
      omega
    have hm2 : 2 ≤ a * (n + 1) - 1 := by
      have h1 : a * L ≤ a * (n + 1) - 1 := haL
      have h2 : L ≤ a * L := Nat.le_mul_of_pos_left L ha
      omega
    have hmX' : a * (n + 1) - 1 ≤ X' := by
      have h1 : a * (n + 1) ≤ a * (X + 1) := Nat.mul_le_mul_left a (by omega)
      have h2 : a * (X + 1) = a * X + a := by ring
      rw [hX'def]
      omega
    have hwide : X' < W' * (a * (n + 1) - 1) := by
      rcases le_or_gt X' (2 * W) with hcase | hcase
      · have hW'eq : W' = X' := by rw [hW'def]; omega
        rw [hW'eq]
        exact (Nat.lt_mul_iff_one_lt_right hX'pos).mpr (by omega)
      · have hW'eq : W' = 2 * W := by rw [hW'def]; omega
        rw [hW'eq]
        have hWL : X < W * L := by
          have h1 : X / W + 1 ≤ L := by
            rw [hLdef, elliottTrimmedLower]; exact le_max_right _ _
          have h2 : W * (X / W) + W ≤ W * L := by
            have := Nat.mul_le_mul_left W h1
            nlinarith [this]
          have h3 : X < W * (X / W) + W := by
            have hdm := Nat.div_add_mod X W
            have hmod : X % W < W := Nat.mod_lt _ hW
            omega
          omega
        have hk1 : a * X < a * (W * L) := mul_lt_mul_of_pos_left hWL ha
        have hk2 : a ≤ a * (W * L) := Nat.le_mul_of_pos_right a (by positivity)
        calc X' = a * X + a := hX'def
          _ < a * (W * L) + a * (W * L) := by omega
          _ = 2 * W * (a * L) := by ring
          _ ≤ 2 * W * (a * (n + 1) - 1) := Nat.mul_le_mul_left _ haL
    exact mem_elliottLogWindow.mpr ⟨by omega, hmX', hwide⟩
  -- the graph criterion
  have hcorr : ‖NormalNumbers.ElliottAffineGraph.affineLogCorrelation L X f₁ f₂ a
      (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ)‖ < η := by
    refine hgraphMain L X hLpos (by omega) hL₀L (hmassThreshold.trans hMlo)
      f₁ f₂ hm₁ hm₂ hu₁ hu₂ ?_
    intro j hj t
    set m := entropyScale H₀ j with hmdef
    set H := a * m with hHdef
    have hmH₀ : H₀ ≤ m := le_entropyScale H₀ j
    have hmH : m ≤ H := Nat.le_mul_of_pos_left m ha
    have hHpos : 0 < H := by
      have : 0 < m := by omega
      rw [hHdef]; positivity
    have hHminH : Hmin ≤ H := (hH₀min.trans hmH₀).trans hmH
    have hHmaxH : H ≤ Hmax := by
      rw [hHmaxdef]
      refine le_max_of_le_right ?_
      exact Nat.mul_le_mul_left a (Finset.le_sup (f := entropyScale H₀) (mem_range.mpr hj))
    have hmrtj := hmrtMain A' X' W' H hA'N hA'W' hW'X' hHminH hHmaxH f₁ hm₁ hu₁ hpret'
      ((t : ℝ) / (a * (4 * h * H + 1) : ℕ))
    have hfirst : logAverageModulatedShortSum f₁ X' W' H
        ((t : ℝ) / (a * (4 * h * H + 1) : ℕ)) ≤ (2 * δ) * Real.log W := by
      refine hmrtj.trans ?_
      calc δ * Real.log W' ≤ δ * (2 * Real.log W) :=
            mul_le_mul_of_nonneg_left hlogW' hδ.le
        _ = (2 * δ) * Real.log W := by ring
    have htrans := NormalNumbers.ElliottDilatedFourier.logProb_fourier_firstMoment_affineBlock_of_MRT
      (L₀ := L₁) (T := (a * (4 * h * H + 1) : ℕ)) ha (by omega : 2 ≤ W) hHpos hincl hM hMlo
      (by positivity : (0:ℝ) ≤ 2 * δ) f₁ t hfirst
    refine htrans.trans ?_
    have hbudget : 4 * (a : ℝ) * (2 * δ) * H = ζ * H := by
      rw [hδdef]; field_simp; ring
    rw [hbudget]
  -- window trimming and the final budget
  have htrim := norm_elliottWindow_trim_error (X := X) hW L₁
    (pairObservable f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ))
    (fun n _ ↦ norm_pairObservable_le_one (fun k hk ↦ (hu₁ k hk).le)
      (fun k hk ↦ (hu₂ k hk).le) a _ _ n)
  rw [← elliottLogCorrelation_eq_window_sum f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) X W] at htrim
  have hsum : ‖∑ n ∈ Finset.Icc L X, (n : ℝ)⁻¹ • pairObservable f₁ f₂ a (c₁ : ℤ)
      ((c₁ + h : ℕ) : ℤ) n‖ < η * (logProbMassNN L X : ℝ) := by
    have hexp : NormalNumbers.ElliottAffineGraph.affineLogCorrelation L X f₁ f₂ a
        (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) = (logProbMassNN L X : ℝ)⁻¹ •
        ∑ n ∈ Finset.Icc L X, (n : ℝ)⁻¹ • pairObservable f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) n :=
      logProbExpectation_eq_mass_inv_smul_sum _ _ _
    rw [hexp, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hM), inv_mul_eq_div] at hcorr
    have := (div_lt_iff₀ hM).1 hcorr
    linarith [this]
  calc ‖elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂) a a
        (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) X W‖
      ≤ ‖∑ n ∈ Finset.Icc L X, (n : ℝ)⁻¹ • pairObservable f₁ f₂ a (c₁ : ℤ)
          ((c₁ + h : ℕ) : ℤ) n‖ + L₁ := by
        have hadd := norm_add_le
          (elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂) a a
              (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) X W -
            ∑ n ∈ Finset.Icc L X, (n : ℝ)⁻¹ • pairObservable f₁ f₂ a (c₁ : ℤ)
              ((c₁ + h : ℕ) : ℤ) n)
          (∑ n ∈ Finset.Icc L X, (n : ℝ)⁻¹ • pairObservable f₁ f₂ a (c₁ : ℤ)
            ((c₁ + h : ℕ) : ℤ) n)
        rw [sub_add_cancel] at hadd
        linarith [hadd, htrim]
    _ ≤ η * (logProbMassNN L X : ℝ) + L₁ := add_le_add hsum.le le_rfl
    _ ≤ η * (2 * Real.log W) + (ε / 2) * Real.log W :=
        add_le_add (mul_le_mul_of_nonneg_left hMhi hη.le) herror
    _ = ε * Real.log W := by rw [hηdef]; ring

/-- **Leaf 2 of the crux, PROVED.**  The mirrored orientation of `dilatedNatShiftCMLogElliott`:
non-pretentiousness now sits on the function at the **larger** shift.

The asymmetry of the dilated stack is only apparent.  In
`NormalNumbers.ElliottDilatedPairing.norm_dilatedPairTwistedMean_le_largeFrequencies` the two blocks
enter the pairing `‖F_b(t+uD)‖ · ‖F_{conj c}(t)‖` symmetrically and Parseval is applied to both, so
which factor survives in the large-frequency sum is a free choice; `ElliottDilatedUpperMirror` makes
the other choice and `ElliottDilatedSelectMirror` pushes it through the (function-symmetric) lower
bound and the entropy selection.  This proof is then the forward one verbatim, with MRT applied to
`conj ∘ f₂` — legitimate because `MRTNonpretentious` is conjugation-invariant
(`NormalNumbers.ElliottTwistedGraph.mrtNonpretentious_conj`). -/
theorem dilatedNatShiftCMLogElliottMirror : DilatedNatShiftCMLogElliottMirror := by
  classical
  intro a c₁ h ha hh ε hε
  have har : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  set η : ℝ := ε / 4 with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  obtain ⟨ζ, hζ, hgraph⟩ :=
    NormalNumbers.ElliottDilatedSelect.exists_affineLogCorrelation_small_of_fourier_first_moments_snd
      ha c₁ hh hη
  set δ : ℝ := ζ / (8 * a) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨Hmin, hHmin, hmrt⟩ := mrtModulatedShortIntervalUnrestricted δ hδ
  obtain ⟨H₀, J, L₀, W₀, hH₀min, hH₀, hH₀a, hJ, hL₀, hW₀, hgraphMain⟩ := hgraph Hmin
  set Hmax : ℕ := max H₀ (a * ((Finset.range J).sup (entropyScale H₀))) with hHmaxdef
  have hHmaxmin : Hmin ≤ Hmax := hH₀min.trans (le_max_left _ _)
  obtain ⟨N, hN, hmrtMain⟩ := hmrt Hmax hHmaxmin
  set L₁ : ℕ := max L₀ 2 with hL₁def
  obtain ⟨A₀, hA₀4, hA₀N, hA₀L, hthreshold⟩ := elliottExists_finalThreshold L₁ N W₀ hε
  refine ⟨2 * a * A₀ + 2 * a * N + 4, by omega, ?_⟩
  intro A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
  -- the mirrored orientation: the graph criterion consumes the moments of `conj ∘ f₂`
  have hmg : IsCompletelyMultiplicativeOnPositive (fun n ↦ conj (f₂ n)) :=
    conj_isCompletelyMultiplicativeOnPositive hm₂
  have hug : ∀ n : ℕ, 0 < n → ‖conj (f₂ n)‖ = 1 := by
    intro n hn; rw [Complex.norm_conj]; exact hu₂ n hn
  have hpretg : MRTNonpretentious (fun n ↦ conj (f₂ n)) A X :=
    NormalNumbers.ElliottTwistedGraph.mrtNonpretentious_conj hpret
  have h2a : 0 < 2 * a := by omega
  have hA₀A : A₀ ≤ A := by
    have : A₀ ≤ 2 * a * A₀ := Nat.le_mul_of_pos_left A₀ h2a
    omega
  have hA₀W : A₀ ≤ W := hA₀A.trans hAW
  have hW4 : 4 ≤ W := hA₀4.trans hA₀W
  have hW : 0 < W := by omega
  obtain ⟨hlog, hmassThreshold, herror⟩ := hthreshold W hA₀W
  obtain ⟨hLpos, hLL₁, hLX⟩ := elliottTrimmedLower_geometry hW4 hWX
    (hA₀L.trans (hA₀W.trans hWX))
  obtain ⟨hMlo, hMhi⟩ := elliottTrimmedMass_bounds (L₀ := L₁) hW hWX hlog
  set L := elliottTrimmedLower X W L₁ with hLdef
  have hM : 0 < (logProbMassNN L X : ℝ) := by
    exact_mod_cast logProbMassNN_pos hLpos (by omega : L ≤ X)
  have hL2 : 2 ≤ L := (le_max_right L₀ 2).trans hLL₁
  have hL₀L : L₀ ≤ L := (le_max_left L₀ 2).trans hLL₁
  have hX1 : 1 ≤ X := by omega
  -- the rescaled MRT data
  set A' := A / (2 * a) with hA'def
  set X' := a * X + a with hX'def
  set W' := min (2 * W) X' with hW'def
  have hA'A : A' ≤ A := Nat.div_le_self _ _
  have hXX' : X ≤ X' := by
    have : X ≤ a * X := Nat.le_mul_of_pos_left X ha
    omega
  have hX'pos : 0 < X' := by omega
  have hA'N : N ≤ A' := by
    rw [hA'def]
    refine (Nat.le_div_iff_mul_le h2a).mpr ?_
    calc N * (2 * a) = 2 * a * N := by ring
      _ ≤ A := by omega
  have hprod : (A' : ℝ) * X' ≤ (A : ℝ) * X := by
    have h1 : (A' : ℝ) ≤ (A : ℝ) / (2 * a) := by
      rw [hA'def]
      have := Nat.cast_div_le (α := ℝ) (m := A) (n := 2 * a)
      push_cast at this ⊢
      linarith
    have h2 : (X' : ℝ) ≤ 2 * a * X := by
      rw [hX'def]
      have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX1
      push_cast
      nlinarith
    have hApos : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hX'nn : (0 : ℝ) ≤ X' := Nat.cast_nonneg X'
    have hA'nn : (0 : ℝ) ≤ A' := Nat.cast_nonneg A'
    calc (A' : ℝ) * X' ≤ ((A : ℝ) / (2 * a)) * (2 * a * X) := by
          apply mul_le_mul h1 h2 hX'nn (by positivity)
      _ = (A : ℝ) * X := by field_simp
  have hpret' : MRTNonpretentious (fun n ↦ conj (f₂ n)) A' X' :=
    NormalNumbers.ElliottDilatedFourier.MRTNonpretentious_of_le hug hpretg hA'A hXX' hprod
  have hA'W' : A' ≤ W' := by
    refine le_min ?_ ?_
    · omega
    · exact hA'A.trans ((hAW.trans hWX).trans hXX')
  have hW'X' : W' ≤ X' := min_le_right _ _
  have hlogW : 0 < Real.log W := by
    have : (1 : ℝ) < W := by exact_mod_cast (by omega : 1 < W)
    exact Real.log_pos this
  have hlogW' : Real.log W' ≤ 2 * Real.log W := by
    have hmono : Real.log W' ≤ Real.log (2 * W : ℕ) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < W'))
      exact_mod_cast (min_le_left (2 * W) X')
    have hcast : ((2 * W : ℕ) : ℝ) = 2 * (W : ℝ) := by push_cast; ring
    have hsplit : Real.log (2 * W : ℕ) = Real.log 2 + Real.log W := by
      rw [hcast, Real.log_mul (by norm_num) (by positivity)]
    have hlog2 : Real.log 2 ≤ Real.log W :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ W))
    linarith [hmono, hsplit]
  -- the inclusion of dilated base points in the stretched window
  have hincl : ∀ n ∈ Finset.Icc L X, a * (n + 1) - 1 ∈ elliottLogWindow X' W' := by
    intro n hn
    obtain ⟨hnL, hnX⟩ := Finset.mem_Icc.mp hn
    have hn2 : 2 ≤ n := hL2.trans hnL
    have haL : a * L ≤ a * (n + 1) - 1 := by
      have h1 : a * L ≤ a * n := Nat.mul_le_mul_left a (by omega)
      have h2 : a * n + a = a * (n + 1) := by ring
      have h3 : 1 ≤ a := ha
      omega
    have hm2 : 2 ≤ a * (n + 1) - 1 := by
      have h1 : a * L ≤ a * (n + 1) - 1 := haL
      have h2 : L ≤ a * L := Nat.le_mul_of_pos_left L ha
      omega
    have hmX' : a * (n + 1) - 1 ≤ X' := by
      have h1 : a * (n + 1) ≤ a * (X + 1) := Nat.mul_le_mul_left a (by omega)
      have h2 : a * (X + 1) = a * X + a := by ring
      rw [hX'def]
      omega
    have hwide : X' < W' * (a * (n + 1) - 1) := by
      rcases le_or_gt X' (2 * W) with hcase | hcase
      · have hW'eq : W' = X' := by rw [hW'def]; omega
        rw [hW'eq]
        exact (Nat.lt_mul_iff_one_lt_right hX'pos).mpr (by omega)
      · have hW'eq : W' = 2 * W := by rw [hW'def]; omega
        rw [hW'eq]
        have hWL : X < W * L := by
          have h1 : X / W + 1 ≤ L := by
            rw [hLdef, elliottTrimmedLower]; exact le_max_right _ _
          have h2 : W * (X / W) + W ≤ W * L := by
            have := Nat.mul_le_mul_left W h1
            nlinarith [this]
          have h3 : X < W * (X / W) + W := by
            have hdm := Nat.div_add_mod X W
            have hmod : X % W < W := Nat.mod_lt _ hW
            omega
          omega
        have hk1 : a * X < a * (W * L) := mul_lt_mul_of_pos_left hWL ha
        have hk2 : a ≤ a * (W * L) := Nat.le_mul_of_pos_right a (by positivity)
        calc X' = a * X + a := hX'def
          _ < a * (W * L) + a * (W * L) := by omega
          _ = 2 * W * (a * L) := by ring
          _ ≤ 2 * W * (a * (n + 1) - 1) := Nat.mul_le_mul_left _ haL
    exact mem_elliottLogWindow.mpr ⟨by omega, hmX', hwide⟩
  -- the graph criterion
  have hcorr : ‖NormalNumbers.ElliottAffineGraph.affineLogCorrelation L X f₁ f₂ a
      (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ)‖ < η := by
    refine hgraphMain L X hLpos (by omega) hL₀L (hmassThreshold.trans hMlo)
      f₁ f₂ hm₁ hm₂ hu₁ hu₂ ?_
    intro j hj t
    set m := entropyScale H₀ j with hmdef
    set H := a * m with hHdef
    have hmH₀ : H₀ ≤ m := le_entropyScale H₀ j
    have hmH : m ≤ H := Nat.le_mul_of_pos_left m ha
    have hHpos : 0 < H := by
      have : 0 < m := by omega
      rw [hHdef]; positivity
    have hHminH : Hmin ≤ H := (hH₀min.trans hmH₀).trans hmH
    have hHmaxH : H ≤ Hmax := by
      rw [hHmaxdef]
      refine le_max_of_le_right ?_
      exact Nat.mul_le_mul_left a (Finset.le_sup (f := entropyScale H₀) (mem_range.mpr hj))
    have hmrtj := hmrtMain A' X' W' H hA'N hA'W' hW'X' hHminH hHmaxH
      (fun n ↦ conj (f₂ n)) hmg hug hpret'
      ((t : ℝ) / (a * (4 * h * H + 1) : ℕ))
    have hfirst : logAverageModulatedShortSum (fun n ↦ conj (f₂ n)) X' W' H
        ((t : ℝ) / (a * (4 * h * H + 1) : ℕ)) ≤ (2 * δ) * Real.log W := by
      refine hmrtj.trans ?_
      calc δ * Real.log W' ≤ δ * (2 * Real.log W) :=
            mul_le_mul_of_nonneg_left hlogW' hδ.le
        _ = (2 * δ) * Real.log W := by ring
    have htrans := NormalNumbers.ElliottDilatedFourier.logProb_fourier_firstMoment_affineBlock_of_MRT
      (L₀ := L₁) (T := (a * (4 * h * H + 1) : ℕ)) ha (by omega : 2 ≤ W) hHpos hincl hM hMlo
      (by positivity : (0:ℝ) ≤ 2 * δ) (fun n ↦ conj (f₂ n)) t hfirst
    refine htrans.trans ?_
    have hbudget : 4 * (a : ℝ) * (2 * δ) * H = ζ * H := by
      rw [hδdef]; field_simp; ring
    rw [hbudget]
  -- window trimming and the final budget
  have htrim := norm_elliottWindow_trim_error (X := X) hW L₁
    (pairObservable f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ))
    (fun n _ ↦ norm_pairObservable_le_one (fun k hk ↦ (hu₁ k hk).le)
      (fun k hk ↦ (hu₂ k hk).le) a _ _ n)
  rw [← elliottLogCorrelation_eq_window_sum f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) X W] at htrim
  have hsum : ‖∑ n ∈ Finset.Icc L X, (n : ℝ)⁻¹ • pairObservable f₁ f₂ a (c₁ : ℤ)
      ((c₁ + h : ℕ) : ℤ) n‖ < η * (logProbMassNN L X : ℝ) := by
    have hexp : NormalNumbers.ElliottAffineGraph.affineLogCorrelation L X f₁ f₂ a
        (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) = (logProbMassNN L X : ℝ)⁻¹ •
        ∑ n ∈ Finset.Icc L X, (n : ℝ)⁻¹ • pairObservable f₁ f₂ a (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) n :=
      logProbExpectation_eq_mass_inv_smul_sum _ _ _
    rw [hexp, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hM), inv_mul_eq_div] at hcorr
    have := (div_lt_iff₀ hM).1 hcorr
    linarith [this]
  calc ‖elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂) a a
        (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) X W‖
      ≤ ‖∑ n ∈ Finset.Icc L X, (n : ℝ)⁻¹ • pairObservable f₁ f₂ a (c₁ : ℤ)
          ((c₁ + h : ℕ) : ℤ) n‖ + L₁ := by
        have hadd := norm_add_le
          (elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂) a a
              (c₁ : ℤ) ((c₁ + h : ℕ) : ℤ) X W -
            ∑ n ∈ Finset.Icc L X, (n : ℝ)⁻¹ • pairObservable f₁ f₂ a (c₁ : ℤ)
              ((c₁ + h : ℕ) : ℤ) n)
          (∑ n ∈ Finset.Icc L X, (n : ℝ)⁻¹ • pairObservable f₁ f₂ a (c₁ : ℤ)
            ((c₁ + h : ℕ) : ℤ) n)
        rw [sub_add_cancel] at hadd
        linarith [hadd, htrim]
    _ ≤ η * (logProbMassNN L X : ℝ) + L₁ := add_le_add hsum.le le_rfl
    _ ≤ η * (2 * Real.log W) + (ε / 2) * Real.log W :=
        add_le_add (mul_le_mul_of_nonneg_left hMhi hη.le) herror
    _ = ε * Real.log W := by rw [hηdef]; ring

/-- **The crux rung, on the live dilated route.**  Replaces
`NormalNumbers.ElliottDilatedSlice.dilatedCMLogElliott`, which sat on the refuted slice route. -/
theorem dilatedCMLogElliott : DilatedCMLogElliott :=
  dilatedCM_of_natShift dilatedNatShiftCMLogElliott dilatedNatShiftCMLogElliottMirror

end

end NormalNumbers.ElliottDilatedRung

#print axioms NormalNumbers.ElliottDilatedRung.dilatedNatShiftCMLogElliott
#print axioms NormalNumbers.ElliottDilatedRung.dilatedNatShiftCMLogElliottMirror
#print axioms NormalNumbers.ElliottDilatedRung.dilatedCMLogElliott
