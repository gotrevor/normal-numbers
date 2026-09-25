import NormalNumbers.ElliottDilatedSlice
import NormalNumbers.ElliottDilatedMean

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
theorem dilatedNatShiftCMLogElliott : DilatedNatShiftCMLogElliott := by
  sorry

/-- **Open leaf 2 of the crux.**  The mirrored orientation of `dilatedNatShiftCMLogElliott`.
In the pure-shift case this was `NormalNumbers.ElliottTwistedGraph.shiftCMLogElliottMirror`, proved
by running the same graph argument with the roles of the two blocks exchanged; the dilated stack is
symmetric in the same way (the asymmetry enters only through which block's Fourier first moments
the upper bound consumes). -/
theorem dilatedNatShiftCMLogElliottMirror : DilatedNatShiftCMLogElliottMirror := by
  sorry

/-- **The crux rung, on the live dilated route.**  Replaces
`NormalNumbers.ElliottDilatedSlice.dilatedCMLogElliott`, which sat on the refuted slice route. -/
theorem dilatedCMLogElliott : DilatedCMLogElliott :=
  dilatedCM_of_natShift dilatedNatShiftCMLogElliott dilatedNatShiftCMLogElliottMirror

end

end NormalNumbers.ElliottDilatedRung
