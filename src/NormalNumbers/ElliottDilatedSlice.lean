import NormalNumbers.ElliottTwoShift
import NormalNumbers.ElliottLadder

/-!
# The dilation-slice rung: where the crux's *common dilation* actually lives

`NormalNumbers.ElliottLadder.DilatedCMLogElliott` is the crux rung: two independent completely
multiplicative unimodular functions against the pair of affine forms `a*n + c₁`, `a*n + c₂`.  The
two-function generality is fully discharged by `NormalNumbers.ElliottTwistedGraph.shiftCMLogElliott`
and its mirror.  What remains is the common dilation `a`, and this file isolates it exactly.

## The substitution that makes the residue class trivial

The tempting move is `m = a*n + c₁`, which turns the correlation into a pure-shift correlation
restricted to the arithmetic progression `m ≡ c₁ (mod a)`.  That is the *wrong* substitution: the
graph step `m ↦ p*m` sends the class `c₁` to `p*c₁`, so the restriction is not preserved and has to
be carried through the whole entropy/graph argument.

The right move is `m = a*n`, keeping **both** shifts inside the observable:

```
∑_{n ∈ (X/W, X]} (1/n) f₁(a n + c₁) f₂(a n + c₂)
  = a * ∑_{m ∈ (aX/W, aX], a ∣ m} (1/m) f₁(m + c₁) f₂(m + c₂).
```

The residue class is now `0`, which **every** dilation `m ↦ p*m` preserves.  And the identity is
*exact*, with no boundary or weight error at all: it is the dependency's own
`Erdos67b.sum_elliottDilationSlice` (the multiples-of-`q` slice of a logarithmic window is an
exact dilation of the window, harmonic weights included), applied to
`F m = positiveIntExtension f₁ (m + c₁) * positiveIntExtension f₂ (m + c₂)`.

So the crux factors as

* `elliottLogCorrelation_eq_slice` — the exact identity (proved here);
* `dilatedCM_of_slice` — `DilatedSliceCMLogElliott → DilatedCMLogElliott` (proved here, free);
* `dilatedSliceCMLogElliott` — the remaining obligation, **strictly smaller** than the old crux:
  a *pure* two-shift correlation with a divisibility restriction at residue `0`.

## Why the Dirichlet-character detour is not a shortcut

Detecting `m ≡ r (mod a)` with `gcd(r,a) = 1` by characters does work, and `χ · f₁` can be kept
completely multiplicative *and unimodular* by replacing `χ` with the completely multiplicative `χ̃`
agreeing with `χ` off the primes dividing `a` and equal to `1` on them (they agree on the coprime
support).  But the leftover coprimality condition, removed by Möbius over `e ∣ a` and `m = e·m'`,
turns every term into a **mixed-dilation** correlation `∑ (1/m') g₁(m') f₂(e m' + d)`, which
`NormalNumbers.ElliottLadder.affineCM_of_dilatedCM` converts back into a common dilation, i.e. back
into a slice at residue `0`.  The loop closes; the slice rung is its fixed point.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottDilatedSlice

open Erdos67b
open NormalNumbers.ElliottTwistedGraph
open NormalNumbers.ElliottTwoShift
open NormalNumbers.ElliottLadder

noncomputable section

/-! ## The slice correlation -/

/-- The two-shift logarithmic correlation restricted to the multiples of `a` inside the window
`(a*X/W, a*X]`.  Compare `Erdos67b.shiftedLogCorrelation`, which is the case `a = 1`, `c₁ = 0`,
`f₂ = conj f₁`. -/
def sliceShiftLogCorrelation (f₁ f₂ : ℕ → ℂ) (a : ℕ) (c₁ c₂ : ℤ) (X W : ℕ) : ℂ :=
  ∑ m ∈ elliottDilationSlice a X W,
    (harmonicWeight m : ℂ) * positiveIntExtension f₁ ((m : ℤ) + c₁) *
      positiveIntExtension f₂ ((m : ℤ) + c₂)

/-- The affine form at a common dilation, written as a translate of the dilated point. -/
theorem integerAffine_eq_natMul (a : ℕ) (c : ℤ) (n : ℕ) :
    integerAffine a c n = ((a * n : ℕ) : ℤ) + c := by
  simp only [integerAffine]
  push_cast
  ring

/-- **The exact dilation identity.**  No boundary terms, no weight discrepancy: the common-dilation
correlation is literally `a` times the multiples-of-`a` slice correlation. -/
theorem elliottLogCorrelation_eq_slice (f₁ f₂ : ℕ → ℂ) {a : ℕ} (ha : 0 < a)
    (c₁ c₂ : ℤ) (X W : ℕ) :
    elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂) a a c₁ c₂ X W =
      (a : ℂ) * sliceShiftLogCorrelation f₁ f₂ a c₁ c₂ X W := by
  have key := sum_elliottDilationSlice
      (fun m ↦ positiveIntExtension f₁ ((m : ℤ) + c₁) * positiveIntExtension f₂ ((m : ℤ) + c₂))
      (q := a) (X := X) (W := W) ha
  have hslice : sliceShiftLogCorrelation f₁ f₂ a c₁ c₂ X W =
      ∑ m ∈ elliottDilationSlice a X W, (harmonicWeight m : ℂ) *
        (positiveIntExtension f₁ ((m : ℤ) + c₁) * positiveIntExtension f₂ ((m : ℤ) + c₂)) :=
    Finset.sum_congr rfl fun m _ ↦ mul_assoc _ _ _
  have hcorr : elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂)
      a a c₁ c₂ X W =
      ∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) *
        (positiveIntExtension f₁ (((a * n : ℕ) : ℤ) + c₁) *
          positiveIntExtension f₂ (((a * n : ℕ) : ℤ) + c₂)) := by
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [integerAffine_eq_natMul, integerAffine_eq_natMul, mul_assoc]
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hcast : (((a : ℝ))⁻¹ : ℂ) = ((a : ℂ))⁻¹ := by push_cast; ring
  rw [hslice, key, hcast, hcorr, ← mul_assoc, mul_inv_cancel₀ ha', one_mul]

/-! ## The rung -/

/-- **The dilation-slice rung.**  A *pure* two-shift correlation of two independent completely
multiplicative unimodular functions, restricted to the multiples of `a`.

Note that the MRT scale stays `X` while the window is `(a*X/W, a*X]`: the factor `a` is baked into
the correlation, not into the non-pretentiousness hypothesis, so the rung composes with
`Erdos67b.MRTNonpretentious f₁ A X` exactly as the proved pure-shift rung does. -/
def DilatedSliceCMLogElliott : Prop :=
  ∀ (a : ℕ) (c₁ c₂ : ℤ), 0 < a → c₁ ≠ c₂ →
    ∀ ε : ℝ, 0 < ε →
      ∃ A₀ : ℕ, 2 ≤ A₀ ∧
        ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
          ∀ f₁ f₂ : ℕ → ℂ,
            IsCompletelyMultiplicativeOnPositive f₁ →
            IsCompletelyMultiplicativeOnPositive f₂ →
            (∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) →
            (∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1) →
            MRTNonpretentious f₁ A X →
            ‖sliceShiftLogCorrelation f₁ f₂ a c₁ c₂ X W‖ ≤ ε * Real.log W

/-- **The common dilation is free once the slice rung is known.** -/
theorem dilatedCM_of_slice (h : DilatedSliceCMLogElliott) : DilatedCMLogElliott := by
  intro a c₁ c₂ ha hne ε hε
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨A₀, hA₀, hmain⟩ := h a c₁ c₂ ha hne (ε / a) (by positivity)
  refine ⟨A₀, hA₀, ?_⟩
  intro A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
  have hres := hmain A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
  rw [elliottLogCorrelation_eq_slice f₁ f₂ ha c₁ c₂ X W, norm_mul, Complex.norm_natCast]
  calc
    (a : ℝ) * ‖sliceShiftLogCorrelation f₁ f₂ a c₁ c₂ X W‖ ≤
        (a : ℝ) * (ε / a * Real.log W) :=
      mul_le_mul_of_nonneg_left hres hapos.le
    _ = ε * Real.log W := by field_simp

/-! ## The `a = 1` anchor -/

/-- At `a = 1` the slice is the whole window: the rung degenerates to the two-shift correlation. -/
@[simp]
theorem elliottDilationSlice_one (X W : ℕ) :
    elliottDilationSlice 1 X W = elliottLogWindow X W := by
  ext m
  simp [elliottDilationSlice]

/-! ## The `a = 1` case is proved -/

/-- At `a = 1` the slice correlation is the two-shift correlation. -/
theorem sliceShiftLogCorrelation_one (f₁ f₂ : ℕ → ℂ) (c₁ c₂ : ℤ) (X W : ℕ) :
    sliceShiftLogCorrelation f₁ f₂ 1 c₁ c₂ X W = twoShiftLogCorrelation f₁ f₂ c₁ c₂ X W := by
  rw [sliceShiftLogCorrelation, elliottDilationSlice_one, twoShiftLogCorrelation]

/-- **The slice rung holds at `a = 1`** (`NormalNumbers.ElliottTwoShift.twoShiftCMLogElliott`). -/
theorem sliceCM_one (c₁ c₂ : ℤ) (hne : c₁ ≠ c₂) (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
        ∀ f₁ f₂ : ℕ → ℂ,
          IsCompletelyMultiplicativeOnPositive f₁ →
          IsCompletelyMultiplicativeOnPositive f₂ →
          (∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) →
          (∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1) →
          MRTNonpretentious f₁ A X →
          ‖sliceShiftLogCorrelation f₁ f₂ 1 c₁ c₂ X W‖ ≤ ε * Real.log W := by
  obtain ⟨A₀, hA₀, hmain⟩ := twoShiftCMLogElliott c₁ c₂ hne ε hε
  refine ⟨A₀, hA₀, ?_⟩
  intro A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
  rw [sliceShiftLogCorrelation_one]
  exact hmain A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret

/-! ## The remaining obligation: the genuinely dilated slices -/

/-- The slice rung restricted to `a ≥ 2` — the only case still open, since `a = 1` is
`sliceCM_one`. -/
def DilatedSliceCMLogElliottGe : Prop :=
  ∀ (a : ℕ) (c₁ c₂ : ℤ), 2 ≤ a → c₁ ≠ c₂ →
    ∀ ε : ℝ, 0 < ε →
      ∃ A₀ : ℕ, 2 ≤ A₀ ∧
        ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
          ∀ f₁ f₂ : ℕ → ℂ,
            IsCompletelyMultiplicativeOnPositive f₁ →
            IsCompletelyMultiplicativeOnPositive f₂ →
            (∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) →
            (∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1) →
            MRTNonpretentious f₁ A X →
            ‖sliceShiftLogCorrelation f₁ f₂ a c₁ c₂ X W‖ ≤ ε * Real.log W

/-- The full slice rung follows from its `a ≥ 2` part, because `a = 1` is proved. -/
theorem dilatedSlice_of_ge (h : DilatedSliceCMLogElliottGe) : DilatedSliceCMLogElliott := by
  intro a c₁ c₂ ha hne ε hε
  rcases Nat.lt_or_ge a 2 with hlt | hge
  · have ha1 : a = 1 := by omega
    subst ha1
    exact sliceCM_one c₁ c₂ hne ε hε
  · exact h a c₁ c₂ hge hne ε hε



/-- **Open (the crux, re-decomposed and narrowed).**  The pure two-shift correlation restricted to
the multiples of `a`, for `a ≥ 2`.

Already discharged: `a = 1` (`sliceCM_one`, from
`NormalNumbers.ElliottTwoShift.twoShiftCMLogElliott`), so the two arbitrary integer shifts cost
nothing beyond the pure-shift rung.

What is left, and why it should go through: the divisibility `a ∣ m` is at **residue `0`**, hence
preserved by every dilation `m ↦ p*m` of the prime graph.  The graph's own observable already
carries a divisibility indicator
(`NormalNumbers.ElliottTwistedGraph.pairTwistedDivisibleObservable`,
`if q ∣ n then w q * (f₁ n * f₂ (n + q*h)) else 0`), and for a dyadic prime `q > a` one has
`gcd(a, q) = 1`, so for `q ∣ n` the conditions `a*q ∣ n` and `a ∣ n / q` agree: the two
divisibilities compose.  The obligation is to re-run the twisted-graph stack with `a*q ∣ n` in
place of `q ∣ n`.

See `PENDING_WORK.md` (2026-09-25) for the attack order and for the refuted detours. -/
theorem dilatedSliceCMLogElliottGe : DilatedSliceCMLogElliottGe := by
  sorry

/-- The slice rung, with its `a = 1` case discharged. -/
theorem dilatedSliceCMLogElliott : DilatedSliceCMLogElliott :=
  dilatedSlice_of_ge dilatedSliceCMLogElliottGe

/-- **The crux rung, reduced to the slice rung.**  Replaces the former
`NormalNumbers.ElliottLadder.dilatedCMLogElliott`. -/
theorem dilatedCMLogElliott : DilatedCMLogElliott :=
  dilatedCM_of_slice dilatedSliceCMLogElliott

end

end NormalNumbers.ElliottDilatedSlice
