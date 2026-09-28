import NormalNumbers.ElliottStageStep
import NormalNumbers.ElliottLadder

/-!
# The finite family of substituted affine pairs, and one threshold for all of them

Leaf 2, Case B.  `AffineCMLogElliott` hands out its threshold `A₀` **per affine pair**, and the two
expansion steps of `ElliottStageStep` replace the original pair `(a₁, a₂; b₁, b₂)` by the
substituted pair

`(a₁d₂, a₂d₁; a₁n₀₂ + c₁, newShift (a₂d₁) (a₂n₀₁+b₂) d₂ n₀₂)`,  `c₁ = newShift a₁ b₁ d₁ n₀₁`,

one for each `(d₁, n₀₁, d₂, n₀₂)` with `d₁, d₂ ≤ D` and `n₀ᵢ < dᵢ`.  Since `D` is fixed **before**
the threshold (that is exactly what `ElliottRankin.exists_squarefull_tail_bound` buys), the family
is finite and a single threshold serves it: `familyThreshold` is the `Finset.sup`.

The decisive arithmetic fact is `det_final`: the determinant of the substituted pair is *exactly*
`a₁b₂ − a₂b₁`, hence nonzero, so `AffineCMLogElliott` applies to every member.  It is two
applications of `ElliottRestricted.det_newShift`, and it needs both divisibility conditions — which
is why `norm_restrictedCorr_le` was narrowed to divisible residue classes.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottThresholdFamily

open Erdos67b NormalNumbers.ElliottLadder NormalNumbers.ElliottRestricted

noncomputable section

/-- The first dilation of the substituted pair. -/
def finalDil₁ (a₁ d₂ : ℕ) : ℕ := a₁ * d₂

/-- The second dilation of the substituted pair. -/
def finalDil₂ (a₂ d₁ : ℕ) : ℕ := a₂ * d₁

/-- The first shift of the substituted pair. -/
def finalShift₁ (a₁ : ℕ) (b₁ : ℤ) (d₁ n₀₁ n₀₂ : ℕ) : ℤ :=
  (a₁ : ℤ) * n₀₂ + newShift a₁ b₁ d₁ n₀₁

/-- The second shift of the substituted pair. -/
def finalShift₂ (a₂ : ℕ) (b₂ : ℤ) (d₁ n₀₁ d₂ n₀₂ : ℕ) : ℤ :=
  newShift (a₂ * d₁) ((a₂ : ℤ) * n₀₁ + b₂) d₂ n₀₂

/-- **The determinant of the substituted pair is exactly the original determinant.**  Two
applications of `det_newShift`: the first expansion contributes
`a₁(a₂n₀₁+b₂) − (a₂d₁)c₁ = a₁b₂ − a₂b₁`, the second (in the swapped orientation) contributes
`(a₂d₁)(a₁n₀₂+c₁) − (a₁d₂)c₂ = (a₂d₁)c₁ − a₁(a₂n₀₁+b₂)`. -/
theorem det_final {a₁ a₂ d₁ n₀₁ d₂ n₀₂ : ℕ} {b₁ b₂ : ℤ}
    (hd₁ : (d₁ : ℤ) ∣ (a₁ : ℤ) * (n₀₁ : ℤ) + b₁)
    (hd₂ : (d₂ : ℤ) ∣ ((a₂ * d₁ : ℕ) : ℤ) * (n₀₂ : ℤ) + ((a₂ : ℤ) * (n₀₁ : ℤ) + b₂)) :
    (finalDil₁ a₁ d₂ : ℤ) * finalShift₂ a₂ b₂ d₁ n₀₁ d₂ n₀₂
        - (finalDil₂ a₂ d₁ : ℤ) * finalShift₁ a₁ b₁ d₁ n₀₁ n₀₂
      = (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ := by
  have h1 := det_newShift (a₁ := a₁) (a₂ := a₂) (d := d₁) (n₀ := n₀₁) (b₁ := b₁) (b₂ := b₂) hd₁
  have h2 := det_newShift (a₁ := a₂ * d₁) (a₂ := a₁) (d := d₂) (n₀ := n₀₂)
    (b₁ := (a₂ : ℤ) * (n₀₁ : ℤ) + b₂) (b₂ := newShift a₁ b₁ d₁ n₀₁) hd₂
  rw [finalDil₁, finalDil₂, finalShift₁, finalShift₂]
  push_cast at h1 h2 ⊢
  linarith [h1, h2]

/-- The per-member threshold supplied by `AffineCMLogElliott`, defaulted to `2` on the (unused)
members whose dilations degenerate or whose determinant vanishes. -/
def memberThreshold (h : AffineCMLogElliott) (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) {ε : ℝ} (hε : 0 < ε)
    (q : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  if H : 0 < finalDil₁ a₁ q.2.2.1 ∧ 0 < finalDil₂ a₂ q.1 ∧
      ((finalDil₁ a₁ q.2.2.1 : ℤ) * finalShift₂ a₂ b₂ q.1 q.2.1 q.2.2.1 q.2.2.2
        - (finalDil₂ a₂ q.1 : ℤ) * finalShift₁ a₁ b₁ q.1 q.2.1 q.2.2.2) ≠ 0 then
    (h (finalDil₁ a₁ q.2.2.1) (finalDil₂ a₂ q.1)
        (finalShift₁ a₁ b₁ q.1 q.2.1 q.2.2.2) (finalShift₂ a₂ b₂ q.1 q.2.1 q.2.2.1 q.2.2.2)
        H.1 H.2.1 H.2.2 ε hε).choose
  else 2

theorem two_le_memberThreshold (h : AffineCMLogElliott) (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) {ε : ℝ}
    (hε : 0 < ε) (q : ℕ × ℕ × ℕ × ℕ) : 2 ≤ memberThreshold h a₁ a₂ b₁ b₂ hε q := by
  rw [memberThreshold]
  split_ifs with H
  · exact (h _ _ _ _ H.1 H.2.1 H.2.2 ε hε).choose_spec.1
  · exact le_rfl

/-- **The threshold's defining property.**  Every member of the family obeys `AffineCMLogElliott`'s
conclusion at its own threshold. -/
theorem memberThreshold_spec (h : AffineCMLogElliott) (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) {ε : ℝ}
    (hε : 0 < ε) (q : ℕ × ℕ × ℕ × ℕ)
    (hp₁ : 0 < finalDil₁ a₁ q.2.2.1) (hp₂ : 0 < finalDil₂ a₂ q.1)
    (hdet : ((finalDil₁ a₁ q.2.2.1 : ℤ) * finalShift₂ a₂ b₂ q.1 q.2.1 q.2.2.1 q.2.2.2
      - (finalDil₂ a₂ q.1 : ℤ) * finalShift₁ a₁ b₁ q.1 q.2.1 q.2.2.2) ≠ 0)
    (A X W : ℕ) (hA : memberThreshold h a₁ a₂ b₁ b₂ hε q ≤ A) (hAW : A ≤ W) (hWX : W ≤ X)
    (f₁ f₂ : ℕ → ℂ)
    (hc₁ : IsCompletelyMultiplicativeOnPositive f₁)
    (hc₂ : IsCompletelyMultiplicativeOnPositive f₂)
    (hu₁ : ∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) (hu₂ : ∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1)
    (hMRT : MRTNonpretentious f₁ A X) :
    ‖elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂)
        (finalDil₁ a₁ q.2.2.1) (finalDil₂ a₂ q.1)
        (finalShift₁ a₁ b₁ q.1 q.2.1 q.2.2.2) (finalShift₂ a₂ b₂ q.1 q.2.1 q.2.2.1 q.2.2.2)
        X W‖ ≤ ε * Real.log W := by
  rw [memberThreshold, dif_pos ⟨hp₁, hp₂, hdet⟩] at hA
  exact (h _ _ _ _ hp₁ hp₂ hdet ε hε).choose_spec.2 A X W hA hAW hWX f₁ f₂ hc₁ hc₂ hu₁ hu₂ hMRT

/-- The index set of the family: `(d₁, n₀₁, d₂, n₀₂)` with all four entries `≤ D`. -/
def familyIndex (D : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  Finset.range (D + 1) ×ˢ (Finset.range (D + 1) ×ˢ
    (Finset.range (D + 1) ×ˢ Finset.range (D + 1)))

theorem mem_familyIndex {D d₁ n₀₁ d₂ n₀₂ : ℕ} (h₁ : d₁ ≤ D) (h₂ : n₀₁ ≤ D) (h₃ : d₂ ≤ D)
    (h₄ : n₀₂ ≤ D) : (d₁, n₀₁, d₂, n₀₂) ∈ familyIndex D := by
  simp only [familyIndex, Finset.mem_product, Finset.mem_range]
  omega

/-- **One threshold for the whole family.** -/
def familyThreshold (h : AffineCMLogElliott) (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) {ε : ℝ} (hε : 0 < ε)
    (D : ℕ) : ℕ :=
  (familyIndex D).sup (memberThreshold h a₁ a₂ b₁ b₂ hε)

theorem memberThreshold_le_familyThreshold (h : AffineCMLogElliott) (a₁ a₂ : ℕ) (b₁ b₂ : ℤ)
    {ε : ℝ} (hε : 0 < ε) {D : ℕ} {q : ℕ × ℕ × ℕ × ℕ} (hq : q ∈ familyIndex D) :
    memberThreshold h a₁ a₂ b₁ b₂ hε q ≤ familyThreshold h a₁ a₂ b₁ b₂ hε D :=
  Finset.le_sup hq

theorem two_le_familyThreshold (h : AffineCMLogElliott) (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) {ε : ℝ}
    (hε : 0 < ε) (D : ℕ) : 2 ≤ familyThreshold h a₁ a₂ b₁ b₂ hε D := by
  refine le_trans (two_le_memberThreshold h a₁ a₂ b₁ b₂ hε (0, 0, 0, 0)) ?_
  exact memberThreshold_le_familyThreshold h a₁ a₂ b₁ b₂ hε
    (mem_familyIndex (Nat.zero_le D) (Nat.zero_le D) (Nat.zero_le D) (Nat.zero_le D))

end

end NormalNumbers.ElliottThresholdFamily
