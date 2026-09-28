import NormalNumbers.ElliottDilatedUpper

/-!
# The lower-bound side of the `a`-dilated graph: edges at a *back-shifted* base point

`NormalNumbers.ElliottAffineGraph.norm_logProb_affineTwistedObservable_sub_correlation_le` says
each translated affine graph edge has mean `C/q`, where `C` is the correlation the crux has to
bound.  It is stated for a **forward** translation `n ↦ n + j`.

The dilated block bookkeeping (`sum_dilatedPairShiftEdge_affineBlock`) produces edges at the index

```
n + 1 + j − ⌊q c₁ / a⌋,
```

i.e. a forward translation by `1 + j < 1 + H` composed with a **backward** shift by
`d = ⌊q c₁ / a⌋`.  The backward shift is the one piece of the lower-bound port that the dependency
does not supply, because its own graph never moves the base point backwards.  It costs exactly what
a forward shift costs: this file proves the backward translation estimate and assembles the
edge-mean estimate at the dilated index.

Since `d ≤ q c₁ / a ≤ P |c₁|` and the window starts at `L ≫ P |c₁|`, the hypothesis `d ≤ L` and the
extra error `2 d / (L · M)` are both free in the application.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottDilatedLower

open Erdos67b
open NormalNumbers.ElliottTwistedGraph
open NormalNumbers.ElliottAffineGraph
open NormalNumbers.ElliottLadder

noncomputable section

/-- **The backward translation estimate.**  Mirror of
`Erdos67b.norm_logProbExpectation_translate_sub_le`, obtained from it by applying it to the
back-shifted function: `(fun n ↦ F (n - d)) (n + d) = F n`. -/
theorem norm_logProbExpectation_backtranslate_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) (d : ℕ)
    (F : ℕ → E) {B : ℝ} (hB : 0 ≤ B) (hF : ∀ n, ‖F n‖ ≤ B) :
    ‖logProbExpectation L U (fun n ↦ F (n - d)) - logProbExpectation L U F‖ ≤
      2 * B * d / ((L : ℝ) * logProbMassNN L U) := by
  have h := norm_logProbExpectation_translate_sub_le hL hLU d
    (fun n ↦ F (n - d)) hB (fun n _ ↦ hF _)
  have hcancel : (fun n ↦ (fun m ↦ F (m - d)) (n + d)) = F := by
    funext n; simp
  rw [hcancel] at h
  rw [norm_sub_rev]
  exact h

/-- **The edge mean at the dilated index.**  The affine graph edge based at `n + j - d` still has
mean `C/q`, with one extra error term `2 d / (L · M)` for the backward shift. -/
theorem norm_logProb_affineTwistedObservable_shift_sub_correlation_le
    {L U q : ℕ} (hL : 0 < L) (hLU : L ≤ U) (hq : 0 < q)
    {f₁ f₂ : ℕ → ℂ}
    (hm₁ : IsCompletelyMultiplicativeOnPositive f₁)
    (hm₂ : IsCompletelyMultiplicativeOnPositive f₂)
    (hu₁ : ∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) (hu₂ : ∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1)
    (a : ℕ) (c₁ c₂ : ℤ) (j d : ℕ) (hd : d ≤ L) :
    ‖logProbExpectation L U
        (fun n ↦ affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂ (n + j - d)) -
      (q : ℝ)⁻¹ • affineLogCorrelation L U f₁ f₂ a c₁ c₂‖ ≤
        2 / (logProbMassNN L U : ℝ) +
          2 * j / ((L : ℝ) * logProbMassNN L U) +
          2 * d / ((L : ℝ) * logProbMassNN L U) := by
  have hu₁' : ∀ n : ℕ, 0 < n → ‖f₁ n‖ ≤ 1 := fun n hn ↦ (hu₁ n hn).le
  have hu₂' : ∀ n : ℕ, 0 < n → ‖f₂ n‖ ≤ 1 := fun n hn ↦ (hu₂ n hn).le
  have htw : ‖pairTwist f₁ f₂ q‖ = 1 := norm_pairTwist hu₁ hu₂ hq
  set O : ℕ → ℂ := fun n ↦ affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂ (n + j)
    with hO
  have hOb : ∀ n, ‖O n‖ ≤ 1 := fun n ↦
    norm_affineTwistedObservable_le_one (by rw [htw]) hu₁' hu₂' a c₁ c₂ _
  -- on the window the two indexings agree
  have hidx : logProbExpectation L U
      (fun n ↦ affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂ (n + j - d)) =
      logProbExpectation L U (fun n ↦ O (n - d)) := by
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    have hLn : L ≤ (n : ℕ) := (mem_logProbWindow.mp n.2).1
    have : (n : ℕ) + j - d = ((n : ℕ) - d) + j := by omega
    rw [hO]
    simp only
    rw [this]
  have hback := norm_logProbExpectation_backtranslate_sub_le hL hLU d O zero_le_one hOb
  have hfwd := norm_logProb_affineTwistedObservable_sub_correlation_le hL hLU hq
    hm₁ hm₂ hu₁ hu₂ a c₁ c₂ j
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (logProbExpectation L U (fun n ↦ O (n - d)))
    (logProbExpectation L U O)
    ((q : ℝ)⁻¹ • affineLogCorrelation L U f₁ f₂ a c₁ c₂)
  rw [hidx]
  have hOeq : logProbExpectation L U O = logProbExpectation L U
      (fun n ↦ affineTwistedObservable (pairTwist f₁ f₂) f₁ f₂ a q c₁ c₂ (n + j)) := rfl
  rw [hOeq] at htri
  linarith

/-! ## The dilated block is an ordinary block at a dilated base point

This is the structural fact that lets the finite-alphabet entropy machinery see the dilated graph
at all.  `affineBlock f a n H` looks like a new kind of block, but it is not: it is the
dependency's own `finiteSequenceBlock` of the **same** sequence, read at the base point
`a*(n+1) - 1`.  So the dilated graph is a graph on consecutive blocks — only the base point moves
with `a`, and the entropy/rare-event layer is a statement about blocks, not about where they sit.
-/

open NormalNumbers.ElliottDilatedPairing in
/-- **The `a`-dilated block is the ordinary block at base point `a*(n+1) - 1`.** -/
theorem affineBlock_eq_finiteSequenceBlock {H : ℕ} (f : ℕ → ℂ) {a : ℕ} (ha : 0 < a) (n : ℕ) :
    affineBlock f a n H = finiteSequenceBlock f H (a * (n + 1) - 1) := by
  funext i
  have hpos : 0 < a * (n + 1) := Nat.mul_pos ha (Nat.succ_pos n)
  have hidx : a * (n + 1) - 1 + i.1 + 1 = a * (n + 1) + i.1 := by omega
  have hz : (((a * (n + 1) : ℕ)) : ℤ) + (i.1 : ℤ) = ((a * (n + 1) + i.1 : ℕ) : ℤ) := by push_cast; ring
  rw [affineBlock, hz, positiveIntExtension_natCast (by omega), finiteSequenceBlock, hidx]

end

end NormalNumbers.ElliottDilatedLower

#print axioms NormalNumbers.ElliottDilatedLower.norm_logProbExpectation_backtranslate_sub_le
#print axioms
  NormalNumbers.ElliottDilatedLower.norm_logProb_affineTwistedObservable_shift_sub_correlation_le
