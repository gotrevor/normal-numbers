import NormalNumbers.ElliottDilatedMean

/-!
# Grouping the alphabet: the dilated block is an ordinary block over `α^a`

Step (iii)(a) of the dilated crux assembly, and the concrete form of lap 28's structural finding.

`NormalNumbers.ElliottGenericGraph.exists_logProb_gen_decoupling` reads its data as
`finiteSequenceBlock F m n` for a sequence `F : ℕ → α` over a **finite** alphabet, at the
**ordinary** base point `n`, and produces a graph of length `a * m`.  The dilated graph instead
wants `NormalNumbers.ElliottDilatedPairing.affineBlock f a n (a*m)`, the block of `f` over
`[a(n+1), a(n+1) + a m)`.  Lap 28 predicted that grouping the alphabet in blocks of `a` makes these
the same object.  This file proves it:

```
ungroupBlock (finiteSequenceBlock (groupSeq a f) m n) = affineBlock f a n (a * m)
```

with `groupSeq a f k i = f (a k + i)` and `ungroupBlock b j = b ⌊j/a⌋ (j mod a)`.  The verification
is the division identity `a·(n + j/a + 1) + j mod a = a(n+1) + j`.

Consequently the entropy/rare-event layer never has to be re-proved at a dilated base point: it is
applied verbatim to the sequence `groupSeq a f` over the alphabet `(Fin a → ·)`, which is still
finite whenever the value alphabet is.

Also here: the perturbation estimates needed to remove the finite-alphabet restriction later
(`norm_ungroupBlock_sub_le`, `norm_dilatedEdgeReindexed_sub_le`), with the dependency's constant
`2Bζ` — the dilated edge splits exactly as the pure-shift one does.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottDilatedGrouped

open Erdos67b
open NormalNumbers.ElliottDilatedPairing
open NormalNumbers.ElliottDilatedBridge

noncomputable section

/-! ## The grouped sequence and the ungrouping of its blocks -/

/-- The sequence `f`, read in consecutive groups of `a`: `groupSeq a f k i = f (a k + i)`.
Its alphabet is `Fin a → ℂ`, and — the point — it is indexed by the *ordinary* position `k`. -/
def groupSeq (a : ℕ) (f : ℕ → ℂ) : ℕ → (Fin a → ℂ) :=
  fun k i ↦ positiveIntExtension f (((a * k : ℕ) : ℤ) + (i.1 : ℤ))

/-- The inverse of the grouping, on blocks: a block of `m` groups of `a` is a block of `a*m`
values. -/
def ungroupBlock {a m : ℕ} (b : Fin m → (Fin a → ℂ)) : Fin (a * m) → ℂ :=
  fun j ↦ b ⟨j.1 / a, Nat.div_lt_of_lt_mul j.2⟩
    ⟨j.1 % a, Nat.mod_lt _ (by
      rcases Nat.eq_zero_or_pos a with h | h
      · exact absurd j.2 (by simp [h])
      · exact h)⟩

/-- **Lap 28, in the kernel.**  The `a`-dilated block at base point `n` is the ungrouping of the
*ordinary* block, of the *grouped* sequence, at the *ordinary* base point `n`.

No positivity hypothesis on `a` is needed: at `a = 0` both sides are functions out of the empty
type `Fin 0`. -/
theorem ungroupBlock_finiteSequenceBlock_groupSeq (f : ℕ → ℂ) (a m n : ℕ) :
    ungroupBlock (finiteSequenceBlock (groupSeq a f) m n) = affineBlock f a n (a * m) := by
  funext j
  have hdiv : a * (j.1 / a) + j.1 % a = j.1 := Nat.div_add_mod j.1 a
  have hidx : ((a * (n + j.1 / a + 1) : ℕ) : ℤ) + ((j.1 % a : ℕ) : ℤ) =
      ((a * (n + 1) : ℕ) : ℤ) + (j.1 : ℤ) := by
    have : (a * (n + j.1 / a + 1) : ℕ) + (j.1 % a) = (a * (n + 1) : ℕ) + j.1 := by
      have hexp : a * (n + j.1 / a + 1) = a * (n + 1) + a * (j.1 / a) := by ring
      omega
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) this
  simp only [ungroupBlock, finiteSequenceBlock, groupSeq, affineBlock]
  rw [hidx]

/-- The grouped sequence of a `1`-bounded function is `1`-bounded componentwise. -/
theorem norm_groupSeq_le {f : ℕ → ℂ} (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) (a k : ℕ) (i : Fin a) :
    ‖groupSeq a f k i‖ ≤ 1 :=
  norm_positiveIntExtension_le_one hf _

/-! ## Perturbation estimates for the dilated edge

These are the dilated analogues of `NormalNumbers.ElliottTwistedGraph.norm_pairShiftEdge_sub_le`,
and they come out with the dependency's constant `2Bζ`: the dilated edge is still a product of two
block values, and `b j c k − b' j c' k = (b j − b' j) c k + b' j (c k − c' k)`.
-/

theorem norm_ungroupBlock_sub_le {a m : ℕ} (b b' : Fin m → (Fin a → ℂ)) {ζ : ℝ}
    (hclose : ∀ i j, ‖b i j - b' i j‖ ≤ ζ) (j : Fin (a * m)) :
    ‖ungroupBlock b j - ungroupBlock b' j‖ ≤ ζ := by
  simp only [ungroupBlock]
  exact hclose _ _

theorem norm_blockExtend_sub_le {H : ℕ} (b b' : Fin H → ℂ) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (hclose : ∀ j, ‖b j - b' j‖ ≤ ζ) (i : ℕ) :
    ‖blockExtend b i - blockExtend b' i‖ ≤ ζ := by
  unfold blockExtend
  split_ifs with hi
  · exact hclose _
  · simpa using hζ

/-- **The dilated edge perturbation estimate**, with the dependency's constant. -/
theorem norm_dilatedEdgeReindexed_sub_le {H : ℕ} (b c b' c' : Fin H → ℂ)
    {B ζ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ)
    (hc : ∀ j, ‖c j‖ ≤ B) (hb' : ∀ j, ‖b' j‖ ≤ B)
    (hbclose : ∀ j, ‖b j - b' j‖ ≤ ζ) (hcclose : ∀ j, ‖c j - c' j‖ ≤ ζ)
    (α c₁ h p : ℕ) (j : Fin H) :
    ‖dilatedEdgeReindexed b c α c₁ h p j - dilatedEdgeReindexed b' c' α c₁ h p j‖ ≤
      2 * B * ζ := by
  unfold dilatedEdgeReindexed
  set u := α * j.1 + p * c₁ % α with hu
  set v := α * j.1 + p * c₁ % α + p * h with hv
  have hid : blockExtend b u * blockExtend c v - blockExtend b' u * blockExtend c' v =
      (blockExtend b u - blockExtend b' u) * blockExtend c v +
        blockExtend b' u * (blockExtend c v - blockExtend c' v) := by ring
  rw [hid]
  have hleft : ‖(blockExtend b u - blockExtend b' u) * blockExtend c v‖ ≤ ζ * B := by
    rw [norm_mul]
    exact mul_le_mul (norm_blockExtend_sub_le b b' hζ hbclose u)
      (norm_blockExtend_le hB hc v) (norm_nonneg _) hζ
  have hright : ‖blockExtend b' u * (blockExtend c v - blockExtend c' v)‖ ≤ B * ζ := by
    rw [norm_mul]
    exact mul_le_mul (norm_blockExtend_le hB hb' u)
      (norm_blockExtend_sub_le c c' hζ hcclose v) (norm_nonneg _) hB
  exact (norm_add_le _ _).trans (by linarith)

end

end NormalNumbers.ElliottDilatedGrouped

#print axioms NormalNumbers.ElliottDilatedGrouped.ungroupBlock_finiteSequenceBlock_groupSeq
#print axioms NormalNumbers.ElliottDilatedGrouped.norm_dilatedEdgeReindexed_sub_le
