/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropySample

/-!
# Entropy expedition §6: the sample is DIGIT-LOCAL

This is the first half of the attack on the brief's primary transfer target `T_E`
(*`E0` for `Z^x_K` implies `IsNormal 2 x`, for every `x`*).

`G4EntropySample.ZSample_eq_blockVal` says `Z^x_{K,α}(n)` is the `m`-bit binary window of `x`
beginning at position `2·kIdx G n α`.  A window only reads finitely many digits, so the whole
entropy statement is a function of the digits of `x` on the **sampled position set**

  `sampledPos G X m = {2·kIdx G n α + h : n ∈ P, α : Atom, h < m}`.

Concretely: `sampledPos_congr` ⟹ `ZSample_congr` ⟹ `ZVec_congr` ⟹ `jointLaw_congr` ⟹
`H₂_jointLaw_congr`.  Two reals agreeing on `sampledPos` have *literally the same joint law*,
hence the same entropy, hence satisfy exactly the same entropy hypotheses.

That is what makes `T_E` a statement about the *density* of `sampledPos`: a transfer theorem
from a digit-local hypothesis to normality forces the sampled positions to be at least half of
all positions.  `G4EntropyPositions` shows they are astronomically sparser than that.

Nothing here is specific to `G₄`, to the schedule, or even to the grid's side conditions: it
is the bookkeeping that the sample reads only the digits it reads.
-/

open Finset

namespace NormalNumbers.G4Entropy

open NormalNumbers.G4

/-! ### Windows read only their own digits -/

/-- A binary window is a function of the digits inside it. -/
lemma blockVal_congr {x y : ℝ} {j m : ℕ}
    (h : ∀ i < m, digitOf 2 x (j + i) = digitOf 2 y (j + i)) :
    blockVal x j m = blockVal y j m := by
  unfold blockVal
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

/-! ### The sampled position set -/

variable (G : GridParams)

/-- **The sampled positions** at scale `(X, m)`: the digit positions the quantized sample
`Z` actually reads.  Each sample point `n ∈ P` and atom `α` contribute the window
`[2·kIdx G n α, 2·kIdx G n α + m)`. -/
noncomputable def sampledPos (X m : ℕ) : Finset ℕ := by
  classical
  exact ((apSample X G.P₀ G.b₀) ×ˢ (Finset.univ : Finset G.Atom) ×ˢ Finset.range m).image
    (fun z => 2 * kIdx G z.1 z.2.1 + z.2.2)

lemma mem_sampledPos {X m j : ℕ} :
    j ∈ sampledPos G X m ↔
      ∃ n ∈ apSample X G.P₀ G.b₀, ∃ α : G.Atom, ∃ h < m, j = 2 * kIdx G n α + h := by
  classical
  unfold sampledPos
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, Finset.mem_range,
    true_and, Prod.exists]
  constructor
  · rintro ⟨n, α, h, ⟨hn, hh⟩, rfl⟩
    exact ⟨n, hn, α, h, hh, rfl⟩
  · rintro ⟨n, hn, α, h, hh, rfl⟩
    exact ⟨n, α, h, ⟨hn, hh⟩, rfl⟩

lemma mem_sampledPos_of {X m n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀) (α : G.Atom) {h : ℕ}
    (hh : h < m) : 2 * kIdx G n α + h ∈ sampledPos G X m :=
  (mem_sampledPos G).2 ⟨n, hn, α, h, hh, rfl⟩

/-! ### Locality of the sample, the joint law and its entropy -/

/-- **Digit locality of one coordinate.** -/
theorem ZSample_congr {X m n : ℕ} {x y : ℝ} (α : G.Atom)
    (hn : n ∈ apSample X G.P₀ G.b₀)
    (hd : ∀ j ∈ sampledPos G X m, digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) :
    ZSample G m x n α = ZSample G m y n α := by
  rw [ZSample_eq_blockVal, ZSample_eq_blockVal]
  exact blockVal_congr fun i hi => hd _ (mem_sampledPos_of G hn α hi)

/-- **Digit locality of the joint vector.** -/
theorem ZVec_congr {X m n : ℕ} {x y : ℝ} (hn : n ∈ apSample X G.P₀ G.b₀)
    (hd : ∀ j ∈ sampledPos G X m, digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) :
    ZVec G m x n = ZVec G m y n := by
  funext α
  exact Fin.ext (ZSample_congr G α hn hd)

/-- A finite law is determined by its mass function (the other fields are proofs). -/
lemma FinLaw.ext' {Ω : Type*} [Fintype Ω] {L₁ L₂ : FinLaw Ω} (h : L₁.p = L₂.p) : L₁ = L₂ := by
  cases L₁ with
  | mk p₁ n₁ s₁ =>
    cases L₂ with
    | mk p₂ n₂ s₂ =>
      simp only at h
      subst h
      rfl

/-- An empirical law only sees the values of its statistic on the sample. -/
theorem empirical_congr {ι Ω : Type*} [Fintype Ω] {S : Finset ι} (hS : S.Nonempty)
    {f g : ι → Ω} (h : ∀ i ∈ S, f i = g i) :
    empirical S hS f = empirical S hS g := by
  classical
  refine FinLaw.ext' ?_
  funext ω
  have hfil : (S.filter fun i => f i = ω) = (S.filter fun i => g i = ω) :=
    Finset.filter_congr fun i hi => by rw [h i hi]
  simp only [empirical_p, hfil]

/-- **Digit locality of the joint law**: two reals whose digits agree on `sampledPos` have
literally the same joint quantized sample law. -/
theorem jointLaw_congr {X : ℕ} (hX : G.b₀ < X) (m : ℕ) {x y : ℝ}
    (hd : ∀ j ∈ sampledPos G X m, digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) :
    jointLaw G hX m x = jointLaw G hX m y :=
  empirical_congr _ fun n hn => ZVec_congr G hn hd

/-- **Digit locality of the sample entropy** — the statement the transfer question turns on:
`H₂(Z^x_K)` depends on `x` only through the digits of `x` at the sampled positions. -/
theorem H₂_jointLaw_congr {X : ℕ} (hX : G.b₀ < X) (m : ℕ) {x y : ℝ}
    (hd : ∀ j ∈ sampledPos G X m, digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) :
    (jointLaw G hX m x).H₂ = (jointLaw G hX m y).H₂ := by
  rw [jointLaw_congr G hX m hd]

end NormalNumbers.G4Entropy
