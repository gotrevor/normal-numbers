import NormalNumbers.TwoPointGramL2

/-!
# The fourth-moment identity for the dilation family

The `ℓ²` route of lap 15 needs the Frobenius norm of the Gram matrix.  This file proves the
identity that converts it into a fourth moment of the dilation family — the object any
large-sieve or entropy-decrement input would actually bound:

    Σ_{p,q ∈ A} ‖Σ_m C_p(m) conj C_q(m)‖²  =  Σ_{m,m'} ‖Σ_{p ∈ A} C_p(m) conj C_p(m')‖² .

Left: correlations between two dilates, summed over pairs of multipliers.
Right: for each pair of *points* `(m, m')`, the superposition over the multiplier set, squared —
a genuine fourth moment of the family `{n ↦ a(pn)}_{p ≤ w}`.

Both sides are the squared Frobenius norm of the same matrix, read by rows and by columns; the
proof is a four-fold interchange plus `z conj z = ‖z‖²`.

For the leaf this says: bounding the `ℓ²` mass is exactly bounding, on average over `(m,m')`, the
cancellation in `Σ_{p ≤ w} a(pm) conj a(pm')` — i.e. equidistribution of the dilation orbit of the
pair `(m,m')`, which is the shape an MRT-style argument produces.  `kataiPairGramSq` is this
quantity minus its `p = q` diagonal, and the diagonal is `Σ_p (Σ_m ‖C_p(m)‖²)²`.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

lemma sum4_comm (A B : Finset ℕ) (T : ℕ → ℕ → ℕ → ℕ → ℂ) :
    ∑ p ∈ A, ∑ q ∈ A, ∑ m ∈ B, ∑ m' ∈ B, T p q m m'
      = ∑ m ∈ B, ∑ m' ∈ B, ∑ p ∈ A, ∑ q ∈ A, T p q m m' := by
  calc ∑ p ∈ A, ∑ q ∈ A, ∑ m ∈ B, ∑ m' ∈ B, T p q m m'
      = ∑ p ∈ A, ∑ m ∈ B, ∑ q ∈ A, ∑ m' ∈ B, T p q m m' :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ m ∈ B, ∑ p ∈ A, ∑ q ∈ A, ∑ m' ∈ B, T p q m m' := Finset.sum_comm
    _ = ∑ m ∈ B, ∑ p ∈ A, ∑ m' ∈ B, ∑ q ∈ A, T p q m m' :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ m ∈ B, ∑ m' ∈ B, ∑ p ∈ A, ∑ q ∈ A, T p q m m' :=
        Finset.sum_congr rfl fun m _ => Finset.sum_comm

lemma normSq_cast (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The superposition of the dilation family at the pair of points `(m, m')`. -/
noncomputable def dilationPairSum (A : Finset ℕ) (C : ℕ → ℕ → ℂ) (m m' : ℕ) : ℂ :=
  ∑ p ∈ A, C p m * (starRingEnd ℂ) (C p m')

/-- **THE FOURTH-MOMENT IDENTITY.**  Gram mass read by multiplier pairs = read by point pairs. -/
theorem gram_frobenius (A : Finset ℕ) (N : ℕ) (C : ℕ → ℕ → ℂ) :
    ∑ p ∈ A, ∑ q ∈ A, ‖csGram C N p q‖ ^ 2
      = ∑ m ∈ Finset.range N, ∑ m' ∈ Finset.range N, ‖dilationPairSum A C m m'‖ ^ 2 := by
  classical
  have hcast : ((∑ p ∈ A, ∑ q ∈ A, ‖csGram C N p q‖ ^ 2 : ℝ) : ℂ)
      = ((∑ m ∈ Finset.range N, ∑ m' ∈ Finset.range N,
          ‖dilationPairSum A C m m'‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    have hL : ∀ p ∈ A, ∀ q ∈ A, ((‖csGram C N p q‖ ^ 2 : ℝ) : ℂ)
        = ∑ m ∈ Finset.range N, ∑ m' ∈ Finset.range N,
            (C p m * (starRingEnd ℂ) (C q m)) *
              ((starRingEnd ℂ) (C p m') * C q m') := by
      intro p _ q _
      rw [normSq_cast, csGram, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
      rw [map_mul, Complex.conj_conj]
    have hR : ∀ m ∈ Finset.range N, ∀ m' ∈ Finset.range N,
        ((‖dilationPairSum A C m m'‖ ^ 2 : ℝ) : ℂ)
          = ∑ p ∈ A, ∑ q ∈ A, (C p m * (starRingEnd ℂ) (C p m')) *
              ((starRingEnd ℂ) (C q m) * C q m') := by
      intro m _ m' _
      rw [normSq_cast, dilationPairSum, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [map_mul, Complex.conj_conj]
    have hLL : (∑ p ∈ A, ∑ q ∈ A, ((‖csGram C N p q‖ ^ 2 : ℝ) : ℂ))
        = ∑ p ∈ A, ∑ q ∈ A, ∑ m ∈ Finset.range N, ∑ m' ∈ Finset.range N,
            (C p m * (starRingEnd ℂ) (C q m)) *
              ((starRingEnd ℂ) (C p m') * C q m') :=
      Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => hL p hp q hq
    have hRR : (∑ m ∈ Finset.range N, ∑ m' ∈ Finset.range N,
          ((‖dilationPairSum A C m m'‖ ^ 2 : ℝ) : ℂ))
        = ∑ m ∈ Finset.range N, ∑ m' ∈ Finset.range N, ∑ p ∈ A, ∑ q ∈ A,
            (C p m * (starRingEnd ℂ) (C p m')) *
              ((starRingEnd ℂ) (C q m) * C q m') :=
      Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun m' hm' => hR m hm m' hm'
    have hswap := sum4_comm A (Finset.range N)
      (fun p q m m' => (C p m * (starRingEnd ℂ) (C q m)) *
        ((starRingEnd ℂ) (C p m') * C q m'))
    push_cast at hLL hRR
    rw [hLL, hRR, hswap]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ =>
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  exact_mod_cast hcast

/-- The `ℓ²` mass of the off-diagonal Gram matrix, via the fourth moment. -/
theorem kataiPairGramSq_eq (a : ℕ → ℂ) (w N : ℕ) :
    kataiPairGramSq a w N
      = (∑ m ∈ Finset.range (N + 1), ∑ m' ∈ Finset.range (N + 1),
          ‖dilationPairSum (primesLe w) (kataiTrunc a N) m m'‖ ^ 2)
        - ∑ p ∈ primesLe w, ‖csGram (kataiTrunc a N) (N + 1) p p‖ ^ 2 := by
  classical
  rw [← gram_frobenius (primesLe w) (N + 1) (kataiTrunc a N)]
  rw [kataiPairGramSq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have h : ∀ q ∈ primesLe w,
      (if p = q then (0:ℝ) else ‖csGram (kataiTrunc a N) (N + 1) p q‖ ^ 2)
        = ‖csGram (kataiTrunc a N) (N + 1) p q‖ ^ 2
          - (if p = q then ‖csGram (kataiTrunc a N) (N + 1) p q‖ ^ 2 else 0) := by
    intro q _
    by_cases hq : p = q <;> simp [hq]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib,
    Finset.sum_ite_eq (primesLe w) p
      (fun q => ‖csGram (kataiTrunc a N) (N + 1) p q‖ ^ 2)]
  simp [hp]

end NormalNumbers.CastingOut
