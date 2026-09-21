import NormalNumbers.PrimeLambertMoments

/-!
# The CRT factorization of the independent model's characteristic function

`IndepCharDecay C` (draft (13)+(15)) asks that `‖indepAvg C N e(q·)‖ → 0`, where `indepAvg` is the
average of `e(q S_N(r))` over a uniform residue `r` modulo `∏_{p small} p`.  The draft proves this
by *factorizing*: since `S_N = ∑_{p small} X_p` and `X_p` is `p`-periodic, the Chinese Remainder
Theorem makes the `X_p` independent under a uniform residue, so

  `indepAvg e(q·) = ∏_{p small} localChar p`,   `localChar p = (1/p) ∑_{u<p} e(q X_p(u))`,

and each local factor is a `p`-average of a phase, bounded away from `1` in modulus whenever `X_p`
is non-constant mod `p`.  `IndepCharDecay` is then a divergence statement for `∑_p (1 − ‖localChar p‖)`
— a Mertens-type sum — rather than anything about the arithmetic sample.

This file supplies the factorization and the wiring from it to `IndepCharDecay`.  The pointwise
Euler-product identity `e(q S_N(n)) = ∏_p e(q X_p(n))` is exact and proved here; the CRT step
(`indepAvg_e_eq_prod`) is the one genuinely combinatorial ingredient.
-/

open Filter Topology Finset Complex
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

lemma e_zero : e 0 = 1 := by unfold e; simp

/-- `e` turns finite sums into finite products. -/
lemma e_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    e (∑ i ∈ s, f i) = ∏ i ∈ s, e (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [e_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, e_mul, ih]

/-- The local factor at a small prime `p`: the average of `e(q X_p)` over one residue period. -/
noncomputable def localChar {q : ℤ} (C : Chain q) (N : ℕ) (p : ℕ) : ℂ :=
  avg (range p) (fun u : ℕ => e (q * primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ)))

/-- **Exact Euler product, pointwise**: the small-prime phase is the product of its local phases. -/
theorem e_smallSum_eq_prod {q : ℤ} (C : Chain q) (N : ℕ) (n : ℤ) :
    e (q * smallSum C N n)
      = ∏ p ∈ (C.S N).small, e (q * primePart (C.c N) (C.K N) (C.S N).J p n) := by
  unfold smallSum classSum
  rw [Finset.mul_sum, e_sum]

/-- **CRT factorization of the independent model.**  Under a uniform residue modulo
`∏_{p small} p` the local variables `X_p` are independent, so the characteristic function is the
product of the local ones.  This is draft §5.3's "independent model" statement, made exact.

Disclosed `sorry`: the Chinese-Remainder reindexing of `range (∏ p)` as `∏_p range p`. -/
theorem indepAvg_e_eq_prod {q : ℤ} (C : Chain q) (N : ℕ) :
    indepAvg C N (fun x => e (q * x)) = ∏ p ∈ (C.S N).small, localChar C N p := by
  sorry

/-- Consequently the modulus of the independent characteristic function is the product of the
moduli of the local factors. -/
theorem norm_indepAvg_e_eq_prod {q : ℤ} (C : Chain q) (N : ℕ) :
    ‖indepAvg C N (fun x => e (q * x))‖ = ∏ p ∈ (C.S N).small, ‖localChar C N p‖ := by
  rw [indepAvg_e_eq_prod, norm_prod]

/-- **Wiring**: `IndepCharDecay` is exactly a statement about the local factors — no reference to
the arithmetic sample survives. -/
theorem indepCharDecay_of_localChar {q : ℤ} (C : Chain q)
    (h : Tendsto (fun N => ∏ p ∈ (C.S N).small, ‖localChar C N p‖) atTop (𝓝 0)) :
    IndepCharDecay C := by
  refine h.congr (fun N => ?_)
  rw [norm_indepAvg_e_eq_prod]

/-- Each local factor has modulus at most `1`. -/
theorem norm_localChar_le_one {q : ℤ} (C : Chain q) (N : ℕ) {p : ℕ} (hp : 0 < p) :
    ‖localChar C N p‖ ≤ 1 := by
  unfold localChar avg
  rw [norm_div, Complex.norm_natCast, Finset.card_range]
  have hpr : (0:ℝ) < p := by exact_mod_cast hp
  rw [div_le_one hpr]
  calc ‖∑ u ∈ range p, e (q * primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ))‖
      ≤ ∑ u ∈ range p, ‖e (q * primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ))‖ := norm_sum_le _ _
    _ = p := by
        rw [Finset.sum_congr rfl (fun u _ => norm_e _), Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]

end NormalNumbers.PrimeLambert
