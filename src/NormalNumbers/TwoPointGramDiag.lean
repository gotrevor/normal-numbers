import NormalNumbers.TwoPointGramFrobenius

/-!
# The diagonal of the fourth moment, computed exactly

Lap 16 wrote the off-diagonal `ℓ²` mass as `fourth moment − Σ_p ⌊N/p⌋²`.  For a unimodular
sequence `a` both the fourth moment's `m = m'` part and the subtracted term are explicit
combinatorial quantities, and this file computes them in kernel.

Write `k(m) = #{p ≤ w prime : p·m ≤ N, m ≥ 1}` (`kataiCount`).  Then, for `‖a n‖ = 1`:

* `dilationPairSum_diag` — `Σ_{p ≤ w} C_p(m) conj C_p(m) = k(m)`;
* `sum_kataiCount_sq` — `Σ_{m ≤ N} k(m)² = Σ_{p,q ≤ w} min(⌊N/p⌋, ⌊N/q⌋)`;
* `norm_csGram_self_trunc` — `‖csGram C (N+1) p p‖ = ⌊N/p⌋`;
* **`kataiPairGramSq_split`** —

      kataiPairGramSq a w N
        = ( Σ_{p,q ≤ w} min(⌊N/p⌋,⌊N/q⌋)  −  Σ_{p ≤ w} ⌊N/p⌋² )
          +  Σ_{m ≠ m' ≤ N} ‖Σ_{p ≤ w} a(pm) conj a(pm')‖² .

## The reading, and why it prices the `ℓ²` route

The first bracket is **negative and of order `−N²`**: `Σ_{p,q} min(⌊N/p⌋,⌊N/q⌋) ≍ N·M'(w)` is
linear in `N` (times a `w`-sum), while `Σ_p ⌊N/p⌋² ≍ N²Σ_{p≤w}1/p²` is quadratic.  Since
`kataiPairGramSq ≥ 0`, the off-diagonal fourth moment `Σ_{m≠m'}‖·‖²` must *itself* be of order
`N²` and must cancel the bracket to within the lap-15 demand `ε²N²L(w)⁴/π(w)²`.

That is the exact price of the `ℓ²` route: it does not ask for a bound on a small quantity, it
asks for an **asymptotic evaluation** of the off-diagonal fourth moment of the dilation family to
relative precision `L(w)⁴/π(w)² → 0`.  No known technique (MRT included) evaluates a fourth
moment of dilates to that precision; MRT-type arguments give `o(1)` savings, not `π(w)²/L(w)⁴`.
This is a concrete, kernel-grounded reason to regard the `ℓ²` route as refuted, and by lap 13 the
`ℓ¹` route is refuted too.  What survives is only a method that exploits the arithmetic of
`ω(pm+1)` directly, not Cauchy–Schwarz over the multiplier set.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- `k(m) = #{p ≤ w prime : 1 ≤ m ≤ ⌊N/p⌋}`. -/
noncomputable def kataiCount (w N m : ℕ) : ℕ :=
  ((primesLe w).filter (fun p => m ∈ Finset.Ioc 0 (N / p))).card

lemma kataiCount_eq_sum (w N m : ℕ) :
    (kataiCount w N m : ℝ)
      = ∑ p ∈ primesLe w, (if m ∈ Finset.Ioc 0 (N / p) then (1:ℝ) else 0) := by
  classical
  rw [kataiCount, ← Finset.sum_boole]

lemma dilationPairSum_diag (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ = 1) (w N m : ℕ) :
    dilationPairSum (primesLe w) (kataiTrunc a N) m m = ((kataiCount w N m : ℝ) : ℂ) := by
  classical
  rw [dilationPairSum, kataiCount_eq_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : m ∈ Finset.Ioc 0 (N / p)
  · simp only [kataiTrunc, if_pos h, if_pos h]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  · simp [kataiTrunc, h]

lemma card_Ioc_min (N p q : ℕ) :
    ((Finset.range (N + 1)).filter
      (fun m => m ∈ Finset.Ioc 0 (N / p) ∧ m ∈ Finset.Ioc 0 (N / q))).card
      = min (N / p) (N / q) := by
  classical
  have hset : (Finset.range (N + 1)).filter
      (fun m => m ∈ Finset.Ioc 0 (N / p) ∧ m ∈ Finset.Ioc 0 (N / q))
      = Finset.Ioc 0 (min (N / p) (N / q)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, le_min_iff]
    have h1 := Nat.div_le_self N p
    constructor
    · rintro ⟨_, ⟨h0, hp⟩, ⟨_, hq⟩⟩; exact ⟨h0, hp, hq⟩
    · rintro ⟨h0, hp, hq⟩; exact ⟨by omega, ⟨h0, hp⟩, ⟨h0, hq⟩⟩
  rw [hset, Nat.card_Ioc]
  simp

/-- `Σ_{m ≤ N} k(m)² = Σ_{p,q ≤ w} min(⌊N/p⌋, ⌊N/q⌋)`. -/
theorem sum_kataiCount_sq (w N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), ((kataiCount w N m : ℝ)) ^ 2
      = ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, ((min (N / p) (N / q) : ℕ) : ℝ) := by
  classical
  have hexp : ∀ m, ((kataiCount w N m : ℝ)) ^ 2
      = ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
          (if m ∈ Finset.Ioc 0 (N / p) then (1:ℝ) else 0)
            * (if m ∈ Finset.Ioc 0 (N / q) then (1:ℝ) else 0) := by
    intro m
    rw [sq, kataiCount_eq_sum, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun m _ => hexp m]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hterm : ∀ m ∈ Finset.range (N + 1),
      (if m ∈ Finset.Ioc 0 (N / p) then (1:ℝ) else 0)
        * (if m ∈ Finset.Ioc 0 (N / q) then (1:ℝ) else 0)
        = if (m ∈ Finset.Ioc 0 (N / p) ∧ m ∈ Finset.Ioc 0 (N / q)) then (1:ℝ) else 0 := by
    intro m _
    by_cases h1 : m ∈ Finset.Ioc 0 (N / p) <;> by_cases h2 : m ∈ Finset.Ioc 0 (N / q) <;>
      simp [h1, h2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole, card_Ioc_min N p q]

lemma card_filter_Ioc (N p : ℕ) :
    ((Finset.range (N + 1)).filter (fun m => m ∈ Finset.Ioc 0 (N / p))).card = N / p := by
  classical
  have hset : (Finset.range (N + 1)).filter (fun m => m ∈ Finset.Ioc 0 (N / p))
      = Finset.Ioc 0 (N / p) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    have := Nat.div_le_self N p
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro ⟨h0, hp⟩; exact ⟨by omega, h0, hp⟩
  rw [hset, Nat.card_Ioc]
  simp

lemma norm_csGram_self_trunc (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ = 1) (N p : ℕ) :
    ‖csGram (kataiTrunc a N) (N + 1) p p‖ = ((N / p : ℕ) : ℝ) := by
  classical
  rw [norm_csGram_self]
  have hterm : ∀ m ∈ Finset.range (N + 1), ‖kataiTrunc a N p m‖ ^ 2
      = if m ∈ Finset.Ioc 0 (N / p) then (1:ℝ) else 0 := by
    intro m _
    by_cases h : m ∈ Finset.Ioc 0 (N / p)
    · simp [kataiTrunc, h, ha]
    · simp [kataiTrunc, h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole, card_filter_Ioc N p]

/-- **THE `ℓ²` MASS, SPLIT EXACTLY.** -/
theorem kataiPairGramSq_split (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ = 1) (w N : ℕ) :
    kataiPairGramSq a w N
      = (∑ p ∈ primesLe w, ∑ q ∈ primesLe w, ((min (N / p) (N / q) : ℕ) : ℝ)
          - ∑ p ∈ primesLe w, ((N / p : ℕ) : ℝ) ^ 2)
        + ∑ m ∈ Finset.range (N + 1), ∑ m' ∈ Finset.range (N + 1),
            (if m = m' then 0
              else ‖dilationPairSum (primesLe w) (kataiTrunc a N) m m'‖ ^ 2) := by
  classical
  rw [kataiPairGramSq_eq]
  have hdiag : ∑ m ∈ Finset.range (N + 1), ∑ m' ∈ Finset.range (N + 1),
      ‖dilationPairSum (primesLe w) (kataiTrunc a N) m m'‖ ^ 2
      = (∑ m ∈ Finset.range (N + 1), ((kataiCount w N m : ℝ)) ^ 2)
        + ∑ m ∈ Finset.range (N + 1), ∑ m' ∈ Finset.range (N + 1),
            (if m = m' then 0
              else ‖dilationPairSum (primesLe w) (kataiTrunc a N) m m'‖ ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have h : ∀ m' ∈ Finset.range (N + 1),
        ‖dilationPairSum (primesLe w) (kataiTrunc a N) m m'‖ ^ 2
          = (if m = m' then ((kataiCount w N m : ℝ)) ^ 2 else 0)
            + (if m = m' then 0
                else ‖dilationPairSum (primesLe w) (kataiTrunc a N) m m'‖ ^ 2) := by
      intro m' _
      by_cases h : m = m'
      · subst h
        rw [dilationPairSum_diag a ha]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ ((kataiCount w N m : ℕ) : ℝ))]
        simp
      · simp [h]
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib,
      Finset.sum_ite_eq (Finset.range (N + 1)) m (fun _ => ((kataiCount w N m : ℝ)) ^ 2)]
    simp [hm]
  rw [hdiag, sum_kataiCount_sq]
  have hself : ∑ p ∈ primesLe w, ‖csGram (kataiTrunc a N) (N + 1) p p‖ ^ 2
      = ∑ p ∈ primesLe w, ((N / p : ℕ) : ℝ) ^ 2 :=
    Finset.sum_congr rfl fun p _ => by rw [norm_csGram_self_trunc a ha]
  rw [hself]
  ring

end NormalNumbers.CastingOut
