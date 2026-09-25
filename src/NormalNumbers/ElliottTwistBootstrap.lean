import NormalNumbers.ElliottZetaOmegaPretentious

/-!
# The power bootstrap: killing the character in `TwistModulusDichotomy`

Attack step (b) on the crux `ElliottZetaOmegaPretentious.TwistModulusDichotomy`.

The dichotomy's hard alternative says `‖C‖ ≤ (1−δ)M`.  Suppose it fails.  Then, with
`β := C/‖C‖` unimodular, the *defect*

  `Δ(β) := ∑_{p≤X} (1 − Re(β̄ · w_p))/p`,   `w_p = conj(χ(p) p^{it})`,

satisfies `Δ(β) = M − ‖C‖ ≤ δM`: the twist values cluster around the single constant `β`.
This file proves that clustering **propagates to powers**:

  `Δ_k(β^k) ≤ k · √(2 · Δ(β) · M)`   (`twistDefect_pow_le`),

where `Δ_k` is the same defect for `p ↦ w_p^k`.  So if `δ` is small the `k`-th power twist
`conj(χ^k(p) p^{ikt})` is *also* clustered, at cost only `k√(2δ)` instead of `δ`.

Taking `k` to be the order of `χ` makes `χ^k` principal, so the clustered object is purely
Archimedean: `∑_{p≤X} p^{-ikt}/p ≈ β^k M`.  That is attack step (c), the zero-free-region input,
and the only remaining piece.

The proof is three elementary inequalities plus Cauchy–Schwarz:
`1 − Re z ≤ ‖1 − z‖`, `‖1 − b^k‖ ≤ k‖1 − b‖` (geometric factorisation), and
`‖1 − b‖² ≤ 2(1 − Re b)` for `‖b‖ ≤ 1`.
-/

open Finset

namespace NormalNumbers.ElliottTwistBootstrap

open Erdos67b NormalNumbers.ElliottZetaOmegaPretentious

noncomputable section

/-- The defect of a family of twist values `w` against a single constant `β`. -/
def twistDefect (w : ℕ → ℂ) (β : ℂ) (X : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo X, (1 - ((starRingEnd ℂ) β * w p).re) / (p : ℝ)

/-! ### The three elementary inequalities -/

theorem one_sub_re_le_norm (z : ℂ) : 1 - z.re ≤ ‖1 - z‖ := by
  have : (1 - z).re ≤ ‖1 - z‖ := Complex.re_le_norm _
  simpa using this

/-- `‖1 − b^k‖ ≤ k‖1 − b‖` for `‖b‖ ≤ 1`, by the geometric factorisation. -/
theorem norm_one_sub_pow_le {b : ℂ} (hb : ‖b‖ ≤ 1) (k : ℕ) :
    ‖1 - b ^ k‖ ≤ k * ‖1 - b‖ := by
  have hfac : 1 - b ^ k = (1 - b) * ∑ i ∈ Finset.range k, b ^ i := by
    have := geom_sum_mul b k
    have h2 : (∑ i ∈ Finset.range k, b ^ i) * (b - 1) = b ^ k - 1 := this
    have : (1 - b) * ∑ i ∈ Finset.range k, b ^ i = -((∑ i ∈ Finset.range k, b ^ i) * (b - 1)) := by
      ring
    rw [this, h2]
    ring
  rw [hfac, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range k, b ^ i‖ ≤ (k : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∀ i ∈ Finset.range k, ‖b ^ i‖ ≤ 1 := by
      intro i _
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg b) hb
    simpa using Finset.sum_le_sum this
  calc ‖1 - b‖ * ‖∑ i ∈ Finset.range k, b ^ i‖ ≤ ‖1 - b‖ * (k : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = (k : ℝ) * ‖1 - b‖ := by ring

/-- `‖1 − b‖² ≤ 2(1 − Re b)` for `‖b‖ ≤ 1`. -/
theorem norm_one_sub_sq_le {b : ℂ} (hb : ‖b‖ ≤ 1) :
    ‖1 - b‖ ^ 2 ≤ 2 * (1 - b.re) := by
  have hnormsq : ‖1 - b‖ ^ 2 = 1 - 2 * b.re + (b.re ^ 2 + b.im ^ 2) := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hbsq : b.re ^ 2 + b.im ^ 2 ≤ 1 := by
    have hb2 : ‖b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg b]
    rw [← Complex.normSq_eq_norm_sq] at hb2
    simpa [Complex.normSq_apply, sq] using hb2
  rw [hnormsq]
  linarith

/-- The combined pointwise bound: `1 − Re(b^k) ≤ k·√(2(1 − Re b))` for `‖b‖ ≤ 1`. -/
theorem one_sub_re_pow_le {b : ℂ} (hb : ‖b‖ ≤ 1) (k : ℕ) :
    1 - (b ^ k).re ≤ (k : ℝ) * Real.sqrt (2 * (1 - b.re)) := by
  have h1 : 1 - (b ^ k).re ≤ ‖1 - b ^ k‖ := one_sub_re_le_norm _
  have h2 : ‖1 - b ^ k‖ ≤ (k : ℝ) * ‖1 - b‖ := norm_one_sub_pow_le hb k
  have h3 : ‖1 - b‖ ≤ Real.sqrt (2 * (1 - b.re)) := by
    have hmono := Real.sqrt_le_sqrt (norm_one_sub_sq_le hb)
    rwa [Real.sqrt_sq (norm_nonneg _)] at hmono
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  calc 1 - (b ^ k).re ≤ (k : ℝ) * ‖1 - b‖ := le_trans h1 h2
    _ ≤ (k : ℝ) * Real.sqrt (2 * (1 - b.re)) := by gcongr

/-! ### The bootstrap -/

theorem twistDefect_nonneg {w : ℕ → ℂ} {β : ℂ} (hw : ∀ p, ‖w p‖ ≤ 1) (hβ : ‖β‖ ≤ 1) (X : ℕ) :
    0 ≤ twistDefect w β X := by
  refine Finset.sum_nonneg ?_
  intro p hp
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (mem_primesUpTo.mp hp).1.pos
  have hnorm : ‖(starRingEnd ℂ) β * w p‖ ≤ 1 := by
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_one₀ hβ (norm_nonneg _) (hw p)
  have : ((starRingEnd ℂ) β * w p).re ≤ 1 :=
    le_trans (Complex.re_le_norm _) hnorm
  have hnum : 0 ≤ 1 - ((starRingEnd ℂ) β * w p).re := by linarith
  positivity

/-- **The power bootstrap.**  Clustering around `β` propagates to the `k`-th powers, at the
cost of one square root.  `‖w p‖ ≤ 1` is all that is needed; `β` is unimodular. -/
theorem twistDefect_pow_le {w : ℕ → ℂ} {β : ℂ} (hw : ∀ p, ‖w p‖ ≤ 1) (hβ : ‖β‖ = 1)
    (k : ℕ) (X : ℕ) :
    twistDefect (fun p => w p ^ k) (β ^ k) X ≤
      (k : ℝ) * Real.sqrt (2 * twistDefect w β X * primeMass X) := by
  classical
  set b : ℕ → ℂ := fun p => (starRingEnd ℂ) β * w p with hb
  have hbnorm : ∀ p, ‖b p‖ ≤ 1 := by
    intro p
    rw [hb, norm_mul, RCLike.norm_conj, hβ, one_mul]
    exact hw p
  -- rewrite both defects in terms of `b`
  have hrw : ∀ p, ((starRingEnd ℂ) (β ^ k) * w p ^ k) = b p ^ k := by
    intro p
    rw [hb, map_pow, mul_pow]
  have hstep : twistDefect (fun p => w p ^ k) (β ^ k) X
      ≤ ∑ p ∈ primesUpTo X, (k : ℝ) * Real.sqrt (2 * (1 - (b p).re)) / (p : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hpR : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (mem_primesUpTo.mp hp).1.pos
    have := one_sub_re_pow_le (hbnorm p) k
    rw [hrw p]
    gcongr
  refine le_trans hstep ?_
  -- Cauchy–Schwarz
  set a : ℕ → ℝ := fun p => 1 - (b p).re with ha
  have hanonneg : ∀ p ∈ primesUpTo X, 0 ≤ a p := by
    intro p _
    have : (b p).re ≤ 1 := le_trans (Complex.re_le_norm _) (hbnorm p)
    rw [ha]; linarith
  have hCS : (∑ p ∈ primesUpTo X, Real.sqrt (a p) / (p : ℝ)) ^ 2 ≤
      twistDefect w β X * primeMass X := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (primesUpTo X)
      (fun p => Real.sqrt (a p) / Real.sqrt (p : ℝ)) (fun p => 1 / Real.sqrt (p : ℝ))
    have heq1 : ∀ p ∈ primesUpTo X,
        Real.sqrt (a p) / Real.sqrt (p : ℝ) * (1 / Real.sqrt (p : ℝ))
          = Real.sqrt (a p) / (p : ℝ) := by
      intro p hp
      have hpR : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (mem_primesUpTo.mp hp).1.pos
      have hs : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := Real.mul_self_sqrt hpR.le
      rw [div_mul_div_comm, mul_one, hs]
    have heq2 : ∀ p ∈ primesUpTo X,
        (Real.sqrt (a p) / Real.sqrt (p : ℝ)) ^ 2 = a p / (p : ℝ) := by
      intro p hp
      have hpR : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (mem_primesUpTo.mp hp).1.pos
      rw [div_pow, Real.sq_sqrt (hanonneg p hp), Real.sq_sqrt hpR.le]
    have heq3 : ∀ p ∈ primesUpTo X, (1 / Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ)⁻¹ := by
      intro p hp
      have hpR : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (mem_primesUpTo.mp hp).1.pos
      rw [div_pow, one_pow, Real.sq_sqrt hpR.le, inv_eq_one_div]
    rw [Finset.sum_congr rfl heq1, Finset.sum_congr rfl heq2,
      Finset.sum_congr rfl heq3] at h
    exact h
  have hsqrtsum : ∑ p ∈ primesUpTo X, Real.sqrt (a p) / (p : ℝ) ≤
      Real.sqrt (twistDefect w β X * primeMass X) := by
    have hnn : 0 ≤ ∑ p ∈ primesUpTo X, Real.sqrt (a p) / (p : ℝ) := by
      refine Finset.sum_nonneg ?_
      intro p hp
      have hpR : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (mem_primesUpTo.mp hp).1.pos
      positivity
    have := Real.sqrt_le_sqrt hCS
    rwa [Real.sqrt_sq hnn] at this
  have hfinal : ∑ p ∈ primesUpTo X, (k : ℝ) * Real.sqrt (2 * a p) / (p : ℝ)
      ≤ (k : ℝ) * Real.sqrt 2 * ∑ p ∈ primesUpTo X, Real.sqrt (a p) / (p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro p hp
    have hpR : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (mem_primesUpTo.mp hp).1.pos
    rw [Real.sqrt_mul (by norm_num) (a p)]
    rw [mul_div_assoc, mul_div_assoc]
    ring_nf
    exact le_rfl
  refine le_trans hfinal ?_
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hmul : (k : ℝ) * Real.sqrt 2 * ∑ p ∈ primesUpTo X, Real.sqrt (a p) / (p : ℝ)
      ≤ (k : ℝ) * Real.sqrt 2 * Real.sqrt (twistDefect w β X * primeMass X) := by
    gcongr
  refine le_trans hmul (le_of_eq ?_)
  rw [mul_assoc, ← Real.sqrt_mul (by norm_num)]
  congr 2
  ring

/-! ### The bridge into `TwistModulusDichotomy` -/

/-- The defect against `β` is `M − Re(β̄·C)` where `C = ∑ w_p/p`. -/
theorem twistDefect_eq_sub (w : ℕ → ℂ) (β : ℂ) (X : ℕ) :
    twistDefect w β X =
      primeMass X - ((starRingEnd ℂ) β * ∑ p ∈ primesUpTo X, w p / (p : ℂ)).re := by
  classical
  simp only [twistDefect, primeMass, Finset.mul_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (mem_primesUpTo.mp hp).1.pos
  have hdiv : ((starRingEnd ℂ) β * (w p / (p : ℂ))).re
      = ((starRingEnd ℂ) β * w p).re / (p : ℝ) := by
    rw [mul_div_assoc']
    rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.div_ofReal_re]
  rw [hdiv]
  field_simp

/-- **The failure of the easy alternative is clustering.**  If `‖C‖ ≥ (1−δ)M` then the twist
values cluster, in the `∑1/p` sense, around the single unimodular constant `β = C/‖C‖`. -/
theorem exists_unimodular_twistDefect_le {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) {X : ℕ}
    {δ : ℝ} (hX : 2 ≤ X) (hδ1 : δ < 1)
    (hfar : (1 - δ) * primeMass X ≤ ‖twistCorr χ t X‖) :
    ∃ β : ℂ, ‖β‖ = 1 ∧
      twistDefect (fun p => (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)) β X
        ≤ δ * primeMass X := by
  classical
  set C : ℂ := twistCorr χ t X with hC
  have hCeq : C = ∑ p ∈ primesUpTo X, (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p) / (p : ℂ) :=
    rfl
  have hMpos : 0 < primeMass X := by
    have h2 : (2 : ℕ) ∈ primesUpTo X :=
      mem_primesUpTo.mpr ⟨Nat.prime_two, hX⟩
    refine Finset.sum_pos' (fun p _ => by positivity) ⟨2, h2, by norm_num⟩
  have hCne : C ≠ 0 := by
    intro h
    rw [h, norm_zero] at hfar
    nlinarith
  have hCnorm : 0 < ‖C‖ := norm_pos_iff.mpr hCne
  refine ⟨C / (‖C‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCnorm, div_self hCnorm.ne']
  · rw [twistDefect_eq_sub, ← hCeq]
    have hre : ((starRingEnd ℂ) (C / (‖C‖ : ℂ)) * C).re = ‖C‖ := by
      have hden : ((‖C‖ : ℝ) : ℂ) ≠ 0 := by simpa using hCnorm.ne'
      have hcc : (starRingEnd ℂ) C * C = ((‖C‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj]
        norm_cast
        exact Complex.normSq_eq_norm_sq C
      have hfrac : (starRingEnd ℂ) (C / (‖C‖ : ℂ)) * C = ((‖C‖ : ℝ) : ℂ) := by
        rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, hcc]
        field_simp
        push_cast
        ring
      rw [hfrac, Complex.ofReal_re]
    rw [hre]
    nlinarith

end

end NormalNumbers.ElliottTwistBootstrap
