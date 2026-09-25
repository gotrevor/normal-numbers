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

open Erdos67b NormalNumbers.ElliottZetaOmegaPretentious NormalNumbers.CastingOut
  NormalNumbers.ElliottTwoPointLog

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

theorem twistDefect_nonneg {w : ℕ → ℂ} {β : ℂ} {X : ℕ} (hw : ∀ p ∈ primesUpTo X, ‖w p‖ ≤ 1)
    (hβ : ‖β‖ ≤ 1) :
    0 ≤ twistDefect w β X := by
  refine Finset.sum_nonneg ?_
  intro p hp
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (mem_primesUpTo.mp hp).1.pos
  have hnorm : ‖(starRingEnd ℂ) β * w p‖ ≤ 1 := by
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_one₀ hβ (norm_nonneg _) (hw p hp)
  have : ((starRingEnd ℂ) β * w p).re ≤ 1 :=
    le_trans (Complex.re_le_norm _) hnorm
  have hnum : 0 ≤ 1 - ((starRingEnd ℂ) β * w p).re := by linarith
  positivity

/-- **The power bootstrap.**  Clustering around `β` propagates to the `k`-th powers, at the
cost of one square root.  `‖w p‖ ≤ 1` is all that is needed; `β` is unimodular. -/
theorem twistDefect_pow_le {w : ℕ → ℂ} {β : ℂ} {X : ℕ} (hw : ∀ p ∈ primesUpTo X, ‖w p‖ ≤ 1)
    (hβ : ‖β‖ = 1) (k : ℕ) :
    twistDefect (fun p => w p ^ k) (β ^ k) X ≤
      (k : ℝ) * Real.sqrt (2 * twistDefect w β X * primeMass X) := by
  classical
  set b : ℕ → ℂ := fun p => (starRingEnd ℂ) β * w p with hb
  have hbnorm : ∀ p ∈ primesUpTo X, ‖b p‖ ≤ 1 := by
    intro p hp
    rw [hb, norm_mul, RCLike.norm_conj, hβ, one_mul]
    exact hw p hp
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
    have := one_sub_re_pow_le (hbnorm p hp) k
    rw [hrw p]
    gcongr
  refine le_trans hstep ?_
  -- Cauchy–Schwarz
  set a : ℕ → ℝ := fun p => 1 - (b p).re with ha
  have hanonneg : ∀ p ∈ primesUpTo X, 0 ≤ a p := by
    intro p hp
    have : (b p).re ≤ 1 := le_trans (Complex.re_le_norm _) (hbnorm p hp)
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

/-! ### Killing the character: the `φ(q)`-th power is purely Archimedean -/

/-- `(p^{it})^k = p^{i(kt)}`. -/
theorem archimedeanTwist_pow {p : ℕ} (hp : 0 < p) (t : ℝ) (k : ℕ) :
    archimedeanTwist t p ^ k = archimedeanTwist ((k : ℝ) * t) p := by
  rw [archimedeanTwist_eq_exp hp, archimedeanTwist_eq_exp hp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Euler.**  A Dirichlet character mod `q` has `(χ p)^{φ(q)} = 1` at every prime `p ∤ q`. -/
theorem dirichletChar_pow_totient {q : ℕ} (χ : DirichletCharacter ℂ q) (hq : 0 < q)
    {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) :
    (χ p) ^ q.totient = 1 := by
  have hcop : Nat.Coprime p q := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
  have heuler : p ^ q.totient ≡ 1 [MOD q] := Nat.ModEq.pow_totient hcop
  have hcast : ((p ^ q.totient : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr heuler
  calc (χ p) ^ q.totient = χ (((p : ZMod q)) ^ q.totient) := (map_pow χ _ _).symm
    _ = χ ((p ^ q.totient : ℕ) : ZMod q) := by push_cast; ring_nf
    _ = χ ((1 : ℕ) : ZMod q) := by rw [hcast]
    _ = 1 := by push_cast; exact MulChar.map_one χ

/-- The purely Archimedean correlation `∑_{p≤X} conj(p^{iv})/p`. -/
def archCorr (v : ℝ) (X : ℕ) : ℂ :=
  ∑ p ∈ primesUpTo X, (starRingEnd ℂ) (archimedeanTwist v p) / (p : ℂ)

/-- **The glue.**  Raising the twist values to the `φ(q)`-th power annihilates the character, so
the `k`-th power correlation is the Archimedean one up to the conductor primes. -/
theorem norm_powCorr_sub_archCorr_le {q : ℕ} (χ : DirichletCharacter ℂ q) (hq : 0 < q)
    (t : ℝ) (X : ℕ) :
    ‖(∑ p ∈ primesUpTo X,
        ((starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)) ^ q.totient / (p : ℂ))
      - archCorr ((q.totient : ℝ) * t) X‖ ≤ 2 * primeMass q := by
  classical
  have hsub : (∑ p ∈ primesUpTo X,
        ((starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)) ^ q.totient / (p : ℂ))
      - archCorr ((q.totient : ℝ) * t) X
      = ∑ p ∈ primesUpTo X,
          ((((starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)) ^ q.totient
            - (starRingEnd ℂ) (archimedeanTwist ((q.totient : ℝ) * t) p)) / (p : ℂ)) := by
    rw [archCorr, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [sub_div]
  rw [hsub]
  refine le_trans (norm_sum_le _ _) ?_
  have hbound : ∀ p ∈ primesUpTo X,
      ‖((((starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)) ^ q.totient
            - (starRingEnd ℂ) (archimedeanTwist ((q.totient : ℝ) * t) p)) / (p : ℂ))‖
        ≤ (if p ∣ q then (2 : ℝ) / p else 0) := by
    intro p hp
    have hp' : p.Prime := (mem_primesUpTo.mp hp).1
    have hppos : 0 < p := hp'.pos
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
    rw [norm_div, Complex.norm_natCast]
    by_cases hdvd : p ∣ q
    · rw [if_pos hdvd]
      gcongr
      have h1 : ‖((starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)) ^ q.totient‖ ≤ 1 := by
        rw [norm_pow, RCLike.norm_conj]
        exact pow_le_one₀ (norm_nonneg _) (norm_dirichletArchimedeanTwist_le_one χ t hppos)
      have h2 : ‖(starRingEnd ℂ) (archimedeanTwist ((q.totient : ℝ) * t) p)‖ = 1 := by
        rw [RCLike.norm_conj]
        exact norm_archimedeanTwist hppos _
      calc ‖_ - _‖ ≤ ‖((starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)) ^ q.totient‖
            + ‖(starRingEnd ℂ) (archimedeanTwist ((q.totient : ℝ) * t) p)‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [h2]; linarith
    · rw [if_neg hdvd]
      have heq : ((starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)) ^ q.totient
          = (starRingEnd ℂ) (archimedeanTwist ((q.totient : ℝ) * t) p) := by
        rw [← map_pow, dirichletArchimedeanTwist, mul_pow,
          dirichletChar_pow_totient χ hq hp' hdvd, one_mul, archimedeanTwist_pow hppos]
      rw [heq, sub_self, norm_zero, zero_div]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hsubq : (primesUpTo X).filter (fun p => p ∣ q) ⊆ primesUpTo q := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hp.1).1, Nat.le_of_dvd hq hp.2⟩
  rw [primeMass, Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubq ?_) ?_
  · intro p _ _; positivity
  · refine Finset.sum_le_sum ?_
    intro p _
    rw [div_eq_mul_inv]

/-! ### Small frequency: de-twisting down to the character alone -/

/-- Comparing two defects against the same `β`: a pointwise bound on `w₁ − w₂` transfers. -/
theorem twistDefect_le_add {w₁ w₂ : ℕ → ℂ} {β : ℂ} {X : ℕ} {e : ℕ → ℝ}
    (hβ : ‖β‖ ≤ 1) (he : ∀ p ∈ primesUpTo X, ‖w₁ p - w₂ p‖ ≤ e p) :
    twistDefect w₁ β X ≤ twistDefect w₂ β X + ∑ p ∈ primesUpTo X, e p / (p : ℝ) := by
  classical
  rw [twistDefect, twistDefect, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro p hp
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (mem_primesUpTo.mp hp).1.pos
  have hdiff : ((starRingEnd ℂ) β * w₂ p).re - ((starRingEnd ℂ) β * w₁ p).re
      ≤ e p := by
    have : ((starRingEnd ℂ) β * w₂ p).re - ((starRingEnd ℂ) β * w₁ p).re
        = ((starRingEnd ℂ) β * (w₂ p - w₁ p)).re := by
      rw [mul_sub, Complex.sub_re]
    rw [this]
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, RCLike.norm_conj]
    calc ‖β‖ * ‖w₂ p - w₁ p‖ ≤ 1 * ‖w₂ p - w₁ p‖ :=
          mul_le_mul_of_nonneg_right hβ (norm_nonneg _)
      _ = ‖w₁ p - w₂ p‖ := by rw [one_mul, norm_sub_rev]
      _ ≤ e p := he p hp
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by linarith) hpR.le

/-- **De-twisting at small frequency.**  If `|t| log X ≤ 1` then clustering of the full twist
values around `β` implies clustering of the *character values alone* around `β`, at an absolute
additive cost.  The Archimedean factor is a bounded perturbation in the `∑1/p` sense by
Mertens' first theorem — exactly as in `ElliottZetaOmegaPretentious`. -/
theorem exists_charDefect_le :
    ∃ K : ℝ, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (β : ℂ) (t : ℝ) (X : ℕ), 2 ≤ X →
      ‖β‖ ≤ 1 → |t| * Real.log (X : ℝ) ≤ 1 →
      twistDefect (fun p => (starRingEnd ℂ) (χ p)) β X
        ≤ twistDefect (fun p => (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)) β X + K := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_mertensOne
  refine ⟨2 + 4 * C, ?_⟩
  intro q χ β t X hX hβ htlog
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  have hlogXpos : (0 : ℝ) < Real.log (X : ℝ) := lt_of_lt_of_le hlog2 hlogX
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have htsmall : |t| ≤ 2 := by
    have : |t| * Real.log 2 ≤ 1 := le_trans (by nlinarith) htlog
    nlinarith [Real.log_two_gt_d9]
  have he : ∀ p ∈ primesUpTo X,
      ‖(starRingEnd ℂ) (χ p) - (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)‖
        ≤ 2 * |t| * Real.log (p : ℝ) := by
    intro p hp
    have hp' : p.Prime := (mem_primesUpTo.mp hp).1
    have hppos : 0 < p := hp'.pos
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
    have hpX : p ≤ X := (mem_primesUpTo.mp hp).2
    have hlogp : Real.log (p : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hpR (by exact_mod_cast hpX)
    have hlogp0 : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    have hsmall : |t| * Real.log (p : ℝ) ≤ 1 := by nlinarith
    have heq : (starRingEnd ℂ) (χ p) - (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)
        = (starRingEnd ℂ) (χ p * (1 - archimedeanTwist t p)) := by
      rw [dirichletArchimedeanTwist, map_mul, map_mul, map_sub, map_one]
      ring
    rw [heq, RCLike.norm_conj, norm_mul]
    have h1 : ‖χ p‖ ≤ 1 := χ.norm_le_one p
    have h2 : ‖1 - archimedeanTwist t p‖ ≤ 2 * (|t| * Real.log (p : ℝ)) := by
      rw [← norm_neg, neg_sub]
      exact norm_archimedeanTwist_sub_one_le hppos t hsmall
    have hnn : (0 : ℝ) ≤ 2 * (|t| * Real.log (p : ℝ)) := by positivity
    calc ‖χ p‖ * ‖1 - archimedeanTwist t p‖
        ≤ 1 * (2 * (|t| * Real.log (p : ℝ))) :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 2 * |t| * Real.log (p : ℝ) := by ring
  refine le_trans (twistDefect_le_add hβ he) ?_
  gcongr
  have heq : ∑ p ∈ primesUpTo X, 2 * |t| * Real.log (p : ℝ) / (p : ℝ)
      = 2 * |t| * ∑ p ∈ primesUpTo X, Real.log (p : ℝ) / (p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  rw [heq]
  nlinarith [hC X, htlog, habs, hC0, htsmall]

/-! ### The reduction of the crux to a character-free Archimedean bound -/

/-- **The reduction, large-frequency branch.**  If the purely Archimedean correlation at the
frequency `φ(q)·t` is bounded away from the full prime mass, then so is `‖C‖` — i.e. the hard
alternative of `TwistModulusDichotomy` holds.

The slack hypothesis is exactly what the bootstrap costs: `φ(q)·√(2δ)·M` from
`twistDefect_pow_le` plus `2M(q)` from the conductor primes must fit inside `η·M`.  Since
`φ(q) ≤ A` and `M(q) ≤ M(A)` are fixed before `X → ∞` and `M(X) → ∞`, it is satisfiable by first
choosing `δ` small and then `X` large. -/
theorem norm_twistCorr_le_of_archCorr_le {q : ℕ} (χ : DirichletCharacter ℂ q) (hq : 0 < q)
    (t : ℝ) {X : ℕ} {η δ : ℝ} (hX : 2 ≤ X) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (harch : ‖archCorr ((q.totient : ℝ) * t) X‖ ≤ (1 - η) * primeMass X)
    (hslack : (q.totient : ℝ) * Real.sqrt (2 * δ) * primeMass X + 2 * primeMass q
      < η * primeMass X) :
    ‖twistCorr χ t X‖ ≤ (1 - δ) * primeMass X := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨β, hβ, hdef⟩ := exists_unimodular_twistDefect_le χ t hX hδ1 hcon.le
  set w : ℕ → ℂ := fun p => (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p) with hw
  have hwn : ∀ p ∈ primesUpTo X, ‖w p‖ ≤ 1 := by
    intro p hp
    rw [hw, RCLike.norm_conj]
    exact norm_dirichletArchimedeanTwist_le_one χ t (mem_primesUpTo.mp hp).1.pos
  set k : ℕ := q.totient with hk
  have hMnn : 0 ≤ primeMass X := primeMass_nonneg X
  -- the bootstrap
  have hpow := twistDefect_pow_le hwn hβ k
  have hdefnn : 0 ≤ twistDefect w β X := twistDefect_nonneg hwn (le_of_eq hβ)
  have hmono : Real.sqrt (2 * twistDefect w β X * primeMass X)
      ≤ Real.sqrt (2 * δ) * primeMass X := by
    have hb : 2 * twistDefect w β X * primeMass X ≤ (2 * δ) * primeMass X ^ 2 := by
      nlinarith [hdef, hMnn, hdefnn]
    have := Real.sqrt_le_sqrt hb
    rwa [Real.sqrt_mul (by linarith : (0:ℝ) ≤ 2 * δ), Real.sqrt_sq hMnn] at this
  have hbootstrap : twistDefect (fun p => w p ^ k) (β ^ k) X
      ≤ (k : ℝ) * (Real.sqrt (2 * δ) * primeMass X) := by
    refine le_trans hpow ?_
    gcongr
  -- unwind to the Archimedean correlation
  set Ck : ℂ := ∑ p ∈ primesUpTo X, w p ^ k / (p : ℂ) with hCk
  have hdefeq : twistDefect (fun p => w p ^ k) (β ^ k) X
      = primeMass X - ((starRingEnd ℂ) (β ^ k) * Ck).re := twistDefect_eq_sub _ _ _
  have hCknorm : primeMass X - (k : ℝ) * (Real.sqrt (2 * δ) * primeMass X) ≤ ‖Ck‖ := by
    have hre : ((starRingEnd ℂ) (β ^ k) * Ck).re ≤ ‖Ck‖ := by
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_mul, RCLike.norm_conj, norm_pow, hβ, one_pow, one_mul]
    linarith [hdefeq ▸ hbootstrap]
  have hglue := norm_powCorr_sub_archCorr_le χ hq t X
  have hCkarch : ‖Ck‖ ≤ ‖archCorr ((k : ℝ) * t) X‖ + 2 * primeMass q := by
    have htri : ‖Ck‖ ≤ ‖Ck - archCorr ((k : ℝ) * t) X‖ + ‖archCorr ((k : ℝ) * t) X‖ := by
      simpa using norm_add_le (Ck - archCorr ((k : ℝ) * t) X) (archCorr ((k : ℝ) * t) X)
    linarith [hglue]
  linarith [harch]

/-! ### The crux, fully decomposed into two classical inputs -/

theorem primeMass_pos {X : ℕ} (hX : 2 ≤ X) : 0 < primeMass X := by
  have h2 : (2 : ℕ) ∈ primesUpTo X := mem_primesUpTo.mpr ⟨Nat.prime_two, hX⟩
  exact Finset.sum_pos' (fun p _ => by positivity) ⟨2, h2, by norm_num⟩

/-- **Input (c): the Archimedean prime correlation bound.**  Outside the near-trivial frequency
range, the purely Archimedean correlation `∑_{p≤X}p^{-iv}/p` is bounded away from the full prime
mass.  No Dirichlet character appears.  This is the classical estimate resting on a zero-free
region; over the polynomial height range `|v| ≤ A²X` it is Vinogradov–Korobov strength and is the
same statement the dependency names as `Erdos67b.PolynomialHeightPrimeCorrelationBound`. -/
def ArchimedeanCorrelationBound (A : ℕ) (η : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ v : ℝ,
    1 < |v| * Real.log (X : ℝ) → |v| ≤ (A : ℝ) * (A : ℝ) * X →
      ‖archCorr v X‖ ≤ (1 - η) * primeMass X

/-- **Input (d): rigidity of character clustering.**  A Dirichlet character whose values cluster
around a single unimodular constant in the `∑1/p` sense is principal.  Classically this is the
prime density in progressions (`∑_{p≤X, p≡a (q)} 1/p ≍ M/φ(q)`) plus the homomorphism property
(`χ(a) ≈ β` for all units forces `β ≈ β²`, hence `β ≈ 1`) plus the finiteness of the value group
(`χ(a)` is a `φ(q)`-th root of unity, so `≈ 1` means `= 1`).  Strictly weaker than (c): no
zero-free region is needed. -/
def CharacterClusterRigidity (A : ℕ) (θ : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
    ∀ χ : DirichletCharacter ℂ q, ∀ β : ℂ, ‖β‖ = 1 →
      twistDefect (fun p => (starRingEnd ℂ) (χ p)) β X ≤ θ * primeMass X →
      PrincipalAtGoodPrimes χ

/-- **THE DECOMPOSITION.**  The crux `TwistModulusDichotomy` follows from the two classical
inputs, with the parameters linked in the natural order: `δ` small enough that the power
bootstrap's loss `A√(2δ)` fits in half of `η`, and `δ < θ` so the de-twisting cost is absorbed
once `X` is large. -/
theorem twistModulusDichotomy_of_inputs {A : ℕ} {η θ δ : ℝ}
    (harch : ArchimedeanCorrelationBound A η) (hrig : CharacterClusterRigidity A θ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδθ : δ < θ)
    (hboot : (A : ℝ) * Real.sqrt (2 * δ) < η / 2) :
    TwistModulusDichotomy A δ := by
  classical
  obtain ⟨Xa, hXa2, hXa⟩ := harch
  obtain ⟨Xr, hXr2, hXr⟩ := hrig
  obtain ⟨K, hK⟩ := exists_charDefect_le
  obtain ⟨Xm, hXm2, hXm⟩ :=
    exists_primeMass_ge (max ((4 / η) * primeMass A) (|K| / (θ - δ)))
  refine ⟨max (max Xa Xr) Xm, le_trans hXa2 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro X hX q hq hqA χ t ht
  have hXXa : Xa ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXXr : Xr ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXXm : Xm ≤ X := le_trans (le_max_right _ _) hX
  have hX2 : 2 ≤ X := le_trans hXa2 hXXa
  have hMpos : 0 < primeMass X := primeMass_pos hX2
  have hbig := hXm X hXXm
  have hM1 : (4 / η) * primeMass A ≤ primeMass X := le_trans (le_max_left _ _) hbig
  have hM2 : |K| / (θ - δ) ≤ primeMass X := le_trans (le_max_right _ _) hbig
  set k : ℕ := q.totient with hk
  have hk1 : 1 ≤ k := Nat.totient_pos.mpr hq
  have hkA : (k : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast le_trans (Nat.totient_le q) hqA
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  by_cases hfreq : 1 < |(k : ℝ) * t| * Real.log (X : ℝ)
  · -- large frequency: the Archimedean bound applies
    right
    have hvbd : |(k : ℝ) * t| ≤ (A : ℝ) * (A : ℝ) * X := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ))]
      have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
      have hApos : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
      calc (k : ℝ) * |t| ≤ (A : ℝ) * ((A : ℝ) * X) := by
            refine mul_le_mul hkA ht (abs_nonneg t) hApos
        _ = (A : ℝ) * (A : ℝ) * X := by ring
    have harchX := hXa X hXXa ((k : ℝ) * t) hfreq hvbd
    refine norm_twistCorr_le_of_archCorr_le χ hq t hX2 hδ0.le hδ1 harchX ?_
    have hηpos : 0 < η := by
      have h0 : (0 : ℝ) ≤ (A : ℝ) * Real.sqrt (2 * δ) := by positivity
      linarith
    have hb1 : (k : ℝ) * Real.sqrt (2 * δ) * primeMass X < (η / 2) * primeMass X := by
      have : (k : ℝ) * Real.sqrt (2 * δ) < η / 2 := by
        have : (k : ℝ) * Real.sqrt (2 * δ) ≤ (A : ℝ) * Real.sqrt (2 * δ) :=
          mul_le_mul_of_nonneg_right hkA (Real.sqrt_nonneg _)
        linarith
      exact mul_lt_mul_of_pos_right this hMpos
    have hb2 : 2 * primeMass q ≤ (η / 2) * primeMass X := by
      have hqm : primeMass q ≤ primeMass A := primeMass_mono hqA
      have : (4 / η) * primeMass A ≤ primeMass X := hM1
      rw [div_mul_eq_mul_div, div_le_iff₀ hηpos] at this
      nlinarith [primeMass_nonneg A]
    linarith
  · -- small frequency: `t` is tiny, so only the character can obstruct
    push_neg at hfreq
    have htlog : |t| * Real.log (X : ℝ) ≤ 1 := by
      have hkt : |t| ≤ |(k : ℝ) * t| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ))]
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        nlinarith [abs_nonneg t]
      nlinarith [abs_nonneg t]
    by_cases hfar : ‖twistCorr χ t X‖ ≤ (1 - δ) * primeMass X
    · exact Or.inr hfar
    · left
      push_neg at hfar
      obtain ⟨β, hβ, hdef⟩ := exists_unimodular_twistDefect_le χ t hX2 hδ1 hfar.le
      have hchar := hK q χ β t X hX2 (le_of_eq hβ) htlog
      have hKle : K ≤ (θ - δ) * primeMass X := by
        have hθδ : 0 < θ - δ := by linarith
        rw [div_le_iff₀ hθδ] at hM2
        have : K ≤ |K| := le_abs_self K
        nlinarith
      refine ⟨hXr X hXXr q hq hqA χ β hβ ?_, htlog⟩
      calc twistDefect (fun p => (starRingEnd ℂ) (χ p)) β X
          ≤ twistDefect (fun p => (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)) β X + K :=
            hchar
        _ ≤ δ * primeMass X + (θ - δ) * primeMass X := by linarith
        _ = θ * primeMass X := by ring

/-- For each level `A`, a `δ` small enough that the bootstrap loss fits. -/
theorem exists_delta_twistModulusDichotomy {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ)
    (harch : ∀ A : ℕ, ArchimedeanCorrelationBound A η)
    (hrig : ∀ A : ℕ, CharacterClusterRigidity A θ) (A : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ TwistModulusDichotomy A δ := by
  set R : ℝ := η / (4 * ((A : ℝ) + 1)) with hR
  have hApos : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hRpos : 0 < R := by rw [hR]; positivity
  set δ : ℝ := min (min (θ / 2) (1 / 2)) (R ^ 2 / 2) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (by linarith) (by norm_num)) (by positivity)
  have hδ1 : δ < 1 := by
    have : δ ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hδθ : δ < θ := by
    have : δ ≤ θ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hboot : (A : ℝ) * Real.sqrt (2 * δ) < η / 2 := by
    have h2δ : 2 * δ ≤ R ^ 2 := by
      have : δ ≤ R ^ 2 / 2 := min_le_right _ _
      linarith
    have hsq : Real.sqrt (2 * δ) ≤ R := by
      have := Real.sqrt_le_sqrt h2δ
      rwa [Real.sqrt_sq hRpos.le] at this
    have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    have hmul : (A : ℝ) * Real.sqrt (2 * δ) ≤ (A : ℝ) * R :=
      mul_le_mul_of_nonneg_left hsq hAnn
    have hAR : (A : ℝ) * R < η / 2 := by
      rw [hR]
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  exact ⟨δ, hδ0, hδ1.le, twistModulusDichotomy_of_inputs (harch A) (hrig A) hδ0 hδ1 hδθ hboot⟩

/-- **THE PAYOFF, from classical inputs only.**  C1's two-point leaf holds in logarithmic average
for every `ζ = e(t/b) ≠ 1`, granted the Archimedean prime correlation bound and the rigidity of
character clustering.  No other unproved statement is involved: the whole Elliott chain beneath
this is machine-checked. -/
theorem twoPointElliottLog_of_classical_inputs {b p q : ℕ} {t : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hu : (phase (t / b)).re < 1) {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ)
    (harch : ∀ A : ℕ, ArchimedeanCorrelationBound A η)
    (hrig : ∀ A : ℕ, CharacterClusterRigidity A θ) :
    TwoPointElliottLog b p q t :=
  twoPointElliottLog_of_dichotomy hp hq hpq hu
    (exists_delta_twistModulusDichotomy hη hθ harch hrig)

end

end NormalNumbers.ElliottTwistBootstrap
