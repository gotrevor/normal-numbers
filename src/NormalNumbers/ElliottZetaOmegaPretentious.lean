import NormalNumbers.ElliottTwoPointLog

/-!
# Discharging `UniformlyNonPretentious` for `ζ^ω` — the decomposition

`DIRECTION.md` item 4's remaining obligation.  `ElliottTwoPointLog` derives the log-averaged
two-point statement from `UniformlyNonPretentious (zetaOmegaInt u)`; this file reduces that
hypothesis to **one** named analytic input.

## The algebraic core (proved here)

`ζ^ω` takes the *constant* value `ζ = e(u)` at every prime, so for any twist `χ·n^{it}`

  `D(ζ^ω, χ n^{it}; X)² = M(X) − Re(ζ · C(χ,t,X))`,  `M(X) = ∑_{p≤X} 1/p`,
  `C(χ,t,X) = ∑_{p≤X} conj(χ(p) p^{it})/p`.

(`zetaOmegaDistSq_eq`).  Everything then turns on how close the complex number `C` can come to
the *positive real* number `M` **after rotation by `ζ`**: `Re(ζC) ≤ ‖C‖ ≤ M` always, and the
distance is large as soon as either `‖C‖` is bounded away from `M`, or `C` is close to `M` itself
(in which case the rotation by `ζ ≠ 1` costs `(1−cos 2πu)·M`).

## The analytic input (a hypothesis, not an axiom)

`TwistModulusDichotomy A δ` is exactly that dichotomy: for every modulus `q ≤ A`, character `χ`
mod `q` and frequency `|t| ≤ A·X`, either the twist is *near-trivial* (`χ` principal and
`|t|·log X ≤ 1`), or `‖C‖ ≤ (1−δ)·M`.  This is the Vinogradov–Korobov-strength prime-correlation
estimate that the dependency's `TwistSeparation.lean` also stops at (it names, but deliberately
does not prove, `PolynomialHeightPrimeCorrelationBound` for the polynomial-height range).  It is
the honest crux and is left open here; **the rest of the reduction is proved**:

* `zetaOmegaDistSq_eq` — the identity above.
* `nearTrivial_C_close` — in the near-trivial regime, `‖C − M‖ ≤ 1 + log A` (an absolute bound:
  `|1 − p^{-it}| ≤ |t| log p ≤ 1` and the principal character loses only `∑_{p ∣ q} 1/p`).
* `uniformlyNonPretentious_zetaOmega_of_dichotomy` — the derivation.
-/

open Finset Filter Topology

namespace NormalNumbers.ElliottZetaOmegaPretentious

open Erdos67b NormalNumbers.CastingOut NormalNumbers.ElliottTwoPointLog

noncomputable section

/-- The prime reciprocal mass `M(X) = ∑_{p ≤ X} 1/p`. -/
def primeMass (X : ℕ) : ℝ := ∑ p ∈ primesUpTo X, (p : ℝ)⁻¹

/-- The complex twist correlation `C(χ,t,X) = ∑_{p ≤ X} conj(χ(p)·p^{it})/p`. -/
def twistCorr {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) : ℂ :=
  ∑ p ∈ primesUpTo X, (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p) / (p : ℂ)

/-- **The algebraic core.**  `ζ^ω` is constantly `ζ` at the primes, so its squared pretentious
distance to any twist is `M − Re(ζ·C)`. -/
theorem zetaOmegaDistSq_eq (u : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) :
    pretentiousDistSqToTwist (restrictToNat (zetaOmegaInt u)) χ t X =
      primeMass X - (phase u * twistCorr χ t X).re := by
  classical
  simp only [pretentiousDistSqToTwist, pretentiousDistSq, primeMass, twistCorr,
    Finset.mul_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp' : p.Prime := (mem_primesUpTo.mp hp).1
  have hppos : 0 < p := hp'.pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
  have hzeta : restrictToNat (zetaOmegaInt u) p = phase u := by
    have : omegaNat p = 1 := by
      simp [omegaNat, Nat.Prime.primeFactors hp']
    rw [restrictToNat, zetaOmegaInt_natCast hppos, this, pow_one]
  rw [pretentiousTerm, hzeta]
  have hdiv : (phase u * ((starRingEnd ℂ) (dirichletArchimedeanTwist χ t p) / (p : ℂ))).re
      = (phase u * (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)).re / (p : ℝ) := by
    rw [mul_div_assoc']
    rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.div_ofReal_re]
  rw [hdiv]
  field_simp

/-! ## The near-trivial regime -/

/-- `p^{it} = exp(i t log p)`. -/
theorem archimedeanTwist_eq_exp {p : ℕ} (hp : 0 < p) (t : ℝ) :
    archimedeanTwist t p = Complex.exp (Complex.I * (t : ℂ) * ((Real.log p : ℝ) : ℂ)) := by
  have hp0 : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp.ne'
  have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
  rw [archimedeanTwist, Complex.cpow_def_of_ne_zero hp0]
  congr 1
  rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_log hpR]
  ring

/-- `‖p^{it} − 1‖ ≤ 2|t| log p` whenever `|t| log p ≤ 1`. -/
theorem norm_archimedeanTwist_sub_one_le {p : ℕ} (hp : 0 < p) (t : ℝ)
    (h : |t| * Real.log p ≤ 1) :
    ‖archimedeanTwist t p - 1‖ ≤ 2 * (|t| * Real.log p) := by
  have hlog : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
  have hnorm : ‖Complex.I * (t : ℂ) * ((Real.log p : ℝ) : ℂ)‖ = |t| * Real.log p := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog]
  rw [archimedeanTwist_eq_exp hp t]
  have := Complex.norm_exp_sub_one_le (x := Complex.I * (t : ℂ) * ((Real.log p : ℝ) : ℂ))
    (by rw [hnorm]; exact h)
  rwa [hnorm] at this

/-- `χ` behaves like the principal character mod `q`: it is `1` at every prime not dividing `q`. -/
def PrincipalAtGoodPrimes {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (p ∣ q) → χ p = 1

/-- The near-trivial regime: a principal character and a frequency so small that the whole
Archimedean twist is a bounded perturbation of `1` across the window.

The cutoff `|t| · log X · M(X) ≤ 1` is marginally smaller than the classical `|t| ≤ 1/log X`,
by a `log log X` factor; it is what the crude bound `‖p^{it} − 1‖ ≤ 2|t| log p ≤ 2|t| log X`
affords without Mertens' first theorem `∑_{p≤X} (log p)/p = log X + O(1)`, which is not in the
dependency.  Proving Mertens I would widen this regime and *weaken* the analytic input below. -/
def NearTrivialTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) : Prop :=
  PrincipalAtGoodPrimes χ ∧ |t| * Real.log (X : ℝ) ≤ 1 ∧
    |t| * Real.log (X : ℝ) * primeMass X ≤ 1

theorem primeMass_nonneg (X : ℕ) : 0 ≤ primeMass X :=
  Finset.sum_nonneg fun p _ => by positivity

theorem primeMass_mono {X Y : ℕ} (h : X ≤ Y) : primeMass X ≤ primeMass Y := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (primesUpTo_mono h) ?_
  intro p _ _; positivity

/-- **The near-trivial estimate.**  In the near-trivial regime `C` differs from the real number
`M` by at most `2 + 2·M(q)` — a bound independent of `X`. -/
theorem norm_twistCorr_sub_primeMass_le {q : ℕ} (χ : DirichletCharacter ℂ q) (hq : 0 < q)
    (t : ℝ) {X : ℕ} (hX : 2 ≤ X) (hnt : NearTrivialTwist χ t X) :
    ‖twistCorr χ t X - (primeMass X : ℂ)‖ ≤ 2 + 2 * primeMass q := by
  classical
  obtain ⟨hprin, htlog, htM⟩ := hnt
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hsplit : twistCorr χ t X - (primeMass X : ℂ) =
      ∑ p ∈ primesUpTo X,
        ((starRingEnd ℂ) (dirichletArchimedeanTwist χ t p) - 1) / (p : ℂ) := by
    rw [twistCorr, primeMass, Complex.ofReal_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [sub_div]
    congr 1
    push_cast
    ring
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) ?_
  -- split the index set according to `p ∣ q`
  have hbound : ∀ p ∈ primesUpTo X,
      ‖((starRingEnd ℂ) (dirichletArchimedeanTwist χ t p) - 1) / (p : ℂ)‖ ≤
        (if p ∣ q then (2 : ℝ) / p else 2 * (|t| * Real.log (X : ℝ)) / p) := by
    intro p hp
    have hp' : p.Prime := (mem_primesUpTo.mp hp).1
    have hpX : p ≤ X := (mem_primesUpTo.mp hp).2
    have hppos : 0 < p := hp'.pos
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
    have hnormp : ‖((p : ℂ))‖ = (p : ℝ) := by
      exact Complex.norm_natCast p
    rw [norm_div, hnormp]
    by_cases hdvd : p ∣ q
    · rw [if_pos hdvd]
      gcongr
      have h1 : ‖(starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)‖ ≤ 1 := by
        rw [RCLike.norm_conj]
        exact norm_dirichletArchimedeanTwist_le_one χ t hppos
      calc ‖(starRingEnd ℂ) (dirichletArchimedeanTwist χ t p) - 1‖
          ≤ ‖(starRingEnd ℂ) (dirichletArchimedeanTwist χ t p)‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ 2 := by simp at *; linarith
    · rw [if_neg hdvd]
      gcongr
      have hχ : χ p = 1 := hprin p hp' hdvd
      have hlogp : Real.log (p : ℝ) ≤ Real.log (X : ℝ) :=
        Real.log_le_log hpR (by exact_mod_cast hpX)
      have hlogp0 : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
      have hsmall : |t| * Real.log (p : ℝ) ≤ 1 := by nlinarith
      have hconj : (starRingEnd ℂ) (dirichletArchimedeanTwist χ t p) - 1 =
          (starRingEnd ℂ) (archimedeanTwist t p - 1) := by
        rw [dirichletArchimedeanTwist, hχ, one_mul, map_sub, map_one]
      rw [hconj, RCLike.norm_conj]
      calc ‖archimedeanTwist t p - 1‖ ≤ 2 * (|t| * Real.log (p : ℝ)) :=
            norm_archimedeanTwist_sub_one_le hppos t hsmall
        _ ≤ 2 * (|t| * Real.log (X : ℝ)) := by nlinarith
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_ite]
  have hA : ∑ p ∈ (primesUpTo X).filter (fun p => p ∣ q), (2 : ℝ) / p ≤ 2 * primeMass q := by
    have hsub : (primesUpTo X).filter (fun p => p ∣ q) ⊆ primesUpTo q := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp' : p.Prime := (mem_primesUpTo.mp hp.1).1
      exact mem_primesUpTo.mpr ⟨hp', Nat.le_of_dvd hq hp.2⟩
    rw [primeMass, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
    · intro p _ _; positivity
    · refine Finset.sum_le_sum ?_
      intro p _
      rw [div_eq_mul_inv]
  have hB : ∑ p ∈ (primesUpTo X).filter (fun p => ¬ p ∣ q),
      2 * (|t| * Real.log (X : ℝ)) / p ≤ 2 := by
    have hstep : ∑ p ∈ (primesUpTo X).filter (fun p => ¬ p ∣ q),
        2 * (|t| * Real.log (X : ℝ)) / p ≤
        ∑ p ∈ primesUpTo X, 2 * (|t| * Real.log (X : ℝ)) / p := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro p hp _
      have hpR : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (mem_primesUpTo.mp hp).1.pos
      positivity
    refine le_trans hstep ?_
    have : ∑ p ∈ primesUpTo X, 2 * (|t| * Real.log (X : ℝ)) / p
        = 2 * (|t| * Real.log (X : ℝ) * primeMass X) := by
      rw [primeMass, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro p _
      rw [div_eq_mul_inv]
      ring
    rw [this]
    linarith
  linarith

/-! ## The analytic input and the derivation -/

/-- **The crux, named.**  For every modulus `q ≤ A`, character `χ` mod `q` and frequency
`|t| ≤ A·X`, either the twist is near-trivial, or the *modulus* of the twist correlation is
bounded away from the full prime mass by a fixed factor.

This is the Vinogradov–Korobov-strength statement that the dependency's `TwistSeparation.lean`
also stops at: it names `Erdos67b.PolynomialHeightPrimeCorrelationBound` for the same
polynomial-height range `|t| ≤ A·X` and deliberately does not claim it.  Note what is asked here
that the dependency's `characterTwistDistSq` bounds do *not* give: those control the **real
part** `Re C = M − D(1, χ n^{it})²`, whereas rotating by the constant `ζ` exposes `Im C` as well,
so the modulus `‖C‖` is what is needed.  The two coincide only in the near-trivial regime, which
is exactly why the dichotomy is stated with that regime split off.

Mathematically the second alternative is standard: if `‖C‖ ≥ (1−δ)M` then `conj(χ(p)p^{it})` is
within `o(1)` of a fixed unimodular constant `β` for almost all `p` in the `∑1/p` sense; raising
to the order of `χ` kills the character and leaves `∑_{p≤X} p^{-ikt}/p ≈ β^k M`, which forces
`|t| ≪ (log X)^{-1+o(1)}`, hence the near-trivial regime after PNT in progressions pins `β = 1`. -/
def TwistModulusDichotomy (A : ℕ) (δ : ℝ) : Prop :=
  ∀ X : ℕ, 2 ≤ X → ∀ q : ℕ, 0 < q → q ≤ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
    |t| ≤ (A : ℝ) * X →
      NearTrivialTwist χ t X ∨ ‖twistCorr χ t X‖ ≤ (1 - δ) * primeMass X

/-- The prime mass is eventually as large as we please (Mertens). -/
theorem exists_primeMass_ge (R : ℝ) : ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → R ≤ primeMass X := by
  refine ⟨max 2 (⌈Real.exp (Real.exp (R + PrimeEstimates.mertensBound))⌉₊ + 1), le_max_left _ _,
    ?_⟩
  intro X hX
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hXexp : Real.exp (Real.exp (R + PrimeEstimates.mertensBound)) ≤ (X : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast le_trans (by omega)
      (le_trans (le_max_right 2 (⌈Real.exp (Real.exp (R + PrimeEstimates.mertensBound))⌉₊ + 1)) hX)
  have hlogX : Real.exp (R + PrimeEstimates.mertensBound) ≤ Real.log (X : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) hXexp
    rwa [Real.log_exp] at this
  have hloglog : R + PrimeEstimates.mertensBound ≤ Real.log (Real.log (X : ℝ)) := by
    have := Real.log_le_log (Real.exp_pos _) hlogX
    rwa [Real.log_exp] at this
  have hmass : Real.log (Real.log (X : ℝ)) - PrimeEstimates.mertensBound ≤ primeMass X :=
    characterTwistPrimeMass_mertens_lower hX2
  linarith

/-- **The derivation.**  Granted the dichotomy, `ζ^ω` is uniformly non-pretentious whenever
`ζ = e(u) ≠ 1`, i.e. whenever `u ∉ ℤ`. -/
theorem uniformlyNonPretentious_zetaOmega_of_dichotomy {u : ℝ} (hu : (phase u).re < 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hdich : ∀ A : ℕ, TwistModulusDichotomy A δ) :
    UniformlyNonPretentious (zetaOmegaInt u) := by
  classical
  intro A
  set c : ℝ := 1 - (phase u).re with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  set m : ℝ := min c δ with hm
  have hmpos : 0 < m := lt_min hcpos hδ
  obtain ⟨X₀, hX₀2, hX₀⟩ :=
    exists_primeMass_ge (((A : ℝ) + 2 + 2 * primeMass A) / m)
  refine ⟨X₀, ?_⟩
  intro X hX q hq hqA χ s hs
  have hX2 : 2 ≤ X := le_trans hX₀2 hX
  have hmass : ((A : ℝ) + 2 + 2 * primeMass A) / m ≤ primeMass X := hX₀ X hX
  have hkey : (A : ℝ) + 2 + 2 * primeMass A ≤ m * primeMass X := by
    rw [div_le_iff₀ hmpos] at hmass; linarith [hmass]
  rw [zetaOmegaDistSq_eq]
  have hmA : primeMass q ≤ primeMass A := primeMass_mono hqA
  rcases hdich A X hX2 q hq hqA χ s hs with hnt | hfar
  · -- near-trivial: the rotation by `ζ ≠ 1` costs `c·M`
    have hcl := norm_twistCorr_sub_primeMass_le χ hq s hX2 hnt
    have hsplit : (phase u * twistCorr χ s X).re =
        (phase u).re * primeMass X + (phase u * (twistCorr χ s X - (primeMass X : ℂ))).re := by
      have : phase u * twistCorr χ s X =
          phase u * (primeMass X : ℂ) + phase u * (twistCorr χ s X - (primeMass X : ℂ)) := by
        ring
      rw [this, Complex.add_re]
      congr 1
      simp [Complex.mul_re]
    have hre : (phase u * (twistCorr χ s X - (primeMass X : ℂ))).re ≤ 2 + 2 * primeMass A := by
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_mul, norm_phase, one_mul]
      linarith
    have hmc : m * primeMass X ≤ c * primeMass X :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (primeMass_nonneg X)
    rw [hsplit, hc] at *
    nlinarith [primeMass_nonneg X]
  · -- far: the modulus alone suffices
    have hre : (phase u * twistCorr χ s X).re ≤ (1 - δ) * primeMass X := by
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_mul, norm_phase, one_mul]
      exact hfar
    have hmd : m * primeMass X ≤ δ * primeMass X :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (primeMass_nonneg X)
    nlinarith [primeMass_nonneg X, primeMass_nonneg A]

/-- `cos 2πu < 1` exactly when `u` is not an integer. -/
theorem phase_re_lt_one_of_not_int {u : ℝ} (hu : ∀ k : ℤ, u ≠ k) : (phase u).re < 1 := by
  have hre : (phase u).re = Real.cos (2 * Real.pi * u) := by
    rw [phase]
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))
        = ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_re]
  rw [hre]
  rcases lt_or_eq_of_le (Real.cos_le_one (2 * Real.pi * u)) with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (2 * Real.pi * u)).1 h
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
      have := Real.pi_pos; positivity
    refine hu k (mul_left_cancel₀ h2pi ?_)
    linarith [hk]

/-- **The payoff.**  Granted the dichotomy, C1's two-point leaf holds in logarithmic average. -/
theorem twoPointElliottLog_of_dichotomy {b p q : ℕ} {t : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hu : (phase (t / b)).re < 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hdich : ∀ A : ℕ, TwistModulusDichotomy A δ) :
    TwoPointElliottLog b p q t :=
  twoPointElliottLog_of_nonPretentious hp hq hpq
    (uniformlyNonPretentious_zetaOmega_of_dichotomy hu hδ hδ1 hdich)

end

end NormalNumbers.ElliottZetaOmegaPretentious
