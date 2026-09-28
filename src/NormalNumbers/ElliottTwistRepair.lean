import NormalNumbers.ElliottArchimedeanRefuted

/-!
# The repaired crux: `AlmostRealTwist` and the honest frequency split

`ElliottArchimedeanRefuted` proves that `ArchimedeanCorrelationBound A η` — the input (c) of laps
85–91 — is **false**, because its frequency range `1 < |v| log X` reaches down to
`|v| ≈ 1/log X`, where `∑_{p≤X}p^{-iv}/p = M(X) + O(1)`.  The truth is

  `‖∑_{p≤X} p^{-iv}/p‖ = log min(log X, 1/|v|) + O(1)`  for `|v| ≤ 1`,

so a *fixed* loss `η` needs `|v| ≥ (log X)^{-1+ε}`, not `|v| ≥ 1/log X`.  Raising the threshold
opens a gap: the old easy branch `NearTrivialTwist` (and the de-twisting behind
`exists_charDefect_le`) both need `|t| log X ≤ 1`, so the intermediate band
`1/log X ≲ |t| ≲ (log X)^{-1+ε}` was covered by neither alternative.

This file repairs the decomposition.  The point is that the consumer never needed `C ≈ M(X)`; it
only needed `C` to be **close to a nonnegative real number at most `M(X)`**, because the rotation
by `ζ = e(u) ≠ 1` then costs `(1 - Re ζ)·M(X)`:

* `AlmostRealTwist K χ t X` — `∃ R ∈ [0, M(X)]`, `‖C − R‖ ≤ K`.  Strictly weaker than
  `NearTrivialTwist` (`almostRealTwist_of_nearTrivial`), and *true across the whole intermediate
  band*: for principal `χ`, `C = log(1/|t|) + O(1)` there, and `log(1/|t|) ∈ [0, M(X)]`.
* `TwistAlmostRealDichotomy A δ K` — the repaired crux, with that easy alternative.
* `uniformlyNonPretentious_zetaOmega_of_almostReal` — the consumer, re-proved against it.
* The two repaired inputs, split at a **threshold function** `T : ℕ → ℝ` (honestly
  `T X = (log X)^{-1+ε}`) instead of at the false `1/log X`:
  * `ArchimedeanCorrelationBoundAbove A η T` — input (c′): the Archimedean bound for
    `T X < |v| ≤ A²X`.  This is the only place a zero-free region enters.
  * `SmallShiftAlmostReal A K T` — input (e): Mertens for characters at small Archimedean shift,
    `|t| ≤ T X ⟹ AlmostRealTwist`.  **No zero-free region**: for non-principal `χ` it is
    `‖∑χ̄(p)p^{-it}/p‖ = O_q(1)` (i.e. `L(1,χ) ≠ 0`), and for principal `χ` it is Mertens with the
    error term `O(1/log u)` integrated against `e^{-ity}`, whose imaginary part is the bounded
    `Si(t log X)`.
* `twistAlmostRealDichotomy_of_inputs` — the dichotomy from (c′) + (e).  Note what has
  *disappeared*: `CharacterClusterRigidity`, `PrimeDensityAP`, `exists_charDefect_le`.  Input (e)
  supplies the easy branch directly, so the character never has to be shown principal.
* `twoPointElliottLog_of_repaired_inputs` — the payoff on (c′) + (e).

`twistAlmostRealDichotomy_of_old` records that the old dichotomy implies the new one, so nothing
proved in laps 85–91 is lost; only the false input is.
-/

open Finset

namespace NormalNumbers.ElliottTwistRepair

open Erdos67b NormalNumbers.ElliottZetaOmegaPretentious NormalNumbers.ElliottTwistBootstrap
  NormalNumbers.CastingOut NormalNumbers.ElliottTwoPointLog

noncomputable section

/-! ### The weakened easy alternative -/

/-- **The easy alternative, weakened.**  The twist correlation is within `K` of a nonnegative real
number at most the full prime mass. -/
def AlmostRealTwist (K : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) : Prop :=
  ∃ R : ℝ, 0 ≤ R ∧ R ≤ primeMass X ∧ ‖twistCorr χ t X - (R : ℂ)‖ ≤ K

/-- The near-trivial regime is the special case `R = M(X)`. -/
theorem almostRealTwist_of_norm_sub_primeMass {K : ℝ} {q : ℕ} {χ : DirichletCharacter ℂ q}
    {t : ℝ} {X : ℕ} (h : ‖twistCorr χ t X - (primeMass X : ℂ)‖ ≤ K) :
    AlmostRealTwist K χ t X :=
  ⟨primeMass X, primeMass_nonneg X, le_rfl, h⟩

/-- **The key inequality.**  Rotating an almost-real twist correlation by a phase costs the full
`(1 − max(Re ζ, 0))` proportion of the prime mass. -/
theorem re_phase_mul_twistCorr_le {K : ℝ} {q : ℕ} {χ : DirichletCharacter ℂ q} {t : ℝ} {X : ℕ}
    (u : ℝ) (h : AlmostRealTwist K χ t X) :
    (phase u * twistCorr χ t X).re ≤ max ((phase u).re) 0 * primeMass X + K := by
  obtain ⟨R, hR0, hRM, hclose⟩ := h
  have hmx0 : (0 : ℝ) ≤ max ((phase u).re) 0 := le_max_right _ _
  have hsplit : phase u * twistCorr χ t X
      = phase u * (R : ℂ) + phase u * (twistCorr χ t X - (R : ℂ)) := by ring
  have hre1 : (phase u * (R : ℂ)).re = (phase u).re * R := by
    simp [Complex.mul_re]
  have hre2 : (phase u * (twistCorr χ t X - (R : ℂ))).re ≤ K := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, norm_phase, one_mul]
    exact hclose
  have hmain : (phase u).re * R ≤ max ((phase u).re) 0 * primeMass X := by
    calc (phase u).re * R ≤ max ((phase u).re) 0 * R :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hR0
      _ ≤ max ((phase u).re) 0 * primeMass X := mul_le_mul_of_nonneg_left hRM hmx0
  rw [hsplit, Complex.add_re, hre1]
  linarith

/-! ### The repaired dichotomy and its consumer -/

/-- **The repaired crux.**  Either the twist correlation is almost real and nonnegative, or its
modulus is bounded away from the full prime mass. -/
def TwistAlmostRealDichotomy (A : ℕ) (δ K : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
    ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| ≤ (A : ℝ) * X →
      AlmostRealTwist K χ t X ∨ ‖twistCorr χ t X‖ ≤ (1 - δ) * primeMass X

/-- The old dichotomy implies the repaired one: nothing proved in laps 85–91 is lost. -/
theorem twistAlmostRealDichotomy_of_old {A : ℕ} {δ : ℝ} (h : TwistModulusDichotomy A δ) :
    ∃ K : ℝ, TwistAlmostRealDichotomy A δ K := by
  obtain ⟨K, hK⟩ := exists_norm_twistCorr_sub_primeMass_le
  obtain ⟨X₀, hX₀2, hX₀⟩ := h
  refine ⟨K + 2 * primeMass A, X₀, hX₀2, ?_⟩
  intro X hX q hq hqA χ t ht
  rcases hX₀ X hX q hq hqA χ t ht with hnt | hfar
  · refine Or.inl (almostRealTwist_of_norm_sub_primeMass ?_)
    refine le_trans (hK q χ hq t X (le_trans hX₀2 hX) hnt) ?_
    have := primeMass_mono (X := q) (Y := A) hqA
    linarith
  · exact Or.inr hfar

/-- **The consumer, re-proved.**  Granted the repaired dichotomy, `ζ^ω` is uniformly
non-pretentious whenever `ζ = e(u) ≠ 1`. -/
theorem uniformlyNonPretentious_zetaOmega_of_almostReal {u : ℝ} (hu : (phase u).re < 1)
    (hdich : ∀ A : ℕ, ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ TwistAlmostRealDichotomy A δ K) :
    UniformlyNonPretentious (zetaOmegaInt u) := by
  classical
  intro A
  obtain ⟨δ, K, hδ, hδ1, hdichA⟩ := hdich A
  set mx : ℝ := max ((phase u).re) 0 with hmx
  have hmx0 : (0 : ℝ) ≤ mx := le_max_right _ _
  have hmx1 : mx < 1 := by
    rw [hmx]
    exact max_lt hu one_pos
  set m : ℝ := min (1 - mx) δ with hmdef
  have hmpos : 0 < m := lt_min (by linarith) hδ
  obtain ⟨X₁, hX₁2, hX₁⟩ := hdichA
  obtain ⟨X₀, hX₀2, hX₀⟩ := exists_primeMass_ge (((A : ℝ) + |K|) / m)
  refine ⟨max X₀ X₁, ?_⟩
  intro X hX q hq hqA χ s hs
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXX₁ : X₁ ≤ X := le_trans (le_max_right _ _) hX
  have hMnn : 0 ≤ primeMass X := primeMass_nonneg X
  have hmass : ((A : ℝ) + |K|) / m ≤ primeMass X := hX₀ X hXX₀
  have hkey : (A : ℝ) + |K| ≤ m * primeMass X := by
    rw [div_le_iff₀ hmpos] at hmass; linarith [hmass]
  have hKabs : K ≤ |K| := le_abs_self K
  rw [zetaOmegaDistSq_eq]
  rcases hX₁ X hXX₁ q hq hqA χ s hs with har | hfar
  · have hre := re_phase_mul_twistCorr_le u har
    have hmm : m * primeMass X ≤ (1 - mx) * primeMass X :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hMnn
    nlinarith
  · have hre : (phase u * twistCorr χ s X).re ≤ (1 - δ) * primeMass X := by
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_mul, norm_phase, one_mul]
      exact hfar
    have hmd : m * primeMass X ≤ δ * primeMass X :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hMnn
    nlinarith [abs_nonneg K]

/-! ### The two repaired inputs -/

/-- **Input (c′).**  The Archimedean prime correlation bound on the honest frequency range: above
the threshold `T X` (mathematically `T X = (log X)^{-1+ε}`, not the false `1/log X`) and below the
polynomial height `A²X`.  This is the one place a zero-free region enters. -/
def ArchimedeanCorrelationBoundAbove (A : ℕ) (η : ℝ) (T : ℕ → ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ v : ℝ,
    T X < |v| → |v| ≤ (A : ℝ) * (A : ℝ) * X → ‖archCorr v X‖ ≤ (1 - η) * primeMass X

/-- **Input (e).**  Mertens for Dirichlet characters at a small Archimedean shift: below the
threshold `T X` the twist correlation is within an absolute constant of a nonnegative real number
at most `M(X)`.  Classical and **free of any zero-free region**: non-principal `χ` gives
`‖C‖ = O_q(1)` from `L(1,χ) ≠ 0`, and principal `χ` gives `C = log(1/|t|) + O(1)` from Mertens with
the error term `O(1/log u)`, the imaginary part being the bounded sine integral `Si(t log X)`. -/
def SmallShiftAlmostReal (A : ℕ) (K : ℝ) (T : ℕ → ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
    ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| ≤ T X → AlmostRealTwist K χ t X

/-- **THE REPAIRED DECOMPOSITION.**  The two inputs split at the same threshold give the
dichotomy.  The only parameter link is the bootstrap loss `A√(2δ) < η`. -/
theorem twistAlmostRealDichotomy_of_inputs {A : ℕ} {η δ K : ℝ} {T : ℕ → ℝ}
    (harch : ArchimedeanCorrelationBoundAbove A η T) (he : SmallShiftAlmostReal A K T)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hboot : (A : ℝ) * Real.sqrt (2 * δ) < η) :
    TwistAlmostRealDichotomy A δ K := by
  classical
  obtain ⟨Xa, hXa2, hXa⟩ := harch
  obtain ⟨Xe, hXe2, hXe⟩ := he
  set G : ℝ := η - (A : ℝ) * Real.sqrt (2 * δ) with hG
  have hGpos : 0 < G := by rw [hG]; linarith
  obtain ⟨Xm, hXm2, hXm⟩ := exists_primeMass_ge ((2 * primeMass A + 1) / G)
  refine ⟨max (max Xa Xe) Xm, le_trans hXa2 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro X hX q hq hqA χ t ht
  have hXXa : Xa ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXXe : Xe ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXXm : Xm ≤ X := le_trans (le_max_right _ _) hX
  have hX2 : 2 ≤ X := le_trans hXa2 hXXa
  have hMnn : 0 ≤ primeMass X := primeMass_nonneg X
  by_cases hsmall : |t| ≤ T X
  · exact Or.inl (hXe X hXXe q hq hqA χ t hsmall)
  · right
    rw [not_le] at hsmall
    set k : ℕ := q.totient with hk
    have hk1 : 1 ≤ k := Nat.totient_pos.mpr hq
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkA : (k : ℝ) ≤ (A : ℝ) := by
      exact_mod_cast le_trans (Nat.totient_le q) hqA
    have habs : |(k : ℝ) * t| = (k : ℝ) * |t| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ))]
    have hfreq : T X < |(k : ℝ) * t| := by
      rw [habs]
      nlinarith [abs_nonneg t]
    have hvup : |(k : ℝ) * t| ≤ (A : ℝ) * (A : ℝ) * X := by
      rw [habs]
      have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
      have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
      calc (k : ℝ) * |t| ≤ (A : ℝ) * ((A : ℝ) * X) :=
            mul_le_mul hkA ht (abs_nonneg t) hAnn
        _ = (A : ℝ) * (A : ℝ) * X := by ring
    refine norm_twistCorr_le_of_archCorr_le χ hq t hX2 hδ0.le hδ1
      (hXa X hXXa ((k : ℝ) * t) hfreq hvup) ?_
    -- the bootstrap slack, from `M(X)` large
    have hbig : (2 * primeMass A + 1) / G ≤ primeMass X := hXm X hXXm
    have hGM : 2 * primeMass A + 1 ≤ G * primeMass X := by
      rw [div_le_iff₀ hGpos] at hbig; linarith [hbig]
    have hsqrt : (0 : ℝ) ≤ Real.sqrt (2 * δ) := Real.sqrt_nonneg _
    have hkle : (k : ℝ) * Real.sqrt (2 * δ) * primeMass X
        ≤ (A : ℝ) * Real.sqrt (2 * δ) * primeMass X := by
      have : (k : ℝ) * Real.sqrt (2 * δ) ≤ (A : ℝ) * Real.sqrt (2 * δ) :=
        mul_le_mul_of_nonneg_right hkA hsqrt
      exact mul_le_mul_of_nonneg_right this hMnn
    have hmq : primeMass q ≤ primeMass A := primeMass_mono hqA
    have hGexp : G * primeMass X = η * primeMass X - (A : ℝ) * Real.sqrt (2 * δ) * primeMass X := by
      rw [hG]; ring
    rw [hGexp] at hGM
    linarith

/-- For each level, a `δ` small enough that the bootstrap loss fits inside `η`. -/
theorem exists_delta_twistAlmostRealDichotomy {η : ℝ} (hη : 0 < η) {T : ℕ → ℝ}
    (harch : ∀ A : ℕ, ArchimedeanCorrelationBoundAbove A η T)
    (he : ∀ A : ℕ, ∃ K : ℝ, SmallShiftAlmostReal A K T) (A : ℕ) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ TwistAlmostRealDichotomy A δ K := by
  obtain ⟨K, heA⟩ := he A
  have hApos : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  set R : ℝ := η / (2 * ((A : ℝ) + 1)) with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  set δ : ℝ := min (1 / 2) (R ^ 2 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hboot : (A : ℝ) * Real.sqrt (2 * δ) < η := by
    have h2δ : 2 * δ ≤ R ^ 2 := by
      have : δ ≤ R ^ 2 / 2 := min_le_right _ _
      linarith
    have hsq : Real.sqrt (2 * δ) ≤ R := by
      have := Real.sqrt_le_sqrt h2δ
      rwa [Real.sqrt_sq hRpos.le] at this
    have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    have hmul : (A : ℝ) * Real.sqrt (2 * δ) ≤ (A : ℝ) * R :=
      mul_le_mul_of_nonneg_left hsq hAnn
    have hAR : (A : ℝ) * R < η := by
      rw [hR, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  exact ⟨δ, K, hδ0, hδ1.le, twistAlmostRealDichotomy_of_inputs (harch A) heA hδ0 hδ1 hboot⟩

/-- **THE PAYOFF, on the repaired inputs.**  C1's two-point leaf in logarithmic average, for every
`ζ = e(t/b) ≠ 1`, granted only

* (c′) `ArchimedeanCorrelationBoundAbove` — the Archimedean bound *above* the threshold `T`, and
* (e) `SmallShiftAlmostReal` — Mertens for characters *below* it.

Everything else is machine-checked.  Compare
`ElliottCharRigidity.twoPointElliottLog_of_archimedean_and_density`, which is vacuous: its
Archimedean hypothesis is refuted by
`ElliottArchimedeanRefuted.not_archimedeanCorrelationBound`. -/
theorem twoPointElliottLog_of_repaired_inputs {b p q : ℕ} {t : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hu : (phase (t / b)).re < 1) {η : ℝ} (hη : 0 < η) {T : ℕ → ℝ}
    (harch : ∀ A : ℕ, ArchimedeanCorrelationBoundAbove A η T)
    (he : ∀ A : ℕ, ∃ K : ℝ, SmallShiftAlmostReal A K T) :
    TwoPointElliottLog b p q t :=
  twoPointElliottLog_of_nonPretentious hp hq hpq
    (uniformlyNonPretentious_zetaOmega_of_almostReal hu
      (exists_delta_twistAlmostRealDichotomy hη harch he))

end

end NormalNumbers.ElliottTwistRepair
