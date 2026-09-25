import ErdosProblems.Erdos67b.ElliottComplete

/-!
# A ladder of intermediate statements towards Tao's general two-point log-Elliott theorem

The dependency `lean-proofs-latest` proves `Erdos67b.unitCircleLogElliott`, the special case of
Tao 2016, Theorem 1.3 with

* `a₁ = a₂ = 1`, `b₁ = 0`, `b₂ = h` (a pure shift),
* `g₁ = f` **completely** multiplicative with `‖f n‖ = 1`,
* `g₂ = conj f`.

The general statement `Erdos67b.NonasymptoticLogElliott` relaxes three things at once.  This file
freezes the intermediate rungs so that each relaxation is a separate, named obligation.

## The rungs

* `DilatedCMLogElliott` — **the crux.**  Two *independent* completely multiplicative unimodular
  functions `f₁, f₂`, non-pretentiousness on `f₁` only, and the two affine forms share a common
  dilation: `a*n + c₁` and `a*n + c₂` with `c₁ ≠ c₂`.
* `AffineCMLogElliott` — the same, but with genuinely independent dilations `a₁, a₂` (i.e. Tao's
  full affine generality) while the functions stay completely multiplicative and unimodular.
* `Erdos67b.NonasymptoticLogElliott` — the full theorem: `g₁, g₂` merely multiplicative and
  `1`-bounded.

## What is proved here

`affineCM_of_dilatedCM` : `DilatedCMLogElliott → AffineCMLogElliott`, with no remaining gap.  The
observation is that for a **completely multiplicative** `f₁` one has
`f₁(a₂ · (a₁ n + b₁)) = f₁(a₂) · f₁(a₁ n + b₁)`, so multiplying the first form by `a₂` and the
second by `a₁` turns the pair `(a₁n+b₁, a₂n+b₂)` into the common-dilation pair
`(a n + a₂b₁, a n + a₁b₂)` with `a = a₁a₂`, at the cost of the *unimodular* constant
`f₁(a₂) f₂(a₁)`, which does not move the norm at all.  The determinant hypothesis
`a₁b₂ - a₂b₁ ≠ 0` is exactly the requirement `a₂b₁ ≠ a₁b₂` that the two new shifts differ.

So Tao's affine generality is **free** on the completely multiplicative unimodular rung: the whole
difficulty of the general theorem is (i) the crux `DilatedCMLogElliott` (which is where the two
independent functions and the common dilation have to be pushed through the entropy-decrement /
graph / MRT machinery) and (ii) the passage from `1`-bounded multiplicative to completely
multiplicative unimodular.

See `KICKOFF-2026-09-24-elliott-general.md` and `HANDOFF-elliott-*.md`.
-/

open scoped BigOperators ComplexConjugate

namespace NormalNumbers.ElliottLadder

open Erdos67b

noncomputable section

/-! ## The rungs -/

/-- **The crux rung.**  Tao's two-point logarithmic Elliott bound for two independent completely
multiplicative unimodular functions against a pair of affine forms with a *common* dilation.

This is the statement the graph/Fourier + MRT + entropy-decrement machinery of
`Erdos67b.unitCircleLogElliott` has to be re-run for: the prime dilation `n ↦ p·n` sends the pair
`(a n + c₁, a n + c₂)` to `(a p n + p c₁, a p n + p c₂)`, whose shift difference is `p·(c₂-c₁)`,
exactly as in the `h ↦ p h` step of the shift case, and the dilation constant picked up is
`f₁(p) f₂(p)`, of modulus one. -/
def DilatedCMLogElliott : Prop :=
  ∀ (a : ℕ) (c₁ c₂ : ℤ), 0 < a → c₁ ≠ c₂ →
    ∀ ε : ℝ, 0 < ε →
      ∃ A₀ : ℕ, 2 ≤ A₀ ∧
        ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
          ∀ f₁ f₂ : ℕ → ℂ,
            IsCompletelyMultiplicativeOnPositive f₁ →
            IsCompletelyMultiplicativeOnPositive f₂ →
            (∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) →
            (∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1) →
            MRTNonpretentious f₁ A X →
            ‖elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂)
                a a c₁ c₂ X W‖ ≤ ε * Real.log W

/-- Tao's full affine generality, still for completely multiplicative unimodular functions. -/
def AffineCMLogElliott : Prop :=
  ∀ (a₁ a₂ : ℕ) (b₁ b₂ : ℤ),
    0 < a₁ → 0 < a₂ → (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ A₀ : ℕ, 2 ≤ A₀ ∧
        ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
          ∀ f₁ f₂ : ℕ → ℂ,
            IsCompletelyMultiplicativeOnPositive f₁ →
            IsCompletelyMultiplicativeOnPositive f₂ →
            (∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) →
            (∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1) →
            MRTNonpretentious f₁ A X →
            ‖elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂)
                a₁ a₂ b₁ b₂ X W‖ ≤ ε * Real.log W

/-! ## Pulling a natural factor out of a positive-integer extension -/

/-- A completely multiplicative function extended by zero off the positive integers still pulls a
positive natural factor out of an arbitrary *integer* argument: at nonpositive arguments both sides
vanish. -/
theorem positiveIntExtension_natMul {f : ℕ → ℂ}
    (hf : IsCompletelyMultiplicativeOnPositive f) {q : ℕ} (hq : 0 < q) (m : ℤ) :
    positiveIntExtension f ((q : ℤ) * m) = f q * positiveIntExtension f m := by
  by_cases hm : 0 < m
  · have hqm : 0 < (q : ℤ) * m := mul_pos (by exact_mod_cast hq) hm
    have htoNat : ((q : ℤ) * m).toNat = q * m.toNat := by
      have : (((q : ℤ) * m).toNat : ℤ) = ((q * m.toNat : ℕ) : ℤ) := by
        push_cast
        rw [Int.toNat_of_nonneg hqm.le, Int.toNat_of_nonneg hm.le]
      exact_mod_cast this
    rw [positiveIntExtension, if_pos hqm, positiveIntExtension, if_pos hm, htoNat,
      hf.2 q m.toNat hq (by omega)]
  · have hqm : ¬ (0 < (q : ℤ) * m) := by
      have hm' : m ≤ 0 := not_lt.mp hm
      have hq' : (0 : ℤ) ≤ (q : ℤ) := by positivity
      exact not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hq' hm')
    rw [positiveIntExtension, if_neg hqm, positiveIntExtension, if_neg hm, mul_zero]

/-- Multiplying the affine form `a₁ n + b₁` by `a₂` gives the common-dilation form. -/
theorem integerAffine_mul (a₁ a₂ : ℕ) (b₁ : ℤ) (n : ℕ) :
    integerAffine (a₁ * a₂) ((a₂ : ℤ) * b₁) n = (a₂ : ℤ) * integerAffine a₁ b₁ n := by
  simp only [integerAffine]
  push_cast
  ring

/-! ## The affine generalisation is free on the completely multiplicative unimodular rung -/

/-- The common-dilation correlation differs from the fully affine one only by the unimodular
constant `f₁(a₂) · f₂(a₁)`. -/
theorem elliottLogCorrelation_common_dilation {f₁ f₂ : ℕ → ℂ}
    (h₁ : IsCompletelyMultiplicativeOnPositive f₁)
    (h₂ : IsCompletelyMultiplicativeOnPositive f₂)
    {a₁ a₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (b₁ b₂ : ℤ) (X W : ℕ) :
    elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂)
        (a₁ * a₂) (a₁ * a₂) ((a₂ : ℤ) * b₁) ((a₁ : ℤ) * b₂) X W =
      (f₁ a₂ * f₂ a₁) *
        elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂)
          a₁ a₂ b₁ b₂ X W := by
  rw [elliottLogCorrelation, elliottLogCorrelation, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have e₁ : integerAffine (a₁ * a₂) ((a₂ : ℤ) * b₁) n = (a₂ : ℤ) * integerAffine a₁ b₁ n :=
    integerAffine_mul a₁ a₂ b₁ n
  have e₂ : integerAffine (a₁ * a₂) ((a₁ : ℤ) * b₂) n = (a₁ : ℤ) * integerAffine a₂ b₂ n := by
    simp only [integerAffine]
    push_cast
    ring
  rw [e₁, e₂, positiveIntExtension_natMul h₁ ha₂, positiveIntExtension_natMul h₂ ha₁]
  ring

/-- **Tao's affine generality is free on the completely multiplicative unimodular rung.** -/
theorem affineCM_of_dilatedCM (h : DilatedCMLogElliott) : AffineCMLogElliott := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hdet ε hε
  have hne : (a₂ : ℤ) * b₁ ≠ (a₁ : ℤ) * b₂ := by
    intro hEq
    exact hdet (by rw [← hEq]; ring)
  obtain ⟨A₀, hA₀, hmain⟩ :=
    h (a₁ * a₂) ((a₂ : ℤ) * b₁) ((a₁ : ℤ) * b₂) (Nat.mul_pos ha₁ ha₂) hne ε hε
  refine ⟨A₀, hA₀, ?_⟩
  intro A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
  have hres := hmain A X W hA hAW hWX f₁ f₂ hm₁ hm₂ hu₁ hu₂ hpret
  rw [elliottLogCorrelation_common_dilation hm₁ hm₂ ha₁ ha₂ b₁ b₂ X W, norm_mul, norm_mul,
    hu₁ a₂ ha₂, hu₂ a₁ ha₁, one_mul, one_mul] at hres
  exact hres

/-! ## Sanity anchor: the crux rung recovers the proved special case -/

/-- The crux rung implies the special case already proved in the dependency.  This is a faithfulness
check that `DilatedCMLogElliott` is genuinely a generalisation of `Erdos67b.unitCircleLogElliott`
and not an accidentally weaker statement. -/
theorem unitCircle_of_dilatedCM (h : DilatedCMLogElliott) : UnitCircleLogElliott := by
  intro ε hε k hk
  obtain ⟨A₀, hA₀, hmain⟩ :=
    affineCM_of_dilatedCM h 1 1 0 (k : ℤ) one_pos one_pos (by
      simpa using (by exact_mod_cast hk.ne' : (k : ℤ) ≠ 0)) ε hε
  refine ⟨A₀, hA₀, ?_⟩
  intro A X W hA hAW hWX f hmul hunit hpret
  have hconjMul : IsCompletelyMultiplicativeOnPositive (fun n ↦ conj (f n)) :=
    conj_isCompletelyMultiplicativeOnPositive hmul
  have hconjUnit : ∀ n : ℕ, 0 < n → ‖conj (f n)‖ = 1 := by
    intro n hn; rw [Complex.norm_conj]; exact hunit n hn
  have hpret' : MRTNonpretentious f A X := by
    intro q hq hqA χ t ht
    exact hpret q hq hqA χ t ht
  have hres := hmain A X W hA hAW hWX f (fun n ↦ conj (f n)) hmul hconjMul hunit hconjUnit hpret'
  rwa [elliottLogCorrelation_positiveIntExtension] at hres

/-! ## The two-function pair observable and its dilation phase

This section pins down, at the level of the compiler, *where* the two-function generality bites.
-/

/-- The two-function, common-dilation pair observable whose logarithmic average is the correlation
bounded by `DilatedCMLogElliott`. -/
def pairObservable (f₁ f₂ : ℕ → ℂ) (a : ℕ) (c₁ c₂ : ℤ) (n : ℕ) : ℂ :=
  positiveIntExtension f₁ (integerAffine a c₁ n) * positiveIntExtension f₂ (integerAffine a c₂ n)

theorem norm_pairObservable_le_one {f₁ f₂ : ℕ → ℂ}
    (h₁ : ∀ n : ℕ, 0 < n → ‖f₁ n‖ ≤ 1) (h₂ : ∀ n : ℕ, 0 < n → ‖f₂ n‖ ≤ 1)
    (a : ℕ) (c₁ c₂ : ℤ) (n : ℕ) : ‖pairObservable f₁ f₂ a c₁ c₂ n‖ ≤ 1 := by
  rw [pairObservable, norm_mul]
  have b₁ := norm_positiveIntExtension_le_one h₁ (integerAffine a c₁ n)
  have b₂ := norm_positiveIntExtension_le_one h₂ (integerAffine a c₂ n)
  simpa using mul_le_mul b₁ b₂ (norm_nonneg _) zero_le_one

theorem elliottLogCorrelation_eq_pairObservable (f₁ f₂ : ℕ → ℂ)
    (a : ℕ) (c₁ c₂ : ℤ) (X W : ℕ) :
    elliottLogCorrelation (positiveIntExtension f₁) (positiveIntExtension f₂) a a c₁ c₂ X W =
      ∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * pairObservable f₁ f₂ a c₁ c₂ n := by
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [pairObservable, mul_assoc]

/-- **The dilation identity for two independent functions picks up a phase.**

Compare `Erdos67b.unit_pair_dilation`, where `f₂ = conj f₁` makes the phase `f(q) conj (f q) = 1`
identically.  Here the constant `f₁(q) f₂(q)` is unimodular but *varies with `q`*, and the prime
graph lower bound (`Erdos67b.exists_logProb_dyadic_primeGraphMean_lower`, via
`Erdos67b.primeGraphMean`, which is a **complex** sum over primes and not a sum of norms) needs all
its edges to contribute the *same* correlation.  So the two-function generality is genuinely new
content, not a free relabelling. -/
theorem pairObservable_dilation {f₁ f₂ : ℕ → ℂ}
    (h₁ : IsCompletelyMultiplicativeOnPositive f₁)
    (h₂ : IsCompletelyMultiplicativeOnPositive f₂)
    {a q : ℕ} (hq : 0 < q) (c₁ c₂ : ℤ) (n : ℕ) :
    pairObservable f₁ f₂ a ((q : ℤ) * c₁) ((q : ℤ) * c₂) (q * n) =
      (f₁ q * f₂ q) * pairObservable f₁ f₂ a c₁ c₂ n := by
  have e₁ : integerAffine a ((q : ℤ) * c₁) (q * n) = (q : ℤ) * integerAffine a c₁ n := by
    simp only [integerAffine]; push_cast; ring
  have e₂ : integerAffine a ((q : ℤ) * c₂) (q * n) = (q : ℤ) * integerAffine a c₂ n := by
    simp only [integerAffine]; push_cast; ring
  rw [pairObservable, pairObservable, e₁, e₂,
    positiveIntExtension_natMul h₁ hq, positiveIntExtension_natMul h₂ hq]
  ring

/-- **The fix: twist each graph edge by the conjugate of its own phase.**

Because `‖f₁(q) f₂(q)‖ = 1`, multiplying the `q`-dilated observable by `conj (f₁(q) f₂(q))` restores
the *exact* equality that `Erdos67b.unit_pair_dilation` provides in the proved case.  The twist is a
**known**, explicitly computable unimodular weight attached to the prime `q`, so inserting it into
the prime graph is legitimate; the whole content of the crux is that the graph/Fourier/entropy
machinery tolerates a per-prime unimodular weight — see `dilatedCMLogElliott`. -/
theorem pairObservable_dilation_twisted {f₁ f₂ : ℕ → ℂ}
    (h₁ : IsCompletelyMultiplicativeOnPositive f₁)
    (h₂ : IsCompletelyMultiplicativeOnPositive f₂)
    (hu₁ : ∀ n : ℕ, 0 < n → ‖f₁ n‖ = 1) (hu₂ : ∀ n : ℕ, 0 < n → ‖f₂ n‖ = 1)
    {a q : ℕ} (hq : 0 < q) (c₁ c₂ : ℤ) (n : ℕ) :
    conj (f₁ q * f₂ q) *
        pairObservable f₁ f₂ a ((q : ℤ) * c₁) ((q : ℤ) * c₂) (q * n) =
      pairObservable f₁ f₂ a c₁ c₂ n := by
  have hnorm : ‖f₁ q * f₂ q‖ = 1 := by rw [norm_mul, hu₁ q hq, hu₂ q hq, one_mul]
  have hcancel : conj (f₁ q * f₂ q) * (f₁ q * f₂ q) = 1 := by
    rw [mul_comm, Complex.mul_conj', hnorm]
    norm_num
  rw [pairObservable_dilation h₁ h₂ hq, ← mul_assoc, hcancel, one_mul]

/-! ## The remaining obligation

The crux `DilatedCMLogElliott` is **not open here**.  Its two-function analytic content is proved
in `NormalNumbers.ElliottTwistedGraph.shiftCMLogElliott` (and its mirror), and the common dilation
`a` is handled by the `a`-dilated prime graph of `NormalNumbers.ElliottDilated*`; the proof lives
at `NormalNumbers.ElliottDilatedRung.dilatedCMLogElliott`, whose remaining leaves are the two
natural-shift rungs there.  (The earlier *dilation-slice* route of
`NormalNumbers.ElliottDilatedSlice` is refuted — see that file — and the headline no longer passes
through it.)  This file keeps only the statement and the free reductions off it.
-/

/-- **Open (from `1`-bounded multiplicative to completely multiplicative unimodular).**

Route, recorded so a later lap can split it further.  Let `g` be `1`-bounded multiplicative and set
`Σ(g) := ∑_{p ≤ X} (1 - ‖g p‖)/p`.

*Case A: `Σ(g₁)` large.*  Then `‖g₁‖` is a nonnegative `1`-bounded multiplicative function with
small logarithmic mean — Hall's inequality / the Wirsing–Halász bound in the *nonnegative* case,
which is elementary compared with Halász proper — and the correlation is bounded pointwise by
`‖g₁(a₁n+b₁)‖`, so the whole bound is trivial.  Only `g₁` needs this, matching the asymmetry of
Tao's hypothesis.

*Case B: `Σ(g₁)` bounded by `C`.*  Two separate reductions, both with **absolutely convergent**
`∑ 1/d` tails, so each is a finite sum of correlations plus an arbitrarily small tail:

* *multiplicative → completely multiplicative.*  With `g̃` the completely multiplicative function
  agreeing with `g` on the primes, `g = g̃ ⋆ u` where `u = g ⋆ (μ g̃)` is multiplicative, `u(p) = 0`,
  `‖u(p^k)‖ ≤ 2`; so `u` is supported on **squarefull** `d`, and `∑_{d squarefull} 1/d < ∞`.
  Expanding gives correlations of `g̃` along the sub-progressions `d ∣ a₁n+b₁`.
* *`1`-bounded → unimodular.*  For completely multiplicative `g̃` write `g̃ = ĝ · ‖g̃‖` pointwise with
  `ĝ(p) := g̃(p)/‖g̃(p)‖` (and `1` when `g̃(p) = 0`); `ĝ` is completely multiplicative unimodular.
  The nonnegative factor is expanded as `‖g̃‖ = 1 ⋆ v` with `v` multiplicative, `v(p) = ‖g̃(p)‖ - 1`,
  so `∑_d ‖v(d)‖/d ≤ exp(O(C))` converges *precisely because we are in Case B*.  Again the
  expansion produces correlations of `ĝ` along progressions `d ∣ m`.

Both expansions leave a divisibility constraint `d ∣ a_i n + b_i`, which is a *dilation* of the
affine form and is therefore absorbed by `AffineCMLogElliott` itself (replace `a_i, b_i` by the
solved progression), so no new AP-restricted machinery is needed.

Finally the non-pretentiousness hypothesis survives: from
`Re(ĝ(p)w) - Re(g̃(p)w) ≤ ‖ĝ(p) - g̃(p)‖ = 1 - ‖g̃(p)‖` one gets
`D(ĝ, χ n^{it}; X)² ≤ D(g̃, χ n^{it}; X)² + C`, and `C` is fixed while `A → ∞`; twisting by a
character of modulus dividing `d` only shifts `q` inside the range `q ≤ A` quantified over. -/
theorem nonasymptotic_of_affineCM (h : AffineCMLogElliott) :
    Erdos67b.NonasymptoticLogElliott := by
  sorry

end

end NormalNumbers.ElliottLadder
