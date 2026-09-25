/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtKPoint

/-!
# The merely-multiplicative anchor — the bridge is a hypothesis artefact

**Lap 60 (deep reflection) finding R1.**  `Erdos67b.IsMultiplicativeOnPositiveInt`
(`Erdos67b/LogElliott.lean:329`) reads

    g 1 = 1 ∧ ∀ m n : ℕ, 0 < m → 0 < n → g ((m * n : ℕ) : ℤ) = g m * g n

with **no coprimality clause**: despite its name it is *complete* multiplicativity.  `ζ^ω`
fails it (`ω(p²) = 1`), which is why lap 4 built `C3MrtOmegaBridge`'s powerful-divisor
expansion `z^ω = z^Ω ⋆ g`, and why `prod_le_lcm_mul_pow`'s `K^{K²}`, the lap-40 budget repair
and the decay class `exp(−C(log log log N)⁴)` entered the ledger at all.

Elliott's conjecture — and Tao's Theorem 1.3, which the dependency is formalising — ask only
for **multiplicative**.  This file installs that hypothesis class and shows what it buys.

## What is here

* `IsCoprimeMultiplicativeInt` — Elliott's actual hypothesis: `g(mn) = g(m)g(n)` for *coprime*
  positive `m, n`.  `isCoprimeMultiplicativeInt_of_completely` : the dependency's predicate
  implies it, so `KPointLogElliottMult` is a **strengthening**, never a weakening.
* `zOmegaInt z` — `z^{ω}` extended by zero off the positives; `isCoprimeMultiplicativeInt_zOmegaInt`,
  `norm_zOmegaInt_le_one`.
* `pretentiousDistSqToTwist_zOmegaInt_eq` — **the certificate transfers verbatim**: the
  pretentious distance is a sum over *primes*, and `ω(p) = Ω(p) = 1`, so `ζ^ω` and `ζ^Ω` have
  literally the same distance to every Dirichlet–Archimedean twist.  Hence
  `nonPretentious_zOmega`, the laps 18–21 archimedean certificate for `ζ^ω`, at zero extra cost.
* `KPointLogElliottMult K` and `kPointLogElliott_of_mult`.
* **The decisive probe.**  `nondegenerateForms_class` : the affine forms `M₀·n + (r+i+1)` are
  pairwise nondegenerate with determinant `M₀(j−i)`, for *any* `M₀ > 0`; and
  `kPointLogCorrelation_zOmega` : the class-restricted `K`-point sum along `n ≡ r (mod M₀)`
  **is** `kPointLogCorrelation` of `zOmegaInt` along those forms.  Therefore
  `class_window_bound_of_mult` : on `KPointLogElliottMult K` the window bound holds with

      no divisor tuples, no truncation, no tuple mass, no lcm, and no `K^{K²}`.

  Compare the route it replaces: `C3MrtOmegaBridge` → `C3MrtMultiForms` → `C3MrtMultiMass` →
  `C3MrtMultiTupleMass` → `C3MrtMultiTrunc` → `C3MrtMultiInner` → `C3MrtProgForms` →
  `C3MrtProgTrunc` → `C3MrtProgInner`, whose entire purpose is to get `ζ^ω` into a
  *completely* multiplicative statement.

Nothing here weakens or replaces anything: the powerful-divisor stack stays in `src/`,
sorry-free, as the correct route *for completely multiplicative inputs*.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-! ## Elliott's actual hypothesis class -/

/-- **Multiplicativity on coprime positive integers** — the hypothesis of Elliott's conjecture
and of Tao's Theorem 1.3, as opposed to the *complete* multiplicativity that
`Erdos67b.IsMultiplicativeOnPositiveInt` demands. -/
def IsCoprimeMultiplicativeInt (g : ℤ → ℂ) : Prop :=
  g 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n →
      g ((m * n : ℕ) : ℤ) = g m * g n

/-- The dependency's predicate is *stronger*: complete multiplicativity implies coprime
multiplicativity. -/
theorem isCoprimeMultiplicativeInt_of_completely {g : ℤ → ℂ}
    (hg : Erdos67b.IsMultiplicativeOnPositiveInt g) : IsCoprimeMultiplicativeInt g :=
  ⟨hg.1, fun m n hm hn _ => hg.2 m n hm hn⟩

/-! ## `ζ^ω` as an admissible Elliott input -/

/-- `z^{ω}`, extended to `ℤ` by zero off the positives. -/
noncomputable def zOmegaInt (z : ℂ) : ℤ → ℂ :=
  Erdos67b.positiveIntExtension (fun n : ℕ => z ^ omegaNat n)

@[simp] lemma zOmegaInt_natCast (z : ℂ) {n : ℕ} (hn : 0 < n) :
    zOmegaInt z (n : ℤ) = z ^ omegaNat n :=
  Erdos67b.positiveIntExtension_natCast hn

/-- `ω` is additive on coprime arguments. -/
lemma omegaNat_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    omegaNat (m * n) = omegaNat m + omegaNat n := by
  classical
  have hdisj : Disjoint m.primeFactors n.primeFactors :=
    Nat.Coprime.disjoint_primeFactors h
  rw [omegaNat, omegaNat, omegaNat, Nat.primeFactors_mul hm.ne' hn.ne',
    Finset.card_union_of_disjoint hdisj]

/-- **`ζ^ω` is an admissible Elliott input** — it is multiplicative on coprime arguments
(and is *not* completely multiplicative, which is the whole point). -/
theorem isCoprimeMultiplicativeInt_zOmegaInt (z : ℂ) :
    IsCoprimeMultiplicativeInt (zOmegaInt z) := by
  refine ⟨?_, fun m n hm hn hmn => ?_⟩
  · have : ((1 : ℕ) : ℤ) = (1 : ℤ) := by norm_num
    rw [← this, zOmegaInt_natCast z Nat.one_pos]
    simp [omegaNat]
  · rw [zOmegaInt_natCast z (Nat.mul_pos hm hn), zOmegaInt_natCast z hm,
      zOmegaInt_natCast z hn, omegaNat_mul_coprime hm hn hmn, pow_add]

theorem norm_zOmegaInt_le_one {z : ℂ} (hz : ‖z‖ = 1) (n : ℤ) : ‖zOmegaInt z n‖ ≤ 1 := by
  rw [zOmegaInt, Erdos67b.positiveIntExtension]
  by_cases h : 0 < n
  · rw [if_pos h, norm_pow, hz, one_pow]
  · rw [if_neg h, norm_zero]; norm_num

/-! ## The archimedean certificate transfers verbatim

`pretentiousDistSq` is a sum over *primes*, and `ω(p) = Ω(p) = 1`.  So `ζ^ω` and `ζ^Ω` are at
literally the same distance from every Dirichlet–Archimedean twist, and laps 18–21 apply to the
merely-multiplicative anchor without a single extra estimate. -/

lemma restrictToNat_zOmegaInt_prime {z : ℂ} {p : ℕ} (hp : p.Prime) :
    Erdos67b.restrictToNat (zOmegaInt z) p = z := by
  rw [Erdos67b.restrictToNat, zOmegaInt_natCast z hp.pos, omegaNat,
    Nat.Prime.primeFactors hp]
  simp

/-- **The certificate transfers verbatim.**  `ζ^ω` and `ζ^Ω` have the *same* pretentious
distance to every twist, because the distance sees a function only at the primes. -/
theorem pretentiousDistSqToTwist_zOmegaInt_eq (z : ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) :
    Erdos67b.pretentiousDistSqToTwist (Erdos67b.restrictToNat (zOmegaInt z)) χ t X
      = Erdos67b.pretentiousDistSqToTwist (Erdos67b.restrictToNat (zOmInt z)) χ t X := by
  rw [Erdos67b.pretentiousDistSqToTwist, Erdos67b.pretentiousDistSqToTwist,
    Erdos67b.pretentiousDistSq, Erdos67b.pretentiousDistSq]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp : p.Prime := (Erdos67b.mem_primesUpTo.mp hp).1
  rw [Erdos67b.pretentiousTerm, Erdos67b.pretentiousTerm,
    restrictToNat_zOmegaInt_prime (z := z) hpp, restrictToNat_zOmInt_prime (z := z) hpp]

/-- **The archimedean non-pretentiousness certificate for `ζ^ω`** — laps 18–21 at zero extra
cost, on the same named Vinogradov–Korobov input. -/
theorem nonPretentious_zOmega {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {A : ℕ} {T : ℝ}
    (hsave : TwistedPrimeSumSaving A T) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| ≤ (A : ℝ) * X →
        (A : ℝ) ≤ Erdos67b.pretentiousDistSqToTwist
          (Erdos67b.restrictToNat (zOmegaInt z)) χ t X := by
  obtain ⟨X₀, hX₀⟩ := nonPretentious_zOm hz hz1 hsave
  refine ⟨X₀, fun X hX q hq hqA χ t ht => ?_⟩
  rw [pretentiousDistSqToTwist_zOmegaInt_eq]
  exact hX₀ X hX q hq hqA χ t ht

/-! ## The `K`-point statement on Elliott's own hypothesis class -/

/-- **The `K`-point log-Elliott conjecture on merely multiplicative inputs.**  `KPointLogElliott`
verbatim, with `IsCoprimeMultiplicativeInt` in place of the dependency's complete-multiplicativity
predicate.  This is the literature's own hypothesis class. -/
def KPointLogElliottMult (K : ℕ) : Prop :=
  ∀ (a : Fin K → ℕ) (b : Fin K → ℤ), NondegenerateForms a b →
    ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
        ∀ g : Fin K → ℤ → ℂ,
          (∀ i, IsCoprimeMultiplicativeInt (g i)) →
          (∀ i, ∀ n : ℤ, ‖g i n‖ ≤ 1) →
          (∀ i : Fin K, (i : ℕ) = 0 → ∀ q : ℕ, 0 < q → q ≤ A →
            ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| ≤ (A : ℝ) * X →
              (A : ℝ) ≤ Erdos67b.pretentiousDistSqToTwist
                (Erdos67b.restrictToNat (g i)) χ t X) →
          ‖kPointLogCorrelation g a b X W‖ ≤ ε * Real.log W

/-- **Nothing is weakened.**  The merely-multiplicative statement is *stronger*: it applies to
more functions, so it implies the completely-multiplicative one, and every existing ledger row
and consumer survives verbatim. -/
theorem kPointLogElliott_of_mult {K : ℕ} (H : KPointLogElliottMult K) : KPointLogElliott K := by
  intro a b hnd ε hε
  obtain ⟨A₀, hA₀2, hA₀⟩ := H a b hnd ε hε
  exact ⟨A₀, hA₀2, fun A X W hA hAW hWX g hmul hbd hpret =>
    hA₀ A X W hA hAW hWX g (fun i => isCoprimeMultiplicativeInt_of_completely (hmul i)) hbd hpret⟩

/-! ## The decisive probe: the class-restricted `K`-point sum IS a `kPointLogCorrelation` -/

/-- **Nondegeneracy is automatic along a progression, for every modulus.**  The forms
`M₀·n + (r+i+1)`, `i < K`, have pairwise determinant `M₀·(j−i) ≠ 0`. -/
theorem nondegenerateForms_class {K : ℕ} {M₀ : ℕ} (hM : 0 < M₀) (r : ℕ) :
    NondegenerateForms (fun _ : Fin K => M₀) (fun i : Fin K => ((r + (i : ℕ) + 1 : ℕ) : ℤ)) := by
  refine ⟨fun _ => hM, fun i j hij => ?_⟩
  have hne : ((i : ℕ) : ℤ) ≠ ((j : ℕ) : ℤ) := by
    exact_mod_cast fun hc => hij (Fin.ext hc)
  have : (M₀ : ℤ) * ((r + (j : ℕ) + 1 : ℕ) : ℤ) - (M₀ : ℤ) * ((r + (i : ℕ) + 1 : ℕ) : ℤ)
      = (M₀ : ℤ) * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) := by push_cast; ring
  rw [this]
  exact mul_ne_zero (by exact_mod_cast hM.ne') (sub_ne_zero.mpr hne.symm)

/-- **The decisive identity.**  The class-restricted `K`-point sum in the progression variable
is *literally* `kPointLogCorrelation` of `zOmegaInt` along the forms `M₀·n + (r+i+1)`.

No divisor tuples, no truncation, no `lcm`, no `K^{K²}`: the substitution `n ↦ M₀·n + r` is the
whole reduction. -/
theorem kPointLogCorrelation_zOmega {K : ℕ} (M₀ r X W : ℕ) (z : ℕ → ℂ) :
    kPointLogCorrelation (fun i : Fin K => zOmegaInt (z (i : ℕ)))
        (fun _ : Fin K => M₀) (fun i : Fin K => ((r + (i : ℕ) + 1 : ℕ) : ℤ)) X W
      = ∑ n ∈ Erdos67b.elliottLogWindow X W,
          (Erdos67b.harmonicWeight n : ℂ) *
            ∏ i : Fin K, (z (i : ℕ)) ^ omegaNat (M₀ * n + (r + (i : ℕ) + 1)) := by
  rw [kPointLogCorrelation]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Erdos67b.integerAffine]
  have hcast : (M₀ : ℤ) * (n : ℤ) + ((r + (i : ℕ) + 1 : ℕ) : ℤ)
      = ((M₀ * n + (r + (i : ℕ) + 1) : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, zOmegaInt_natCast _ (by positivity)]

/-- **What the merely-multiplicative anchor buys, in one step.**  On `KPointLogElliottMult K`,
the class-restricted `K`-point correlation of `ζ^ω` over the window obeys the `ε·log W` bound —
with the powerful-divisor stack of `C3MrtOmegaBridge` … `C3MrtProgInner` entirely bypassed. -/
theorem class_window_bound_of_mult {K : ℕ} (H : KPointLogElliottMult K)
    {M₀ : ℕ} (hM : 0 < M₀) (r : ℕ) (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (hz01 : z 0 ≠ 1)
    {A : ℕ} {T : ℝ} (hsave : TwistedPrimeSumSaving A T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ X₀ : ℕ, 2 ≤ A₀ ∧ ∀ X W : ℕ, X₀ ≤ X → A₀ ≤ A → A ≤ W → W ≤ X →
      ‖∑ n ∈ Erdos67b.elliottLogWindow X W,
          (Erdos67b.harmonicWeight n : ℂ) *
            ∏ i : Fin K, (z (i : ℕ)) ^ omegaNat (M₀ * n + (r + (i : ℕ) + 1))‖
        ≤ ε * Real.log W := by
  obtain ⟨A₀, hA₀2, hA₀⟩ := H _ _ (nondegenerateForms_class (K := K) hM r) ε hε
  obtain ⟨X₀, hX₀⟩ := nonPretentious_zOmega (hz 0) hz01 hsave
  refine ⟨A₀, X₀, hA₀2, fun X W hX hA hAW hWX => ?_⟩
  rw [← kPointLogCorrelation_zOmega]
  refine hA₀ A X W hA hAW hWX _ (fun i => isCoprimeMultiplicativeInt_zOmegaInt _)
    (fun i n => norm_zOmegaInt_le_one (hz _) n) ?_
  intro i hi q hq hqA χ t ht
  have : (i : ℕ) = 0 := hi
  rw [this]
  exact hX₀ X hX q hq hqA χ t ht

#print axioms class_window_bound_of_mult

end CastingOut

end NormalNumbers
