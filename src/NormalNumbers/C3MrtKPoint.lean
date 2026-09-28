/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtArchimedean

/-!
# The `K`-point log-Elliott conjecture, and where the `D ≥ 3` rung has to come from

`rung_two_correlation` (`C3MrtArchimedean`) closes the `D = 2` rung of `ConjC3` on exactly two
named literature inputs, one of which is the dependency's own
`Erdos67b.NonasymptoticLogElliott`.  That statement is **strictly two-point**: two multiplicative
functions `g₁, g₂` along two affine forms.  The depth-`D` obligation of `ConjC3`
(`DepthElliott` / `QuantDepthElliott`) is a `D`-point correlation, so for `D ≥ 3` the dependency's
bet is *not* the input we need.

This file names the input that is, and settles its relation to the dependency's:

* `KPointLogElliott K` — the `K`-point version, in the dependency's own nonasymptotic shape
  (same window, same harmonic weight, same non-pretentiousness hypothesis on the first factor).
* `kPointLogElliott_two_iff` — at `K = 2` it is **equivalent** to
  `Erdos67b.NonasymptoticLogElliott`.  So `KPointLogElliott` is a faithful generalisation, not a
  differently-shaped guess: the `D = 2` rung of lap 33 is exactly the `K = 2` case.
* `kPointLogElliott_of_succ` — the hierarchy is **monotone downward**: `KPointLogElliott (K+2)`
  implies `KPointLogElliott (K+1)`.  Padding with the constant function `1` along a form
  `n + B` chosen nondegenerate against all the others is admissible (constant `1` is
  multiplicative and unimodular, and the non-pretentiousness hypothesis constrains only the
  *first* factor, which is untouched).

The consequence for the campaign: `KPointLogElliott 3` is a **strictly new** named input — it
implies `KPointLogElliott 2 ↔ NonasymptoticLogElliott` but nothing in the dependency implies it.
`KPointLogElliott 0` is *false* (the empty product is `1`, so the correlation is the full
logarithmic mass `≍ log W`), which is why the downward step is stated from `K + 2`.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- The unnormalised logarithmic `K`-point correlation, in the dependency's shape
(`Erdos67b.elliottLogCorrelation` is the `K = 2` case). -/
noncomputable def kPointLogCorrelation {K : ℕ} (g : Fin K → ℤ → ℂ)
    (a : Fin K → ℕ) (b : Fin K → ℤ) (X W : ℕ) : ℂ :=
  ∑ n ∈ Erdos67b.elliottLogWindow X W,
    (Erdos67b.harmonicWeight n : ℂ) *
      ∏ i : Fin K, g i (Erdos67b.integerAffine (a i) (b i) n)

/-- Pairwise nondegeneracy of a family of affine forms `a i · n + b i`: all leading coefficients
positive, and no two forms proportional. -/
def NondegenerateForms {K : ℕ} (a : Fin K → ℕ) (b : Fin K → ℤ) : Prop :=
  (∀ i, 0 < a i) ∧ ∀ i j : Fin K, i ≠ j → (a i : ℤ) * b j - (a j : ℤ) * b i ≠ 0

/-- **The `K`-point log-Elliott conjecture**, in `Erdos67b.NonasymptoticLogElliott`'s
nonasymptotic shape. -/
def KPointLogElliott (K : ℕ) : Prop :=
  ∀ (a : Fin K → ℕ) (b : Fin K → ℤ), NondegenerateForms a b →
    ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
        ∀ g : Fin K → ℤ → ℂ,
          (∀ i, Erdos67b.IsMultiplicativeOnPositiveInt (g i)) →
          (∀ i, ∀ n : ℤ, ‖g i n‖ ≤ 1) →
          (∀ i : Fin K, (i : ℕ) = 0 → ∀ q : ℕ, 0 < q → q ≤ A →
            ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| ≤ (A : ℝ) * X →
              (A : ℝ) ≤ Erdos67b.pretentiousDistSqToTwist
                (Erdos67b.restrictToNat (g i)) χ t X) →
          ‖kPointLogCorrelation g a b X W‖ ≤ ε * Real.log W

/-! ## `K = 2` is the dependency's statement -/

lemma kPointLogCorrelation_two (g : Fin 2 → ℤ → ℂ) (a : Fin 2 → ℕ) (b : Fin 2 → ℤ) (X W : ℕ) :
    kPointLogCorrelation g a b X W
      = Erdos67b.elliottLogCorrelation (g 0) (g 1) (a 0) (a 1) (b 0) (b 1) X W := by
  rw [kPointLogCorrelation, Erdos67b.elliottLogCorrelation]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Fin.prod_univ_two]
  ring

/-- **Faithfulness at `K = 2`.**  `KPointLogElliott 2` is exactly
`Erdos67b.NonasymptoticLogElliott`. -/
theorem kPointLogElliott_two_iff :
    KPointLogElliott 2 ↔ Erdos67b.NonasymptoticLogElliott := by
  constructor
  · intro H a₁ a₂ b₁ b₂ ha₁ ha₂ hdet ε hε
    have hnd : NondegenerateForms ![a₁, a₂] ![b₁, b₂] := by
      refine ⟨fun i => ?_, fun i j hij => ?_⟩
      · fin_cases i
        · simpa using ha₁
        · simpa using ha₂
      · fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · simpa using hdet
        · simpa [sub_ne_zero] using (sub_ne_zero.mp hdet).symm
        · exact absurd rfl hij
    obtain ⟨A₀, hA₀2, hA₀⟩ := H _ _ hnd ε hε
    refine ⟨A₀, hA₀2, fun A X W hA hAW hWX g₁ g₂ hm₁ hm₂ hb₁ hb₂ hpret => ?_⟩
    have hmain := hA₀ A X W hA hAW hWX ![g₁, g₂]
      (by
        intro i
        fin_cases i
        · simpa using hm₁
        · simpa using hm₂)
      (by
        intro i n
        fin_cases i
        · simpa using hb₁ n
        · simpa using hb₂ n)
      (by
        intro i hi q hq hqA χ t ht
        have hi' : i = 0 := by ext; simpa using hi
        subst hi'
        simpa using hpret q hq hqA χ t ht)
    rw [kPointLogCorrelation_two] at hmain
    simpa using hmain
  · intro H a b hnd ε hε
    obtain ⟨A₀, hA₀2, hA₀⟩ :=
      H (a 0) (a 1) (b 0) (b 1) (hnd.1 0) (hnd.1 1)
        (hnd.2 0 1 (by decide)) ε hε
    refine ⟨A₀, hA₀2, fun A X W hA hAW hWX g hm hbd hpret => ?_⟩
    rw [kPointLogCorrelation_two]
    exact hA₀ A X W hA hAW hWX (g 0) (g 1) (hm 0) (hm 1) (hbd 0) (hbd 1)
      (fun q hq hqA χ t ht => hpret 0 rfl q hq hqA χ t ht)

/-! ## The hierarchy is monotone downward

Padding with the constant function `1` shows `K + 2` points is at least as strong as `K + 1`.
The padding form is `n + B` with `B` larger than every `|b i|`, which makes it nonproportional
to each `a i · n + b i` (since `a i ≥ 1` forces `a i · B ≥ B > |b i|`).
-/

lemma isMultiplicativeOnPositiveInt_one :
    Erdos67b.IsMultiplicativeOnPositiveInt (fun _ : ℤ => (1 : ℂ)) :=
  ⟨rfl, fun _ _ _ _ => by norm_num⟩

/-- **The `K`-point hierarchy decreases in strength.**  `K + 2` points imply `K + 1` points. -/
theorem kPointLogElliott_of_succ {K : ℕ} (H : KPointLogElliott (K + 2)) :
    KPointLogElliott (K + 1) := by
  intro a b hnd ε hε
  -- the padding offset
  set B : ℤ := (∑ i : Fin (K + 1), |b i|) + 1 with hB
  have hne : ∀ i : Fin (K + 1), (a i : ℤ) * B ≠ b i := by
    intro i
    have h1 : |b i| ≤ ∑ j : Fin (K + 1), |b j| :=
      Finset.single_le_sum (f := fun j : Fin (K + 1) => |b j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hlt : |b i| < B := by rw [hB]; omega
    have ha : (1 : ℤ) ≤ (a i : ℤ) := by exact_mod_cast hnd.1 i
    have hB0 : (0 : ℤ) < B := lt_of_le_of_lt (abs_nonneg _) hlt
    have h3 : B ≤ (a i : ℤ) * B := by nlinarith
    have h2 : b i ≤ |b i| := le_abs_self _
    omega
  -- the padded data
  set a' : Fin (K + 2) → ℕ := Fin.snoc a 1 with ha'
  set b' : Fin (K + 2) → ℤ := Fin.snoc b B with hb'
  have ha'c : ∀ i : Fin (K + 1), a' i.castSucc = a i := by intro i; simp [ha']
  have hb'c : ∀ i : Fin (K + 1), b' i.castSucc = b i := by intro i; simp [hb']
  have ha'l : a' (Fin.last (K + 1)) = 1 := by simp [ha']
  have hb'l : b' (Fin.last (K + 1)) = B := by simp [hb']
  have hnd' : NondegenerateForms a' b' := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [ha'c]; exact hnd.1 i'
      · rw [ha'l]; norm_num
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · rw [ha'c, hb'c, ha'c, hb'c]
          exact hnd.2 i' j' (fun h => hij (by rw [h]))
        · rw [ha'c, hb'c, ha'l, hb'l]
          simpa using sub_ne_zero.mpr (hne i')
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · rw [ha'l, hb'l, ha'c, hb'c]
          simpa using sub_ne_zero.mpr (hne j').symm
        · exact absurd rfl hij
  obtain ⟨A₀, hA₀2, hA₀⟩ := H a' b' hnd' ε hε
  refine ⟨A₀, hA₀2, fun A X W hA hAW hWX g hm hbd hpret => ?_⟩
  set g' : Fin (K + 2) → ℤ → ℂ := Fin.snoc g (fun _ => (1 : ℂ)) with hg'
  have hg'c : ∀ i : Fin (K + 1), g' i.castSucc = g i := by intro i; simp [hg']
  have hg'l : g' (Fin.last (K + 1)) = (fun _ => (1 : ℂ)) := by simp [hg']
  have heq : kPointLogCorrelation g' a' b' X W = kPointLogCorrelation g a b X W := by
    rw [kPointLogCorrelation, kPointLogCorrelation]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp only [ha'c, hb'c, hg'c, ha'l, hb'l, hg'l, mul_one]
  have hmain := hA₀ A X W hA hAW hWX g'
    (by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [hg'c]; exact hm i'
      · rw [hg'l]; exact isMultiplicativeOnPositiveInt_one)
    (by
      intro i n
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [hg'c]; exact hbd i' n
      · rw [hg'l]; norm_num)
    (by
      intro i hi q hq hqA χ t ht
      have hi' : i = Fin.castSucc (⟨0, by omega⟩ : Fin (K + 1)) := by ext; simpa using hi
      have hgi : g' i = g ⟨0, by omega⟩ := by rw [hi', hg'c]
      rw [hgi]
      exact hpret ⟨0, by omega⟩ rfl q hq hqA χ t ht)
  rwa [heq] at hmain

/-- **What the `D = 3` rung needs.**  `KPointLogElliott 3` implies the dependency's own bet, but
nothing in the dependency implies it: it is a strictly new named input.  (The implication is the
content; the non-implication is a statement about the literature, not a theorem.) -/
theorem nonasymptoticLogElliott_of_kPointLogElliott_three (H : KPointLogElliott 3) :
    Erdos67b.NonasymptoticLogElliott :=
  kPointLogElliott_two_iff.mp (kPointLogElliott_of_succ (K := 1) H)

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.kPointLogCorrelation_two
#print axioms NormalNumbers.CastingOut.kPointLogElliott_two_iff
#print axioms NormalNumbers.CastingOut.kPointLogElliott_of_succ
#print axioms NormalNumbers.CastingOut.nonasymptoticLogElliott_of_kPointLogElliott_three
