/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2TTHyp
import NormalNumbers.G4Base2Cov
import NormalNumbers.G4VeryLargeCov
import NormalNumbers.G4SchedBE
import NormalNumbers.LiteratureTTEquidistributedDefect

/-!
# N3–N6: the very-large covariance supply, decomposed

* `exists_bins` (N3): greedy partition of a prime set into bins of harmonic mass `≤ 2θ`.
* `binErr_le_pairs`: `c − 1[c > 0] ≤ C(c, 2)`, so the bin error is a pair count.
* `avg_binErr_le` (N4 average): sample mean of the bin error `≤ Σ_ℓ mass_ℓ² + C₆·P₀/log Y`.
* `abs_one_sub_binDelta_le`: `|1 − δ_I(N)| ≤ 2·mass(I)` for `mass(I) ≤ 1`.
* `sum_inv_vlPrimes_le`: the very-large primes up to `Y^{102}` have mass `≤ 5`.
* `omegaVLS_le`: `ω_{S,>Y}(m) ≤ 101` for `m < Y^{102}`.
* `binPair_cov` (N6 core): from TT (dyadic), a power-of-two `X` at which all bin-pair cross
  moments of the centred indicators are `≤ ε₂`.
-/

open Finset

namespace NormalNumbers.G4.Base2

/-- Harmonic mass of a finset. -/
noncomputable def mass (I : Finset ℕ) : ℝ := ∑ p ∈ I, (p : ℝ)⁻¹

/-- The dyadic base of `n`: `2^k` for `n ∈ (2^k, 2^{k+1}]`. -/
noncomputable def dyBase (n : ℕ) : ℝ := (2 : ℝ) ^ Nat.log 2 (n - 1)

/-- **N3.** -/
theorem exists_bins (Q : Finset ℕ) {θ : ℝ} (hθ : 0 < θ) (hQ : ∀ p ∈ Q, (p : ℝ)⁻¹ ≤ θ) :
    ∃ B : ℕ, ∃ bins : Fin B → Finset ℕ,
      (∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (bins ℓ) (bins ℓ')) ∧ univ.biUnion bins = Q ∧
      (∀ ℓ, mass (bins ℓ) ≤ 2 * θ) ∧ (B : ℝ) ≤ mass Q / θ + 1 := by
  sorry

theorem binErr_le_pairs (c : ℕ) : (c : ℝ) - (if c = 0 then 0 else 1) ≤ (c.choose 2 : ℝ) := by
  rcases c with _ | c
  · simp
  · rw [if_neg (Nat.succ_ne_zero c), Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    have : (0 : ℝ) ≤ (c.choose 2 : ℝ) := by positivity
    linarith

theorem abs_one_sub_binDelta_le (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime) (hm : mass I ≤ 1)
    (N : ℝ) : |1 - binDelta I N| ≤ 2 * mass I := by
  sorry

variable (S : ℕ → Prop) [DecidablePred S]

theorem sum_inv_vlPrimes_le : ∃ Y₀ : ℕ, ∀ Y P₀ M : ℕ, Y₀ ≤ Y → M ≤ Y ^ 102 →
    mass (vlPrimes S Y P₀ M) ≤ 5 := by
  sorry

theorem omegaVLS_le {Y P₀ m : ℕ} (hY : 2 ≤ Y) (hm : m < Y ^ 102) : omegaVLS S Y P₀ m ≤ 101 := by
  by_contra hc
  push Not at hc
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp [omegaVLS] at hc
  set F := m.primeFactors.filter (fun p => S p ∧ ¬ p ∣ P₀ ∧ Y < p) with hF
  have hdvd : ∏ p ∈ F, p ∣ m := by
    refine (Finset.prod_dvd_prod_of_subset _ _ id (filter_subset _ _)).trans ?_
    exact Nat.prod_primeFactors_dvd m
  have hle : Y ^ F.card ≤ ∏ p ∈ F, p := by
    rw [← prod_const]
    exact prod_le_prod' fun p hp => ((mem_filter.1 hp).2.2.2).le
  have h1 : Y ^ 102 ≤ Y ^ F.card :=
    Nat.pow_le_pow_right (by omega) (by unfold omegaVLS at hc; exact hc)
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
  omega

/-- **N4, average.** -/
theorem avg_binErr_le : ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (X Y P₀ b₀ ρ : ℕ) (B : ℕ) (bins : Fin B → Finset ℕ),
    0 < P₀ → b₀ < P₀ → P₀ < Y → Y ≤ X → ρ ≤ X → 2 * P₀ ≤ X →
    (∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (bins ℓ) (bins ℓ')) →
    (∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ Y < p) →
    ((apSample X P₀ b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X P₀ b₀, ∑ ℓ,
        ((binCount (bins ℓ) (n + ρ) : ℝ) - (if binCount (bins ℓ) (n + ρ) = 0 then 0 else 1))
      ≤ ∑ ℓ, mass (bins ℓ) ^ 2 + C₆ * P₀ / Real.log Y := by
  sorry

/-- **N6 core.**  From TT 3.1(i) (dyadic) and N5 (`binInd_ap_mean`).  75%. -/
theorem binPair_cov (htt : CastingOut.TTEquidistributedDyadic) (K N : ℕ) (hK : 1 ≤ K)
    {ε₂ : ℝ} (hε : 0 < ε₂) (Bmax : ℕ) : ∃ e₀ : ℕ, ∀ e, e₀ ≤ e → ∀ B ≤ Bmax,
      ∀ bins : Fin B → Finset ℕ, (∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ SchedB.YE K e < p) →
      ∃ x : ℕ, 100 * 2 ^ SchedB.mE K e ≤ x ∧ x ≤ 101 * 2 ^ SchedB.mE K e ∧
        ∀ ℓ ℓ' : Fin B, ∀ i j : (gridOf K N hK).Idx, i ≠ j →
          |((apSample (2 ^ x) (gridOf K N hK).P₀ (gridOf K N hK).b₀).card : ℝ)⁻¹ *
            ∑ n ∈ apSample (2 ^ x) (gridOf K N hK).P₀ (gridOf K N hK).b₀,
              ((binInd (bins ℓ) (n + shiftAL (gridOf K N hK).B (gridOf K N hK).Q
                  (gridOf K N hK).D₀ i)).re - binDelta (bins ℓ) (dyBase n))
              * ((binInd (bins ℓ') (n + shiftAL (gridOf K N hK).B (gridOf K N hK).Q
                  (gridOf K N hK).D₀ j)).re - binDelta (bins ℓ') (dyBase n))| ≤ ε₂ := by
  sorry

/-- `(1 − g_I(m)).re ≤ binCount I m`, and both are nonnegative. -/
lemma one_sub_binInd_re_le (I : Finset ℕ) (m : ℕ) :
    0 ≤ (1 - binInd I m).re ∧ (1 - binInd I m).re ≤ binCount I m := by
  rw [one_sub_binInd_re]
  split_ifs with h
  · simp [h]
  · refine ⟨zero_le_one, ?_⟩
    have : 1 ≤ binCount I m := Nat.one_le_iff_ne_zero.2 h
    exact_mod_cast this

lemma avg_le_of_le (P : Finset ℕ) (f : ℕ → ℝ) {V : ℝ} (hV : 0 ≤ V) (h : ∀ n ∈ P, f n ≤ V) :
    (P.card : ℝ)⁻¹ * ∑ n ∈ P, f n ≤ V := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simpa using hV
  · have hc : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
    rw [inv_mul_le_iff₀ hc]
    calc ∑ n ∈ P, f n ≤ ∑ _n ∈ P, V := sum_le_sum h
      _ = P.card * V := by simp

/-- **The deterministic assembly.**  Bins covering the very-large primes, an error-mean bound
`ε₁` and bin-pair bounds `ε₂` give `VeryLargeCov` with `V = 20000`,
`κ = B²·ε₂ + 323·ε₁`. -/
theorem veryLargeCov_of_bins (G : GridParams) (X Y M : ℕ) {B : ℕ} (bins : Fin B → Finset ℕ)
    (hdisj : ∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (bins ℓ) (bins ℓ'))
    (hcover : univ.biUnion bins = vlPrimes S Y G.P₀ M)
    (hprime : ∀ ℓ, ∀ p ∈ bins ℓ, p.Prime)
    (hM : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx, n + shiftAL G.B G.Q G.D₀ i ≤ M)
    (hω : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      omegaVLS S Y G.P₀ (n + shiftAL G.B G.Q G.D₀ i) ≤ 101)
    (hmass : ∀ ℓ, mass (bins ℓ) ≤ 1) (htot : ∑ ℓ, mass (bins ℓ) ≤ 5)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁)
    (herr : ∀ i : G.Idx, ((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
      ∑ ℓ, ((binCount (bins ℓ) (n + shiftAL G.B G.Q G.D₀ i) : ℝ)
        - (if binCount (bins ℓ) (n + shiftAL G.B G.Q G.D₀ i) = 0 then 0 else 1)) ≤ ε₁)
    (hpair : ∀ ℓ ℓ' : Fin B, ∀ i j : G.Idx, i ≠ j →
      |((apSample X G.P₀ G.b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X G.P₀ G.b₀,
        ((binInd (bins ℓ) (n + shiftAL G.B G.Q G.D₀ i)).re - binDelta (bins ℓ) (dyBase n))
        * ((binInd (bins ℓ') (n + shiftAL G.B G.Q G.D₀ j)).re - binDelta (bins ℓ') (dyBase n))|
        ≤ ε₂) :
    VeryLargeCov S G X Y 20000 ((B : ℝ) ^ 2 * ε₂ + (2 * 111 + 101) * ε₁) := by
  set P := apSample X G.P₀ G.b₀ with hP
  set ρ := fun i : G.Idx => shiftAL G.B G.Q G.D₀ i with hρ
  set μ : ℕ → ℝ := fun n => ∑ ℓ, (1 - binDelta (bins ℓ) (dyBase n)) with hμ
  set F : G.Idx → ℕ → ℝ := fun i n => ∑ ℓ, (1 - binInd (bins ℓ) (n + ρ i)).re with hF
  set E : G.Idx → ℕ → ℝ := fun i n => ∑ ℓ, ((binCount (bins ℓ) (n + ρ i) : ℝ)
        - (if binCount (bins ℓ) (n + ρ i) = 0 then 0 else 1)) with hE
  have hbinI : ∀ ℓ, ∀ p ∈ bins ℓ, p.Prime := hprime
  -- the decomposition ω = F + E
  have hdec : ∀ n ∈ P, ∀ i, (omegaVLS S Y G.P₀ (n + ρ i) : ℝ) = F i n + E i n := by
    intro n hn i
    have hpos : 0 < n + ρ i := by have := shiftAL_pos G i; simp only [hρ]; omega
    rw [omegaVLS_eq_sum_bins S hpos (hM n hn i) bins hdisj hcover]
    simp only [hF, hE]
    push_cast
    rw [← sum_add_distrib]
    refine sum_congr rfl fun ℓ _ => ?_
    rw [one_sub_binInd_re]; ring
  have hFE : ∀ n ∈ P, ∀ i, 0 ≤ F i n ∧ 0 ≤ E i n := by
    intro n _ i
    refine ⟨sum_nonneg fun ℓ _ => (one_sub_binInd_re_le _ _).1, sum_nonneg fun ℓ _ => ?_⟩
    have h := one_sub_binInd_re_le (bins ℓ) (n + ρ i)
    rw [one_sub_binInd_re] at h
    linarith [h.2]
  have hFle : ∀ n ∈ P, ∀ i, F i n + E i n ≤ 101 := by
    intro n hn i
    rw [← hdec n hn i]; exact_mod_cast hω n hn i
  have hμb : ∀ n, |μ n| ≤ 10 := by
    intro n
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ ℓ, |1 - binDelta (bins ℓ) (dyBase n)| ≤ ∑ ℓ, 2 * mass (bins ℓ) :=
          sum_le_sum fun ℓ _ => abs_one_sub_binDelta_le _ (hbinI ℓ) (hmass ℓ) _
      _ = 2 * ∑ ℓ, mass (bins ℓ) := by rw [mul_sum]
      _ ≤ 10 := by linarith
  have hFμ : ∀ n ∈ P, ∀ i, |F i n - μ n| ≤ 111 := by
    intro n hn i
    have h1 := hFE n hn i; have h2 := hFle n hn i; have h3 := hμb n
    rw [abs_le] at h3 ⊢; constructor <;> linarith
  refine ⟨μ, fun i => ?_, fun i j hij => ?_⟩
  · refine avg_le_of_le P _ (by norm_num) fun n hn => ?_
    have h1 := hFE n hn i; have h2 := hFle n hn i; have h3 := hμb n
    have hω' := hdec n hn i
    have hb : |(omegaVLS S Y G.P₀ (n + ρ i) : ℝ) - μ n| ≤ 111 := by
      rw [abs_le] at h3 ⊢; constructor <;> linarith
    have := sq_abs ((omegaVLS S Y G.P₀ (n + ρ i) : ℝ) - μ n)
    nlinarith [abs_nonneg ((omegaVLS S Y G.P₀ (n + ρ i) : ℝ) - μ n)]
  · have hmain : |(P.card : ℝ)⁻¹ * ∑ n ∈ P, (F i n - μ n) * (F j n - μ n)| ≤ (B : ℝ) ^ 2 * ε₂ := by
      have hu : ∀ k : G.Idx, ∀ n, F k n - μ n
          = ∑ ℓ, ((binDelta (bins ℓ) (dyBase n)) - (binInd (bins ℓ) (n + ρ k)).re) := by
        intro k n
        simp only [hF, hμ]
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun ℓ _ => ?_
        simp only [Complex.sub_re, Complex.one_re]; ring
      simp_rw [hu]
      refine abs_avg_binSum_le P _ _ fun ℓ ℓ' => ?_
      have h := hpair ℓ ℓ' i j hij
      have heq : ∀ n, (binDelta (bins ℓ) (dyBase n) - (binInd (bins ℓ) (n + ρ i)).re)
            * (binDelta (bins ℓ') (dyBase n) - (binInd (bins ℓ') (n + ρ j)).re)
          = ((binInd (bins ℓ) (n + ρ i)).re - binDelta (bins ℓ) (dyBase n))
            * ((binInd (bins ℓ') (n + ρ j)).re - binDelta (bins ℓ') (dyBase n)) := fun n => by
        ring
      simp_rw [heq]; exact h
    have := abs_avg_cross_le P (F i) (F j) (E i) (E j) μ (C₀ := 111) (A := 101) (by norm_num)
      (by norm_num) (fun n hn => hFμ n hn i) (fun n hn => hFμ n hn j)
      (fun n hn => (hFE n hn i).2) (fun n hn => (hFE n hn j).2)
      (fun n hn => by linarith [hFle n hn i, (hFE n hn i).1]) (herr i) (herr j) hmain
    have hrw : ∀ n ∈ P, ((omegaVLS S Y G.P₀ (n + ρ i) : ℝ) - μ n)
        * ((omegaVLS S Y G.P₀ (n + ρ j) : ℝ) - μ n)
        = (F i n + E i n - μ n) * (F j n + E j n - μ n) := fun n hn => by
      rw [hdec n hn i, hdec n hn j]
    rw [sum_congr rfl hrw]
    simpa using this

end NormalNumbers.G4.Base2
