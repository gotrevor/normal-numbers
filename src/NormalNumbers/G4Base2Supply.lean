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
import NormalNumbers.G4Base2Mertens
import NormalNumbers.G4Base2N5
import NormalNumbers.G4Base2Pairs

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

theorem exists_bins_aux (Q : Finset ℕ) {θ : ℝ} (hθ : 0 < θ) (hQ : ∀ p ∈ Q, (p : ℝ)⁻¹ ≤ θ) :
    ∃ B : ℕ, ∃ bins : Fin B → Finset ℕ,
      (∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (bins ℓ) (bins ℓ')) ∧ univ.biUnion bins = Q ∧
      (∀ ℓ, mass (bins ℓ) ≤ 2 * θ) ∧
      (∀ ℓ ℓ', ℓ ≠ ℓ' → θ ≤ mass (bins ℓ) ∨ θ ≤ mass (bins ℓ')) := by
  induction Q using Finset.induction_on with
  | empty => exact ⟨0, Fin.elim0, fun ℓ => ℓ.elim0, by simp, fun ℓ => ℓ.elim0, fun ℓ => ℓ.elim0⟩
  | insert p Q hpQ ih =>
    obtain ⟨B, bins, hd, hu, hm, hp⟩ := ih fun q hq => hQ q (mem_insert_of_mem hq)
    have hpθ := hQ p (mem_insert_self _ _)
    have hpn : ∀ ℓ, p ∉ bins ℓ := fun ℓ h => hpQ (hu ▸ mem_biUnion.2 ⟨ℓ, mem_univ _, h⟩)
    have hmi : ∀ I, p ∉ I → mass (insert p I) = mass I + (p : ℝ)⁻¹ := fun I h => by
      unfold mass; rw [sum_insert h]; ring
    by_cases hs : ∃ ℓ₀, mass (bins ℓ₀) < θ
    · obtain ⟨ℓ₀, hℓ₀⟩ := hs
      refine ⟨B, Function.update bins ℓ₀ (insert p (bins ℓ₀)), ?_, ?_, ?_, ?_⟩
      · intro ℓ ℓ' hne
        simp only [Function.update_apply]
        split_ifs with h1 h2 h2
        · exact absurd (h1.trans h2.symm) hne
        · subst h1; exact disjoint_insert_left.2 ⟨hpn ℓ', hd _ _ hne⟩
        · subst h2; exact disjoint_insert_right.2 ⟨hpn ℓ, hd _ _ hne⟩
        · exact hd _ _ hne
      · ext x
        simp only [mem_biUnion, mem_univ, true_and, Function.update_apply, mem_insert]
        constructor
        · rintro ⟨ℓ, hx⟩
          split_ifs at hx with h1
          · rcases mem_insert.1 hx with h | h
            · exact Or.inl h
            · exact Or.inr (hu ▸ mem_biUnion.2 ⟨ℓ₀, mem_univ _, h⟩)
          · exact Or.inr (hu ▸ mem_biUnion.2 ⟨ℓ, mem_univ _, hx⟩)
        · rintro (rfl | hx)
          · exact ⟨ℓ₀, by simp⟩
          · obtain ⟨ℓ, -, hℓ⟩ := mem_biUnion.1 (hu.symm ▸ hx)
            refine ⟨ℓ, ?_⟩
            split_ifs with h1
            · subst h1; exact mem_insert_of_mem hℓ
            · exact hℓ
      · intro ℓ
        simp only [Function.update_apply]
        split_ifs with h1
        · subst h1; rw [hmi _ (hpn _)]; linarith
        · exact hm ℓ
      · intro ℓ ℓ' hne
        simp only [Function.update_apply]
        split_ifs with h1 h2 h2
        · exact absurd (h1.trans h2.symm) hne
        · subst h1
          exact Or.inr ((hp ℓ ℓ' hne).resolve_left (by linarith))
        · subst h2
          exact Or.inl ((hp ℓ' ℓ (Ne.symm hne)).resolve_left (by linarith))
        · exact hp ℓ ℓ' hne
    · push Not at hs
      refine ⟨B + 1, Fin.cons {p} bins, ?_, ?_, ?_, ?_⟩
      · intro ℓ ℓ' hne
        cases ℓ using Fin.cases <;> cases ℓ' using Fin.cases
        · exact absurd rfl hne
        · simpa using hpn _
        · simpa using hpn _
        · simpa using hd _ _ (fun h => hne (by rw [h]))
      · ext x
        simp only [mem_biUnion, mem_univ, true_and, mem_insert, Fin.exists_fin_succ, Fin.cons_zero,
          Fin.cons_succ, mem_singleton]
        rw [← hu]; simp
      · intro ℓ
        cases ℓ using Fin.cases
        · simp only [Fin.cons_zero]; unfold mass; simp; linarith
        · simpa using hm _
      · intro ℓ ℓ' hne
        cases ℓ using Fin.cases
        · cases ℓ' using Fin.cases
          · exact absurd rfl hne
          · simpa using Or.inr (hs _)
        · simpa using Or.inl (hs _)

/-- **N3.** -/
theorem exists_bins (Q : Finset ℕ) {θ : ℝ} (hθ : 0 < θ) (hQ : ∀ p ∈ Q, (p : ℝ)⁻¹ ≤ θ) :
    ∃ B : ℕ, ∃ bins : Fin B → Finset ℕ,
      (∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (bins ℓ) (bins ℓ')) ∧ univ.biUnion bins = Q ∧
      (∀ ℓ, mass (bins ℓ) ≤ 2 * θ) ∧ (B : ℝ) ≤ mass Q / θ + 1 := by
  obtain ⟨B, bins, hd, hu, hm, hp⟩ := exists_bins_aux Q hθ hQ
  refine ⟨B, bins, hd, hu, hm, ?_⟩
  have hmQ : mass Q = ∑ ℓ, mass (bins ℓ) := by
    unfold mass; rw [← hu, sum_biUnion (fun ℓ _ ℓ' _ h => hd ℓ ℓ' h)]
  have hnn : ∀ ℓ, 0 ≤ mass (bins ℓ) := fun ℓ => sum_nonneg fun _ _ => by positivity
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp; positivity
  obtain ⟨ℓ₀, -, hmin⟩ := exists_min_image univ (fun ℓ => mass (bins ℓ)) ⟨⟨0, hB⟩, mem_univ _⟩
  have hge : ∀ ℓ ∈ univ.erase ℓ₀, θ ≤ mass (bins ℓ) := by
    intro ℓ hℓ
    rcases hp ℓ ℓ₀ (ne_of_mem_erase hℓ) with h | h
    · exact h
    · exact h.trans (hmin ℓ (mem_univ _))
  have h1 : ((B : ℝ) - 1) * θ ≤ mass Q := by
    rw [hmQ, ← add_sum_erase _ _ (mem_univ ℓ₀)]
    have := card_nsmul_le_sum _ _ _ hge
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub hB] at this
    push_cast at this
    linarith [hnn ℓ₀]
  have : (B : ℝ) - 1 ≤ mass Q / θ := by rw [le_div_iff₀ hθ]; exact h1
  linarith

theorem binErr_le_pairs (c : ℕ) : (c : ℝ) - (if c = 0 then 0 else 1) ≤ (c.choose 2 : ℝ) := by
  rcases c with _ | c
  · simp
  · rw [if_neg (Nat.succ_ne_zero c), Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    have : (0 : ℝ) ≤ (c.choose 2 : ℝ) := by positivity
    linarith

/-- The leaf as first stated (no lower bound on `N`) is **false**: for `I = ∅`, `N = 0` the
truncation empties `binDelta`, so `|1 − δ| = 1 > 0`.  The repaired leaf below adds `1 ≤ 2N`
(all call sites have `N = dyBase n ≥ 1`, or need only `|δ| ≤ 3`, see `abs_binDelta_le`). -/
theorem not_abs_one_sub_binDelta_le :
    ¬ (∀ (I : Finset ℕ), (∀ p ∈ I, p.Prime) → mass I ≤ 1 → ∀ N : ℝ,
      |1 - binDelta I N| ≤ 2 * mass I) := by
  intro h
  have := h ∅ (by simp) (by simp [mass]) 0
  simp [binDelta, mass, filter_singleton] at this; norm_num at this

theorem abs_one_sub_binDelta_le (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime) (hm : mass I ≤ 1)
    {N : ℝ} (hN : 1 ≤ 2 * N) : |1 - binDelta I N| ≤ 2 * mass I := by
  set F := I.powerset.filter (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) ≤ 2 * N) with hF
  have h0 : ∅ ∈ F := by simp [hF, hN]
  have hpos : ∀ T ∈ I.powerset, (0 : ℝ) < ((∏ p ∈ T, p : ℕ) : ℝ) := by
    intro T hT
    have : 0 < ∏ p ∈ T, p := prod_pos fun p hp => (hI p (mem_powerset.1 hT hp)).pos
    exact_mod_cast this
  have hδ : binDelta I N = 1 + ∑ T ∈ F.erase ∅, (-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ) := by
    unfold binDelta; rw [← hF, ← add_sum_erase _ _ h0]; simp
  have hm0 : 0 ≤ mass I := sum_nonneg fun p _ => by positivity
  have hprod : ∑ T ∈ I.powerset, ∏ p ∈ T, (p : ℝ)⁻¹ ≤ Real.exp (mass I) := by
    rw [← prod_one_add]; exact Real.prod_one_add_le_exp_sum _ fun p => by positivity
  have hexp : Real.exp (mass I) ≤ 1 + 2 * mass I := by
    have := Real.abs_exp_sub_one_sub_id_le (x := mass I) (by rw [abs_of_nonneg hm0]; exact hm)
    rw [abs_le] at this; nlinarith
  rw [hδ, sub_add_cancel_left, abs_neg]
  calc |∑ T ∈ F.erase ∅, (-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ)|
      ≤ ∑ T ∈ F.erase ∅, |(-1 : ℝ) ^ T.card / ((∏ p ∈ T, p : ℕ) : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ I.powerset.erase ∅, ∏ p ∈ T, (p : ℝ)⁻¹ := by
        rw [sum_congr rfl fun T hT => ?_]
        · exact sum_le_sum_of_subset_of_nonneg (erase_subset_erase _ (filter_subset _ _))
            (fun T _ _ => prod_nonneg fun p _ => by positivity)
        · have hT' : T ∈ I.powerset := (filter_subset _ _) (mem_of_mem_erase hT)
          rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (hpos T hT'), Nat.cast_prod,
            prod_inv_distrib, one_div]
    _ = ∑ T ∈ I.powerset, ∏ p ∈ T, (p : ℝ)⁻¹ - 1 := by
        rw [← add_sum_erase _ _ (empty_mem_powerset I)]; simp
    _ ≤ 2 * mass I := by linarith

theorem binDelta_eq_zero_of_lt (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime) {N : ℝ} (hN : 2 * N < 1) :
    binDelta I N = 0 := by
  unfold binDelta
  rw [sum_eq_zero]
  intro T hT
  exfalso
  rw [mem_filter, mem_powerset] at hT
  have : 0 < ∏ p ∈ T, p := prod_pos fun p hp => (hI p (hT.1 hp)).pos
  have : (1 : ℝ) ≤ ((∏ p ∈ T, p : ℕ) : ℝ) := by exact_mod_cast this
  linarith [hT.2]

theorem abs_binDelta_le (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime) (hm : mass I ≤ 1) (N : ℝ) :
    |binDelta I N| ≤ 3 := by
  by_cases hN : 1 ≤ 2 * N
  · have h := abs_one_sub_binDelta_le I hI hm hN
    rw [abs_le] at h ⊢; constructor <;> linarith
  · rw [binDelta_eq_zero_of_lt I hI (by linarith)]; norm_num

lemma one_le_two_mul_dyBase (n : ℕ) : 1 ≤ 2 * dyBase n := by
  unfold dyBase
  have : (1 : ℝ) ≤ 2 ^ Nat.log 2 (n - 1) := one_le_pow₀ (by norm_num)
  linarith

variable (S : ℕ → Prop) [DecidablePred S]

theorem sum_inv_vlPrimes_le : ∃ Y₀ : ℕ, ∀ Y P₀ M : ℕ, Y₀ ≤ Y → M ≤ Y ^ 102 →
    mass (vlPrimes S Y P₀ M) ≤ 5 := by
  refine ⟨⌈Real.exp 13860⌉₊, fun Y P₀ M hY hM => ?_⟩
  have hY' : Real.exp 13860 ≤ Y := (Nat.ceil_le).1 hY
  have hlog : 13860 ≤ Real.log Y := by
    have := Real.log_le_log (Real.exp_pos _) hY'
    rwa [Real.log_exp] at this
  refine le_trans ?_ (sum_inv_primes_Y102_le hlog)
  unfold mass vlPrimes
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => by positivity)
  simp only [mem_filter, mem_range] at hp ⊢
  exact ⟨by omega, hp.2.1, hp.2.2.2.2⟩

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

lemma exists_primes_card_gt (K : ℕ) : ∃ J : Finset ℕ, J.card = K ∧ ∀ p ∈ J, p.Prime ∧ K < p := by
  have hinf : {p : ℕ | p.Prime ∧ K < p}.Infinite := by
    have := Nat.infinite_setOfPred_prime.sdiff (Set.finite_le_nat K)
    refine this.mono fun p hp => ⟨hp.1, by simpa using hp.2⟩
  obtain ⟨J, hJ, hc⟩ := hinf.exists_subset_card_eq K
  exact ⟨J, hc, fun p hp => hJ hp⟩

/-- The N4 leaf as first stated (no `0 < ρ`) is **false**: at `ρ = 0, b₀ = 0` the sample
contains `n = 0`, every prime divides `0`, and a bin of `K` huge primes (mass `≤ 1`) gives
mean bin error `(K − 1)/2`. -/
theorem not_avg_binErr_le_rho_zero : ¬ ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (X Y P₀ b₀ ρ : ℕ) (B : ℕ)
    (bins : Fin B → Finset ℕ),
    0 < P₀ → b₀ < P₀ → P₀ < Y → Y ≤ X → ρ ≤ X → 2 * P₀ ≤ X →
    (∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (bins ℓ) (bins ℓ')) →
    (∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ Y < p) →
    ((apSample X P₀ b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X P₀ b₀, ∑ ℓ,
        ((binCount (bins ℓ) (n + ρ) : ℝ) - (if binCount (bins ℓ) (n + ρ) = 0 then 0 else 1))
      ≤ ∑ ℓ, mass (bins ℓ) ^ 2 + C₆ * P₀ / Real.log Y := by
  rintro ⟨C₆, hC₆, h⟩
  set K : ℕ := ⌈2 * (1 + C₆ / Real.log 2) + 3⌉₊ with hK
  have hKr : 2 * (1 + C₆ / Real.log 2) + 3 ≤ K := Nat.le_ceil _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK2 : 2 ≤ K := by
    have : (2 : ℝ) ≤ K := by
      have : 0 ≤ C₆ / Real.log 2 := by positivity
      linarith
    exact_mod_cast this
  obtain ⟨J, hJc, hJ⟩ := exists_primes_card_gt K
  have hm := h 2 2 1 0 0 1 (fun _ => J) (by norm_num) (by norm_num) (by norm_num) le_rfl
    (by norm_num) le_rfl (fun ℓ ℓ' hne => absurd (Subsingleton.elim ℓ ℓ') hne)
    (fun _ p hp => ⟨(hJ p hp).1, by have := (hJ p hp).2; omega⟩)
  have hS : apSample 2 1 0 = {0, 1} := by decide
  have hc0 : binCount J 0 = K := by
    unfold binCount; rw [filter_true_of_mem fun p _ => dvd_zero p, hJc]
  have hc1 : binCount J 1 = 0 := by
    unfold binCount; rw [card_eq_zero, filter_eq_empty_iff]
    intro p hp; exact (hJ p hp).1.not_dvd_one
  have hmass : mass J ≤ 1 := by
    unfold mass
    calc ∑ p ∈ J, (p : ℝ)⁻¹ ≤ ∑ _p ∈ J, (K : ℝ)⁻¹ := sum_le_sum fun p hp => by
          have : (K : ℝ) < p := by exact_mod_cast (hJ p hp).2
          exact inv_anti₀ (by positivity) this.le
      _ = 1 := by rw [sum_const, hJc, nsmul_eq_mul, mul_inv_cancel₀ (by positivity)]
  rw [hS] at hm
  simp only [Fin.sum_univ_one, sum_insert (by decide : (0 : ℕ) ∉ ({1} : Finset ℕ)), sum_singleton,
    zero_add, hc0, hc1] at hm
  rw [if_neg (by omega)] at hm
  norm_num at hm
  have hm2 : mass J ^ 2 ≤ 1 := by
    have : 0 ≤ mass J := sum_nonneg fun _ _ => by positivity
    nlinarith
  linarith
/-- **N4, average** (repaired: `0 < ρ`; see `not_avg_binErr_le_rho_zero`). -/
theorem avg_binErr_le : ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (X Y P₀ b₀ ρ : ℕ) (B : ℕ) (bins : Fin B → Finset ℕ),
    0 < P₀ → b₀ < P₀ → P₀ < Y → Y ≤ X → ρ ≤ X → 0 < ρ → 2 * P₀ ≤ X →
    (∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (bins ℓ) (bins ℓ')) →
    (∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ Y < p) →
    ((apSample X P₀ b₀).card : ℝ)⁻¹ * ∑ n ∈ apSample X P₀ b₀, ∑ ℓ,
        ((binCount (bins ℓ) (n + ρ) : ℝ) - (if binCount (bins ℓ) (n + ρ) = 0 then 0 else 1))
      ≤ ∑ ℓ, mass (bins ℓ) ^ 2 + C₆ * P₀ / Real.log Y := by
  refine ⟨250, by norm_num, fun X Y P₀ b₀ ρ B bins hP₀ hb hP₀Y hYX hρX hρ h2P hdisj hpr => ?_⟩
  set S := apSample X P₀ b₀ with hS
  have hY2 : 2 ≤ Y := by omega
  have hYr : (2 : ℝ) ≤ Y := by exact_mod_cast hY2
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hPr : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have hXr : (2 : ℝ) * P₀ ≤ X := by exact_mod_cast h2P
  have hX0 : (0 : ℝ) < X := by linarith
  have hs : (X : ℝ) / (2 * P₀) ≤ S.card := by
    have h := card_apSample_ge X P₀ b₀ hP₀ hb
    have : (X : ℝ) / (2 * P₀) ≤ (X : ℝ) / P₀ - 1 := by
      rw [div_le_iff₀ (by positivity)]
      have : (X : ℝ) / P₀ * P₀ = X := div_mul_cancel₀ _ hPr.ne'
      nlinarith
    linarith
  have hspos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hs
  have hIp : ∀ ℓ, ∀ p ∈ bins ℓ, p.Prime := fun ℓ p hp => (hpr ℓ p hp).1
  -- pointwise: bin error ≤ number of dividing pairs
  set D : Fin B → Finset ℕ → ℕ → ℝ := fun ℓ T n => if (∏ p ∈ T, p) ∣ n + ρ then 1 else 0
  have hpt : ∀ n ∈ S, ∑ ℓ, ((binCount (bins ℓ) (n + ρ) : ℝ)
      - (if binCount (bins ℓ) (n + ρ) = 0 then 0 else 1))
      ≤ ∑ ℓ, ∑ T ∈ (bins ℓ).powersetCard 2, D ℓ T n := by
    intro n _
    refine sum_le_sum fun ℓ _ => ?_
    refine (binErr_le_pairs _).trans (le_of_eq ?_)
    rw [choose_binCount_eq (hIp ℓ), card_filter]; push_cast; rfl
  -- per-pair count
  have hpair : ∀ ℓ, ∀ T ∈ (bins ℓ).powersetCard 2, ∑ n ∈ S, D ℓ T n
      ≤ (X : ℝ) / P₀ * ∏ p ∈ T, (p : ℝ)⁻¹ + (if ∏ p ∈ T, p ≤ 2 * X then 1 else 0) := by
    intro ℓ T hT
    have hTs := (mem_powersetCard.1 hT).1
    have hTp : ∀ p ∈ T, p.Prime := fun p hp => hIp ℓ p (hTs hp)
    have hd : 0 < ∏ p ∈ T, p := prod_pos fun p hp => (hTp p hp).pos
    have hdr : (0 : ℝ) < ((∏ p ∈ T, p : ℕ) : ℝ) := by exact_mod_cast hd
    have heq : (X : ℝ) / P₀ * ∏ p ∈ T, (p : ℝ)⁻¹ = (X : ℝ) / (P₀ * ((∏ p ∈ T, p : ℕ) : ℝ)) := by
      rw [prod_inv_distrib, ← Nat.cast_prod]; field_simp
    rw [heq]
    simp only [D]
    rw [sum_boole]
    split_ifs with h2X
    · have hcop : P₀.Coprime (∏ p ∈ T, p) := Nat.Coprime.prod_right fun p hp =>
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hTp p hp)).2
          fun h => absurd (Nat.le_of_dvd hP₀ h) (by have := (hpr ℓ p (hTs hp)).2; omega)))
      exact card_apSample_dvd_le hP₀ hd hρ hcop
    · rw [add_zero]
      have : S.filter (fun n => (∏ p ∈ T, p) ∣ n + ρ) = ∅ := by
        rw [filter_eq_empty_iff]
        intro n hn hdv
        have hn' : n < X := by
          simp only [hS, apSample, mem_filter, mem_range] at hn; exact hn.1
        have := Nat.le_of_dvd (by omega) hdv
        omega
      rw [this]; simp only [card_empty, Nat.cast_zero]; positivity
  -- the total
  have hswap : ∑ n ∈ S, ∑ ℓ, ∑ T ∈ (bins ℓ).powersetCard 2, D ℓ T n
      = ∑ ℓ, ∑ T ∈ (bins ℓ).powersetCard 2, ∑ n ∈ S, D ℓ T n := by
    rw [sum_comm]; refine sum_congr rfl fun ℓ _ => ?_; rw [sum_comm]
  have hmain : ∀ ℓ, ∑ T ∈ (bins ℓ).powersetCard 2, ∏ p ∈ T, (p : ℝ)⁻¹ ≤ mass (bins ℓ) ^ 2 / 2 := by
    intro ℓ
    have := two_mul_sum_pairs_le (bins ℓ) (fun p => (p : ℝ)⁻¹) (fun p => by positivity)
    unfold mass; linarith
  set A : Fin B → Finset (Finset ℕ) := fun ℓ =>
    ((bins ℓ).powersetCard 2).filter (fun T => ∏ p ∈ T, p ≤ 2 * X)
  set U := univ.biUnion bins
  have hU : ∀ p ∈ U, p.Prime ∧ Y < p := by
    intro p hp; obtain ⟨ℓ, -, hℓ⟩ := mem_biUnion.1 hp; exact hpr ℓ p hℓ
  have hcnt : ∑ ℓ, ∑ T ∈ (bins ℓ).powersetCard 2, (if ∏ p ∈ T, p ≤ 2 * X then (1 : ℝ) else 0)
      ≤ 40 * Real.log 4 * (2 * X : ℕ) / Real.log Y := by
    have e : ∑ ℓ, ∑ T ∈ (bins ℓ).powersetCard 2, (if ∏ p ∈ T, p ≤ 2 * X then (1 : ℝ) else 0)
        = ((univ.biUnion A).card : ℝ) := by
      rw [card_biUnion]
      · push_cast; refine sum_congr rfl fun ℓ _ => ?_; rw [sum_boole]
      · intro ℓ _ ℓ' _ hne
        rw [Function.onFun, disjoint_left]
        intro T hT hT'
        have h1 := (mem_powersetCard.1 (mem_filter.1 hT).1)
        have h2 := (mem_powersetCard.1 (mem_filter.1 hT').1)
        obtain ⟨a, ha⟩ : T.Nonempty := card_pos.1 (by omega)
        exact disjoint_left.1 (hdisj ℓ ℓ' hne) (h1.1 ha) (h2.1 ha)
    rw [e]
    refine le_trans (Nat.cast_le.2 (card_le_card ?_)) (card_pairs_le hY2 hU (2 * X))
    intro T hT
    obtain ⟨ℓ, -, hℓ⟩ := mem_biUnion.1 hT
    obtain ⟨h1, h2⟩ := mem_filter.1 hℓ
    refine mem_filter.2 ⟨mem_powersetCard.2 ⟨fun p hp => mem_biUnion.2 ⟨ℓ, mem_univ _,
      (mem_powersetCard.1 h1).1 hp⟩, (mem_powersetCard.1 h1).2⟩, h2⟩
  have htot : ∑ n ∈ S, ∑ ℓ, ((binCount (bins ℓ) (n + ρ) : ℝ)
      - (if binCount (bins ℓ) (n + ρ) = 0 then 0 else 1))
      ≤ (X : ℝ) / P₀ * ∑ ℓ, mass (bins ℓ) ^ 2 / 2 + 40 * Real.log 4 * (2 * X : ℕ) / Real.log Y := by
    refine (sum_le_sum hpt).trans ?_
    rw [hswap]
    calc ∑ ℓ, ∑ T ∈ (bins ℓ).powersetCard 2, ∑ n ∈ S, D ℓ T n
        ≤ ∑ ℓ, ∑ T ∈ (bins ℓ).powersetCard 2, ((X : ℝ) / P₀ * ∏ p ∈ T, (p : ℝ)⁻¹
            + (if ∏ p ∈ T, p ≤ 2 * X then 1 else 0)) :=
          sum_le_sum fun ℓ _ => sum_le_sum fun T hT => hpair ℓ T hT
      _ = (X : ℝ) / P₀ * ∑ ℓ, ∑ T ∈ (bins ℓ).powersetCard 2, ∏ p ∈ T, (p : ℝ)⁻¹
          + ∑ ℓ, ∑ T ∈ (bins ℓ).powersetCard 2, (if ∏ p ∈ T, p ≤ 2 * X then (1 : ℝ) else 0) := by
          simp only [sum_add_distrib, mul_sum]
      _ ≤ (X : ℝ) / P₀ * ∑ ℓ, mass (bins ℓ) ^ 2 / 2 + 40 * Real.log 4 * (2 * X : ℕ) / Real.log Y := by
          gcongr with ℓ
          exact hmain ℓ
  have hinv : ((S.card : ℝ))⁻¹ ≤ 2 * P₀ / X := by
    rw [inv_le_comm₀ hspos (by positivity), inv_div]; exact hs
  have hl4 := log_four_lt
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hM0 : 0 ≤ ∑ ℓ, mass (bins ℓ) ^ 2 / 2 := sum_nonneg fun _ _ => by positivity
  have hR0 : 0 ≤ (X : ℝ) / P₀ * ∑ ℓ, mass (bins ℓ) ^ 2 / 2
      + 40 * Real.log 4 * (2 * X : ℕ) / Real.log Y := by positivity
  calc ((S.card : ℝ))⁻¹ * ∑ n ∈ S, ∑ ℓ, ((binCount (bins ℓ) (n + ρ) : ℝ)
        - (if binCount (bins ℓ) (n + ρ) = 0 then 0 else 1))
      ≤ ((S.card : ℝ))⁻¹ * ((X : ℝ) / P₀ * ∑ ℓ, mass (bins ℓ) ^ 2 / 2
          + 40 * Real.log 4 * (2 * X : ℕ) / Real.log Y) :=
        mul_le_mul_of_nonneg_left htot (by positivity)
    _ ≤ 2 * P₀ / X * ((X : ℝ) / P₀ * ∑ ℓ, mass (bins ℓ) ^ 2 / 2
          + 40 * Real.log 4 * (2 * X : ℕ) / Real.log Y) := by gcongr
    _ = ∑ ℓ, mass (bins ℓ) ^ 2 + 160 * Real.log 4 * P₀ / Real.log Y := by
        rw [← sum_div]; push_cast; field_simp; ring
    _ ≤ ∑ ℓ, mass (bins ℓ) ^ 2 + 250 * P₀ / Real.log Y := by
        gcongr; linarith

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
          sum_le_sum fun ℓ _ => abs_one_sub_binDelta_le _ (hbinI ℓ) (hmass ℓ) (one_le_two_mul_dyBase n)
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
