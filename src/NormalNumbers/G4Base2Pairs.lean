/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2N5
import NormalNumbers.G4Base2Bins

/-!
# N4 ingredients: prime pairs

* `sum_inv_mul_log_le`: `Σ_{p > Y} 1/(p log p) ≤ 40/log Y` (Mertens on linear log-blocks).
* `card_pairs_le`: prime pairs `> Y` with product `≤ x` number `≤ 40 log 4 · x / log Y`.
* `two_mul_sum_pairs_le`: `2 Σ_{p<q} f(p)f(q) ≤ (Σ f)²`.
* `card_apSample_ge`, `card_apSample_dvd_le`: AP sample size and CRT count of `d ∣ n + ρ`.
* `choose_binCount_eq`: `C(binCount I m, 2)` is the number of prime pairs of `I` dividing `m`.
-/

open Finset
namespace NormalNumbers.G4.Base2
open NormalNumbers.CastingOut

lemma sum_inv_sq_le_two : ∀ n : ℕ, ∑ i ∈ range n, ((i + 1 : ℕ) : ℝ)⁻¹ ^ 2 ≤ 2 - 2 * (n + 1 : ℝ)⁻¹
  | 0 => by norm_num
  | n + 1 => by
    rw [Finset.sum_range_succ]
    have ih := sum_inv_sq_le_two n
    have h1 : (0 : ℝ) < n + 1 := by positivity
    have : ((n + 1 : ℕ) : ℝ)⁻¹ ^ 2 ≤ 2 * ((n : ℝ) + 1)⁻¹ - 2 * ((n : ℝ) + 2)⁻¹ := by
      push_cast
      rw [inv_pow, ← mul_sub, inv_sub_inv (by positivity) (by positivity), ← one_div,
        mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast at this ih ⊢
    have e : (n : ℝ) + 1 + 1 = n + 2 := by ring
    rw [e]; linarith

/-- `Σ_{Y < p ≤ x, p prime} 1/(p log p) ≤ 40 / log Y` for `Y ≥ 2`. -/
theorem sum_inv_mul_log_le {Y : ℕ} (hY : 2 ≤ Y) (x : ℕ) :
    ∑ p ∈ (Iic x).filter (fun p => p.Prime ∧ Y < p), ((p : ℝ) * Real.log p)⁻¹
      ≤ 40 / Real.log Y := by
  set W := (Iic x).filter (fun p => p.Prime ∧ Y < p) with hW
  have hYr : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  set L := Real.log Y with hL
  have hL0 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hYr
  have hl2 := Real.log_two_gt_d9
  have hLpos : 0 < L := by linarith
  set g : ℕ → ℕ := fun p => ⌈Real.log p / L⌉₊ - 2 with hg
  set K := ⌈Real.log x / L⌉₊ with hK
  have hblk : ∀ p ∈ W, g p ∈ range K ∧ ((g p + 1 : ℕ) : ℝ) * L < Real.log p ∧
      Real.log p ≤ ((g p + 2 : ℕ) : ℝ) * L := by
    intro p hp
    rw [hW, mem_filter, mem_Iic] at hp
    have hpY : (Y : ℝ) < p := by exact_mod_cast hp.2.2
    have hpx : (p : ℝ) ≤ x := by exact_mod_cast hp.1
    have h1 : L < Real.log p := Real.log_lt_log (by linarith) hpY
    have h2 : Real.log p ≤ Real.log x := Real.log_le_log (by linarith) hpx
    have hr1 : 1 < Real.log p / L := by rw [lt_div_iff₀ hLpos]; linarith
    set c := ⌈Real.log p / L⌉₊ with hc
    have hc1 : Real.log p / L ≤ c := Nat.le_ceil _
    have hc2 : (c : ℝ) < Real.log p / L + 1 := Nat.ceil_lt_add_one (by linarith)
    have hc21 : 2 ≤ c := by
      have : (1 : ℝ) < c := by linarith
      exact_mod_cast (show (1 : ℝ) < c from this)
    have hcK : c ≤ K := Nat.ceil_le_ceil (div_le_div_of_nonneg_right h2 hLpos.le)
    have hgc : ((g p + 2 : ℕ) : ℝ) = c := by
      simp only [hg]; rw [← hc]; congr 1; omega
    have hgc' : ((g p + 1 : ℕ) : ℝ) = c - 1 := by
      rw [show g p + 1 = (g p + 2) - 1 by omega, Nat.cast_sub (by omega), hgc]; simp
    refine ⟨mem_range.2 (by simp only [hg]; omega), ?_, ?_⟩
    · rw [hgc']
      have := (lt_div_iff₀ hLpos).1 (by linarith : (c : ℝ) - 1 < Real.log p / L)
      linarith
    · rw [hgc]; exact (div_le_iff₀ hLpos).1 hc1
  rw [← sum_fiberwise_of_maps_to (g := g) (t := range K) (fun p hp => (hblk p hp).1)]
  have hfib : ∀ i ∈ range K, ∑ p ∈ W with g p = i, ((p : ℝ) * Real.log p)⁻¹
      ≤ (L + 12) / L ^ 2 * ((i + 1 : ℕ) : ℝ)⁻¹ ^ 2 := by
    intro i _
    have hk : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ i + 1)
    have hkL : 0 < ((i + 1 : ℕ) : ℝ) * L := by positivity
    have hpt : ∀ p ∈ W.filter (fun p => g p = i),
        ((p : ℝ) * Real.log p)⁻¹ ≤ ((((i + 1 : ℕ) : ℝ) * L)⁻¹) ^ 2 * (Real.log p / (p : ℝ)) := by
      intro p hp
      obtain ⟨hpW, hgi⟩ := mem_filter.1 hp
      obtain ⟨-, hlo, -⟩ := hblk p hpW
      rw [hgi] at hlo
      have hp0 : (0 : ℝ) < p := by
        have := (mem_filter.1 hpW).2.1.pos; exact_mod_cast this
      have hlp : 0 < Real.log p := by linarith
      have e : ((p : ℝ) * Real.log p)⁻¹ = (Real.log p)⁻¹ ^ 2 * (Real.log p / (p : ℝ)) := by
        field_simp
      rw [e]
      gcongr
    have hsubW : W.filter (fun p => g p = i) ⊆
        primesLe ⌊Real.exp (((i + 2 : ℕ) : ℝ) * L)⌋₊ \ primesLe ⌊Real.exp (((i + 1 : ℕ) : ℝ) * L)⌋₊ := by
      intro p hp
      obtain ⟨hpW, hgi⟩ := mem_filter.1 hp
      obtain ⟨-, hlo, hhi⟩ := hblk p hpW
      rw [hgi] at hlo hhi
      have hpr := (mem_filter.1 hpW).2.1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
      rw [mem_sdiff]
      simp only [primesLe, mem_filter, mem_range]
      refine ⟨⟨Nat.lt_succ_of_le (Nat.le_floor ?_), hpr⟩, fun h => ?_⟩
      · rw [← Real.exp_log hp0]; exact Real.exp_le_exp.2 hhi
      · have h1 : (p : ℝ) ≤ ⌊Real.exp (((i + 1 : ℕ) : ℝ) * L)⌋₊ := by exact_mod_cast (by omega)
        have h2 := Nat.floor_le (Real.exp_pos (((i + 1 : ℕ) : ℝ) * L)).le
        have h3 := Real.log_le_log hp0 (h1.trans h2)
        rw [Real.log_exp] at h3
        linarith
    have hw := mertens_window (a := ((i + 1 : ℕ) : ℝ) * L) (b := ((i + 2 : ℕ) : ℝ) * L)
      (by positivity) (by gcongr; omega)
    have hw' : ((i + 2 : ℕ) : ℝ) * L - ((i + 1 : ℕ) : ℝ) * L = L := by push_cast; ring
    rw [hw'] at hw
    calc ∑ p ∈ W with g p = i, ((p : ℝ) * Real.log p)⁻¹
        ≤ ∑ p ∈ W with g p = i, ((((i + 1 : ℕ) : ℝ) * L)⁻¹) ^ 2 * (Real.log p / (p : ℝ)) :=
          sum_le_sum hpt
      _ = ((((i + 1 : ℕ) : ℝ) * L)⁻¹) ^ 2 * ∑ p ∈ W with g p = i, Real.log p / (p : ℝ) := by
          rw [mul_sum]
      _ ≤ ((((i + 1 : ℕ) : ℝ) * L)⁻¹) ^ 2 * (L + 12) := by
          gcongr
          refine (sum_le_sum_of_subset_of_nonneg hsubW fun p hp _ => ?_).trans hw
          have := (mem_filter.1 (mem_sdiff.1 hp).1).2.pos
          have : (1 : ℝ) ≤ p := by exact_mod_cast this
          exact div_nonneg (Real.log_nonneg this) (by linarith)
      _ = (L + 12) / L ^ 2 * ((i + 1 : ℕ) : ℝ)⁻¹ ^ 2 := by field_simp
  refine (sum_le_sum hfib).trans ?_
  rw [← mul_sum]
  have hS := sum_inv_sq_le_two K
  have hS' : ∑ i ∈ range K, ((i + 1 : ℕ) : ℝ)⁻¹ ^ 2 ≤ 2 := by
    have : 0 ≤ 2 * ((K : ℝ) + 1)⁻¹ := by positivity
    linarith
  have hc0 : 0 ≤ (L + 12) / L ^ 2 := by positivity
  calc (L + 12) / L ^ 2 * ∑ i ∈ range K, ((i + 1 : ℕ) : ℝ)⁻¹ ^ 2 ≤ (L + 12) / L ^ 2 * 2 := by gcongr
    _ ≤ 40 / L := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hLpos]
        nlinarith

/-- **Pair count.**  Pairs of primes `> Y` with product `≤ x` number `≤ 40 log 4 · x / log Y`. -/
theorem card_pairs_le {U : Finset ℕ} {Y : ℕ} (hY : 2 ≤ Y) (hU : ∀ p ∈ U, p.Prime ∧ Y < p) (x : ℕ) :
    (((U.powersetCard 2).filter (fun T => ∏ p ∈ T, p ≤ x)).card : ℝ)
      ≤ 40 * Real.log 4 * x / Real.log Y := by
  set W := (Iic x).filter (fun p => p.Prime ∧ Y < p)
  set V : ℕ → Finset ℕ := fun p => (Iic (x / p)).filter (fun q => q.Prime ∧ p < q)
  have hsub : (U.powersetCard 2).filter (fun T => ∏ p ∈ T, p ≤ x) ⊆
      W.biUnion (fun p => (V p).image (fun q => ({p, q} : Finset ℕ))) := by
    intro T hT
    rw [mem_filter, mem_powersetCard, card_eq_two] at hT
    obtain ⟨⟨hTU, a, b, hab, rfl⟩, hx⟩ := hT
    have ha := hU a (hTU (by simp)); have hb := hU b (hTU (by simp))
    rw [prod_pair hab] at hx
    rw [mem_biUnion]
    rcases lt_or_gt_of_ne hab with h | h
    · refine ⟨a, ?_, mem_image.2 ⟨b, ?_, rfl⟩⟩
      · simp only [W, mem_filter, mem_Iic]
        exact ⟨le_trans (Nat.le_mul_of_pos_right a hb.1.pos) hx, ha⟩
      · simp only [V, mem_filter, mem_Iic]
        exact ⟨(Nat.le_div_iff_mul_le ha.1.pos).2 (by linarith [mul_comm a b]), hb.1, h⟩
    · refine ⟨b, ?_, mem_image.2 ⟨a, ?_, pair_comm _ _⟩⟩
      · simp only [W, mem_filter, mem_Iic]
        exact ⟨le_trans (Nat.le_mul_of_pos_left b ha.1.pos) hx, hb⟩
      · simp only [V, mem_filter, mem_Iic]
        exact ⟨(Nat.le_div_iff_mul_le hb.1.pos).2 hx, ha.1, h⟩
  have hYr : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ((Nat.cast_le (α := ℝ)).2 ((card_le_card hsub).trans card_biUnion_le)).trans ?_
  push_cast
  have hterm : ∀ p ∈ W, (((V p).image (fun q => ({p, q} : Finset ℕ))).card : ℝ)
      ≤ x * Real.log 4 * ((p : ℝ) * Real.log p)⁻¹ := by
    intro p hp
    have hpr := (mem_filter.1 hp).2.1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
    have hlp : 0 < Real.log p := Real.log_pos (by linarith)
    refine (Nat.cast_le.2 card_image_le).trans ?_
    have hc := card_primes_window_mul_log_le p (x / p) hpr.one_lt.le
    have hd : ((x / p : ℕ) : ℝ) ≤ (x : ℝ) / p := Nat.cast_div_le
    rw [← le_div_iff₀ hlp] at hc
    refine hc.trans ?_
    rw [div_le_iff₀ hlp]
    calc ((x / p : ℕ) : ℝ) * Real.log 4 ≤ (x : ℝ) / p * Real.log 4 := by gcongr
      _ = _ := by field_simp
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hs := sum_inv_mul_log_le hY x
  calc x * Real.log 4 * ∑ p ∈ W, ((p : ℝ) * Real.log p)⁻¹ ≤ x * Real.log 4 * (40 / Real.log Y) := by
        gcongr
    _ = _ := by ring

/-- `2 Σ_{p<q} f(p) f(q) ≤ (Σ f)²` for `f ≥ 0`. -/
theorem two_mul_sum_pairs_le (I : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    2 * ∑ T ∈ I.powersetCard 2, ∏ p ∈ T, f p ≤ (∑ p ∈ I, f p) ^ 2 := by
  induction I using Finset.induction_on with
  | empty => rw [powersetCard_eq_empty.2 (by simp)]; simp
  | insert a s ha ih =>
    rw [powersetCard_succ_insert ha, sum_union, sum_image, sum_insert ha]
    · have h1 : ∑ T ∈ s.powersetCard 1, ∏ p ∈ insert a T, f p = f a * ∑ p ∈ s, f p := by
        rw [powersetCard_one, sum_map, mul_sum]
        refine sum_congr rfl fun q hq => ?_
        have : a ≠ q := fun h => ha (h ▸ hq)
        exact prod_pair this
      rw [h1]
      have := hf a
      have : 0 ≤ ∑ p ∈ s, f p := sum_nonneg fun p _ => hf p
      nlinarith
    · intro T hT T' hT' h
      have hT1 : a ∉ T := fun h' => ha ((mem_powersetCard.1 hT).1 h')
      have hT1' : a ∉ T' := fun h' => ha ((mem_powersetCard.1 hT').1 h')
      have := congrArg (fun S => S.erase a) h
      simpa [erase_insert hT1, erase_insert hT1'] using this
    · rw [disjoint_left]
      intro T hT hT'
      obtain ⟨T', -, rfl⟩ := mem_image.1 hT'
      exact ha ((mem_powersetCard.1 hT).1 (mem_insert_self a T'))

/-- The AP sample has `≥ X/P₀ − 1` points. -/
lemma card_apSample_ge (X P₀ b₀ : ℕ) (hP₀ : 0 < P₀) (hb : b₀ < P₀) :
    (X : ℝ) / P₀ - 1 ≤ (apSample X P₀ b₀).card := by
  rw [apSample_eq_filter_modEq X P₀ b₀ hb, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card _ hP₀]
  have h1 : ((X / P₀ : ℕ) : ℝ) ≤ ((X / P₀ + if b₀ % P₀ < X % P₀ then 1 else 0 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right _ _
  have h2 : (X : ℝ) / P₀ - 1 ≤ ((X / P₀ : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := X) hP₀
    have hP : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
    rw [sub_le_iff_le_add, div_le_iff₀ hP]
    have : (X : ℝ) < ((X / P₀ : ℕ) : ℝ) * P₀ + P₀ := by exact_mod_cast this
    linarith
  linarith

/-- AP count of `d ∣ n + ρ`, `d` coprime to `P₀`. -/
lemma card_apSample_dvd_le {X P₀ b₀ ρ d : ℕ} (hP₀ : 0 < P₀) (hd : 0 < d) (hρ : 0 < ρ)
    (hcop : P₀.Coprime d) :
    (((apSample X P₀ b₀).filter (fun n => d ∣ n + ρ)).card : ℝ) ≤ (X : ℝ) / (P₀ * d) + 1 := by
  set A := ρ - 1
  have hinj : ((apSample X P₀ b₀).filter (fun n => d ∣ n + ρ)).card ≤
      ((Ioc A (A + X)).filter (fun m => m % P₀ = (b₀ + ρ) % P₀ ∧ d ∣ m)).card := by
    refine card_le_card_of_injOn (fun n => n + ρ) (fun n hn => ?_) (fun a _ b _ h => by simpa using h)
    simp only [apSample, mem_filter, mem_range, coe_filter, Set.mem_ofPred_eq] at hn ⊢
    refine ⟨mem_Ioc.2 ⟨by omega, by omega⟩, ?_, hn.2⟩
    rw [Nat.add_mod, hn.1.2, Nat.add_mod_mod]
  have hc := abs_card_Ioc_mod_dvd_sub_le (A := A) (B := A + X) (by omega) hP₀ hd hcop (b₀ + ρ)
  rw [abs_le] at hc
  have : ((A + X : ℕ) : ℝ) - A = X := by push_cast; ring
  rw [this] at hc
  have := (Nat.cast_le (α := ℝ)).2 hinj
  linarith

/-- `C(binCount I m, 2)` counts the prime pairs of `I` dividing `m`. -/
lemma choose_binCount_eq {I : Finset ℕ} (hI : ∀ p ∈ I, p.Prime) (m : ℕ) :
    (binCount I m).choose 2 = ((I.powersetCard 2).filter (fun T => (∏ p ∈ T, p) ∣ m)).card := by
  unfold binCount
  rw [← card_powersetCard]
  congr 1
  ext T
  simp only [mem_powersetCard, mem_filter]
  constructor
  · rintro ⟨hT, hc⟩
    refine ⟨⟨fun p hp => (mem_filter.1 (hT hp)).1, hc⟩, ?_⟩
    exact (prod_dvd_iff (fun p hp => hI p (mem_filter.1 (hT hp)).1) m).2
      fun p hp => (mem_filter.1 (hT hp)).2
  · rintro ⟨⟨hT, hc⟩, hd⟩
    refine ⟨fun p hp => mem_filter.2 ⟨hT hp, ?_⟩, hc⟩
    exact (prod_dvd_iff (fun p hp => hI p (hT hp)) m).1 hd p hp
end NormalNumbers.G4.Base2
