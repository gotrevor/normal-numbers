/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4TransferMoment
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# G4 §4C, C3a: the CRT input

The single remaining input of `G4TransferMoment.norm_sampleAvg_prod_sub_prod_le'`: over the
sample `{n < X : n ≡ a (mod P₀)}`, the average of a product of functions `h_i` periodic modulo
pairwise-coprime moduli `p_i` (all coprime to `P₀`) is within `2Q/|sample|` of the product of
the residue means, `Q = ∏ p_i`.

* `PeriodicMod h p` — `h n = h (n % p)`.
* `sum_range_mul_eq_mul_sum` — the two-modulus CRT factorisation of `∑_{b < mn} f b · g b`.
* `resMean_prod` — the residue mean of a product over pairwise-coprime moduli is the product of
  the residue means (induction on the index set).
* `norm_sampleAvg_sub_resMean_le` — an equidistributed sample (every class mod `Q` within `δ` of
  `|P|/Q`) averages a bounded `Q`-periodic function to within `Qδ/|P|` of its residue mean.
* `abs_card_filter_apSample_sub_le` — the AP segment is equidistributed mod `Q` with `δ = 2`.
* **`crt_input`** — the assembly.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-- `h` depends only on `n mod p`. -/
def PeriodicMod (h : ℕ → ℂ) (p : ℕ) : Prop := ∀ n, h n = h (n % p)

lemma PeriodicMod.of_dvd {h : ℕ → ℂ} {p q : ℕ} (hpq : p ∣ q) (hh : PeriodicMod h p) :
    PeriodicMod h q := by
  intro n
  rw [hh n, hh (n % q), Nat.mod_mod_of_dvd n hpq]

lemma PeriodicMod.congr {h : ℕ → ℂ} {p : ℕ} (hh : PeriodicMod h p) {a b : ℕ}
    (hab : a ≡ b [MOD p]) : h a = h b := by
  rw [hh a, hh b]; exact congrArg h hab

lemma periodicMod_prod {ι : Type*} (T : Finset ι) (h : ι → ℕ → ℂ) (p : ι → ℕ)
    (hper : ∀ i ∈ T, PeriodicMod (h i) (p i)) :
    PeriodicMod (fun n => ∏ i ∈ T, h i n) (∏ i ∈ T, p i) := by
  intro n
  refine Finset.prod_congr rfl fun i hi => ?_
  exact (hper i hi).of_dvd (Finset.dvd_prod_of_mem p hi) n

/-- Residue mean of `h` modulo `p`. -/
noncomputable def resMean (h : ℕ → ℂ) (p : ℕ) : ℂ := (p : ℂ)⁻¹ * ∑ b ∈ range p, h b

/-- **Two-modulus CRT.**  For coprime `m, n` and `f`, `g` periodic mod `m`, `n`,
`∑_{b < mn} f b g b = (∑_{i<m} f i)(∑_{j<n} g j)`. -/
lemma sum_range_mul_eq_mul_sum {m n : ℕ} (hcop : m.Coprime n) (hm : 0 < m) (hn : 0 < n)
    (f g : ℕ → ℂ) (hf : PeriodicMod f m) (hg : PeriodicMod g n) :
    ∑ b ∈ range (m * n), f b * g b = (∑ i ∈ range m, f i) * (∑ j ∈ range n, g j) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij (fun b _ => (b % m, b % n)) ?_ ?_ ?_ ?_
  · intro b _
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hm, Nat.mod_lt _ hn⟩
  · intro b₁ hb₁ b₂ hb₂ heq
    simp only [Prod.mk.injEq] at heq
    have h1 : b₁ ≡ b₂ [MOD m] := heq.1
    have h2 : b₁ ≡ b₂ [MOD n] := heq.2
    have h3 : b₁ ≡ b₂ [MOD m * n] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h1, h2⟩
    have := h3
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 hb₁), Nat.mod_eq_of_lt (Finset.mem_range.1 hb₂)]
      at this
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_product, Finset.mem_range] at hij
    obtain ⟨k, hk⟩ := Nat.chineseRemainder hcop i j
    refine ⟨k % (m * n), Finset.mem_range.2 (Nat.mod_lt _ (Nat.mul_pos hm hn)), ?_⟩
    simp only [Prod.mk.injEq]
    constructor
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m n)]
      have := hk.1; unfold Nat.ModEq at this
      rw [this]; exact Nat.mod_eq_of_lt hij.1
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_left n m)]
      have := hk.2; unfold Nat.ModEq at this
      rw [this]; exact Nat.mod_eq_of_lt hij.2
  · intro b _
    simp only
    rw [hf b, hg b]

/-- **The residue mean of a product is the product of the residue means**, for pairwise-coprime
moduli. -/
lemma resMean_prod {ι : Type*} [DecidableEq ι] (T : Finset ι) (h : ι → ℕ → ℂ) (p : ι → ℕ)
    (hp : ∀ i ∈ T, 0 < p i) (hcop : (T : Set ι).Pairwise (fun i j => (p i).Coprime (p j)))
    (hper : ∀ i ∈ T, PeriodicMod (h i) (p i)) :
    resMean (fun n => ∏ i ∈ T, h i n) (∏ i ∈ T, p i) = ∏ i ∈ T, resMean (h i) (p i) := by
  induction T using Finset.induction_on with
  | empty =>
    simp [resMean]
  | insert a T haT ih =>
    have hpa : 0 < p a := hp a (Finset.mem_insert_self a T)
    have hpT : ∀ i ∈ T, 0 < p i := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hperT : ∀ i ∈ T, PeriodicMod (h i) (p i) := fun i hi =>
      hper i (Finset.mem_insert_of_mem hi)
    have hcopT : (T : Set ι).Pairwise (fun i j => (p i).Coprime (p j)) :=
      hcop.mono (by intro x hx; simp only [Finset.coe_insert, Set.mem_insert_iff]; exact Or.inr hx)
    have hcopa : (p a).Coprime (∏ i ∈ T, p i) := by
      rw [Nat.coprime_prod_right_iff]
      intro i hi
      exact hcop (Finset.mem_insert_self a T) (Finset.mem_insert_of_mem hi)
        (fun h => haT (h ▸ hi))
    have hQT : 0 < ∏ i ∈ T, p i := Finset.prod_pos hpT
    rw [Finset.prod_insert haT, Finset.prod_insert haT, ← ih hpT hcopT hperT]
    simp only [resMean]
    rw [show (fun n => ∏ i ∈ insert a T, h i n) = fun n => h a n * ∏ i ∈ T, h i n from
      funext fun n => Finset.prod_insert haT]
    rw [sum_range_mul_eq_mul_sum hcopa hpa hQT (h a) (fun n => ∏ i ∈ T, h i n)
      (hper a (Finset.mem_insert_self a T)) (periodicMod_prod T h p hperT)]
    push_cast
    rw [mul_inv]
    ring

/-! ### From equidistribution of the sample to the average -/

/-- An equidistributed sample averages a bounded `Q`-periodic function to within `Qδ/|P|` of its
residue mean. -/
lemma norm_sampleAvg_sub_resMean_le (P : Finset ℕ) (hP : P.Nonempty) {Q : ℕ} (hQ : 0 < Q)
    (h : ℕ → ℂ) (hper : PeriodicMod h Q) (hb : ∀ n, ‖h n‖ ≤ 1) {δ : ℝ}
    (hδ : ∀ c ∈ range Q,
      |((P.filter (fun n => n % Q = c)).card : ℝ) - (P.card : ℝ) / Q| ≤ δ) :
    ‖sampleAvg P id h - resMean h Q‖ ≤ Q * δ / P.card := by
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.2 hP
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  set N : ℕ → ℕ := fun c => (P.filter (fun n => n % Q = c)).card with hN
  -- fiberwise decomposition of the sample sum
  have hsum : ∑ n ∈ P, h n = ∑ c ∈ range Q, (N c : ℂ) * h c := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := range Q) (g := fun n => n % Q)
      (fun n _ => Finset.mem_range.2 (Nat.mod_lt n hQ))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_congr rfl (fun n hn => by
      rw [hper n, (Finset.mem_filter.1 hn).2] : ∀ n ∈ P.filter (fun n => n % Q = c), h n = h c)]
    rw [Finset.sum_const, nsmul_eq_mul]
  -- the difference as a single weighted sum
  have hdiff : sampleAvg P id h - resMean h Q
      = (P.card : ℂ)⁻¹ * ∑ c ∈ range Q, h c * (((N c : ℝ) - (P.card : ℝ) / Q : ℝ) : ℂ) := by
    unfold sampleAvg resMean
    simp only [id_eq, hsum, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    have hc0 : (P.card : ℂ) ≠ 0 := by exact_mod_cast hcard.ne'
    have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQr.ne'
    push_cast
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun c _ => by ring
    · exact Finset.sum_congr rfl fun c _ => by field_simp
  rw [hdiff, norm_mul, norm_inv, Complex.norm_natCast]
  rw [show (Q : ℝ) * δ / P.card = (P.card : ℝ)⁻¹ * (δ * Q) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hcard.le)
  calc ‖∑ c ∈ range Q, h c * (((N c : ℝ) - (P.card : ℝ) / Q : ℝ) : ℂ)‖
      ≤ ∑ c ∈ range Q, ‖h c * (((N c : ℝ) - (P.card : ℝ) / Q : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ range Q, δ := by
        refine Finset.sum_le_sum fun c hc => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc ‖h c‖ * |(N c : ℝ) - (P.card : ℝ) / Q| ≤ 1 * δ :=
              mul_le_mul (hb c) (hδ c hc) (abs_nonneg _) zero_le_one
          _ = δ := one_mul δ
    _ = δ * Q := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/-! ### The arithmetic-progression sample is equidistributed modulo coprime `Q` -/

/-- `|#{n < X : n ≡ c (mod m)} − X/m| ≤ 1`. -/
lemma abs_card_filter_modEq_sub_le (X m c : ℕ) (hm : 0 < m) :
    |(((range X).filter (fun n => n ≡ c [MOD m])).card : ℝ) - (X : ℝ) / m| ≤ 1 := by
  have hcount : ((range X).filter (fun n => n ≡ c [MOD m])).card
      = X / m + if c % m < X % m then 1 else 0 := by
    rw [← Nat.count_eq_card_filter_range]
    exact Nat.count_modEq_card X hm c
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  -- `X/m` (floor) is within one of the real quotient
  have hdiv : (X : ℝ) / m - 1 < ((X / m : ℕ) : ℝ) ∧ ((X / m : ℕ) : ℝ) ≤ (X : ℝ) / m := by
    constructor
    · have h1 : X = m * (X / m) + X % m := (Nat.div_add_mod X m).symm
      have h2 : X % m < m := Nat.mod_lt X hm
      have h1r : (X : ℝ) = m * ((X / m : ℕ) : ℝ) + ((X % m : ℕ) : ℝ) := by exact_mod_cast h1
      have h2r : ((X % m : ℕ) : ℝ) < m := by exact_mod_cast h2
      rw [div_sub_one hmr.ne', div_lt_iff₀ hmr]
      linarith
    · exact Nat.cast_div_le
  rw [hcount]
  split_ifs with hc
  · push_cast
    rw [abs_le]; constructor <;> linarith [hdiv.1, hdiv.2]
  · push_cast
    rw [abs_le]; constructor <;> linarith [hdiv.1, hdiv.2]

/-- The sample `{n < X : n % P₀ = a}`. -/
def apSample (X P₀ a : ℕ) : Finset ℕ := (range X).filter (fun n => n % P₀ = a)

lemma apSample_eq_filter_modEq (X P₀ a : ℕ) (ha : a < P₀) :
    apSample X P₀ a = (range X).filter (fun n => n ≡ a [MOD P₀]) := by
  unfold apSample
  congr 1
  ext n
  simp only [Nat.ModEq, Nat.mod_eq_of_lt ha]

/-- The class `n % Q = c` inside the AP sample is a single class modulo `P₀ Q`. -/
lemma apSample_filter_eq (X P₀ a Q c : ℕ) (hcop : P₀.Coprime Q) (ha : a < P₀) (hc : c < Q) :
    (apSample X P₀ a).filter (fun n => n % Q = c)
      = (range X).filter (fun n => n ≡ (Nat.chineseRemainder hcop a c : ℕ) [MOD P₀ * Q]) := by
  unfold apSample
  rw [Finset.filter_filter]
  congr 1
  ext n
  obtain ⟨hk1, hk2⟩ := (Nat.chineseRemainder hcop a c).prop
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · exact (show n ≡ a [MOD P₀] by unfold Nat.ModEq; rw [h1, Nat.mod_eq_of_lt ha]).trans hk1.symm
    · exact (show n ≡ c [MOD Q] by unfold Nat.ModEq; rw [h2, Nat.mod_eq_of_lt hc]).trans hk2.symm
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := h1.trans hk1; unfold Nat.ModEq at this; rwa [Nat.mod_eq_of_lt ha] at this
    · have := h2.trans hk2; unfold Nat.ModEq at this; rwa [Nat.mod_eq_of_lt hc] at this

/-- **Equidistribution of the AP sample modulo coprime `Q`**, with deviation `2`. -/
lemma abs_card_filter_apSample_sub_le (X P₀ a Q : ℕ) (hP₀ : 0 < P₀) (hQ : 0 < Q)
    (hcop : P₀.Coprime Q) (ha : a < P₀) (c : ℕ) (hc : c ∈ range Q) :
    |(((apSample X P₀ a).filter (fun n => n % Q = c)).card : ℝ)
        - ((apSample X P₀ a).card : ℝ) / Q| ≤ 2 := by
  have hcQ : c < Q := Finset.mem_range.1 hc
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hP₀r : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have h1 := abs_card_filter_modEq_sub_le X (P₀ * Q) (Nat.chineseRemainder hcop a c) (Nat.mul_pos hP₀ hQ)
  have h2 := abs_card_filter_modEq_sub_le X P₀ a hP₀
  rw [← apSample_filter_eq X P₀ a Q c hcop ha hcQ] at h1
  rw [← apSample_eq_filter_modEq X P₀ a ha] at h2
  push_cast at h1
  have hQ1 : (1 : ℝ) / Q ≤ 1 := by
    rw [div_le_one hQr]; exact_mod_cast hQ
  set N : ℝ := (((apSample X P₀ a).filter (fun n => n % Q = c)).card : ℝ)
  set C : ℝ := ((apSample X P₀ a).card : ℝ)
  have hu : (X : ℝ) / (P₀ * Q) = (X : ℝ) / P₀ / Q := by rw [div_div]
  rw [hu] at h1
  rw [abs_le] at h1 h2 ⊢
  have h2' : |C / Q - (X : ℝ) / P₀ / Q| ≤ 1 / Q := by
    rw [← sub_div, abs_div, abs_of_pos hQr]
    exact div_le_div_of_nonneg_right (abs_le.2 h2) hQr.le
  rw [abs_le] at h2'
  constructor <;> linarith [h1.1, h1.2, h2'.1, h2'.2, hQ1]

/-! ### The assembly -/

/-- **The CRT input (C3a).**  Over the AP sample `{n < X : n ≡ a (mod P₀)}`, the average of a
product of bounded functions periodic modulo pairwise-coprime moduli `p_i` (each coprime to `P₀`)
is within `2Q/|sample|` of the product of the residue means, `Q = ∏ p_i`. -/
theorem crt_input {ι : Type*} [DecidableEq ι] (X P₀ a : ℕ) (hP₀ : 0 < P₀) (ha : a < P₀)
    (hne : (apSample X P₀ a).Nonempty)
    (T : Finset ι) (p : ι → ℕ) (hp : ∀ i ∈ T, 0 < p i)
    (hcop : (T : Set ι).Pairwise (fun i j => (p i).Coprime (p j)))
    (hcopP : ∀ i ∈ T, (p i).Coprime P₀)
    (h : ι → ℕ → ℂ) (hper : ∀ i ∈ T, PeriodicMod (h i) (p i))
    (hb : ∀ i ∈ T, ∀ n, ‖h i n‖ ≤ 1) :
    ‖sampleAvg (apSample X P₀ a) id (fun n => ∏ i ∈ T, h i n) - ∏ i ∈ T, resMean (h i) (p i)‖
      ≤ 2 * (∏ i ∈ T, (p i : ℝ)) / (apSample X P₀ a).card := by
  have hQ : 0 < ∏ i ∈ T, p i := Finset.prod_pos hp
  have hcopQ : P₀.Coprime (∏ i ∈ T, p i) := by
    rw [Nat.coprime_prod_right_iff]
    exact fun i hi => (hcopP i hi).symm
  rw [← resMean_prod T h p hp hcop hper]
  have hbound : ∀ n, ‖∏ i ∈ T, h i n‖ ≤ 1 := fun n => by
    rw [norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) fun i hi => hb i hi n
  have := norm_sampleAvg_sub_resMean_le (apSample X P₀ a) hne hQ _ (periodicMod_prod T h p hper)
    hbound (δ := 2) (fun c hc => abs_card_filter_apSample_sub_le X P₀ a _ hP₀ hQ hcopQ ha c hc)
  calc _ ≤ ((∏ i ∈ T, p i : ℕ) : ℝ) * 2 / (apSample X P₀ a).card := this
    _ = _ := by push_cast; ring

end NormalNumbers.G4
