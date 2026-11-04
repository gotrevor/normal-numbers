/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ArithmeticDigitBridge
import NormalNumbers.ArithmeticCoefficientLemmas
import NormalNumbers.ArithmeticWitnessSupply
import NormalNumbers.JointLambertEncodingProof

/-!
# Generic simultaneous words from coefficient arithmetic

The exact-valuation witness supplies one offset with prescribed coefficient
divisibilities and one survivor coefficient.  The digit bridge then reads the
encoded word in each base; the coefficient axioms enter only in this supply
lemma and in the tail majorant.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Finset NormalNumbers.JointLambert

/-- Generic coefficient divisibilities, one prescribed survivor, and a
uniformly small tail in every base. -/
@[blueprint (title := "Coefficient-system supply from exact prime valuations")]
theorem exists_coefficient_small_tail_all_bases
    {f : ℕ → ℕ} (hf : CoefficientSystem f) {c a r : ℕ}
    (hc : 2 ≤ c) (ha : 2 ≤ a) (hr : 1 ≤ r)
    {ε : ℝ} (hε : 0 < ε) (K N : ℕ) :
    ∃ k M : ℕ, K ≤ k ∧ r < k ∧ N ≤ M ∧
      (∀ j, j < k → j ≠ r → c ^ (j + 1) ∣ f (M + 1 + j)) ∧
      f (M + 1 + r) = 2 * a ∧
      ∀ b : ℕ, 2 ≤ b →
        0 ≤ ∑' t : ℕ, (f (M + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) ∧
        ∑' t : ℕ, (f (M + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) < ε / 2 := by
  obtain ⟨e, he, heval⟩ := hf.values c hc
  obtain ⟨E, hE, hsurvivor⟩ := exists_survivor_exponent hf a ha
  obtain ⟨k, n, hkK, hkr, hn1, hnN, hvaluation, hsurvivorData, htail⟩ :=
    exists_exact_valuation_small_tail e E r he hE hr hε K (N + 1)
  let M : ℕ := n - 1
  have hMplus : M + 1 = n := by dsimp [M]; omega
  have hMN : N ≤ M := by dsimp [M]; omega
  have hkill : ∀ j, j < k → j ≠ r → c ^ (j + 1) ∣ f (M + 1 + j) := by
    intro j hj hjr
    obtain ⟨P, hcard, hP⟩ := hvaluation j hj hjr
    have hdvd := pow_card_dvd_of_exact_valuations hf (by omega : 0 < n + j) he P hP heval
    rw [hcard] at hdvd
    simpa [hMplus, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdvd
  have hsurv : f (M + 1 + r) = 2 * a := by
    obtain ⟨p, q, hp, hq, hpq, hfactor⟩ := hsurvivorData
    rw [hMplus, hfactor]
    exact hsurvivor p q hp hq hpq
  refine ⟨k, M, hkK, hkr, hMN, hkill, hsurv, ?_⟩
  intro b hb
  have hb0 : 0 < b := by omega
  have hsTau := JointLambert.summable_base_tail n k hb
  have hsF : Summable (fun t : ℕ =>
      (f (n + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) (fun t => by
      have hnum : (f (n + k + t) : ℝ) ≤ NormalNumbers.SwingC2.tau (n + k + t) :=
        by exact_mod_cast hf.bound (n + k + t)
      exact div_le_div_of_nonneg_right hnum (by positivity)) hsTau
  have hpoint : ∀ t : ℕ,
      (f (n + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) ≤
        (NormalNumbers.SwingC2.tau (n + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) := by
    intro t
    have hnum : (f (n + k + t) : ℝ) ≤ NormalNumbers.SwingC2.tau (n + k + t) :=
      by exact_mod_cast hf.bound (n + k + t)
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hsumle := Summable.tsum_le_tsum hpoint hsF hsTau
  have hsumleM :
      ∑' t : ℕ, (f (M + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) ≤
        ∑' t : ℕ, (NormalNumbers.SwingC2.tau (M + 1 + k + t) : ℝ) /
          (b : ℝ) ^ (k + t + 1) := by
    simpa only [← hMplus] using hsumle
  have hbase := JointLambert.base_tail_le_half_binary_tail n k hb
  have hnonneg : 0 ≤ ∑' t : ℕ,
      (f (n + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) :=
    tsum_nonneg fun t => by positivity
  have hnonnegM : 0 ≤ ∑' t : ℕ,
      (f (M + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) := by
    simpa only [← hMplus] using hnonneg
  refine ⟨hnonnegM, ?_⟩
  calc
    ∑' t : ℕ, (f (M + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1)
      ≤ ∑' t : ℕ,
          (NormalNumbers.SwingC2.tau (n + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) := by
        simpa only [← hMplus] using hsumleM
    _ ≤ (1 / 2 : ℝ) *
        ∑' t : ℕ, (NormalNumbers.SwingC2.tau (n + k + t) : ℝ) / (2 : ℝ) ^ (k + t) := by
      nlinarith [hbase.2]
    _ < ε / 2 := by linarith

/-- One arithmetic coefficient sequence supplies any finite collection of
simultaneous words at a common arbitrarily late offset. -/
@[blueprint (title := "Generic coefficient arithmetic supplies simultaneous words")]
theorem jointCoefficientWords
    (f : ℕ → ℕ) (hf : CoefficientSystem f) (S : Finset ℕ)
    (hb : ∀ b ∈ S, 2 ≤ b) : JointCoefficientWords f S := by
  intro lengths values hwin N
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨N, le_rfl, by simp⟩
  let c : ℕ := ∏ b ∈ S, b
  have hbc : ∀ b ∈ S, b ∣ c := fun b hbS => Finset.dvd_prod_of_mem _ hbS
  have hc2 : 2 ≤ c := by
    obtain ⟨b₀, hb₀⟩ := hne
    have h1 : b₀ ≤ c :=
      Finset.single_le_prod' (f := fun i => i) (fun i hi => by have := hb i hi; omega) hb₀
    have hb₀' := hb b₀ hb₀
    omega
  let P : ℕ := ∏ b ∈ S, b ^ lengths b
  have hPbig : ∀ b ∈ S, b ^ lengths b ≤ P :=
    fun b hbS => Finset.single_le_prod' (f := fun i => i ^ lengths i)
      (fun i hi => Nat.one_le_pow _ _ (by have := hb i hi; omega)) hbS
  have hPpos : 0 < P := Finset.prod_pos fun b hbS => Nat.pow_pos (by have := hb b hbS; omega)
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
  let ε : ℝ := 1 / (P : ℝ)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨s, a, hs2, ha2, hbox⟩ := evenEncoding S hb
      (fun b => (values b : ℝ) / (b : ℝ) ^ lengths b)
      (fun b => ((values b : ℝ) + 1 / 2) / (b : ℝ) ^ lengths b) (by
        intro b hbS
        have hb2 := hb b hbS
        have hb0 : (0 : ℝ) < b := by
          have : (2 : ℝ) ≤ b := by exact_mod_cast hb2
          linarith
        have hbase : (0 : ℝ) < (b : ℝ) ^ lengths b := by positivity
        obtain ⟨hlen, hval⟩ := hwin b hbS
        have hle : (values b : ℝ) + 1 ≤ (b : ℝ) ^ lengths b := by
          have hleN : values b + 1 ≤ b ^ lengths b := by omega
          exact_mod_cast hleN
        refine ⟨by positivity, ?_, ?_⟩
        · rw [div_lt_div_iff₀ hbase hbase]
          nlinarith
        · rw [div_le_one hbase]
          linarith)
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  have hr1 : 1 ≤ r := by omega
  obtain ⟨k, M, hk0, hkr, hMN, hkill, hsurv, htails⟩ :=
    exists_coefficient_small_tail_all_bases hf hc2 ha2 hr1 hε 0 N
  refine ⟨M, hMN, fun b hbS => ?_⟩
  have hb2 := hb b hbS
  have hbase : (0 : ℝ) < (b : ℝ) ^ lengths b := by positivity
  obtain ⟨hlen, hval⟩ := hwin b hbS
  obtain ⟨hlo, hhi⟩ := hbox b hbS
  obtain ⟨hT0, hT⟩ := htails b hb2
  have hmargin : ε / 2 ≤ (1 / 2) / (b : ℝ) ^ lengths b := by
    have hPbigR : (b ^ lengths b : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPbig b hbS
    dsimp [ε]
    rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hPbigR, hbase]
  exact floor_digit_of_coefficient_offset f (coefficient_le_self hf)
    b (lengths b) (values b) c a r k M hb2 (hbc b hbS) hval hkr
    hkill hsurv hlo hhi hT0 (lt_of_lt_of_le hT hmargin)

/-- The generic coefficient arithmetic hypotheses imply the frozen
simultaneous-word target. -/
@[blueprint (title := "Generic arithmetic coefficient system supplies joint words")]
theorem genericArithmeticDisjunctivity : GenericArithmeticDisjunctivity := by
  intro f hf S hb
  exact jointCoefficientWords f hf S hb

/-- Each coefficient series is disjunctive in its defining integer base. -/
@[blueprint (title := "Coefficient series are disjunctive in their defining bases")]
theorem isDisjunctive_coefficientValue
    (f : ℕ → ℕ) (hf : CoefficientSystem f) (b : ℕ) (hb : 2 ≤ b) :
    NormalNumbers.IsDisjunctive b (coefficientValue f b) := by
  rw [NormalNumbers.isDisjunctive_iff_forall_occursAt b hb (coefficientValue f b)]
  intro w hw
  by_cases hnil : w = []
  · subst w
    exact ⟨0, by simp [NormalNumbers.OccursAt]⟩
  have hlen : 0 < w.length := by cases w with | nil => contradiction | cons => simp
  let A := NormalNumbers.blockNatVal b w
  have hA : A < b ^ w.length := by
    dsimp [A]
    exact NormalNumbers.blockNatVal_lt b w hw
  let lengths : ℕ → ℕ := fun _ => w.length
  let values : ℕ → ℕ := fun _ => A
  have hwindow : ∀ x ∈ ({b} : Finset ℕ),
      0 < lengths x ∧ values x < x ^ lengths x := by
    intro x hx
    have hx' : x = b := Finset.mem_singleton.mp hx
    subst x
    exact ⟨hlen, hA⟩
  obtain ⟨n, -, hfloor⟩ := jointCoefficientWords f hf {b} (by simp [hb])
    lengths values hwindow 0
  have hfloor' := hfloor b (by simp)
  have hcell : NormalNumbers.orbit b (coefficientValue f b) n ∈
      Set.Ico ((A : ℝ) / (b : ℝ) ^ w.length)
        (((A : ℝ) + 1) / (b : ℝ) ^ w.length) := by
    rw [Int.floor_eq_iff] at hfloor'
    obtain ⟨hlo, hhi⟩ := hfloor'
    have hbpos : (0 : ℝ) < (b : ℝ) ^ w.length := by positivity
    constructor
    · rw [div_le_iff₀ hbpos]
      simpa [lengths, values, A, mul_comm] using hlo
    · rw [lt_div_iff₀ hbpos]
      simpa [lengths, values, A, mul_comm] using hhi
  exact ⟨n, (NormalNumbers.occursAt_iff_orbit_mem b hb (coefficientValue f b) w hw n).2 hcell⟩

end NormalNumbers.ArithmeticDisjunctivity
