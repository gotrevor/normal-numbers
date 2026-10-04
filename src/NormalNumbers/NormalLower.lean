/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFConcat

/-!
# Normality from lower bounds alone

Generic counting tools for Champernowne-type normality proofs (after the
`ChampernowneNormality` project, Apache 2.0, same author):

* `isNormalSequence_of_lower` — the upper frequency bound is free: if every word of length `ℓ`
  has `count ≥ (b^{-ℓ} - ε) n` eventually, the window pigeonhole over all `b^ℓ` words of that
  length forces `count ≤ (b^{-ℓ} + ε) n` as well.
* `le_card_Ico_filter_div_mod'` — a periodic digit condition `n / p % q = d` holds at least
  `(t/(pq) - 1)·p` times on ANY interval of length `t` (no alignment needed).
* `mod_pow_eq_lval` — a residue `x mod k^ℓ` equal to the little-endian value of `v` pins the
  digits of `x` at places `0, …, ℓ-1` to `v`.
-/

namespace NormalNumbers.NormalLower

open Filter Finset

/-- All length-`ℓ` words over `{0, …, b-1}`. -/
def allWords (b : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | ℓ + 1 => (Finset.range b).biUnion fun d => (allWords b ℓ).image (d :: ·)

theorem mem_allWords {b ℓ : ℕ} {l : List ℕ} :
    l ∈ allWords b ℓ ↔ l.length = ℓ ∧ ∀ d ∈ l, d < b := by
  induction ℓ generalizing l with
  | zero => cases l <;> simp [allWords]
  | succ ℓ ih =>
    simp only [allWords, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨d, hd, v, hv, rfl⟩
      obtain ⟨hlen, hlt⟩ := ih.mp hv
      refine ⟨by simp [hlen], ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · exact hd
      · exact hlt e he'
    · rintro ⟨hlen, hlt⟩
      cases l with
      | nil => simp at hlen
      | cons d v =>
        exact ⟨d, hlt d (List.mem_cons_self ..), v,
          ih.mpr ⟨by simpa using hlen, fun e he => hlt e (List.mem_cons_of_mem d he)⟩, rfl⟩

theorem card_allWords (b ℓ : ℕ) : (allWords b ℓ).card = b ^ ℓ := by
  induction ℓ with
  | zero => simp [allWords]
  | succ ℓ ih =>
    have hdisj : ∀ d₁ ∈ Finset.range b, ∀ d₂ ∈ Finset.range b, d₁ ≠ d₂ →
        Disjoint ((allWords b ℓ).image (d₁ :: ·)) ((allWords b ℓ).image (d₂ :: ·)) := by
      intro d₁ _ d₂ _ hne
      rw [Finset.disjoint_left]
      rintro l hl₁ hl₂
      obtain ⟨v₁, -, rfl⟩ := Finset.mem_image.mp hl₁
      obtain ⟨v₂, -, heq⟩ := Finset.mem_image.mp hl₂
      injection heq with h1 _
      exact hne h1.symm
    calc (allWords b (ℓ + 1)).card
        = ∑ d ∈ Finset.range b, ((allWords b ℓ).image (d :: ·)).card :=
          Finset.card_biUnion hdisj
    _ = ∑ _d ∈ Finset.range b, (allWords b ℓ).card :=
          Finset.sum_congr rfl fun d _ =>
            Finset.card_image_of_injective _ fun v₁ v₂ h => by injection h
    _ = b ^ (ℓ + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ih, pow_succ']

/-- Window pigeonhole: each start position matches at most one word of a given length. -/
theorem sum_countOccurrences_allWords_le (b ℓ : ℕ) (l : List ℕ) :
    ∑ v ∈ allWords b ℓ, countOccurrences v l ≤ l.length + 1 := by
  have hdisj : ∀ v₁ ∈ allWords b ℓ, ∀ v₂ ∈ allWords b ℓ, v₁ ≠ v₂ →
      Disjoint
        ((Finset.range (l.length + 1)).filter (fun j => v₁.isPrefixOf (l.drop j)))
        ((Finset.range (l.length + 1)).filter (fun j => v₂.isPrefixOf (l.drop j))) := by
    intro v₁ h₁ v₂ h₂ hne
    rw [Finset.disjoint_left]
    rintro j hj₁ hj₂
    have hp₁ := List.isPrefixOf_iff_prefix.mp (Finset.mem_filter.mp hj₁).2
    have hp₂ := List.isPrefixOf_iff_prefix.mp (Finset.mem_filter.mp hj₂).2
    have hlen₁ := (mem_allWords.mp h₁).1
    have hlen₂ := (mem_allWords.mp h₂).1
    apply hne
    calc v₁ = (l.drop j).take v₁.length := List.prefix_iff_eq_take.mp hp₁
    _ = (l.drop j).take v₂.length := by rw [hlen₁, hlen₂]
    _ = v₂ := (List.prefix_iff_eq_take.mp hp₂).symm
  calc ∑ v ∈ allWords b ℓ, countOccurrences v l
      = ∑ v ∈ allWords b ℓ, ((Finset.range (l.length + 1)).filter
            (fun j => v.isPrefixOf (l.drop j))).card :=
        Finset.sum_congr rfl fun v _ => countOccurrences_eq_card v l
  _ = ((allWords b ℓ).biUnion fun v => (Finset.range (l.length + 1)).filter
          (fun j => v.isPrefixOf (l.drop j))).card := (Finset.card_biUnion hdisj).symm
  _ ≤ (Finset.range (l.length + 1)).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr fun v _ => Finset.filter_subset _ _)
  _ = l.length + 1 := Finset.card_range _

/-- **Upper from lower.**  Eventual lower frequency bounds for every word give normality. -/
theorem isNormalSequence_of_lower {b : ℕ} (hb : 2 ≤ b) {s : ℕ → ℕ}
    (h : ∀ v : List ℕ, v ≠ [] → (∀ d ∈ v, d < b) → ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      (((b : ℝ) ^ v.length)⁻¹ - ε) * n ≤ countOccurrences v ((List.range n).map s)) :
    IsNormalSequence b s := by
  intro v hv hvb
  set ℓ := v.length with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    rcases v with _ | ⟨a, v⟩
    · exact absurd rfl hv
    · simp [hℓ]
  set B : ℝ := (b : ℝ) ^ ℓ with hB
  have hB1 : (1 : ℝ) ≤ B := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ b))
  have hBpos : (0 : ℝ) < B := by linarith
  set W := allWords b ℓ
  have hvW : v ∈ W := mem_allWords.mpr ⟨rfl, hvb⟩
  have hWne : ∀ u ∈ W, u ≠ [] ∧ ∀ d ∈ u, d < b := by
    intro u hu
    obtain ⟨hl, hd⟩ := mem_allWords.mp hu
    refine ⟨fun h0 => ?_, hd⟩
    rw [h0] at hl; simp at hl; omega
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (2 * B) with hε'
  have hε'pos : 0 < ε' := by positivity
  have hall : ∀ᶠ n : ℕ in atTop, ∀ u ∈ W,
      (B⁻¹ - ε') * n ≤ countOccurrences u ((List.range n).map s) := by
    rw [Filter.eventually_all_finset]
    intro u hu
    have := h u (hWne u hu).1 (hWne u hu).2 ε' hε'pos
    rwa [(mem_allWords.mp hu).1] at this
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hall
  obtain ⟨N2, hN2⟩ := exists_nat_gt (2 / ε)
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2' : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : (2 / ε : ℝ) < n := lt_of_lt_of_le hN2 (by exact_mod_cast hn2')
  have hnpos : (0 : ℝ) < n := lt_trans (by positivity) hn2
  have hlow := hN1 n hn1
  set f : List ℕ → ℝ := fun u => (countOccurrences u ((List.range n).map s) : ℝ)
  have hsum : ∑ u ∈ W, f u ≤ n + 1 := by
    have := sum_countOccurrences_allWords_le b ℓ ((List.range n).map s)
    simp only [List.length_map, List.length_range] at this
    simp only [f]; exact_mod_cast this
  have hsplit : ∑ u ∈ W, f u = f v + ∑ u ∈ W.erase v, f u := (Finset.add_sum_erase W f hvW).symm
  have hcard : ((W.erase v).card : ℝ) = B - 1 := by
    rw [Finset.card_erase_of_mem hvW, card_allWords]
    have : 1 ≤ b ^ ℓ := Nat.one_le_pow _ _ (by omega)
    push_cast [Nat.cast_sub this]; rfl
  have hrest : (B - 1) * ((B⁻¹ - ε') * n) ≤ ∑ u ∈ W.erase v, f u := by
    rw [← hcard, ← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ fun u hu => hlow u (Finset.mem_of_mem_erase hu)
  have hv1 := hlow v hvW
  have h2n : 2 < ε * n := by rwa [div_lt_iff₀ hε, mul_comm] at hn2
  have hBi : B * B⁻¹ = 1 := mul_inv_cancel₀ hBpos.ne'
  have hε'B : (B - 1) * ε' ≤ ε / 2 := by
    rw [hε']; rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  rw [Real.dist_eq, abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add, div_lt_iff₀ hnpos,
    lt_div_iff₀ hnpos]
  constructor
  · have : ε' ≤ ε / 2 := by
      rw [hε', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  · have hfv : f v ≤ n + 1 - (B - 1) * ((B⁻¹ - ε') * n) := by linarith
    have : (B - 1) * ((B⁻¹ - ε') * n) = n - B⁻¹ * n - (B - 1) * ε' * n := by
      have : (B - 1) * B⁻¹ = 1 - B⁻¹ := by rw [sub_mul, hBi, one_mul]
      linear_combination n * this
    nlinarith

/-- Periodic counting on an aligned interval (from `ChampernowneNormality`). -/
theorem le_card_Ico_filter_div_mod {A t p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hd : d < q) (hA : p * q ∣ A) :
    t / (p * q) * p
      ≤ ((Finset.Ico A (A + t)).filter (fun n => n / p % q = d)).card := by
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have hdpr : ∀ r < p, d * p + r < p * q := by
    intro r hr
    calc d * p + r < (d + 1) * p := by rw [Nat.succ_mul]; omega
    _ ≤ q * p := Nat.mul_le_mul_right p (by omega)
    _ = p * q := Nat.mul_comm q p
  rw [show t / (p * q) * p
      = (Finset.range (t / (p * q)) ×ˢ Finset.range p).card by
    rw [Finset.card_product, Finset.card_range, Finset.card_range]]
  apply Finset.card_le_card_of_injOn
    (fun x => A + (x.1 * (p * q) + d * p + x.2))
  · -- the map lands in the filtered interval
    rintro ⟨h, r⟩ hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
      Finset.mem_range] at hx
    obtain ⟨hh, hr⟩ := hx
    have hlt : h * (p * q) + d * p + r < t :=
      calc h * (p * q) + d * p + r
          < h * (p * q) + p * q := by have := hdpr r hr; omega
      _ = (h + 1) * (p * q) := by ring
      _ ≤ t / (p * q) * (p * q) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ t := Nat.div_mul_le_self t (p * q)
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico]
    refine ⟨⟨Nat.le_add_right _ _, by omega⟩, ?_⟩
    obtain ⟨a, rfl⟩ := hA
    have hrew : p * q * a + (h * (p * q) + d * p + r)
        = r + p * (d + q * (a + h)) := by ring
    rw [hrew, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  · -- injectivity: extract `h` and `r` back out by div/mod
    have hext : ∀ h r, r < p →
        (h * (p * q) + d * p + r) / (p * q) = h
          ∧ (h * (p * q) + d * p + r) % p = r := by
      intro h r hr
      constructor
      · have hrew : h * (p * q) + d * p + r = d * p + r + (p * q) * h := by
          ring
        rw [hrew, Nat.add_mul_div_left _ _ hpq, Nat.div_eq_of_lt (hdpr r hr),
          Nat.zero_add]
      · have hrew : h * (p * q) + d * p + r = p * (h * q + d) + r := by ring
        rw [hrew, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    rintro ⟨h₁, r₁⟩ hx₁ ⟨h₂, r₂⟩ hx₂ heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
      Finset.mem_range] at hx₁ hx₂
    have hcancel : h₁ * (p * q) + d * p + r₁ = h₂ * (p * q) + d * p + r₂ :=
      Nat.add_left_cancel heq
    have hh : h₁ = h₂ := by
      rw [← (hext h₁ r₁ hx₁.2).1, ← (hext h₂ r₂ hx₂.2).1, hcancel]
    have hr : r₁ = r₂ := by
      rw [← (hext h₁ r₁ hx₁.2).2, ← (hext h₂ r₂ hx₂.2).2, hcancel]
    exact Prod.ext hh hr

/-- Periodic counting on an arbitrary interval. -/
theorem le_card_Ico_filter_div_mod' {A t p q d : ℕ} (hp : 0 < p) (hq : 0 < q) (hd : d < q) :
    (t / (p * q) - 1) * p ≤ ((Finset.Ico A (A + t)).filter (fun n => n / p % q = d)).card := by
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  set A' := (A / (p * q) + 1) * (p * q) with hA'
  have hAA : A < A' := by
    have := Nat.lt_div_mul_add (a := A) hpq
    rw [hA', add_mul, one_mul]; exact this
  have hAA2 : A' ≤ A + p * q := by
    rw [hA', add_mul, one_mul]; have := Nat.div_mul_le_self A (p * q); omega
  by_cases ht : A' ≤ A + t
  · have hdvd : p * q ∣ A' := ⟨A / (p * q) + 1, by rw [hA', mul_comm]⟩
    have h1 := le_card_Ico_filter_div_mod (t := A + t - A') hp hq hd hdvd
    have h2 : (t / (p * q) - 1) ≤ (A + t - A') / (p * q) := by
      have : t - p * q ≤ A + t - A' := by omega
      calc t / (p * q) - 1 ≤ (t - p * q) / (p * q) := by
            rw [Nat.le_div_iff_mul_le hpq, Nat.sub_mul, one_mul]
            have := Nat.div_mul_le_self t (p * q)
            omega
        _ ≤ _ := Nat.div_le_div_right this
    calc (t / (p * q) - 1) * p ≤ (A + t - A') / (p * q) * p := Nat.mul_le_mul_right _ h2
      _ ≤ _ := h1
      _ ≤ _ := by
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        intro x hx; simp only [Finset.mem_Ico] at hx ⊢; omega
  · have : t / (p * q) = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]

/-- Little-endian value of a word. -/
def lval (k : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: v => d + k * lval k v

theorem lval_lt {k : ℕ} (v : List ℕ) (hv : ∀ d ∈ v, d < k) : lval k v < k ^ v.length := by
  induction v with
  | nil => simp [lval]
  | cons d v ih =>
    simp only [lval, List.length_cons, pow_succ]
    have h1 := hv d (List.mem_cons_self ..)
    have h2 := ih fun e he => hv e (List.mem_cons_of_mem d he)
    nlinarith

theorem mod_pow_eq_lval {k : ℕ} (hk : 0 < k) (v : List ℕ) (hv : ∀ d ∈ v, d < k) (x : ℕ)
    (hx : x % k ^ v.length = lval k v) (t : ℕ) (ht : t < v.length) :
    x / k ^ t % k = v.getD t 0 := by
  induction v generalizing x t with
  | nil => simp at ht
  | cons d v ih =>
    have hd := hv d (List.mem_cons_self ..)
    have hm : x % (k * k ^ v.length) = x % k + k * (x / k % k ^ v.length) := Nat.mod_mul
    simp only [List.length_cons, pow_succ'] at hx
    rw [hm] at hx
    simp only [lval] at hx
    have hxk : x % k = d := by
      have := congrArg (· % k) hx
      simp only [Nat.add_mul_mod_self_left, Nat.mod_mod] at this
      rwa [Nat.mod_eq_of_lt hd] at this
    rcases t with _ | t
    · simpa using hxk
    · have hrest : x / k % k ^ v.length = lval k v := by
        rw [hxk] at hx
        have := Nat.add_left_cancel hx
        exact Nat.eq_of_mul_eq_mul_left hk this
      have := ih (fun e he => hv e (List.mem_cons_of_mem d he)) (x / k) hrest t
        (by simpa using ht)
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      simpa using this

end NormalNumbers.NormalLower
