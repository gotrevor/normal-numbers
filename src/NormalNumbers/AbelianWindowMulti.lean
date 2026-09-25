/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianWindowGad

/-!
# The multi-gadget block law

Item 3 of the nested-layer route.  `AbelianWindowGad` gives two removal lemmas
(`blockGf_cons_of_high`, `blockGf_cons_of_low`) and the single-gadget closed form
(`blockGf_single`).  Here they are fed down a whole list of gadgets:

* `blockGf_eq_plain` — if the trace `I` fails to separate at least ONE pair of EVERY gadget in
  the list, the whole list drops out and `blockGf` is the plain binomial product;
* the interval geometry: an interval `Ico lo hi` separates the low pair `{p, p+1}` iff
  `lo = p + 1` or `hi = p + 1`, and the high pair iff `lo = p+a+1` or `hi = p+a+1`; a PREFIX
  (`lo = 0`) or a SUFFIX (`hi = q`) can therefore never separate both, so every gadget drops out
  and `BinomSeg` holds — the long-window half of the law, for ANY number of gadgets.
-/

open Finset Polynomial

namespace NormalNumbers.Abelian

open NormalNumbers.PowerBase

/-- Two gadgets occupy disjoint quadruples. -/
def GadDisj (g h : ℕ × ℕ) : Prop := ∀ u ∈ quadSet h.1 h.2, u ∉ quadSet g.1 g.2

/-- A gadget fits in a width-`q` block with a usable arm. -/
def GadOk (q : ℕ) (pa : ℕ × ℕ) : Prop := 2 ≤ pa.2 ∧ pa.1 + pa.2 + 1 < q

theorem blockGf_nil (q : ℕ) (I : Finset ℕ) (hI : I ⊆ range q) :
    blockGf q (multiG q []) I = ∏ i ∈ range q, (if i ∈ I then (1 + X : ℝ[X]) else 2) := by
  rw [blockGf, ← gad_sum_plain q I]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  exact pow_card_filter q I hI (fun u => multiG q [] u d) (fun u => multiG_lt_two q [] u d)

/-- **The multi-gadget removal.**  If `I` leaves at least one pair of every gadget unseparated,
every gadget drops out. -/
theorem blockGf_eq_plain (q : ℕ) (gs : List (ℕ × ℕ)) (I : Finset ℕ) (hI : I ⊆ range q)
    (hok : ∀ pa ∈ gs, GadOk q pa) (hpw : gs.Pairwise GadDisj)
    (hsep : ∀ pa ∈ gs, (pa.1 ∈ I ↔ pa.1 + 1 ∈ I) ∨ (pa.1 + pa.2 ∈ I ↔ pa.1 + pa.2 + 1 ∈ I)) :
    blockGf q (multiG q gs) I = ∏ i ∈ range q, (if i ∈ I then (1 + X : ℝ[X]) else 2) := by
  induction gs with
  | nil => exact blockGf_nil q I hI
  | cons pa gs ih =>
      obtain ⟨p, a⟩ := pa
      obtain ⟨ha, hq⟩ := hok (p, a) (by simp)
      rw [List.pairwise_cons] at hpw
      have hdisj : ∀ pa ∈ gs, ∀ u ∈ quadSet pa.1 pa.2, u ∉ quadSet p a := hpw.1
      have htail : blockGf q (multiG q gs) I
          = ∏ i ∈ range q, (if i ∈ I then (1 + X : ℝ[X]) else 2) :=
        ih (fun qa hqa => hok qa (by simp [hqa])) hpw.2 (fun qa hqa => hsep qa (by simp [hqa]))
      rcases hsep (p, a) (by simp) with h | h
      · rw [blockGf_cons_of_low q p a gs ha hq hdisj I h, htail]
      · rw [blockGf_cons_of_high q p a gs ha hdisj I h, htail]

/-! ## Interval geometry -/

/-- A **prefix** of the block never separates both pairs of a gadget. -/
theorem sep_of_prefix {hi p a : ℕ} (ha : 2 ≤ a) :
    (p ∈ Finset.Ico 0 hi ↔ p + 1 ∈ Finset.Ico 0 hi) ∨
      (p + a ∈ Finset.Ico 0 hi ↔ p + a + 1 ∈ Finset.Ico 0 hi) := by
  simp only [Finset.mem_Ico, Nat.zero_le, true_and]
  by_cases hp : p + 1 < hi
  · exact Or.inl ⟨fun _ => hp, fun _ => by omega⟩
  · exact Or.inr ⟨fun hc => by omega, fun hc => by omega⟩

/-- A **suffix** of the block never separates both pairs of a gadget. -/
theorem sep_of_suffix {lo q p a : ℕ} (ha : 2 ≤ a) (hq : p + a + 1 < q) :
    (p ∈ Finset.Ico lo q ↔ p + 1 ∈ Finset.Ico lo q) ∨
      (p + a ∈ Finset.Ico lo q ↔ p + a + 1 ∈ Finset.Ico lo q) := by
  simp only [Finset.mem_Ico]
  by_cases hp : lo ≤ p
  · exact Or.inl ⟨fun _ => ⟨by omega, by omega⟩, fun _ => ⟨hp, by omega⟩⟩
  · by_cases hp2 : lo ≤ p + 1
    · exact Or.inr ⟨fun _ => ⟨by omega, by omega⟩, fun _ => ⟨by omega, by omega⟩⟩
    · exact Or.inl ⟨fun hc => by omega, fun hc => by omega⟩

/-! ## `BinomSeg` for any number of gadgets -/

/-- The plain product is the exact Binomial generating function, at any width. -/
theorem prod_base_eq (q : ℕ) (I : Finset ℕ) (hI : I ⊆ range q) :
    (∏ i ∈ range q, (if i ∈ I then (1 + X : ℝ[X]) else 2))
      = C ((2 : ℝ) ^ q / 2 ^ I.card) * (1 + X) ^ I.card := by
  classical
  rw [← Finset.prod_sdiff hI]
  have h1 : ∏ i ∈ I, (if i ∈ I then (1 + X : ℝ[X]) else 2) = (1 + X) ^ I.card := by
    rw [Finset.prod_congr rfl (fun i hi => if_pos hi), Finset.prod_const]
  have h2 : ∏ i ∈ (range q) \ I, (if i ∈ I then (1 + X : ℝ[X]) else 2)
      = 2 ^ ((range q) \ I).card := by
    rw [Finset.prod_congr rfl (fun i hi => if_neg (Finset.mem_sdiff.mp hi).2), Finset.prod_const]
  have hcard : ((range q) \ I).card = q - I.card := by
    rw [Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.mpr hI]
  have hle : I.card ≤ q := by simpa using Finset.card_le_card hI
  rw [h1, h2, hcard]
  have hsplit : ((2 : ℝ) ^ q / 2 ^ I.card) = 2 ^ (q - I.card) := by
    rw [div_eq_iff (by positivity), ← pow_add]
    congr 1
    omega
  rw [hsplit, Polynomial.C_pow, Polynomial.C_ofNat]

/-- **Every prefix and every suffix of a multi-gadget block law is Binomial** — so the
block-driven sequence is abelian at every window length `L ≥ q`, no matter how many gadgets the
block carries. -/
theorem multi_binomSeg (q : ℕ) (gs : List (ℕ × ℕ)) (hok : ∀ pa ∈ gs, GadOk q pa)
    (hpw : gs.Pairwise GadDisj) : BinomSeg (multiG q gs) q (2 ^ q) := by
  classical
  intro lo hi hhi hps
  have hI : Finset.Ico lo hi ⊆ range q := by
    intro i hi'
    rw [Finset.mem_Ico] at hi'
    exact Finset.mem_range.mpr (by omega)
  have hsep : ∀ pa ∈ gs, (pa.1 ∈ Finset.Ico lo hi ↔ pa.1 + 1 ∈ Finset.Ico lo hi) ∨
      (pa.1 + pa.2 ∈ Finset.Ico lo hi ↔ pa.1 + pa.2 + 1 ∈ Finset.Ico lo hi) := by
    intro pa hpa
    obtain ⟨ha, hq⟩ := hok pa hpa
    rcases hps with rfl | rfl
    · exact sep_of_prefix ha
    · exact sep_of_suffix ha hq
  have hcard : (Finset.Ico lo hi).card = hi - lo := by simp
  have := blockGf_eq_plain q gs (Finset.Ico lo hi) hI hok hpw hsep
  rw [blockGf] at this
  rw [this, prod_base_eq q _ hI, hcard]
  norm_num

end NormalNumbers.Abelian
