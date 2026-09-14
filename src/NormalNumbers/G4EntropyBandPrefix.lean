/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandSeq

/-!
# Entropy expedition — prefixes of a band

`tendsto_bandRead_freq` gives the correct word frequencies at the band cutoffs `bT (i+1)`.  This
module prices a cutoff *inside* a band: after `a` of band `i`'s windows, the read content is the
sub-collection `bandPre i a` of sample times, of relative size `a/|P_K|`, and a sample-time
restriction costs `(δ+1)/σ`.  So a prefix is certified as soon as `a ≫ |P_K|·δ/m_K`, i.e. as
soon as it is more than a `≈ K^{−1/2}` fraction of the band.

That is what turns the band cutoffs into a **density-one** set of cutoffs: only the first
`O(K^{−1/2})` fraction of each band is uncontrolled, and that fraction vanishes with the scale.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The prefix of a band -/

open Classical in
/-- The first `a` sample times of band `i`, in increasing order. -/
noncomputable def bandPre (i a : ℕ) : Finset ℕ := (Finset.range a).image (bnth i)

lemma bandPre_subset (i a : ℕ) (ha : a ≤ (bandS i).card) : bandPre i a ⊆ bandS i := by
  classical
  intro n hn
  rw [bandPre, Finset.mem_image] at hn
  obtain ⟨j, -, rfl⟩ := hn
  exact bnth_mem i j

lemma bandPre_subset_PK (i a : ℕ) (ha : a ≤ (bandS i).card) : bandPre i a ⊆ PK i :=
  fun n hn => bandS_subset i (bandPre_subset i a ha hn)

lemma card_bandPre (i a : ℕ) (ha : a ≤ (bandS i).card) : (bandPre i a).card = a := by
  classical
  rw [bandPre, Finset.card_image_of_injOn, Finset.card_range]
  intro j hj k hk hjk
  rcases Nat.lt_trichotomy j k with h | h | h
  · exact absurd hjk (by
      have := bnth_lt_bnth h (lt_of_lt_of_le (Finset.mem_range.1 hk) ha)
      omega)
  · exact h
  · exact absurd hjk (by
      have := bnth_lt_bnth h (lt_of_lt_of_le (Finset.mem_range.1 hj) ha)
      omega)

lemma bandPre_nonempty (i a : ℕ) (ha : 0 < a) : (bandPre i a).Nonempty := by
  classical
  refine ⟨bnth i 0, ?_⟩
  rw [bandPre, Finset.mem_image]
  exact ⟨0, Finset.mem_range.2 ha, rfl⟩

/-! ### The prefix law -/

open Classical in
/-- The window law at the good atom, restricted to the first `a` sample times of band `i`. -/
noncomputable def preLaw (i a : ℕ) (ha : 0 < a) (x : ℝ) : FinLaw (Unit → Fin (2 ^ kk i)) :=
  empirical (bandPre i a) (bandPre_nonempty i a ha)
    (fun n => fun _ : Unit => ZVec (gridAt i) (kk i) x n (goodAtom i))

open Classical in
lemma H₂_preLaw (i a : ℕ) (ha : 0 < a) (x : ℝ) :
    (preLaw i a ha x).H₂
      = (empirical (bandPre i a) (bandPre_nonempty i a ha)
          (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i))).H₂ := by
  classical
  have hmap := (map_empirical (Ω := Fin (2 ^ kk i)) (Ω' := Unit → Fin (2 ^ kk i))
    (bandPre_nonempty i a ha) (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i))
    (fun u => fun _ : Unit => u)).symm
  have hH := FinLaw.H₂_map_injective
    (empirical (bandPre i a) (bandPre_nonempty i a ha)
      (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i)))
    (g := fun u : Fin (2 ^ kk i) => fun _ : Unit => u) (fun u u' h => congrFun h ())
  rw [← hH, ← hmap]
  rfl

open Classical in
/-- **The prefix's deficit.**  A prefix of relative size `σ = a/|P_K|` costs `(δ+1)/σ`. -/
theorem H₂_preLaw_ge (i a : ℕ) (ha : 0 < a) (haS : a ≤ (bandS i).card) :
    (kk i : ℝ) - (atomDeficit i + 1) * ((PK i).card : ℝ) / (a : ℝ)
      ≤ (preLaw i a ha (primeLambertAtBase 4)).H₂ := by
  classical
  set f : ℕ → Fin (2 ^ kk i) :=
    fun n => ZVec (gridAt i) (kk i) (primeLambertAtBase 4) n (goodAtom i) with hf
  have hfull : ((kk i : ℝ) - atomDeficit i) ≤ (empirical (PK i) (PK_nonempty i) f).H₂ := by
    have hmap := map_coord_jointLawAt i (primeLambertAtBase 4) (goodAtom i)
    have hd := goodAtom_deficit i
    rw [FinLaw.coordDeficit] at hd
    rw [hmap] at hd
    linarith
  have hrest := H₂_empirical_window_restrict_ge (m := kk i) (PK_nonempty i)
    (bandPre_nonempty i a ha) (bandPre_subset_PK i a haS) f (δ := atomDeficit i) hfull
  rw [card_bandPre i a haS] at hrest
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hPpos : (0 : ℝ) < ((PK i).card : ℝ) := by exact_mod_cast PK_card_pos i
  have hdiv : (atomDeficit i + 1) / ((a : ℝ) / ((PK i).card : ℝ))
      = (atomDeficit i + 1) * ((PK i).card : ℝ) / (a : ℝ) := by
    field_simp
  rw [hdiv] at hrest
  rw [H₂_preLaw]
  exact hrest

/-! ### The prefix's capture bound -/

set_option maxHeartbeats 1000000 in
/-- **A certified prefix.**  After `a` of band `i`'s windows the word frequencies are within
`2√(2 log 2·ℓ·(δ+1)|P_K|/(a·m_K))` of `2^{−ℓ}`. -/
theorem abs_posAvg_preLaw_le (i a ℓ : ℕ) (ha : 0 < a) (haS : a ≤ (bandS i).card)
    (hℓ : 0 < ℓ) (hℓm : 2 * ℓ ≤ kk i) (w : Fin (2 ^ ℓ)) :
    |posAvg (kk i) ℓ (preLaw i a ha (primeLambertAtBase 4)) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (2 * Real.log 2 * (ℓ : ℝ)
          * ((atomDeficit i + 1) * ((PK i).card : ℝ)) / ((a : ℝ) * (kk i : ℝ))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hPpos : (0 : ℝ) < ((PK i).card : ℝ) := by exact_mod_cast PK_card_pos i
  have hkkpos : (0 : ℝ) < (kk i : ℝ) := by
    have := kk_pos' i; exact_mod_cast this
  have hδ : (0 : ℝ) < (atomDeficit i + 1) * ((PK i).card : ℝ) / (a : ℝ) := by
    have := atomDeficit_pos i
    positivity
  have hdef : ((kk i : ℝ) - (atomDeficit i + 1) * ((PK i).card : ℝ) / (a : ℝ))
      * (Fintype.card Unit : ℝ) ≤ (preLaw i a ha (primeLambertAtBase 4)).H₂ := by
    simp only [Fintype.card_unit, Nat.cast_one, mul_one]
    exact H₂_preLaw_ge i a ha haS
  have hmain := abs_posAvg_sub_le hℓ (by omega) (preLaw i a ha (primeLambertAtBase 4)) w hδ hdef
  refine hmain.trans ?_
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hhalf : (kk i : ℝ) / 2 ≤ (kk i : ℝ) - ℓ + 1 := by
    have : (2 : ℝ) * ℓ ≤ (kk i : ℝ) := by exact_mod_cast hℓm
    linarith
  have hden : (0 : ℝ) < (kk i : ℝ) - ℓ + 1 := by
    have : (2 : ℝ) * ℓ ≤ (kk i : ℝ) := by exact_mod_cast hℓm
    linarith
  have hstep : Real.log 2 * (ℓ : ℝ) * ((atomDeficit i + 1) * ((PK i).card : ℝ) / (a : ℝ))
      / ((kk i : ℝ) - ℓ + 1)
      ≤ 2 * Real.log 2 * (ℓ : ℝ) * ((atomDeficit i + 1) * ((PK i).card : ℝ))
          / ((a : ℝ) * (kk i : ℝ)) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have hd0 : (0 : ℝ) < atomDeficit i + 1 := by
      have := atomDeficit_pos i; linarith
    have hc : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * ((atomDeficit i + 1) * ((PK i).card : ℝ)) := by
      positivity
    have hexp : Real.log 2 * (ℓ : ℝ) * ((atomDeficit i + 1) * ((PK i).card : ℝ) / (a : ℝ))
        * ((a : ℝ) * (kk i : ℝ))
        = (Real.log 2 * (ℓ : ℝ) * ((atomDeficit i + 1) * ((PK i).card : ℝ))) * (kk i : ℝ) := by
      field_simp
    rw [hexp]
    nlinarith [hc, hhalf, hkkpos]
  have hpos1 : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ)
      * ((atomDeficit i + 1) * ((PK i).card : ℝ) / (a : ℝ)) / ((kk i : ℝ) - ℓ + 1) := by
    have := hδ.le
    positivity
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by norm_num)

/-! ### The prefix count -/

open Classical in
/-- **The prefix's count rendering.** -/
theorem posAvg_preLaw_eq_count (i a ℓ : ℕ) (ha : 0 < a) (haS : a ≤ (bandS i).card) (x : ℝ)
    (w : Fin (2 ^ ℓ)) :
    posAvg (kk i) ℓ (preLaw i a ha x) w
      = (∑ p : Fin (kk i - ℓ + 1),
            (((bandPre i a).filter fun n =>
              posAt (kk i) ℓ (p : ℕ) (ZVec (gridAt i) (kk i) x n (goodAtom i)) = w).card : ℝ))
        / ((a : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ)) := by
  classical
  have hp : ∀ p : Fin (kk i - ℓ + 1),
      ((preLaw i a ha x).map
          (fun z : Unit → Fin (2 ^ kk i) => posAt (kk i) ℓ (p : ℕ) (z default))).prob {w}
        = (((bandPre i a).filter fun n =>
              posAt (kk i) ℓ (p : ℕ) (ZVec (gridAt i) (kk i) x n (goodAtom i)) = w).card : ℝ)
          / ((bandPre i a).card : ℝ) := by
    intro p
    rw [preLaw, FinLaw.prob, Finset.sum_singleton]
    exact map_empirical_p (bandPre_nonempty i a ha) _ _ w
  rw [posAvg, Fintype.sum_prod_type]
  simp only [Fintype.card_unit, Nat.cast_one, one_mul, Finset.univ_unique,
    Finset.sum_singleton, hp]
  rw [← Finset.sum_div, div_div, card_bandPre i a haS]

open Classical in
/-- **The prefix's digit rendering.** -/
theorem posAvg_preLaw_eq_digits (i a ℓ : ℕ) (ha : 0 < a) (haS : a ≤ (bandS i).card)
    (hℓm : ℓ ≤ kk i) (x : ℝ) (w : Fin (2 ^ ℓ)) :
    posAvg (kk i) ℓ (preLaw i a ha x) w
      = (∑ p : Fin (kk i - ℓ + 1),
            (((bandPre i a).filter fun n =>
              blockVal (Int.fract x) (2 * kIdx (gridAt i) n (goodAtom i) + (p : ℕ)) ℓ
                = (w : ℕ)).card : ℝ))
        / ((a : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ)) := by
  classical
  rw [posAvg_preLaw_eq_count i a ℓ ha haS x w]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  have hZ : ∀ n : ℕ, ZVec (gridAt i) (kk i) x n (goodAtom i)
      = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n (goodAtom i)) (kk i),
        blockVal_lt _ _ _⟩ :=
    fun n => Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n (goodAtom i))
  have hfit : (p : ℕ) + ℓ ≤ kk i := by
    have := p.isLt
    omega
  refine Finset.filter_congr fun n _ => ?_
  rw [hZ n, posAt_blockVal _ _ _ _ _ hfit]
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

/-! ### The read count at a mid-band cutoff -/

open Classical in
/-- The number of fitting in-window occurrences of `v` in the first `a` windows of band `i`. -/
noncomputable def preGood (i a : ℕ) (x : ℝ) (v : List ℕ) : ℕ :=
  ∑ j ∈ Finset.range a,
    ((Finset.range (kk i - v.length + 1)).filter
      (fun q => OccursAt 2 x v (bpos i j + q))).card

open Classical in
/-- `preGood` re-summed over the prefix's sample times. -/
theorem preGood_eq (i a : ℕ) (haS : a ≤ (bandS i).card) (x : ℝ) (v : List ℕ) :
    preGood i a x v
      = ∑ q ∈ Finset.range (kk i - v.length + 1),
          ((bandPre i a).filter fun n =>
            OccursAt 2 x v (2 * kIdx (gridAt i) n (goodAtom i) + q)).card := by
  classical
  unfold preGood
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [bandPre, Finset.sum_image]
  · rfl
  · intro j hj k hk hjk
    rcases Nat.lt_trichotomy j k with h | h | h
    · exact absurd hjk (by
        have := bnth_lt_bnth h (lt_of_lt_of_le (Finset.mem_range.1 hk) haS)
        omega)
    · exact h
    · exact absurd hjk (by
        have := bnth_lt_bnth h (lt_of_lt_of_le (Finset.mem_range.1 hj) haS)
        omega)

open Classical in
/-- **The mid-band read count.**  Reading `a` of band `i`'s windows contributes `preGood`
occurrences, up to one word length per window. -/
theorem pre_winCount_bounds (x : ℝ) (i a : ℕ) (haS : a ≤ (bandS i).card) (v : List ℕ)
    (hv : 0 < v.length) (hvm : v.length ≤ kk i) :
    preGood i a x v
        ≤ ((Finset.Ico (bT i) (bT i + a * kk i)).filter (MatchesAt (bandDig x) v)).card ∧
      ((Finset.Ico (bT i) (bT i + a * kk i)).filter (MatchesAt (bandDig x) v)).card
        ≤ preGood i a x v + a * v.length := by
  classical
  have hsplit : ((Finset.Ico (bT i) (bT i + a * kk i)).filter (MatchesAt (bandDig x) v)).card
      = ∑ j ∈ Finset.range a,
          ((Finset.range (kk i)).filter
            (fun q => MatchesAt (bandDig x) v (bT i + (j * kk i + q)))).card := by
    rw [card_Ico_shift _ (bT i) (a * kk i), card_filter_range_mul]
  rw [hsplit]
  have hper : ∀ j ∈ Finset.range a,
      ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (bpos i j + q))).card
        ≤ ((Finset.range (kk i)).filter
          (fun q => MatchesAt (bandDig x) v (bT i + (j * kk i + q)))).card ∧
      ((Finset.range (kk i)).filter
          (fun q => MatchesAt (bandDig x) v (bT i + (j * kk i + q)))).card
        ≤ ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (bpos i j + q))).card + v.length := by
    intro j hj
    have hj' : j < (bandS i).card := lt_of_lt_of_le (Finset.mem_range.1 hj) haS
    have hcongr : ((Finset.range (kk i - v.length + 1)).filter
        (fun q => MatchesAt (bandDig x) v (bT i + (j * kk i + q)))).card
        = ((Finset.range (kk i - v.length + 1)).filter
          (fun q => OccursAt 2 x v (bpos i j + q))).card := by
      congr 1
      refine Finset.filter_congr fun q hq => ?_
      have hqfit : q + v.length ≤ kk i := by
        have := Finset.mem_range.1 hq
        omega
      have hassoc : bT i + (j * kk i + q) = bT i + j * kk i + q := by ring
      rw [hassoc]
      simpa using matchesAt_bandDig_iff x i j q v hj' hqfit
    have h := card_filter_fit
      (fun q => MatchesAt (bandDig x) v (bT i + (j * kk i + q))) (m := kk i)
      (ℓ := v.length) hv hvm
    rw [hcongr] at h
    exact h
  constructor
  · exact Finset.sum_le_sum fun j hj => (hper j hj).1
  · calc ∑ j ∈ Finset.range a,
          ((Finset.range (kk i)).filter
            (fun q => MatchesAt (bandDig x) v (bT i + (j * kk i + q)))).card
        ≤ ∑ j ∈ Finset.range a,
            (((Finset.range (kk i - v.length + 1)).filter
              (fun q => OccursAt 2 x v (bpos i j + q))).card + v.length) :=
          Finset.sum_le_sum fun j hj => (hper j hj).2
      _ = preGood i a x v + a * v.length := by
          rw [Finset.sum_add_distrib, preGood]
          simp [mul_comm]

open Classical in
/-- The full read count at a mid-band cutoff. -/
theorem winCount_mid_bounds (x : ℝ) (i a : ℕ) (haS : a ≤ (bandS i).card) (v : List ℕ)
    (hv : 0 < v.length) (hvm : v.length ≤ kk i) :
    preGood i a x v ≤ winCount (bandDig x) v (bT i + a * kk i) ∧
      winCount (bandDig x) v (bT i + a * kk i) ≤ preGood i a x v + bT i + a * v.length := by
  classical
  have hle : bT i ≤ bT i + a * kk i := by omega
  have hsplit := winCount_split (bandDig x) v hle
  obtain ⟨h1, h2⟩ := pre_winCount_bounds x i a haS v hv hvm
  have hhist : winCount (bandDig x) v (bT i) ≤ bT i := winCount_le _ _ _
  generalize hc : a * v.length = c at h2 ⊢
  rw [hsplit]
  omega

/-! ### The frequency at a fixed fraction through each band -/

/-- The index of the cutoff a `c`-fraction through band `i`. -/
noncomputable def aOf (i : ℕ) (c : ℝ) : ℕ := ⌈c * ((bandS i).card : ℝ)⌉₊

lemma aOf_pos (i : ℕ) {c : ℝ} (hc : 0 < c) : 0 < aOf i c := by
  have hS : (0 : ℝ) < ((bandS i).card : ℝ) := by
    have := card_bandS_pos i
    exact_mod_cast this
  rw [aOf, Nat.lt_ceil]
  push_cast
  positivity

lemma aOf_le (i : ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) : aOf i c ≤ (bandS i).card := by
  have hS : (0 : ℝ) ≤ ((bandS i).card : ℝ) := Nat.cast_nonneg _
  rw [aOf, Nat.ceil_le]
  nlinarith [hS]

lemma le_aOf (i : ℕ) (c : ℝ) : c * ((bandS i).card : ℝ) ≤ (aOf i c : ℝ) := Nat.le_ceil _

lemma aOf_le_card_real (i : ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ((aOf i c : ℕ) : ℝ) ≤ ((bandS i).card : ℝ) := by
  exact_mod_cast aOf_le i hc0 hc1

set_option maxHeartbeats 1000000 in
/-- **The frequency a fixed fraction through each band.**  For every `c ∈ (0,1]`, the frequency
of `v` in the first `bT i + aOf i c · m_i` digits read along `bandPos` tends to `2^{−|v|}`.

`tendsto_bandRead_freq` is the case `c = 1`.  Only the initial `O(K^{−1/2})` fraction of each
band is out of reach, so the cutoffs at which the frequency is correct are *most* of them. -/
theorem tendsto_midRead_freq (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun i =>
        (winCount (bandDig (primeLambertAtBase 4)) v (bT i + aOf i c * kk i) : ℝ)
          / ((bT i + aOf i c * kk i : ℕ) : ℝ))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
  classical
  set x := primeLambertAtBase 4 with hx
  have hScard : ∀ i, (0 : ℝ) < ((bandS i).card : ℝ) := fun i => by
    have := card_bandS_pos i
    exact_mod_cast this
  have hkkpos : ∀ i, (0 : ℝ) < (kk i : ℝ) := fun i => by
    have := kk_pos' i
    exact_mod_cast this
  have hapos : ∀ i, (0 : ℝ) < ((aOf i c : ℕ) : ℝ) := fun i => by
    have := aOf_pos i hc0
    exact_mod_cast this
  have hNpos : ∀ i, (0 : ℝ) < ((bT i + aOf i c * kk i : ℕ) : ℝ) := by
    intro i
    have h1 : 0 < aOf i c * kk i := Nat.mul_pos (aOf_pos i hc0) (kk_pos' i)
    have : 0 < bT i + aOf i c * kk i := by omega
    exact_mod_cast this
  have hNeq : ∀ i, ((bT i + aOf i c * kk i : ℕ) : ℝ)
      = (bT i : ℝ) + ((aOf i c : ℕ) : ℝ) * (kk i : ℝ) := by
    intro i; push_cast; ring
  -- the history is at most `4/c` windows' worth
  have hTa : ∀ i, (bT i : ℝ) ≤ (4 / c) * ((aOf i c : ℕ) : ℝ) := by
    intro i
    have h1 : (bT i : ℝ) ≤ 4 * ((bandS i).card : ℝ) := by
      have h := bT_kk_le i
      have hbl : (bL i : ℝ) = ((bandS i).card : ℝ) * (kk i : ℝ) := by
        show ((((bandS i).card * kk i : ℕ)) : ℝ) = _
        push_cast; ring
      rw [hbl] at h
      nlinarith [hkkpos i, hScard i]
    have h2 : c * ((bandS i).card : ℝ) ≤ ((aOf i c : ℕ) : ℝ) := le_aOf i c
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    nlinarith [h2, h1]
  -- the prefix ratio
  have hcast : ∀ i, v.length ≤ kk i →
      ((kk i - v.length + 1 : ℕ) : ℝ) = (kk i : ℝ) - (v.length : ℝ) + 1 := by
    intro i hi
    have h1 : (kk i - v.length + 1 : ℕ) = kk i + 1 - v.length := by omega
    rw [h1, Nat.cast_sub (by omega)]
    push_cast
    ring
  -- the capture bound for the prefix, as a vanishing sequence
  have hεlim : Tendsto (fun i => 2 * Real.sqrt (2 * Real.log 2 * (v.length : ℝ)
      * ((atomDeficit i + 1) * ((PK i).card : ℝ))
        / (((aOf i c : ℕ) : ℝ) * (kk i : ℝ)))) atTop (nhds 0) := by
    have hbig : ∀ i, ((atomDeficit i + 1) * ((PK i).card : ℝ))
        / (((aOf i c : ℕ) : ℝ) * (kk i : ℝ))
        ≤ (2 / c) * (atomDeficit i + 1) / (kk i : ℝ) := by
      intro i
      have hd : (0 : ℝ) < atomDeficit i + 1 := by
        have := atomDeficit_pos i; linarith
      have hP : ((PK i).card : ℝ) ≤ 2 * ((bandS i).card : ℝ) := card_bandS_ge' i
      have h2 : c * ((bandS i).card : ℝ) ≤ ((aOf i c : ℕ) : ℝ) := le_aOf i c
      rw [div_le_div_iff₀ (by
        have := hapos i
        have := hkkpos i
        positivity) (hkkpos i)]
      have hstep : (atomDeficit i + 1) * ((PK i).card : ℝ) * (kk i : ℝ)
          ≤ (2 / c) * (atomDeficit i + 1) * (((aOf i c : ℕ) : ℝ) * (kk i : ℝ)) := by
        have hA : (atomDeficit i + 1) * ((PK i).card : ℝ)
            ≤ (2 / c) * (atomDeficit i + 1) * ((aOf i c : ℕ) : ℝ) := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc0]
          nlinarith [mul_le_mul_of_nonneg_left h2 hd.le,
            mul_le_mul_of_nonneg_left hP hd.le, hScard i, hd]
        nlinarith [hA, hkkpos i]
      linarith [hstep]
    have hlim0 : Tendsto (fun i => (2 / c) * (atomDeficit i + 1) / (kk i : ℝ))
        atTop (nhds 0) := by
      -- `atomDeficit i = 100√K`, `kk i = K/4`, so the ratio is `≈ 800/(c√K)`
      have hform : ∀ i, (2 / c) * (atomDeficit i + 1) / (kk i : ℝ)
          ≤ (808 / c) / Real.sqrt (KK i) := by
        intro i
        have hKpos : (0 : ℝ) < (KK i : ℝ) := by
          have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
          linarith
        have hS0 : 0 < Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_pos.2 hKpos
        have hS400 : (400 : ℝ) ≤ Real.sqrt ((KK i : ℕ) : ℝ) := by
          have h : (160000 : ℝ) ≤ ((KK i : ℕ) : ℝ) := by exact_mod_cast KK_ge i
          have h2 : Real.sqrt (160000 : ℝ) ≤ Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_le_sqrt h
          have h400 : Real.sqrt (160000 : ℝ) = 400 := by
            rw [show (160000 : ℝ) = 400 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          linarith [h400 ▸ h2]
        have hkk4 : (KK i : ℝ) = 4 * (kk i : ℝ) := by unfold KK; push_cast; ring
        have hsq : Real.sqrt ((KK i : ℕ) : ℝ) * Real.sqrt ((KK i : ℕ) : ℝ) = 4 * (kk i : ℝ) := by
          rw [Real.mul_self_sqrt hKpos.le, hkk4]
        have hdle : atomDeficit i + 1 ≤ 101 * Real.sqrt ((KK i : ℕ) : ℝ) := by
          rw [atomDeficit]
          linarith [hS400]
        rw [div_le_div_iff₀ (hkkpos i) hS0]
        have hc' : (0 : ℝ) < 2 / c := by positivity
        have hkey : (2 / c) * (atomDeficit i + 1) * Real.sqrt ((KK i : ℕ) : ℝ)
            ≤ (2 / c) * (101 * Real.sqrt ((KK i : ℕ) : ℝ)) * Real.sqrt ((KK i : ℕ) : ℝ) := by
          have h0 : (0 : ℝ) ≤ (2 / c) * Real.sqrt ((KK i : ℕ) : ℝ) := by positivity
          nlinarith [hdle, h0]
        have hrw : (2 / c) * (101 * Real.sqrt ((KK i : ℕ) : ℝ)) * Real.sqrt ((KK i : ℕ) : ℝ)
            = (808 / c) * (kk i : ℝ) := by
          field_simp
          linear_combination (202 : ℝ) * hsq
        linarith [hkey, hrw ▸ hkey]
      refine squeeze_zero_norm' ?_ (by
        have hsqrt : Tendsto (fun i => Real.sqrt (KK i)) atTop atTop :=
          Real.tendsto_sqrt_atTop.comp tendsto_KK_atTop
        exact hsqrt.const_div_atTop (808 / c))
      filter_upwards with i
      have hnn : (0 : ℝ) ≤ (2 / c) * (atomDeficit i + 1) / (kk i : ℝ) := by
        have := atomDeficit_pos i
        have hc' : (0 : ℝ) < 2 / c := by positivity
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hform i
    have hmono : Tendsto (fun i => ((atomDeficit i + 1) * ((PK i).card : ℝ))
        / (((aOf i c : ℕ) : ℝ) * (kk i : ℝ))) atTop (nhds 0) := by
      refine squeeze_zero ?_ hbig hlim0
      intro i
      have hd : (0 : ℝ) < atomDeficit i + 1 := by
        have := atomDeficit_pos i; linarith
      have := hapos i
      have := hkkpos i
      positivity
    have h2 : Tendsto (fun i => 2 * Real.log 2 * (v.length : ℝ)
        * (((atomDeficit i + 1) * ((PK i).card : ℝ))
          / (((aOf i c : ℕ) : ℝ) * (kk i : ℝ)))) atTop (nhds 0) := by
      have := hmono.const_mul (2 * Real.log 2 * (v.length : ℝ))
      simpa using this
    have h3 : Tendsto (fun i => Real.sqrt (2 * Real.log 2 * (v.length : ℝ)
        * (((atomDeficit i + 1) * ((PK i).card : ℝ))
          / (((aOf i c : ℕ) : ℝ) * (kk i : ℝ))))) atTop (nhds 0) := by
      simpa using h2.sqrt
    have h4 := h3.const_mul (2 : ℝ)
    simp only [mul_zero] at h4
    refine h4.congr fun i => ?_
    congr 1
    congr 1
    ring
  -- the prefix's own ratio
  have hrlim : Tendsto (fun i => (preGood i (aOf i c) x v : ℝ)
      / (((aOf i c : ℕ) : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
    have hzero : Tendsto (fun i => (preGood i (aOf i c) x v : ℝ)
        / (((aOf i c : ℕ) : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ))
          - 1 / (2 : ℝ) ^ v.length) atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ hεlim
      filter_upwards [eventually_ge_atTop (2 * v.length)] with i hi
      have hli : 2 * v.length ≤ kk i := by unfold kk; omega
      have hli' : v.length ≤ kk i := by omega
      have haS := aOf_le i hc0 hc1
      have hapos' := aOf_pos i hc0
      have hmain := abs_posAvg_preLaw_le i (aOf i c) v.length hapos' haS hlen hli
        ⟨wordVal v, wordVal_lt hv⟩
      have hren : posAvg (kk i) v.length (preLaw i (aOf i c) hapos' x)
          ⟨wordVal v, wordVal_lt hv⟩
          = (preGood i (aOf i c) x v : ℝ)
            / (((aOf i c : ℕ) : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)) := by
        rw [posAvg_preLaw_eq_digits i (aOf i c) v.length hapos' haS hli' x
          ⟨wordVal v, wordVal_lt hv⟩]
        congr 1
        rw [preGood_eq i (aOf i c) haS x v]
        push_cast
        rw [← Fin.sum_univ_eq_sum_range (fun q =>
          ((((bandPre i (aOf i c)).filter fun n =>
            OccursAt 2 x v (2 * kIdx (gridAt i) n (goodAtom i) + q)).card : ℕ) : ℝ))]
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 2
        refine Finset.filter_congr fun n _ => ?_
        exact blockVal_eq_wordVal_iff (y := x) hv
      rw [hren] at hmain
      simpa [Real.norm_eq_abs] using hmain
    have := hzero.add (tendsto_const_nhds (x := (1 : ℝ) / (2 : ℝ) ^ v.length) (f := atTop))
    rw [zero_add] at this
    exact this.congr fun i => by ring
  -- the denominator correction and the seam, both `≤ (ℓ + 4/c)/m_i`
  have hgd : Tendsto (fun i => ((v.length : ℝ) + 4 / c) / (kk i : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_kk _
  have hulim : Tendsto (fun i => (((aOf i c : ℕ) : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ))
      / ((bT i + aOf i c * kk i : ℕ) : ℝ)) atTop (nhds 1) := by
    have hsq : Tendsto (fun i => (((aOf i c : ℕ) : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ))
        / ((bT i + aOf i c * kk i : ℕ) : ℝ) - 1) atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ hgd
      filter_upwards [eventually_ge_atTop v.length] with i hi
      have hli : v.length ≤ kk i := by unfold kk; omega
      have ha := hapos i
      have hk := hkkpos i
      have hN := hNpos i
      have hTnn : (0 : ℝ) ≤ (bT i : ℝ) := Nat.cast_nonneg _
      have hNge : ((aOf i c : ℕ) : ℝ) * (kk i : ℝ) ≤ ((bT i + aOf i c * kk i : ℕ) : ℝ) := by
        rw [hNeq i]; linarith
      have hLnn : (0 : ℝ) ≤ (v.length : ℝ) := Nat.cast_nonneg _
      rw [Real.norm_eq_abs, hcast i hli, hNeq i, abs_le]
      set A : ℝ := ((aOf i c : ℕ) : ℝ) with hA
      set K : ℝ := (kk i : ℝ) with hK
      set T : ℝ := (bT i : ℝ) with hT
      set L : ℝ := (v.length : ℝ) with hL
      have hTa' : T ≤ (4 / c) * A := hTa i
      have hden : (0 : ℝ) < T + A * K := by nlinarith
      have hAK : A * K ≤ T + A * K := by linarith
      have hcpos : (0 : ℝ) < 4 / c := by positivity
      have hnn : (0 : ℝ) ≤ (L + 4 / c) / K := by positivity
      have hmul : (L + 4 / c) * A ≤ (L + 4 / c) / K * (T + A * K) := by
        have h1 : (L + 4 / c) / K * (A * K) = (L + 4 / c) * A := by field_simp
        have h2 : (L + 4 / c) / K * (A * K) ≤ (L + 4 / c) / K * (T + A * K) :=
          mul_le_mul_of_nonneg_left hAK hnn
        linarith [h1 ▸ h2]
      have hkeyL : 1 - (L + 4 / c) / K ≤ A * (K - L + 1) / (T + A * K) := by
        rw [le_div_iff₀ hden]
        nlinarith [hmul, hTa', ha]
      have hc4 : (4 : ℝ) ≤ 4 / c := by
        rw [le_div_iff₀ hc0]
        nlinarith [hc1, hc0]
      have hkeyR : A * (K - L + 1) / (T + A * K) ≤ 1 + (L + 4 / c) / K := by
        rw [div_le_iff₀ hden]
        nlinarith [hmul, ha, hLnn, hTnn, mul_le_mul_of_nonneg_right hc4 ha.le]
      constructor
      · linarith [hkeyL]
      · linarith [hkeyR]
    have := hsq.add (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
    rw [zero_add] at this
    exact this.congr fun i => by ring
  have hABlim : Tendsto (fun i => (preGood i (aOf i c) x v : ℝ)
      / ((bT i + aOf i c * kk i : ℕ) : ℝ)) atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
    have h := hrlim.mul hulim
    rw [mul_one] at h
    refine h.congr fun i => ?_
    have hane := (hapos i).ne'
    have hNne := (hNpos i).ne'
    have hfit : ((kk i - v.length + 1 : ℕ) : ℝ) ≠ 0 := by
      have h0 : 0 < kk i - v.length + 1 := by omega
      have : (0 : ℝ) < ((kk i - v.length + 1 : ℕ) : ℝ) := by exact_mod_cast h0
      exact this.ne'
    field_simp
  have hdlim : Tendsto (fun i =>
      (winCount (bandDig x) v (bT i + aOf i c * kk i) : ℝ)
          / ((bT i + aOf i c * kk i : ℕ) : ℝ)
        - (preGood i (aOf i c) x v : ℝ) / ((bT i + aOf i c * kk i : ℕ) : ℝ))
      atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hgd
    filter_upwards [eventually_ge_atTop v.length] with i hi
    have hli : v.length ≤ kk i := by unfold kk; omega
    have haS := aOf_le i hc0 hc1
    have ha := hapos i
    have hk := hkkpos i
    have hN := hNpos i
    have hTnn : (0 : ℝ) ≤ (bT i : ℝ) := Nat.cast_nonneg _
    obtain ⟨hlo, hhi⟩ := winCount_mid_bounds x i (aOf i c) haS v hlen hli
    have hlowR : (preGood i (aOf i c) x v : ℝ)
        ≤ (winCount (bandDig x) v (bT i + aOf i c * kk i) : ℝ) := by exact_mod_cast hlo
    have hhighR : (winCount (bandDig x) v (bT i + aOf i c * kk i) : ℝ)
        ≤ (preGood i (aOf i c) x v : ℝ) + (bT i : ℝ)
          + ((aOf i c : ℕ) : ℝ) * (v.length : ℝ) := by
      have heq : ((preGood i (aOf i c) x v + bT i + aOf i c * v.length : ℕ) : ℝ)
          = (preGood i (aOf i c) x v : ℝ) + (bT i : ℝ)
            + ((aOf i c : ℕ) : ℝ) * (v.length : ℝ) := by push_cast; ring
      rw [← heq]
      exact_mod_cast hhi
    have hNge : ((aOf i c : ℕ) : ℝ) * (kk i : ℝ) ≤ ((bT i + aOf i c * kk i : ℕ) : ℝ) := by
      rw [hNeq i]; linarith
    rw [Real.norm_eq_abs, div_sub_div_same, abs_le]
    have hnn : (0 : ℝ) ≤ ((v.length : ℝ) + 4 / c) / (kk i : ℝ) := by
      have : (0 : ℝ) < 4 / c := by positivity
      positivity
    constructor
    · rw [neg_le, ← neg_div, neg_sub]
      have hle : (preGood i (aOf i c) x v : ℝ)
          - (winCount (bandDig x) v (bT i + aOf i c * kk i) : ℝ) ≤ 0 := by linarith
      have : ((preGood i (aOf i c) x v : ℝ)
          - (winCount (bandDig x) v (bT i + aOf i c * kk i) : ℝ))
          / ((bT i + aOf i c * kk i : ℕ) : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hle hN.le
      linarith
    · rw [div_le_div_iff₀ hN hk]
      have hWA : (winCount (bandDig x) v (bT i + aOf i c * kk i) : ℝ)
          - (preGood i (aOf i c) x v : ℝ)
          ≤ (4 / c) * ((aOf i c : ℕ) : ℝ) + ((aOf i c : ℕ) : ℝ) * (v.length : ℝ) := by
        linarith [hTa i]
      nlinarith [hWA, hNge, ha, hk]
  have hfin := hdlim.add hABlim
  rw [zero_add] at hfin
  exact hfin.congr fun i => by ring

end NormalNumbers.G4.Sched
