/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBad

/-!
# A power-potential avoidance engine with averaged new charges and legal children

A variant of `UniformBad.exists_avoid_of_stagePotential` tuned for sharper exponents:

* the weight of an obstacle on a stage-`k` window is `(r/ℓ_k)^α` for a real `α > 0`;
* the threshold is `ρ^α`, and an obstacle of relative size `< ρ` meets at most `2Kρ + 2`
  children (`card_children_le_real`);
* the newly charged obstacles enter only through their **sum over the `K` children**, so the
  application bounds an average, not a worst child;
* a predicate `Good` restricts the children (at least `K'` good children of a good window), so
  constraints handled exactly (small bases) can be layered on top.
-/

namespace NormalNumbers.UniformBadThreshold

open NormalNumbers.UniformBad (obstacle window)
open scoped ENNReal

section PowerEngine

variable {ι : Type*}

/-- Obstacles with stage in `P` meeting the stage-`k` window at `x`. -/
def potSetP (c r : ι → ℝ) (st : ι → ℕ) (ℓ₀ : ℝ) (K : ℕ) (P : ℕ → Prop) (k : ℕ) (x : ℝ) :
    Set ι :=
  {i | P (st i) ∧ (obstacle c r i ∩ window ℓ₀ K k x).Nonempty}

/-- The power potential `Σ (r_i/ℓ_k)^α` over `potSetP`. -/
noncomputable def powPot (c r : ι → ℝ) (st : ι → ℕ) (ℓ₀ α : ℝ) (K : ℕ) (P : ℕ → Prop)
    (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∑' i, (potSetP c r st ℓ₀ K P k x).indicator
    (fun i => ENNReal.ofReal ((r i / (ℓ₀ / (K : ℝ) ^ k)) ^ α)) i

open Classical in
/-- A closed interval of length `2r` meets at most `2r/ℓ + 2` of the closed children. -/
theorem card_children_le_real (c r x ℓ : ℝ) (hr : 0 ≤ r) (hℓ : 0 < ℓ) (K : ℕ) :
    (((Finset.range K).filter (fun j : ℕ =>
      (Set.Icc (c - r) (c + r) ∩ Set.Icc (x + j * ℓ) (x + j * ℓ + ℓ)).Nonempty)).card : ℝ) ≤
      2 * r / ℓ + 2 := by
  set F := (Finset.range K).filter (fun j : ℕ =>
      (Set.Icc (c - r) (c + r) ∩ Set.Icc (x + j * ℓ) (x + j * ℓ + ℓ)).Nonempty)
  rcases F.eq_empty_or_nonempty with h | h
  · rw [h, Finset.card_empty, Nat.cast_zero]; positivity
  set m := F.min' h
  set M := F.max' h
  have hm : m ∈ F := F.min'_mem h
  have hM : M ∈ F := F.max'_mem h
  simp only [F, Finset.mem_filter] at hm hM
  obtain ⟨-, y, ⟨hy1, hy2⟩, hy3, hy4⟩ := hm
  obtain ⟨-, z, ⟨hz1, hz2⟩, hz3, hz4⟩ := hM
  have hsub : F ⊆ Finset.Icc m M := fun j hj =>
    Finset.mem_Icc.2 ⟨F.min'_le j hj, F.le_max' j hj⟩
  have hcard : (F.card : ℝ) ≤ (M : ℝ) - m + 1 := by
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    have hmM : m ≤ M := F.min'_le M (F.max'_mem h)
    have : (F.card : ℝ) ≤ ((M + 1 - m : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  have hgap : ((M : ℝ) - m) * ℓ ≤ 2 * r + ℓ := by nlinarith
  have : (F.card : ℝ) * ℓ ≤ 2 * r + 2 * ℓ := by nlinarith
  rw [show 2 * r / ℓ + 2 = (2 * r + 2 * ℓ) / ℓ by field_simp]
  exact (le_div_iff₀ hℓ).2 this


/-- Child windows lie in the parent window. -/
theorem child_sub_window {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) {K : ℕ} (hK : 0 < K) (k : ℕ) (x : ℝ) {j : ℕ}
    (hj : j < K) : window ℓ₀ K (k + 1) (x + j * (ℓ₀ / (K : ℝ) ^ (k + 1))) ⊆ window ℓ₀ K k x := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hℓ' : 0 < ℓ₀ / (K : ℝ) ^ (k + 1) := div_pos hℓ₀ (pow_pos hKpos _)
  have hℓK : ℓ₀ / (K : ℝ) ^ k = K * (ℓ₀ / (K : ℝ) ^ (k + 1)) := by
    rw [pow_succ]; field_simp
  have hj' : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
  rintro y ⟨h1, h2⟩
  refine ⟨le_trans (by nlinarith [mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) hℓ'.le]) h1,
    h2.trans ?_⟩
  rw [hℓK]; nlinarith

open Classical in
/-- **Power engine step.**  A good stage-`k` window with carried potential `< ρ^α` has a good
child with carried potential `< ρ^α`. -/
theorem powPot_step (c r : ι → ℝ) (st : ι → ℕ) {K K' : ℕ} (hK : 0 < K) {ℓ₀ α ρ g : ℝ}
    (hℓ₀ : 0 < ℓ₀) (hα : 0 < α) (hρ : 0 < ρ) (hr : ∀ i, 0 ≤ r i) (hg : 0 ≤ g)
    (hbal : (2 * K * ρ + 2) * (K : ℝ) ^ α * ρ ^ α + g ≤ K' * ρ ^ α)
    (hnew : ∀ k x, ∑ j ∈ Finset.range K, powPot c r st ℓ₀ α K (· = k + 1) (k + 1)
        (x + j * (ℓ₀ / (K : ℝ) ^ (k + 1))) ≤ ENNReal.ofReal g)
    (Good : ℕ → ℝ → Prop)
    (hGood : ∀ k x, Good k x → K' ≤ ((Finset.range K).filter
        fun j : ℕ => Good (k + 1) (x + j * (ℓ₀ / (K : ℝ) ^ (k + 1)))).card)
    {k : ℕ} {x : ℝ} (hgk : Good k x)
    (hk : powPot c r st ℓ₀ α K (· ≤ k) k x < ENNReal.ofReal (ρ ^ α)) :
    ∃ j : ℕ, j < K ∧ Good (k + 1) (x + j * (ℓ₀ / (K : ℝ) ^ (k + 1))) ∧
      powPot c r st ℓ₀ α K (· ≤ k + 1) (k + 1) (x + j * (ℓ₀ / (K : ℝ) ^ (k + 1))) <
        ENNReal.ofReal (ρ ^ α) := by
  classical
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  set ℓ := ℓ₀ / (K : ℝ) ^ k with hℓ
  set ℓ' := ℓ₀ / (K : ℝ) ^ (k + 1) with hℓ'
  have hℓpos : 0 < ℓ := div_pos hℓ₀ (pow_pos hKpos k)
  have hℓ'pos : 0 < ℓ' := div_pos hℓ₀ (pow_pos hKpos (k + 1))
  have hℓK : ℓ = K * ℓ' := by simp only [hℓ, hℓ', pow_succ]; field_simp
  set f : ι → ℝ≥0∞ := fun i => ENNReal.ofReal ((r i / ℓ) ^ α) with hf
  set f' : ι → ℝ≥0∞ := fun i => ENNReal.ofReal ((r i / ℓ') ^ α) with hf'
  have hff' : ∀ i, f' i = ENNReal.ofReal ((K : ℝ) ^ α) * f i := by
    intro i
    simp only [hf, hf']
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hKpos.le _), ← Real.mul_rpow hKpos.le
      (div_nonneg (hr i) hℓpos.le), hℓK]
    congr 2; field_simp
  set Φ := powPot c r st ℓ₀ α K (· ≤ k) k x with hΦ
  set S : ℕ → Set ι := fun j => potSetP c r st ℓ₀ K (· ≤ k) (k + 1) (x + j * ℓ') with hS
  set old : ℕ → ℝ≥0∞ := fun j => ∑' i, (S j).indicator f' i with hold
  set new : ℕ → ℝ≥0∞ := fun j => powPot c r st ℓ₀ α K (· = k + 1) (k + 1) (x + j * ℓ')
  have hsplit : ∀ j : ℕ, powPot c r st ℓ₀ α K (· ≤ k + 1) (k + 1) (x + j * ℓ') ≤
      old j + new j := by
    intro j
    simp only [powPot, hold, new]
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    simp only [Set.indicator_apply, potSetP, hS, Set.mem_ofPred_eq]
    by_cases h1 : st i ≤ k + 1 ∧ (obstacle c r i ∩ window ℓ₀ K (k + 1) (x + j * ℓ')).Nonempty
    · rw [if_pos h1]
      rcases Nat.lt_or_ge (st i) (k + 1) with h | h
      · rw [if_pos ⟨by omega, h1.2⟩]; exact le_self_add
      · rw [if_neg (fun h' => by omega), if_pos ⟨by omega, h1.2⟩, zero_add]
    · rw [if_neg h1]; exact zero_le
  set a : ℝ := (2 * K * ρ + 2) * (K : ℝ) ^ α with ha
  have ha0 : 0 < a := by positivity
  have hpt : ∀ i, ∑ j ∈ Finset.range K, (S j).indicator f' i ≤
      ENNReal.ofReal a * (potSetP c r st ℓ₀ K (· ≤ k) k x).indicator f i := by
    intro i
    by_cases hi : i ∈ potSetP c r st ℓ₀ K (· ≤ k) k x
    · rw [Set.indicator_of_mem hi]
      have hfi : f i < ENNReal.ofReal (ρ ^ α) := by
        refine lt_of_le_of_lt ?_ hk
        rw [hΦ, powPot]
        exact ENNReal.le_tsum (f := fun i => (potSetP c r st ℓ₀ K (· ≤ k) k x).indicator
          (fun i => ENNReal.ofReal ((r i / (ℓ₀ / (K : ℝ) ^ k)) ^ α)) i) i |>.trans' (by
            rw [Set.indicator_of_mem hi])
      rw [hf, ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hρ _),
        Real.rpow_lt_rpow_iff (div_nonneg (hr i) hℓpos.le) hρ.le hα] at hfi
      have hcard := card_children_le_real (c i) (r i) x ℓ' (hr i) hℓ'pos K
      have hcard' : (((Finset.range K).filter (fun j : ℕ => (Set.Icc (c i - r i) (c i + r i) ∩
          Set.Icc (x + j * ℓ') (x + j * ℓ' + ℓ')).Nonempty)).card : ℝ) ≤ 2 * K * ρ + 2 := by
        refine hcard.trans ?_
        have : r i / ℓ' = K * (r i / ℓ) := by rw [hℓK]; field_simp
        rw [mul_div_assoc, this]; nlinarith
      calc ∑ j ∈ Finset.range K, (S j).indicator f' i
          ≤ ∑ j ∈ Finset.range K, (if (Set.Icc (c i - r i) (c i + r i) ∩
              Set.Icc (x + j * ℓ') (x + j * ℓ' + ℓ')).Nonempty then f' i else 0) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [Set.indicator_apply]
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd h1.2 h2
            · exact zero_le
            · exact le_rfl
        _ = ((Finset.range K).filter (fun j : ℕ => (Set.Icc (c i - r i) (c i + r i) ∩
              Set.Icc (x + j * ℓ') (x + j * ℓ' + ℓ')).Nonempty)).card * f' i := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ ENNReal.ofReal (2 * K * ρ + 2) * f' i := by
            gcongr
            rw [← ENNReal.ofReal_natCast]
            exact ENNReal.ofReal_le_ofReal hcard'
        _ = ENNReal.ofReal a * f i := by
            rw [hff', ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    · rw [Set.indicator_of_notMem hi, mul_zero]
      refine le_of_eq (Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem ?_ _)
      rintro ⟨h1, y, hy, hyw⟩
      exact hi ⟨h1, y, hy, child_sub_window hℓ₀ hK k x (Finset.mem_range.1 hj) hyw⟩
  have hsumold : ∑ j ∈ Finset.range K, old j ≤ ENNReal.ofReal a * Φ := by
    simp only [hold]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), hΦ, powPot,
      ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hpt
  set G := (Finset.range K).filter fun j : ℕ => Good (k + 1) (x + j * ℓ')
  have hGcard : K' ≤ G.card := hGood k x hgk
  have hΦtop : Φ ≠ ⊤ := ne_top_of_lt hk
  have hlt : ENNReal.ofReal a * Φ < ENNReal.ofReal a * ENNReal.ofReal (ρ ^ α) := by
    rw [mul_comm, mul_comm (ENNReal.ofReal a)]
    exact ENNReal.mul_lt_mul_left (by simpa using ha0) ENNReal.ofReal_ne_top hk
  have htot : ∑ j ∈ G, powPot c r st ℓ₀ α K (· ≤ k + 1) (k + 1) (x + j * ℓ') <
      G.card * ENNReal.ofReal (ρ ^ α) := by
    calc ∑ j ∈ G, powPot c r st ℓ₀ α K (· ≤ k + 1) (k + 1) (x + j * ℓ')
        ≤ ∑ j ∈ Finset.range K, (old j + new j) :=
          (Finset.sum_le_sum fun j _ => hsplit j).trans
            (Finset.sum_le_sum_of_subset (f := fun j : ℕ => old j + new j)
              (Finset.filter_subset _ _))
      _ = ∑ j ∈ Finset.range K, old j + ∑ j ∈ Finset.range K, new j := Finset.sum_add_distrib
      _ ≤ ENNReal.ofReal a * Φ + ENNReal.ofReal g := add_le_add hsumold (hnew k x)
      _ < ENNReal.ofReal a * ENNReal.ofReal (ρ ^ α) + ENNReal.ofReal g :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hlt
      _ = ENNReal.ofReal (a * ρ ^ α + g) := by
          rw [← ENNReal.ofReal_mul ha0.le, ← ENNReal.ofReal_add (by positivity) hg]
      _ ≤ ENNReal.ofReal (K' * ρ ^ α) := ENNReal.ofReal_le_ofReal hbal
      _ = (K' : ℝ≥0∞) * ENNReal.ofReal (ρ ^ α) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ G.card * ENNReal.ofReal (ρ ^ α) := by gcongr
  by_contra hcon
  push Not at hcon
  have : G.card * ENNReal.ofReal (ρ ^ α) ≤
      ∑ j ∈ G, powPot c r st ℓ₀ α K (· ≤ k + 1) (k + 1) (x + j * ℓ') := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj := Finset.mem_filter.1 hj
    exact hcon j (Finset.mem_range.1 hj.1) hj.2
  exact absurd (lt_of_le_of_lt this htot) (lt_irrefl _)


open Classical in
/-- **Power engine.**  Obstacles of positive radius, all charged at stages `≥ 1`, whose new
charges summed over the `K` children are `≤ g`, with the balance
`(2Kρ + 2) K^α ρ^α + g ≤ K' ρ^α`, are all avoided by a point that lies in a good window at every
stage. -/
theorem exists_avoid_powPot (c r : ι → ℝ) (st : ι → ℕ) {K K' : ℕ} (hK : 2 ≤ K)
    {x₀ ℓ₀ α ρ g : ℝ} (hℓ₀ : 0 < ℓ₀) (hα : 0 < α) (hρ : 0 < ρ) (hr : ∀ i, 0 < r i)
    (hst : ∀ i, 1 ≤ st i) (hg : 0 ≤ g)
    (hbal : (2 * K * ρ + 2) * (K : ℝ) ^ α * ρ ^ α + g ≤ K' * ρ ^ α)
    (hnew : ∀ k x, ∑ j ∈ Finset.range K, powPot c r st ℓ₀ α K (· = k + 1) (k + 1)
        (x + j * (ℓ₀ / (K : ℝ) ^ (k + 1))) ≤ ENNReal.ofReal g)
    (Good : ℕ → ℝ → Prop) (hG0 : Good 0 x₀)
    (hGood : ∀ k x, Good k x → K' ≤ ((Finset.range K).filter
        fun j : ℕ => Good (k + 1) (x + j * (ℓ₀ / (K : ℝ) ^ (k + 1)))).card) :
    ∃ ξ ∈ Set.Icc x₀ (x₀ + ℓ₀), (∀ i, ξ ∉ obstacle c r i) ∧
      ∀ k, ∃ x, Good k x ∧ ξ ∈ window ℓ₀ K k x := by
  have hK0 : 0 < K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
  set θ := ENNReal.ofReal (ρ ^ α)
  set ℓ : ℕ → ℝ := fun k => ℓ₀ / (K : ℝ) ^ k with hℓ
  have hℓpos : ∀ k, 0 < ℓ k := fun k => div_pos hℓ₀ (pow_pos hKpos k)
  have hℓsucc : ∀ k, (K : ℝ) * ℓ (k + 1) = ℓ k := by
    intro k; simp only [hℓ, pow_succ]; field_simp
  have hθpos : 0 < θ := ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hρ _)
  have h0 : Good 0 x₀ ∧ powPot c r st ℓ₀ α K (· ≤ 0) 0 x₀ < θ := by
    refine ⟨hG0, lt_of_eq_of_lt ?_ hθpos⟩
    rw [powPot]
    refine ENNReal.tsum_eq_zero.2 fun i => Set.indicator_of_notMem ?_ _
    rintro ⟨h, -⟩; have := hst i; exact absurd h (by omega)
  have step := fun (k : ℕ) (x : ℝ) (hk : Good k x ∧ powPot c r st ℓ₀ α K (· ≤ k) k x < θ) =>
    powPot_step c r st hK0 hℓ₀ hα hρ (fun i => (hr i).le) hg hbal hnew Good hGood hk.1 hk.2
  let seq : ∀ k : ℕ, {x : ℝ // Good k x ∧ powPot c r st ℓ₀ α K (· ≤ k) k x < θ} := fun k =>
    Nat.rec (motive := fun k => {x : ℝ // Good k x ∧ powPot c r st ℓ₀ α K (· ≤ k) k x < θ})
      ⟨x₀, h0⟩
      (fun k s => ⟨s.1 + (Classical.choose (step k s.1 s.2) : ℕ) * (ℓ₀ / (K : ℝ) ^ (k + 1)),
        (Classical.choose_spec (step k s.1 s.2)).2⟩) k
  let x : ℕ → ℝ := fun k => (seq k).1
  have hpot : ∀ k, Good k (x k) ∧ powPot c r st ℓ₀ α K (· ≤ k) k (x k) < θ := fun k => (seq k).2
  have hxs : ∀ k, ∃ j : ℕ, j < K ∧ x (k + 1) = x k + j * ℓ (k + 1) := fun k =>
    ⟨_, (Classical.choose_spec (step k (seq k).1 (seq k).2)).1, rfl⟩
  have hmono : ∀ k, x k ≤ x (k + 1) := by
    intro k
    obtain ⟨j, -, hj⟩ := hxs k
    rw [hj]
    linarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) (hℓpos (k + 1)).le]
  have hright : ∀ k, x (k + 1) + ℓ (k + 1) ≤ x k + ℓ k := by
    intro k
    obtain ⟨j, hj, hjx⟩ := hxs k
    rw [hjx, ← hℓsucc k]
    have : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
    nlinarith [hℓpos (k + 1)]
  have hxmono : Monotone x := monotone_nat_of_le_succ hmono
  have hranti : Antitone (fun k => x k + ℓ k) := antitone_nat_of_succ_le hright
  have hℓ0 : ℓ 0 = ℓ₀ := by simp [hℓ]
  have hx0 : x 0 = x₀ := rfl
  have hbdd : BddAbove (Set.range x) := by
    refine ⟨x₀ + ℓ₀, ?_⟩
    rintro _ ⟨k, rfl⟩
    have := hranti (Nat.zero_le k)
    simp only [hℓ0, hx0] at this
    linarith [hℓpos k]
  set ξ := ⨆ k, x k with hξ
  have hξlo : ∀ k, x k ≤ ξ := fun k => le_ciSup hbdd k
  have hξhi : ∀ k, ξ ≤ x k + ℓ k := by
    intro k
    refine ciSup_le fun m => ?_
    rcases le_total m k with hmk | hkm
    · linarith [hxmono hmk, hℓpos k]
    · linarith [hranti hkm, hℓpos m]
  have hξwin : ∀ k, ξ ∈ window ℓ₀ K k (x k) := fun k => ⟨hξlo k, hξhi k⟩
  refine ⟨ξ, ⟨hx0 ▸ hξlo 0, by have := hξhi 0; rwa [hℓ0, hx0] at this⟩, ?_,
    fun k => ⟨x k, (hpot k).1, hξwin k⟩⟩
  intro i hi
  have hri := hr i
  obtain ⟨k₁, hk₁⟩ := pow_unbounded_of_one_lt (ρ * ℓ₀ / r i) hK1
  set k := max k₁ (st i)
  have hKk : (K : ℝ) ^ k₁ ≤ (K : ℝ) ^ k := pow_le_pow_right₀ hK1.le (le_max_left _ _)
  have hmem : i ∈ potSetP c r st ℓ₀ K (· ≤ k) k (x k) := ⟨le_max_right _ _, _, hi, hξwin k⟩
  have hterm : ENNReal.ofReal ((r i / (ℓ₀ / (K : ℝ) ^ k)) ^ α) ≤
      powPot c r st ℓ₀ α K (· ≤ k) k (x k) := by
    rw [powPot]
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum i)
    rw [Set.indicator_of_mem hmem]
  have hlt := lt_of_le_of_lt hterm (hpot k).2
  rw [ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hρ _),
    Real.rpow_lt_rpow_iff (div_nonneg hri.le (hℓpos k).le) hρ.le hα] at hlt
  have h1 : ρ * ℓ₀ < r i * (K : ℝ) ^ k := by
    rw [div_lt_iff₀ hri] at hk₁; nlinarith
  rw [div_lt_iff₀ (hℓpos k)] at hlt
  simp only [hℓ] at hlt
  rw [mul_div_assoc', lt_div_iff₀ (pow_pos hKpos k)] at hlt
  linarith

end PowerEngine

end NormalNumbers.UniformBadThreshold
