/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Headline
import NormalNumbers.CFLimit
import NormalNumbers.Counting

/-!
# The Moshchevitin–Shkredov hot-spot criterion is false for continued fractions

Moshchevitin–Shkredov 2003, Theorem 1 (the Pyatetskii-Shapiro criterion in their form) is
the step Vandehey 2017 cites for his Lemma 3.3 (3.2 in arXiv v1).  Airey–Mance
(arXiv:1912.10265) show it is false on non-compact spaces.  This file states the CF
specialization and asks for its refutation (open target, not yet wired into
`src/NormalNumbers.lean` - wire it in once proved).

Counterexample (Airey–Mance's `(1,2,3,…)`, lifted): `x = [0; 1, 2, 3, 4, …]`.  Its digits
strictly increase, so every block occurs at most once, every block frequency tends to `0`,
and the hypothesis holds vacuously for any `σ`; but digit `1` has frequency `0 ≠ γ(I₁)`,
so `x` is not CF-normal.  Recorded as the `.falseAsStated` `Maze.lean` row
`hall_moshchevitin_shkredov_cf_false`.
-/

namespace NormalNumbers

/-- The CF specialization of Moshchevitin–Shkredov Theorem 1 (as Vandehey uses it, with a
linear `φ(t) = σ t`): uniformly bounded upper block frequencies imply CF-normality. -/
def moshchevitinShkredov_cf : Prop :=
  ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → Irrational x →
    (∃ σ : ℝ, ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
      Filter.limsup
          (fun p => (countOccurrences v ((List.range p).map (cfDigit x)) : ℝ) / p)
          Filter.atTop
        ≤ σ * (gaussMeasure (cfCylinder v)).toReal) →
    IsCFNormal x

/-! ## The witness `[0; 1, 2, 3, …]` -/

/-- The prefix words of the counterexample: `msWord s = [1, 2, …, s+1]`. -/
private def msWord (s : ℕ) : List ℕ := (List.range (s + 1)).map (· + 1)

private lemma msWord_length (s : ℕ) : (msWord s).length = s + 1 := by
  simp [msWord]

private lemma msWord_ne (s : ℕ) : msWord s ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [msWord_length] at this
  simp at this

private lemma msWord_pos (s : ℕ) : ∀ a ∈ msWord s, 1 ≤ a := by
  intro a ha
  simp only [msWord, List.mem_map, List.mem_range] at ha
  obtain ⟨k, -, rfl⟩ := ha
  omega

private lemma msWord_ext (s : ℕ) : msWord (s + 1) = msWord s ++ [s + 2] := by
  simp [msWord, List.range_succ]

private lemma msWord_getD (s i : ℕ) (hi : i < s + 1) :
    (msWord s).getD i 0 = i + 1 := by
  have hlen : i < (msWord s).length := by rw [msWord_length]; exact hi
  rw [List.getD_eq_getElem _ _ hlen]
  simp [msWord]

/-- The counterexample exists: an irrational `x ∈ (0,1)` whose CF digits are
`1, 2, 3, …` — strictly increasing, so no genuine block repeats. -/
theorem exists_irrational_cfDigit_succ :
    ∃ x : ℝ, Irrational x ∧ x ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i, cfDigit x i = i + 1 := by
  obtain ⟨x, hirr, hmem⟩ :=
    exists_irrational_mem_iInter_cfCylinder msWord msWord_ne msWord_pos
      (fun s => ⟨[s + 2], by simp, msWord_ext s⟩)
  refine ⟨x, hirr, (hmem 0).1, fun i => ?_⟩
  have h := (hmem i).2 i (by rw [msWord_length]; omega)
  rw [h, msWord_getD i i (by omega)]

/-- With strictly increasing digits every genuine block occurs at most once:
its first letter pins the only possible start position. -/
private lemma countOccurrences_succ_le_one (v : List ℕ) (hv : v ≠ []) (p : ℕ) :
    countOccurrences v ((List.range p).map (fun i => i + 1)) ≤ 1 := by
  classical
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hv
  rw [countOccurrences_range_map]
  have hsub : ((Finset.range (p + 1)).filter
      (fun i => i + (a :: t).length ≤ p ∧ MatchesAt (fun i => i + 1) (a :: t) i))
      ⊆ {a - 1} := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have h0 := hi.2.2 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    simp only [Finset.mem_singleton]
    omega
  calc _ ≤ ({a - 1} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 1 := by simp

/-- **Refutation**: witnessed by `x = [0; 1, 2, 3, …]`.  Every genuine block
occurs at most once, so every block frequency tends to `0` and the hypothesis
holds with `σ = 0`; but CF-normality would force the frequency of the digit
`1` to be `γ(I₁) = log₂(4/3) > 0`. -/
theorem moshchevitinShkredov_cf_false : ¬ moshchevitinShkredov_cf := by
  intro hMS
  obtain ⟨x, hirr, hx01, hdig⟩ := exists_irrational_cfDigit_succ
  -- every genuine block frequency tends to `0`
  have hmap : ∀ p : ℕ, (List.range p).map (cfDigit x) = (List.range p).map (fun i => i + 1) := by
    intro p; exact List.map_congr_left (fun i _ => hdig i)
  have htend : ∀ v : List ℕ, v ≠ [] →
      Filter.Tendsto
        (fun p => (countOccurrences v ((List.range p).map (cfDigit x)) : ℝ) / p)
        Filter.atTop (nhds 0) := by
    intro v hv
    apply squeeze_zero (fun p => by positivity) (g := fun p : ℕ => 1 / (p : ℝ))
    · intro p
      rw [hmap p]
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp
      · have hpR : (0 : ℝ) ≤ p := by positivity
        have hle : ((countOccurrences v ((List.range p).map (fun i => i + 1)) : ℕ) : ℝ) ≤ 1 := by
          exact_mod_cast countOccurrences_succ_le_one v hv p
        gcongr
    · exact tendsto_one_div_atTop_nhds_zero_nat
  -- the hypothesis of the criterion holds with `σ = 0`
  have hCF : IsCFNormal x := by
    refine hMS x hx01 hirr ⟨0, fun v hv _ => ?_⟩
    rw [(htend v hv).limsup_eq]
    simp
  -- but digit `1` has frequency `0 ≠ γ(I₁)`
  have h1 := hCF [1] (by simp) (by simp)
  have huniq := tendsto_nhds_unique h1 (htend [1] (by simp))
  have hγ : gaussMeasure (cfCylinder [1]) = ENNReal.ofReal (Real.logb 2 (4 / 3)) := by
    rw [gaussMeasure_digit_cylinder 1 le_rfl]
    norm_num
  rw [hγ, ENNReal.toReal_ofReal (Real.logb_nonneg (by norm_num) (by norm_num))] at huniq
  have : (0 : ℝ) < Real.logb 2 (4 / 3) := Real.logb_pos (by norm_num) (by norm_num)
  linarith

end NormalNumbers
