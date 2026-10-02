/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MasterLnTwoBase3
import NormalNumbers.MasterPiSq
import NormalNumbers.MasterConsequences
import NormalNumbers.LnTwoFreq
import NormalNumbers.LnTwoPrimeWindow
import NormalNumbers.G4EntropyStable

/-!
# Phase 3: the Maze test for the master conjectures

For every `Maze.lean` row whose missing input is equidistribution, normality or a
BBP/Bailey–Crandall orbit: does Hypothesis A (or Borel) supply it?  Implied rows get a wiring
theorem; the verdicts are collected as Lean data in `mazeTestImplied` / `mazeTestNotImplied`,
whose double-backtick names fail the build if a cited declaration disappears.

New mathematics on the way: `run_sublinear_of_isNormal` (normality ⇒ single-digit runs are
`o(n)`) and `equidistributed_lnTwoOrbit_iff` (the Maze restatement row, now a kernel `↔`).
-/

namespace NormalNumbers.MasterConjectures
open Filter NormalNumbers

theorem orbit_mem_cell {b : ℕ} (hb : 2 ≤ b) {x : ℝ} {n d : ℕ}
    (h : digitOf b (Int.fract x) n = d) :
    orbit b x n ∈ Set.Ico ((d : ℝ) / b) ((d + 1 : ℝ) / b) := by
  have h1 := digitOf_fract_eq_floor_mul_orbit b hb x n
  rw [h] at h1
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbR : (0 : ℝ) < b := by linarith
  have h2 := (Int.floor_eq_iff.1 h1.symm)
  push_cast at h2
  constructor
  · rw [div_le_iff₀ hbR]; linarith [h2.1]
  · rw [lt_div_iff₀ hbR]; linarith [h2.2]

/-- **Normality forces sublinear runs**: in a base-`b`-normal number, a run of a single digit
starting at position `n` has length `o(n)`.  (Equidistribution of the orbit in the digit cell.) -/
theorem run_sublinear_of_isNormal {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (h : IsNormal b x) (d : ℕ)
    (hd : d < b) : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      OccursAt b x (List.replicate k d) n → (k : ℝ) ≤ ε * n := by
  intro ε hε
  rw [isNormal_iff_equidistributed_orbit b hb] at h
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hdR : (d : ℝ) + 1 ≤ b := by exact_mod_cast hd
  have hE := h ((d : ℝ) / b) ((d + 1 : ℝ) / b) (by positivity)
    (by rw [div_le_div_iff_of_pos_right (by linarith)]; linarith)
    (by rw [div_le_one (by linarith)]; exact hdR)
  have hlen : ((d + 1 : ℝ) / b - (d : ℝ) / b) = 1 / b := by ring
  rw [hlen] at hE
  set δ := min (ε / 8) (1 / 4) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hE δ hδ0
  have hV : ∀ m, M ≤ m → |(visitCount (orbit b x) ((d : ℝ) / b) ((d + 1 : ℝ) / b) m : ℝ)
      - m / b| ≤ δ * m := by
    intro m hm
    have := hM m hm
    rw [Real.dist_eq] at this
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [visitCount]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hpos
    have : |(visitCount (orbit b x) ((d : ℝ) / b) ((d + 1 : ℝ) / b) m : ℝ) - m / b|
        = m * |(visitCount (orbit b x) ((d : ℝ) / b) ((d + 1 : ℝ) / b) m : ℝ) / m - 1 / b| := by
      rw [← abs_of_pos hmR, ← abs_mul, abs_of_pos hmR]; congr 1; field_simp
    rw [this]; nlinarith [abs_nonneg ((visitCount (orbit b x) ((d : ℝ) / b) ((d + 1 : ℝ) / b) m : ℝ) / m - 1 / b)]
  filter_upwards [eventually_ge_atTop M] with n hn k hk
  set V := fun m => (visitCount (orbit b x) ((d : ℝ) / b) ((d + 1 : ℝ) / b) m : ℝ)
  have hrun : V n + k ≤ V (n + k) := by
    simp only [V, visitCount_eq_sum]
    rw [Finset.sum_range_add]
    gcongr
    calc (k : ℝ) = ∑ j ∈ Finset.range k, (1 : ℝ) := by simp
      _ ≤ _ := by
        refine le_of_eq (Finset.sum_congr rfl fun j hj => ?_)
        rw [if_pos]
        apply orbit_mem_cell hb
        have := hk j (by simpa using Finset.mem_range.1 hj)
        simpa using this
  have h1 := abs_le.1 (hV n hn)
  have h2 := abs_le.1 (hV (n + k) (by omega))
  simp only [V] at hrun
  push_cast at h2
  have hδ8 : δ ≤ ε / 8 := min_le_left _ _
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hinv : (n + k : ℝ) / b ≤ (n + k) / 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hbR
  have hnb : (n : ℝ) / b ≥ 0 := by positivity
  have hkey : (k : ℝ) ≤ (n + k) / b - n / b + 2 * δ * n + δ * k := by nlinarith
  have hkb : (n + k : ℝ) / b - n / b = k / b := by ring
  have hkb2 : (k : ℝ) / b ≤ k / 2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hbR
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  nlinarith

/-! ## Phase 3: wiring edges into the Maze -/

/-- Hypothesis A gives the surrogate-orbit equidistribution directly (the attractor branch is
excluded by `irrational_log_two`). -/
theorem hypA_equidistributed_lnTwoOrbit (hA : BaileyCrandallHypA) :
    Equidistributed lnTwoOrbit := by
  rcases hA (Polynomial.C 1) Polynomial.X 2 (by simp) (by simp) (fun n hn => by simp; omega)
    le_rfl with hfa | heq
  · exfalso
    rw [bcOrbit_lnTwo] at hfa
    have hpert := hasFiniteAttractor_perturb _ _ hfa tendsto_pow_mul_lnTwoTail
    rw [← funext orbit_log_two_eq] at hpert
    exact not_irrational_of_hasFiniteAttractor _ hpert irrational_log_two
  · rwa [bcOrbit_lnTwo] at heq

/-- **Maze "Hypothesis A as weaker", made a kernel equivalence**: for `ln 2`, equidistribution of
the surrogate orbit is *equivalent* to base-2 normality (the reverse direction is the two-sided
perturbation lemma applied to `lnTwoOrbit = fract(orbit − tail)`). -/
theorem equidistributed_lnTwoOrbit_iff : Equidistributed lnTwoOrbit ↔ IsNormal 2 (Real.log 2) := by
  refine ⟨isNormal_log_two_of_equidistributed, fun h => ?_⟩
  rw [isNormal_iff_equidistributed_orbit 2 le_rfl] at h
  have hδ : Tendsto (fun n : ℕ => -(2 ^ n * lnTwoTail n)) atTop (nhds 0) := by
    simpa using tendsto_pow_mul_lnTwoTail.neg
  have := equidistributed_of_fract_perturb_abs _ _ h (fun n => ⟨Int.fract_nonneg _,
    Int.fract_lt_one _⟩) hδ
  convert this using 1
  funext n
  rw [orbit_log_two_eq]
  rw [show Int.fract (lnTwoOrbit n + 2 ^ n * lnTwoTail n) + -(2 ^ n * lnTwoTail n)
      = lnTwoOrbit n + ((-⌊lnTwoOrbit n + 2 ^ n * lnTwoTail n⌋ : ℤ) : ℝ) by
        rw [Int.fract]; push_cast; ring, Int.fract_add_intCast,
    Int.fract_eq_self.2 (lnTwoOrbit_mem_Ico n)]

/-- Maze "frequency hypothesis" for `ln 2`: Hypothesis A implies every binary word's cylinder is
visited at a positive rate. -/
theorem hypA_lnTwoHypothesisFreq (hA : BaileyCrandallHypA) (w : List ℕ) (hw : ∀ d ∈ w, d < 2) :
    LnTwoHypothesisFreq w :=
  hypothesisFreq_of_equidistributed (hypA_equidistributed_lnTwoOrbit hA) w hw

/-- Hypothesis A ⇒ `ln 2` disjunctive in base 2 (maze rows "Bugeaud–Kim complexity from μ":
full subword complexity `2ⁿ`). -/
theorem hypA_lnTwo_isDisjunctive (hA : BaileyCrandallHypA) : IsDisjunctive 2 (Real.log 2) :=
  (hypA_lnTwo hA).isDisjunctive le_rfl

/-- Hypothesis A ⇒ Axiom Λ for `ln 2`. -/
theorem hypA_lnTwoHypothesisLambda (hA : BaileyCrandallHypA) : LnTwoHypothesisLambda :=
  (circleOmegaLimit_volume_pos_iff_isDisjunctive 2 le_rfl _).2 (hypA_lnTwo_isDisjunctive hA)

/-- Maze rows "beta below 9 (run cap)" and "abc path A": Hypothesis A caps every binary run of
`ln 2` at `ε·n` eventually, for every `ε > 0` — far below the unconditional `9n`. -/
theorem hypA_lnTwo_run_sublinear (hA : BaileyCrandallHypA) (d : ℕ) (hd : d < 2) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      OccursAt 2 (Real.log 2) (List.replicate k d) n → (k : ℝ) ≤ ε * n :=
  run_sublinear_of_isNormal le_rfl (hypA_lnTwo hA) d hd

/-- Hypothesis A ⇒ the prime-window run-bound node with a linear cap `⌊ε n⌋`, any `ε > 0`. -/
theorem hypA_lnTwoPrimeRunBound (hA : BaileyCrandallHypA) (ε : ℝ) (hε : 0 < ε) :
    ∃ P₀, LnTwoPrimeRunBound (fun n => ⌊ε * n⌋₊) P₀ := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hypA_lnTwo_run_sublinear hA 0 (by norm_num) ε hε)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hypA_lnTwo_run_sublinear hA 1 (by norm_num) ε hε)
  refine ⟨max N0 N1 + 1, fun p k _ hp h => ?_⟩
  have hk : (k : ℝ) ≤ ε * ((p - 1 : ℕ) : ℝ) := by
    rcases h with h | h
    · exact hN0 (p - 1) (by omega) k h
    · exact hN1 (p - 1) (by omega) k h
  exact Nat.le_floor hk

/-- Maze "BBP extraction for pi normality" (a wall): Hypothesis A alone (the BBP formula is proved
in-repo) reopens it, giving normality of `π` in bases 2 and 16. -/
theorem hypA_reopens_bbp_pi (hA : BaileyCrandallHypA) :
    IsNormal 2 Real.pi ∧ IsNormal 16 Real.pi :=
  ⟨hypA_pi_base2_uncond hA, hypA_pi_base16 hA piBBP_proved⟩

/-- **Maze test, implied rows**: `(row name, wiring theorem)`. -/
def mazeTestImplied : List (String × Lean.Name) := [
  ("BBP extraction for pi normality", ``hypA_reopens_bbp_pi),
  ("Hypothesis A as weaker", ``equidistributed_lnTwoOrbit_iff),
  ("KickBootstrap", ``hypA_equidistributed_lnTwoOrbit),
  ("beta below 9 (run cap)", ``hypA_lnTwo_run_sublinear),
  ("abc path A (non-Wieferich)", ``hypA_lnTwoPrimeRunBound),
  ("Bugeaud-Kim complexity from mu", ``hypA_lnTwo_isDisjunctive),
  ("Axiom Λ / D_w / Freq nodes for ln 2 (ConditionalDisjunctive, LnTwoFreq)",
    ``hypA_lnTwoHypothesisFreq)]

/-- **Maze test, not implied**: `(row name, declaration exhibiting the gap)`.

* "T3 ShortOrbitCancel": the needed cancellation lives on segments of length `log q`, a
  density-zero position set; normality — all that Borel or Hypothesis A deliver — is blind to any
  density-zero set of digit changes (`isNormalSequence_congr_of_density_zero`).
* "kick-floor-only lemma": the Lagarias adversarial kicks are not ratios of integer polynomials;
  Hypothesis A (`BaileyCrandallHypA`) and its machine (`hypA_isNormal_of_kicked`) quantify only
  over `p, q ∈ ℤ[X]`, so they say nothing about that family. -/
def mazeTestNotImplied : List (String × Lean.Name) := [
  ("T3 ShortOrbitCancel", ``NormalNumbers.G4Entropy.isNormalSequence_congr_of_density_zero),
  ("kick-floor-only lemma", ``hypA_isNormal_of_kicked)]

end NormalNumbers.MasterConjectures
