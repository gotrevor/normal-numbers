import NormalNumbers.TwoPointGramChain

/-!
# What the remaining leaf actually says, arithmetically

`conjC1_of_delange_pairGramSmall` (lap 11) reduces `ConjC1` to `TwoPointPairGramSmall b t`, a
statement about `kataiPairGram` — a Gram sum of the *abstract* sequence `a = ζ^{ω_tail}`.  This
file unfolds it into the two-point arithmetic form, so the leaf can be read against the
literature (Tao 2016, MRT 2015) and against the ratified `twoPointWeightedAvg_all`:

    kataiPairGram a w N
      = Σ_{p ≠ q ≤ w} ‖ Σ_{m ≤ min(⌊N/p⌋, ⌊N/q⌋)} ζ^{ω(pm+1)} conj ζ^{ω(qm+1)} · W_{p,q}(m) ‖ .

Two differences from the ratified leaf, both in the honest direction: the inner sum is
**unnormalised** and runs over the truncated range `m ≤ min(N/p, N/q)` (what the Cauchy–Schwarz
genuinely produces), and the whole pair sum is measured against `N·L(w)²`, not `π(w)²`.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The truncated two-point correlation sum along the forms `pm+1`, `qm+1`. -/
noncomputable def twoPointTruncSum (b p q : ℕ) (t : ℝ) (N : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc 0 (min (N / p) (N / q)),
    twoPointFactor b p q t m * peelWeight b p q t m

/-- The pair sum of truncated two-point correlations. -/
noncomputable def twoPointGramSum (b : ℕ) (t : ℝ) (w N : ℕ) : ℝ :=
  ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
    if p = q then 0 else ‖twoPointTruncSum b p q t N‖

lemma csGram_kataiTrunc (a : ℕ → ℂ) (N p q : ℕ) :
    csGram (kataiTrunc a N) (N + 1) p q
      = ∑ m ∈ Finset.Ioc 0 (min (N / p) (N / q)), a (p * m) * (starRingEnd ℂ) (a (q * m)) := by
  classical
  have hsub : Finset.Ioc 0 (min (N / p) (N / q)) ⊆ Finset.range (N + 1) := by
    intro m hm
    simp only [Finset.mem_Ioc, le_min_iff] at hm
    have := Nat.div_le_self N p
    simp only [Finset.mem_range]
    omega
  rw [csGram, ← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    simp only [Finset.mem_Ioc, le_min_iff] at hm
    have hp : m ∈ Finset.Ioc 0 (N / p) := Finset.mem_Ioc.mpr ⟨hm.1, hm.2.1⟩
    have hq : m ∈ Finset.Ioc 0 (N / q) := Finset.mem_Ioc.mpr ⟨hm.1, hm.2.2⟩
    simp [kataiTrunc, hp, hq]
  · intro m _ hnot
    simp only [Finset.mem_Ioc, le_min_iff, not_and, not_le] at hnot
    by_cases h0 : 0 < m
    · have := hnot h0
      rcases not_and_or.mp (by omega : ¬ (m ≤ N / p ∧ m ≤ N / q)) with h | h
      · simp [kataiTrunc, Finset.mem_Ioc, h]
      · simp [kataiTrunc, Finset.mem_Ioc, h]
    · simp [kataiTrunc, Finset.mem_Ioc, h0]

/-- **THE LEAF, UNFOLDED.**  The abstract Gram sum of `ζ^{ω_tail}` is the pair sum of truncated
weighted two-point correlations. -/
theorem kataiPairGram_eq (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (w N : ℕ) :
    kataiPairGram (fun n => phase (t * omegaTail b n)) w N = twoPointGramSum b t w N := by
  classical
  have heq : ∀ p q m : ℕ,
      phase (t * omegaTail b (p * m)) * (starRingEnd ℂ) (phase (t * omegaTail b (q * m)))
        = twoPointFactor b p q t m * peelWeight b p q t m := by
    intro p q m
    rw [conj_phase, ← phase_add, show t * omegaTail b (p * m) + -(t * omegaTail b (q * m))
      = t * (omegaTail b (p * m) - omegaTail b (q * m)) by ring]
    have h := pairPhase_eq_twoPoint b hb t p q m
    rw [pairTail] at h
    rw [h, twoPointFactor]
  unfold kataiPairGram twoPointGramSum
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hpq : p = q
  · simp [hpq]
  · rw [if_neg hpq, if_neg hpq, csGram_kataiTrunc, twoPointTruncSum]
    exact congrArg _ (Finset.sum_congr rfl fun m _ => heq p q m)

/-- The open leaf, stated purely arithmetically: the truncated weighted two-point correlations
must have pair mass `o(N · L(w(N))²)` along a slowly growing cutoff. -/
theorem twoPointPairGramSmall_iff (b : ℕ) (hb : 2 ≤ b) (t : ℝ) :
    TwoPointPairGramSmall b t ↔
      ∃ w : ℕ → ℕ, Tendsto w atTop atTop ∧
        (∀ᶠ N : ℕ in atTop, 2 ≤ w N ∧ ((w N : ℝ)) ^ 2 ≤ (N : ℝ)) ∧
        Tendsto (fun N => twoPointGramSum b t (w N) N / ((N : ℝ) * (kataiPrimeRecip (w N)) ^ 2))
          atTop (𝓝 0) := by
  unfold TwoPointPairGramSmall PairGramSmallGrowing
  constructor <;> rintro ⟨w, h1, h2, h3⟩ <;> exact ⟨w, h1, h2, h3.congr fun N => by
    rw [kataiPairGram_eq b hb]⟩

/-- **C1, FULLY UNFOLDED.**  Delange plus the arithmetic two-point leaf. -/
theorem conjC1_of_delange_twoPointGram
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∃ w : ℕ → ℕ, Tendsto w atTop atTop ∧
        (∀ᶠ N : ℕ in atTop, 2 ≤ w N ∧ ((w N : ℝ)) ^ 2 ≤ (N : ℝ)) ∧
        Tendsto (fun N => twoPointGramSum b (((m : ℤ) : ℝ) / b) (w N) N
            / ((N : ℝ) * (kataiPrimeRecip (w N)) ^ 2)) atTop (𝓝 0)) :
    ConjC1 :=
  conjC1_of_delange_pairGramSmall hD fun b hb m hm hdvd =>
    (twoPointPairGramSmall_iff b (by omega) (((m : ℤ) : ℝ) / b)).mpr (hP b hb m hm hdvd)

end NormalNumbers.CastingOut
