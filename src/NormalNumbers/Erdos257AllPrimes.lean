/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Erdos257Base2
import NormalNumbers.G4Base2WeakSched

/-!
# Erdős #257 for every infinite set of primes: the case split (audit 2026-10-02)

Target: `erdos257_allPrimes`, for every infinite `S ⊆ primes`, `Σ_{p∈S} 1/(2ᵖ − 1)` is
irrational.  Direction doc: `docs/ERDOS257-ALLPRIMES-AUDIT-2026-10-02.md`.

Write `F_S(e) = Σ_{p ∈ S, p < 2^{2^e}} 1/p` (`sumInvPrimesIn S (2^2^e)`; Mertens gives
`F_S(e) ≤ e·log 2 + O(1)` for every `S`).  The split:

* **(ii) convergent**, `Σ_{p∈S} 1/p < ∞`: Erdős 1968 (cited, `Literature.Erdos1968CoprimeSummable`),
  since distinct primes are coprime.  `erdos257_convergent`, proved from the citation.
* **(i) regular**, `F_S(e) ≥ e^ε − C` for some `ε > 0` (`WeakMertensRate`): the base-2 route of
  `Erdos257Base2` with the schedule's demand/cap window re-checked.  The proved headline
  `erdos257_primeSubset` needs the stronger `MertensRate` (`F_S(e) ≥ c·e − C`);
  `weakMertensRate_of_mertensRate` shows (i) contains it.  `erdos257_weakRate`, proved.
* **(iii) the gap**, divergent but `F_S(e) = e^{o(1)}` along a subsequence (`GapSet`), e.g.
  `towerGapPrimes` (`F_S(e) ≈ log₂ e · log 2`).  `erdos257_gapSet`, `sorry` (30%).

The wiring `erdos257_allPrimes_of_cases` is proved.

**Splitting does not shrink the gap** (`weakMertensRate_mono`, `gapSet_subset_noWeakRate`): the
rate is monotone in `S`, so a gap set has no regular subset at all, and splitting
`S = S_reg ∪ S_sparse` adds nothing.  (Separately, the two constants would be
irrational + irrational, which proves nothing about their sum.)
-/

namespace NormalNumbers.Erdos257

open Filter

/-! ### The cited input for case (ii) -/

/-- **Erdős 1968, the cited input** (P. Erdős, *On the irrationality of certain series*, Math.
Student 36 (1968), 222-226, Theorem on p. 222; read from the scan
`users.renyi.hu/~p_erdos/1969-09.pdf` on 2026-10-02).  Erdős: if `(nᵢ, nⱼ) = 1` for `i ≠ j` and
`Σ 1/nᵢ < ∞`, then `Σ 1/(t^{nᵢ} − 1)` is irrational for every integer `t ≥ 2`.  Weaker here:
only `t = 2`, and exponents `≥ 2` (Erdős allows `nᵢ ≥ 1`).  Erdős adds that coprimality "is
superfluous" by a more complicated, unpublished argument; that coprimality-free form is not
cited here (a Lean proof is claimed by wcook04/plectis-erdos, formal-conjectures PR #6529, open). -/
def Literature.Erdos1968CoprimeSummable : Prop :=
  ∀ A : Set ℕ, A.Infinite → (∀ a ∈ A, 2 ≤ a) →
    (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → Nat.Coprime a a') →
    Summable (fun a : A => (1 : ℝ) / a.1) →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))

/-! ### Case (ii): convergent prime sets -/

/-- **Case (ii).**  A prime set with `Σ_{p∈S} 1/p < ∞` is covered by Erdős 1968. -/
theorem erdos257_convergent (h68 : Literature.Erdos1968CoprimeSummable) {S : Set ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hinf : S.Infinite) (hconv : Summable (fun p : S => (1 : ℝ) / p.1)) :
    Irrational (∑' n : S, (1 : ℝ) / (2 ^ n.1 - 1)) :=
  h68 S hinf (fun a ha => (hS a ha).two_le)
    (fun a ha b hb hne => (Nat.coprime_primes (hS a ha) (hS b hb)).2 hne) hconv

/-! ### Case (i): regular prime sets -/

/-- **The relaxed rate.**  `F_S(e) = Σ_{p∈S, p<2^{2^e}} 1/p ≥ e^ε − C`.  `MertensRate` is the
case `ε = 1` (up to the constant); `ε` may be arbitrarily small. -/
def WeakMertensRate (S : ℕ → Prop) [DecidablePred S] (ε : ℝ) : Prop :=
  0 < ε ∧ ∃ C : ℝ, ∀ e : ℕ, (e : ℝ) ^ ε - C ≤ G4.MertensAP.sumInvPrimesIn S (2 ^ 2 ^ e)

/-- A Mertens rate gives the relaxed rate with `ε = 1/2`, so case (i) contains the proved
headline `erdos257_primeSubset`. -/
theorem weakMertensRate_of_mertensRate {S : ℕ → Prop} [DecidablePred S] {c C : ℝ}
    (hm : G4.MertensAP.MertensRate S c C) : WeakMertensRate S (1 / 2) := by
  obtain ⟨hc, hm⟩ := hm
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set a : ℝ := c * Real.log 2 with ha_def
  have ha : 0 < a := mul_pos hc h2
  refine ⟨by norm_num, C + c / 2 + 1 / (4 * a), fun e => ?_⟩
  have hN : 2 ≤ (2 : ℕ) ^ 2 ^ e := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 2 ^ e := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  have h1 := hm _ hN
  have h3 := G4.MertensAP.log_log_tower_ge e
  set s : ℝ := (e : ℝ) ^ ((1 : ℝ) / 2) with hs_def
  have hs : s * s = e := by
    rw [hs_def, ← Real.rpow_add' (Nat.cast_nonneg _) (by norm_num)]
    norm_num
  have hkey : 0 ≤ (2 * a * s - 1) ^ 2 / (4 * a) := by positivity
  have hexp : (2 * a * s - 1) ^ 2 / (4 * a) = a * (s * s) - s + 1 / (4 * a) := by
    field_simp
    ring
  rw [hs] at hexp
  have h4 : c * ((e : ℝ) * Real.log 2) - c / 2
      ≤ c * Real.log (Real.log ((2 ^ 2 ^ e : ℕ) : ℝ)) := by
    have := mul_le_mul_of_nonneg_left h3 hc.le
    linarith
  have h5 : a * (e : ℝ) = c * ((e : ℝ) * Real.log 2) := by rw [ha_def]; ring
  linarith

/-- **Monotonicity: why splitting `S` buys nothing.**  The relaxed rate passes to supersets. -/
theorem weakMertensRate_mono {S S' : ℕ → Prop} [DecidablePred S] [DecidablePred S']
    (h : ∀ p, S p → S' p) {ε : ℝ} (hw : WeakMertensRate S ε) : WeakMertensRate S' ε := by
  obtain ⟨hε, C, hC⟩ := hw
  exact ⟨hε, C, fun e => (hC e).trans (G4.MertensAP.sumInvPrimesIn_le_of_subset h _)⟩

/-- **The stretched base-2 theorem** (case (i)).  Proved: the cap check is
`G4.SchedB.moment_cap_weak` (cutoff `n^⌈1/ε⌉` at `K = 2^{j+2}`), the witness
`G4.SchedB.exists_scheduleWitnessSC_two_of_supplyEff_weak`.

Sketch.  The Mertens rate is consumed once, by `MertensAP.exists_cutoff_subset`: the schedule
needs a cutoff exponent `e` with `F_S(e) ≥ M(K)`, demand `M(K) = exp(O(K log K))`, inside the
moment cap `10⁵·T K·e ≤ 2^{8K²}` (`G4SchedBE`, `G4Base2Sched`).  With `F_S(e) ≥ e^ε − C`, the
choice `e ≈ M(K)^{2/ε}` meets the demand, and `log e = O(K log K / ε) ≪ K²` fits the cap for
large `K`.  Even `F_S(e) ≥ exp(C₀ √(log e)·log log e)` would do.  Unchecked: that the base-2
covariance supply (`VeryLargeCovSupplyEff`, effective in `e`) and `four_mul_le_two_pow_NE`
tolerate `e` at the top of the window (b ≥ 3: 70%; base 2: 50%). -/
theorem isDisjunctive_subsetLambert_two_of_weakRate
    (htt : CastingOut.TTEquidistributedDyadic) {S : ℕ → Prop} [DecidablePred S] {ε : ℝ}
    (hw : WeakMertensRate S ε) : IsDisjunctive 2 (PrimeLambert.subsetLambert S 2) := by
  obtain ⟨hε, C, hC⟩ := hw
  refine G4.isDisjunctive_subsetLambert_of_witnessC S 2 le_rfl fun ℓ w hw homit => ?_
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · exfalso
    subst hℓ
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    have := homit 0
    simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
    exact this (orbit_mem_Ico 2 (PrimeLambert.subsetLambert S 2) 0)
  · exact G4.SchedB.exists_scheduleWitnessSC_two_of_supplyEff_weak S
      (veryLargeCovSupplyEff_of_TT htt) hε hC ℓ w hℓ

/-- For a prime set, `k·S` at `k = 1` is `S`. -/
theorem kMulPrimes_one_eq {S : Set ℕ} (hS : ∀ p ∈ S, p.Prime) :
    kMulPrimes (· ∈ S) 1 = S := by
  ext n
  simp only [kMulPrimes, Set.mem_ofPred_eq, one_mul]
  constructor
  · rintro ⟨p, -, hpS, rfl⟩
    exact hpS
  · intro hn
    exact ⟨n, hS n hn, hn, rfl⟩

/-- `Σ_{p∈S} 1/(2ᵖ − 1) = subsetLambert S 2` for a prime set `S`. -/
theorem tsum_eq_subsetLambert_two {S : Set ℕ} [DecidablePred (· ∈ S)] (hS : ∀ p ∈ S, p.Prime) :
    ∑' n : S, (1 : ℝ) / (2 ^ n.1 - 1) = PrimeLambert.subsetLambert (· ∈ S) 2 := by
  have h := subsetLambert_two_pow_eq (S := (· ∈ S)) (k := 1) le_rfl
  rw [pow_one, kMulPrimes_one_eq hS] at h
  exact h.symm

/-- **Case (i)** in the #257 shape. -/
theorem erdos257_weakRate (htt : CastingOut.TTEquidistributedDyadic) {S : Set ℕ}
    [DecidablePred (· ∈ S)] (hS : ∀ p ∈ S, p.Prime) {ε : ℝ} (hw : WeakMertensRate (· ∈ S) ε) :
    Irrational (∑' n : S, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  rw [tsum_eq_subsetLambert_two hS]
  exact (isDisjunctive_subsetLambert_two_of_weakRate htt hw).irrational

/-! ### Case (iii): the gap -/

/-- **The gap.**  A prime set with divergent reciprocal sum and no relaxed rate for any `ε > 0`:
`F_S(e) < e^ε − C` infinitely often, for every `ε, C`.  Neither Erdős 1968 nor the base-2 route
(even stretched) reaches these. -/
def GapSet (S : Set ℕ) [DecidablePred (· ∈ S)] : Prop :=
  (∀ p ∈ S, p.Prime) ∧ ¬ Summable (fun p : S => (1 : ℝ) / p.1) ∧
    ∀ ε : ℝ, ¬ WeakMertensRate (· ∈ S) ε

/-- **No regular part.**  Every subset of a gap set lacks the relaxed rate (from
`weakMertensRate_mono`), so a regular-plus-sparse split of a gap set has empty regular part.
Records the splitting route as closed. -/
theorem gapSet_subset_noWeakRate {S T : Set ℕ} [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hS : GapSet S) (hTS : T ⊆ S) (ε : ℝ) : ¬ WeakMertensRate (· ∈ T) ε :=
  fun hw => hS.2.2 ε (weakMertensRate_mono (fun _ hp => hTS hp) hw)

/-- **Explicit gap set**: primes `p` with `⌊log₂ ⌊log₂ p⌋⌋` a power of two.  The block
`2^{2^m} ≤ p < 2^{2^{m+1}}` carries `Σ 1/p = log 2 + O(2^{-m})` (Mertens), so
`F_S(e) = log 2 · log₂ e + O(1)`: divergent, and below `e^ε − C` for large `e`. -/
def towerGapPrimes : Set ℕ := {p | p.Prime ∧ ∃ j : ℕ, Nat.log 2 (Nat.log 2 p) = 2 ^ j}

open Classical in
/-- `towerGapPrimes` is a gap set.  `sorry`, 85% (Mertens with error term per block). -/
theorem towerGapPrimes_gapSet : GapSet towerGapPrimes := by
  sorry

/-- **Between the two rates**: primes with `⌊log₂ ⌊log₂ p⌋⌋` a perfect square.
`F_S(e) ≈ log 2 · √e`, so it has the relaxed rate but no Mertens rate: the stretch of case (i)
is strict. -/
def squareBlockPrimes : Set ℕ := {p | p.Prime ∧ IsSquare (Nat.log 2 (Nat.log 2 p))}

open Classical in
/-- `sorry`, 85%. -/
theorem squareBlockPrimes_weakRate : WeakMertensRate (· ∈ squareBlockPrimes) (1 / 3) := by
  sorry

open Classical in
/-- `sorry`, 85%. -/
theorem squareBlockPrimes_not_mertensRate (c C : ℝ) :
    ¬ G4.MertensAP.MertensRate (· ∈ squareBlockPrimes) c C := by
  sorry

/-- **Case (iii), the open step.**  `sorry`, 30%.

Sketch.  In the base-2 frame the cutoff exponent `e` enters in two ways: through the demand
`F_S(e) ≥ M(K)` and through the moment cap `10⁵·T K·e ≤ 2^{8K²}`, whose factor `e` comes from
the *upper* harmonic sum over all primes below `R` (`term_b`, `term_c` in `G4SchedBE`: the bound
`Σ_{p<R} 1/p ≤ 3e + 5`).  For `ω_S` that sum may be restricted to `S`-primes, `≤ F_S(e) + O(1)`.
If every `e`-dependence of the witness can be routed through `F_S(e)` (the decoupling), demand and
cap are both conditions on `F_S(e)` alone, and since `F_S(e + 1) − F_S(e) ≤ log 2 + o(1)`, any
divergent `S` hits the window `[M(K), 2^{8K²}/(10⁵ T K)]`.  The unverified parts are the size facts
that are not monotone in the cutoff (`four_mul_le_two_pow_NE`: `e ≤ 2^{8K²}` against
`N K = 100 K²`), the effective covariance supply at huge `e`, and the variance step when the
`S`-mass sits on primes dividing the grid modulus.  No Erdős-1968-style argument is known for
divergent sets: his proof needs the tail `Σ 1/nᵢ` beyond the chosen moduli to be `< 1`. -/
theorem isDisjunctive_subsetLambert_two_of_gapSet (htt : CastingOut.TTEquidistributedDyadic)
    {S : Set ℕ} [DecidablePred (· ∈ S)] (hS : GapSet S) :
    IsDisjunctive 2 (PrimeLambert.subsetLambert (· ∈ S) 2) := by
  sorry

/-- **Case (iii)** in the #257 shape. -/
theorem erdos257_gapSet (htt : CastingOut.TTEquidistributedDyadic) {S : Set ℕ}
    [DecidablePred (· ∈ S)] (hS : GapSet S) :
    Irrational (∑' n : S, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  rw [tsum_eq_subsetLambert_two hS.1]
  exact (isDisjunctive_subsetLambert_two_of_gapSet htt hS).irrational

/-! ### Wiring -/

/-- **The case split is exhaustive** (proved): convergent, regular, or gap. -/
theorem erdos257_allPrimes_of_cases (h68 : Literature.Erdos1968CoprimeSummable)
    (htt : CastingOut.TTEquidistributedDyadic) :
    ∀ S : Set ℕ, (∀ p ∈ S, p.Prime) → S.Infinite →
      Irrational (∑' n : S, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  classical
  intro S hS hinf
  by_cases hconv : Summable (fun p : S => (1 : ℝ) / p.1)
  · exact erdos257_convergent h68 hS hinf hconv
  by_cases hw : ∃ ε : ℝ, WeakMertensRate (· ∈ S) ε
  · obtain ⟨ε, hε⟩ := hw
    exact erdos257_weakRate htt hS hε
  · exact erdos257_gapSet htt ⟨hS, hconv, not_exists.mp hw⟩

/-- **Erdős #257 for every infinite set of primes.**  `sorry`, 30%.

Sketch: `erdos257_allPrimes_of_cases` with the two cited inputs (Erdős 1968; Tao–Teräväinen
Thm 3.1(i)) and the two open lemmas `isDisjunctive_subsetLambert_two_of_weakRate` (50%) and
`isDisjunctive_subsetLambert_two_of_gapSet` (30%, the hardest step: decoupling the cutoff exponent
from `K`).  Unconditional form: also needs both citations discharged. -/
theorem erdos257_allPrimes : ∀ S : Set ℕ, (∀ p ∈ S, p.Prime) → S.Infinite →
    Irrational (∑' n : S, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  sorry

end NormalNumbers.Erdos257
