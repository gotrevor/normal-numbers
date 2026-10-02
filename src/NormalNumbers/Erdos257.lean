/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SubsetAssembly
import NormalNumbers.DisjunctiveCorollaries
import NormalNumbers.PrimeModelFamilyGraded

/-!
# Erdős #257 for `A = k·S` (campaign launched 2026-10-02)

Erdős #257 (erdosproblems.com/257; formal-conjectures `Erdos257.erdos_257`, open): for infinite
`A ⊆ ℕ`, is `Σ_{n∈A} 1/(2ⁿ − 1)` irrational?  Source of this lane:
`docs/OPEN-PROBLEMS-SWEEP-2026-10-02.md`, rank 1 (Tao–Teräväinen arXiv:2512.01739 settle primes
and call other prime-like sets "likely"; no checked source lists a dilated prime set).

**The identity.**  `ω_S(n) = #{p ∣ n prime : S p}`, so
`subsetLambert S b = Σ_n ω_S(n)/bⁿ = Σ_{p∈S} Σ_{j≥1} b^{−pj} = Σ_{p∈S} 1/(bᵖ − 1)`.  At `b = 2ᵏ`
this is `Σ_{n∈k·S} 1/(2ⁿ − 1)`, and `n ↦ k·n` is injective.  So:
* `isDisjunctive_subsetLambert` (any `S` with a Mertens rate, base `≥ 3`) gives disjunctivity,
  hence irrationality, for every `k ≥ 2`;
* C′ (`isNormal_subsetLambert_of_sqrtFreshMassZero`, base 4) gives normality in base 2 at `k = 2`
  (base change `4 = 2²`).

## Frozen statements (do not edit; prove them)

* `kMulPrimes_infinite`, `erdos257_kMul`, `erdos257_kMul_primes`, `erdos257_kMul_residueClass`,
  `erdos257_twoMul_normal`.

## Guard rule

**Content locator.**  `k = 1`, `S` = all primes is Tao–Teräväinen's theorem, which base 2 puts out
of reach of the fixed-base machinery (`3 ≤ b` fails); the dilation `k ≥ 2` is exactly what moves
the constant into base `2ᵏ ≥ 4`.  **Degenerate cases.**  A finite `S` gives a finite `A`, excluded
from #257 and by the Mertens rate (which forces divergence); `k = 0` collapses `A` to `{0}`; `k = 1`
is the open base-2 case, not claimed.
-/

namespace NormalNumbers.Erdos257

open Filter Topology

/-- `k·S = {k·p : p prime, S p}`. -/
def kMulPrimes (S : ℕ → Prop) (k : ℕ) : Set ℕ := {n | ∃ p, p.Prime ∧ S p ∧ n = k * p}

variable {S : ℕ → Prop} [DecidablePred S]

/-! ### The Lambert identity -/

/-- **The Lambert identity.**  `c_S(2ᵏ) = Σ_{n∈k·S} 1/(2ⁿ − 1)` for `k ≥ 1`. -/
theorem subsetLambert_two_pow_eq {k : ℕ} (hk : 1 ≤ k) :
    PrimeLambert.subsetLambert S (2 ^ k) = ∑' n : kMulPrimes S k, (1 : ℝ) / (2 ^ n.1 - 1) := by
  classical
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [PrimeLambert.subsetLambert_eq_tsum_inv h2k, tsum_subtype (kMulPrimes S k)
    (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1))]
  have hinj : Function.Injective (fun p : ℕ => k * p) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (by omega) h
  have hsupp : Function.support ((kMulPrimes S k).indicator fun n : ℕ => (1 : ℝ) / (2 ^ n - 1))
      ⊆ Set.range (fun p : ℕ => k * p) := by
    intro n hn
    rw [Function.mem_support] at hn
    by_contra hr
    apply hn
    rw [Set.indicator_of_notMem]
    rintro ⟨q, -, -, rfl⟩
    exact hr ⟨q, rfl⟩
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun p => ?_
  simp only [Set.indicator, kMulPrimes, Set.mem_setOf_eq]
  have hiff : (∃ q, q.Prime ∧ S q ∧ k * p = k * q) ↔ (p.Prime ∧ S p) := by
    constructor
    · rintro ⟨q, hq, hSq, he⟩
      rw [hinj he]; exact ⟨hq, hSq⟩
    · rintro ⟨hp, hSp⟩; exact ⟨p, hp, hSp, rfl⟩
  by_cases h : p.Prime ∧ S p
  · rw [if_pos h, if_pos (hiff.2 h)]
    push_cast
    rw [pow_mul]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

/-! ### Base change `4 → 2` -/

lemma visitCount_succ (u : ℕ → ℝ) (a c : ℝ) (n : ℕ) :
    visitCount u a c (n + 1) = visitCount u a c n + if u n ∈ Set.Ico a c then 1 else 0 := by
  unfold visitCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

lemma orbit_two_even (x : ℝ) (m : ℕ) : orbit 2 x (2 * m) = orbit 4 x m := by
  unfold orbit; rw [pow_mul]; norm_num

lemma orbit_two_odd (x : ℝ) (m : ℕ) : orbit 2 x (2 * m + 1) = Int.fract (2 * orbit 4 x m) := by
  unfold orbit
  have : 2 * Int.fract (x * (4 : ℕ) ^ m) = 2 * (x * (4 : ℕ) ^ m) - ((2 * ⌊x * (4 : ℕ) ^ m⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [this, Int.fract_sub_intCast, pow_succ, pow_mul]; norm_num; ring_nf

lemma ind_doubling {a c u : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (if Int.fract (2 * u) ∈ Set.Ico a c then 1 else 0 : ℕ)
      = (if u ∈ Set.Ico (a / 2) (c / 2) then 1 else 0)
        + (if u ∈ Set.Ico ((1 + a) / 2) ((1 + c) / 2) then 1 else 0) := by
  simp only [Set.mem_Ico]
  rcases lt_or_ge u (1 / 2) with hu | hu
  · have hf : Int.fract (2 * u) = 2 * u := Int.fract_eq_self.2 ⟨by linarith, by linarith⟩
    rw [hf, if_neg (show ¬((1 + a) / 2 ≤ u ∧ u < (1 + c) / 2) by intro h; linarith [h.1])]
    by_cases h : a ≤ 2 * u ∧ 2 * u < c
    · rw [if_pos h, if_pos ⟨by linarith [h.1], by linarith [h.2]⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩)]
  · have hf : Int.fract (2 * u) = 2 * u - 1 := by
      rw [show Int.fract (2 * u) = Int.fract ((2 * u - 1) + ((1 : ℤ) : ℝ)) by push_cast; ring_nf,
        Int.fract_add_intCast,
        Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
    rw [hf, if_neg (show ¬(a / 2 ≤ u ∧ u < c / 2) by intro h; linarith [h.2])]
    by_cases h : a ≤ 2 * u - 1 ∧ 2 * u - 1 < c
    · rw [if_pos h, if_pos ⟨by linarith [h.1], by linarith [h.2]⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩)]

lemma visitCount_two_even (x : ℝ) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (n : ℕ) :
    visitCount (orbit 2 x) a c (2 * n) = visitCount (orbit 4 x) a c n
      + visitCount (orbit 4 x) (a / 2) (c / 2) n
      + visitCount (orbit 4 x) ((1 + a) / 2) ((1 + c) / 2) n := by
  induction n with
  | zero => simp [visitCount]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, visitCount_succ, visitCount_succ, ih,
      visitCount_succ, visitCount_succ, visitCount_succ, orbit_two_even, orbit_two_odd,
      ind_doubling ha hac hc (u := orbit 4 x n) (by unfold orbit; exact Int.fract_nonneg _)
        (by unfold orbit; exact Int.fract_lt_one _)]
    ring

/-- **Base change.**  A number normal in base `4` is normal in base `2`. -/
theorem isNormal_two_of_four {x : ℝ} (h : IsNormal 4 x) : IsNormal 2 x := by
  rw [isNormal_iff_equidistributed_orbit 4 (by norm_num)] at h
  rw [isNormal_iff_equidistributed_orbit 2 le_rfl]
  intro a c ha hac hc
  have h1 := h a c ha hac hc
  have h2 := h (a / 2) (c / 2) (by linarith) (by linarith) (by linarith)
  have h3 := h ((1 + a) / 2) ((1 + c) / 2) (by linarith) (by linarith) (by linarith)
  set V := visitCount (orbit 2 x) a c with hV
  -- even subsequence
  have heven : Tendsto (fun m : ℕ => (V (2 * m) : ℝ) / m) atTop (𝓝 (2 * (c - a))) := by
    have := (h1.add h2).add h3
    convert this using 1
    · funext m; rw [hV, visitCount_two_even x ha hac hc]; push_cast; ring
    · ring
  -- general `N`, squeezed between `V (2⌊N/2⌋)` and `V (2⌊N/2⌋) + 1`
  have hmono : ∀ N, V (2 * (N / 2)) ≤ V N ∧ V N ≤ V (2 * (N / 2)) + 1 := by
    intro N
    rcases Nat.even_or_odd' N with ⟨m, rfl | rfl⟩
    · rw [show 2 * m / 2 = m by omega]; omega
    · rw [show (2 * m + 1) / 2 = m by omega, hV, visitCount_succ]
      split_ifs <;> omega
  have hhalf : Tendsto (fun N : ℕ => N / 2) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun N hN => by omega⟩
  have hE := heven.comp hhalf
  -- ratio `(N/2)/N → 1/2`
  have hratio : Tendsto (fun N : ℕ => ((N / 2 : ℕ) : ℝ) / N) atTop (𝓝 (1 / 2)) := by
    have hlo : Tendsto (fun N : ℕ => (1 / 2 : ℝ) - 1 / (N : ℝ)) atTop (𝓝 (1 / 2)) := by
      simpa using (tendsto_one_div_atTop_nhds_zero_nat).const_sub (1 / 2 : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hNR]
      have : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
        have := Nat.lt_mul_div_succ N (show 0 < 2 by norm_num); exact_mod_cast (by omega : N ≤ 2 * (N / 2) + 1)
      nlinarith
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_iff₀ hNR]
      have : 2 * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N 2
      linarith
  have hlow : Tendsto (fun N : ℕ => (V (2 * (N / 2)) : ℝ) / N) atTop (𝓝 (c - a)) := by
    have := hE.mul hratio
    rw [show 2 * (c - a) * (1 / 2) = c - a by ring] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have : (0 : ℝ) < ((N / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N / 2)
    simp only [Function.comp]
    field_simp
  have hup : Tendsto (fun N : ℕ => (V (2 * (N / 2)) : ℝ) / N + 1 / N) atTop (𝓝 (c - a)) := by
    simpa using hlow.add tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun N => ?_) (fun N => ?_)
  · exact div_le_div_of_nonneg_right (Nat.cast_le.2 (hmono N).1) (Nat.cast_nonneg N)
  · rw [← add_div]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
    have := Nat.cast_le (α := ℝ) |>.2 (hmono N).2
    push_cast at this; linarith

/-- A set with a Mertens rate has infinitely many primes, so `k·S` is infinite for `k ≥ 1`. -/
theorem kMulPrimes_infinite {c C : ℝ} (hm : G4.MertensAP.MertensRate S c C) {k : ℕ}
    (hk : 1 ≤ k) : (kMulPrimes S k).Infinite := by
  classical
  intro hfin
  -- the primes of `S` would be finite
  have hT : {p : ℕ | p.Prime ∧ S p}.Finite := by
    refine (hfin.preimage (f := fun p => k * p) ?_).subset ?_
    · exact fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by omega) h
    · rintro p ⟨hp, hSp⟩; exact ⟨p, hp, hSp, rfl⟩
  set T := hT.toFinset
  set B : ℝ := ∑ p ∈ T, (p : ℝ)⁻¹
  have hbound : ∀ N : ℕ, G4.MertensAP.sumInvPrimesIn S N ≤ B := by
    intro N
    unfold G4.MertensAP.sumInvPrimesIn
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp only [T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨Nat.prime_of_mem_primesBelow hp.1, hp.2⟩
  obtain ⟨hc, hm⟩ := hm
  have hlim : Tendsto (fun N : ℕ => c * Real.log (Real.log N)) atTop atTop :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).const_mul_atTop hc
  obtain ⟨N, hN, hN2⟩ := ((hlim.eventually_gt_atTop (B + C)).and
    (eventually_ge_atTop 2)).exists
  linarith [hm N hN2, hbound N]

/-- **Erdős #257 for `A = k·S`, `k ≥ 2`.**  Any prime set with a Mertens rate. -/
theorem erdos257_kMul {c C : ℝ} (hm : G4.MertensAP.MertensRate S c C) {k : ℕ} (hk : 2 ≤ k) :
    Irrational (∑' n : kMulPrimes S k, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  rw [← subsetLambert_two_pow_eq (by omega)]
  refine IsDisjunctive.irrational (G4.isDisjunctive_subsetLambert (S := S) hm ?_)
  calc 3 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- All primes: `Σ_p 1/(2^{kp} − 1)` is irrational for every `k ≥ 2`. -/
theorem erdos257_kMul_primes {k : ℕ} (hk : 2 ≤ k) :
    Irrational (∑' n : kMulPrimes (fun _ => True) k, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  exact erdos257_kMul G4.mertensRate_univ hk

/-- Primes in a residue class: `Σ_{p ≡ a (q)} 1/(2^{kp} − 1)` is irrational for `k ≥ 2`. -/
theorem erdos257_kMul_residueClass {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {k : ℕ}
    (hk : 2 ≤ k) :
    Irrational (∑' n : kMulPrimes (fun p => (p : ZMod q) = a) k, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  obtain ⟨c, C, hm⟩ := G4.MertensAP.mertensRate_residueClass ha
  exact erdos257_kMul hm hk

/-- **Normality at `k = 2`.**  For a C′ set (vanishing square-root fresh mass, divergent
reciprocal sum), `Σ_{n∈2·P} 1/(2ⁿ − 1)` is normal in base 2. -/
theorem erdos257_twoMul_normal (hS : PrimeModel.SqrtFresh.SqrtFreshMassZero S)
    (hP : G4Sparse.DivergentRecip S) :
    IsNormal 2 (∑' n : kMulPrimes S 2, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  rw [← subsetLambert_two_pow_eq (by norm_num)]
  apply isNormal_two_of_four
  exact PrimeModel.FamilyGraded.isNormal_subsetLambert_of_sqrtFreshMassZero S hS hP

end NormalNumbers.Erdos257
