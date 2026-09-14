import Mathlib

/-!
# Prime Lambert constant: definitions, tails, and the exact ω-transport identity

The constant is

  `primeLambert = ∑_{n ≥ 1} ω(n) / 2^n`,

where `ω = ArithmeticFunction.cardDistinctFactors` counts distinct prime factors.
Equivalently `∑_p 1/(2^p - 1)` (that Lambert-series form is not needed here).

This module holds the *exact* arithmetic that the compressed-cancellation
irrationality argument (see `docs/prime-lambert-irrationality.md`) rests on:

* `tailT k = ∑_{j ≥ 1} ω(k + j) 2^{-j}` equals `2^k · primeLambert` minus an integer
  (`tailT_eq`), so if `q · primeLambert ∈ ℤ` then `q · tailT k ∈ ℤ` (`rational_tail_int`).
* The exact composite-transport identity
  `ω(d·m) = ω(m) + ω(d) − #{p ∣ d : p ∣ m}` (`omega_mul_eq`), and its binary-tail form
  `∑_{j≥1} 2^{-j} ω(d(k+j)) = tailT k + ω d − transportCorr d k` (`dilatedTail_eq`).
* The correction `transportCorr d k` is *exactly periodic*: it depends only on
  `k mod p` for the primes `p ∣ d` (`transportCorr_congr`).

Nothing here is estimated; every statement is an identity.
-/

open Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-- `ω n` as a real number (number of distinct prime factors; mathlib's arithmetic function). -/
noncomputable def omegaR (n : ℕ) : ℝ := (ArithmeticFunction.cardDistinctFactors n : ℝ)

lemma cardDistinctFactors_eq_card_primeFactors (n : ℕ) :
    ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

lemma omegaR_eq (n : ℕ) : omegaR n = (n.primeFactors.card : ℝ) := by
  rw [omegaR, cardDistinctFactors_eq_card_primeFactors]

lemma omegaR_nonneg (n : ℕ) : 0 ≤ omegaR n := by rw [omegaR_eq]; positivity

lemma primeFactors_subset_divisors (n : ℕ) : n.primeFactors ⊆ n.divisors := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  exact Nat.mem_divisors.mpr ⟨hp.2.1, hp.2.2⟩

lemma card_primeFactors_le_self (n : ℕ) : n.primeFactors.card ≤ n :=
  (Finset.card_le_card (primeFactors_subset_divisors n)).trans (Nat.card_divisors_le_self n)

lemma omegaR_le (n : ℕ) : omegaR n ≤ n := by
  rw [omegaR_eq]; exact_mod_cast card_primeFactors_le_self n

/-- The prime Lambert constant `∑_{n≥1} ω(n)/2^n` (the `n = 0` term vanishes since `ω 0 = 0`). -/
noncomputable def primeLambert : ℝ := ∑' n : ℕ, omegaR n / 2 ^ n

lemma summable_omegaR_div_two_pow : Summable (fun n : ℕ => omegaR n / 2 ^ n) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1/2 : ℝ)) (by
    rw [Real.norm_eq_abs]; norm_num)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h
  · have := omegaR_nonneg n; positivity
  · rw [div_eq_mul_inv, ← inv_pow, pow_one, one_div]
    gcongr
    exact omegaR_le n

/-- `T(k) = ∑_{j ≥ 1} ω(k + j) 2^{-j}`, indexed here by `j = i + 1`. -/
noncomputable def tailT (k : ℕ) : ℝ := ∑' i : ℕ, omegaR (k + i + 1) / 2 ^ (i + 1)

/-- The integer `∑_{m ≤ k} 2^{k-m} ω(m)` subtracted from `2^k G` to obtain `T(k)`. -/
def tailInt (k : ℕ) : ℕ := ∑ m ∈ Finset.range (k + 1), 2 ^ (k - m) * ArithmeticFunction.cardDistinctFactors m

/-- `T(k) = 2^k · G − (integer)`: the tail is an integer translate of a dilate of `G`. -/
theorem tailT_eq (k : ℕ) : tailT k = 2 ^ k * primeLambert - tailInt k := by
  have hs : Summable (fun n : ℕ => (2 : ℝ) ^ k * (omegaR n / 2 ^ n)) :=
    summable_omegaR_div_two_pow.mul_left _
  have h := hs.sum_add_tsum_nat_add (k + 1)
  have hfin : ∑ i ∈ Finset.range (k + 1), (2 : ℝ) ^ k * (omegaR i / 2 ^ i) = tailInt k := by
    rw [tailInt]; push_cast
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hm' : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [omegaR, pow_sub₀ (2:ℝ) (by norm_num) hm']
    field_simp
  have htail : ∑' i : ℕ, (2 : ℝ) ^ k * (omegaR (i + (k + 1)) / 2 ^ (i + (k + 1))) = tailT k := by
    rw [tailT]
    refine tsum_congr (fun i => ?_)
    rw [show i + (k + 1) = k + i + 1 by ring, pow_add, pow_add]
    field_simp
    ring
  rw [primeLambert, ← tsum_mul_left, ← h, hfin, htail]
  ring

/-- If `q · G` is an integer then so is every `q · T(k)`. -/
theorem rational_tail_int {q : ℤ} {z : ℤ} (hq : (q : ℝ) * primeLambert = z) (k : ℕ) :
    ∃ w : ℤ, (q : ℝ) * tailT k = w := by
  refine ⟨2 ^ k * z - q * tailInt k, ?_⟩
  rw [tailT_eq]; push_cast
  linear_combination (2:ℝ) ^ k * hq

/-! ### The exact ω-transport identity -/

/-- `#{p ∣ d prime : p ∣ m}`, the overlap of prime supports. -/
def overlap (d m : ℕ) : ℕ := (d.primeFactors.filter (fun p => p ∣ m)).card

lemma primeFactors_inter (d m : ℕ) (hm : m ≠ 0) :
    d.primeFactors ∩ m.primeFactors = d.primeFactors.filter (fun p => p ∣ m) := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.2.1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h1.1, h2, hm⟩

/-- `ω(d·m) + #{p ∣ d : p ∣ m} = ω(m) + ω(d)` for `d, m ≠ 0`. -/
theorem omega_mul_eq (d m : ℕ) (hd : d ≠ 0) (hm : m ≠ 0) :
    ArithmeticFunction.cardDistinctFactors (d * m) + overlap d m =
      ArithmeticFunction.cardDistinctFactors m + ArithmeticFunction.cardDistinctFactors d := by
  simp only [cardDistinctFactors_eq_card_primeFactors, overlap]
  rw [Nat.primeFactors_mul hd hm, ← primeFactors_inter d m hm, Finset.card_union_add_card_inter,
    add_comm]

lemma omegaR_mul_eq (d m : ℕ) (hd : d ≠ 0) (hm : m ≠ 0) :
    omegaR (d * m) = omegaR m + omegaR d - overlap d m := by
  have := omega_mul_eq d m hd hm
  simp only [omegaR]
  have h' : ((ArithmeticFunction.cardDistinctFactors (d * m) + overlap d m : ℕ) : ℝ) =
      ((ArithmeticFunction.cardDistinctFactors m + ArithmeticFunction.cardDistinctFactors d : ℕ) : ℝ) := by
    rw [this]
  push_cast at h'
  linarith

/-- `E_d(k) = ∑_{p ∣ d} ∑_{j ≥ 1} 2^{-j} 1[p ∣ k + j]`, written as `∑_{j≥1} 2^{-j} · overlap d (k+j)`. -/
noncomputable def transportCorr (d k : ℕ) : ℝ := ∑' i : ℕ, (overlap d (k + i + 1) : ℝ) / 2 ^ (i + 1)

lemma overlap_le (d m : ℕ) : overlap d m ≤ d.primeFactors.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma summable_geom_shift : Summable (fun i : ℕ => (1 : ℝ) / 2 ^ (i + 1)) := by
  have := (summable_geometric_two).mul_left (1/2 : ℝ)
  refine this.congr (fun i => ?_)
  rw [pow_succ, one_div_pow]; field_simp

lemma tsum_geom_shift : ∑' i : ℕ, (1 : ℝ) / 2 ^ (i + 1) = 1 := by
  have h : ∑' i : ℕ, (1 : ℝ) / 2 ^ (i + 1) = (1/2 : ℝ) * ∑' i : ℕ, ((1:ℝ)/2) ^ i := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun i => ?_)
    rw [pow_succ, one_div_pow]; field_simp
  rw [h, tsum_geometric_two]; norm_num

lemma summable_transportCorr (d k : ℕ) :
    Summable (fun i : ℕ => (overlap d (k + i + 1) : ℝ) / 2 ^ (i + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (summable_geom_shift.mul_left (d.primeFactors.card : ℝ))
  rw [← mul_div_assoc, mul_one]
  gcongr
  exact_mod_cast overlap_le d _

lemma summable_tailT (k : ℕ) : Summable (fun i : ℕ => omegaR (k + i + 1) / 2 ^ (i + 1)) := by
  have := ((summable_nat_add_iff (k + 1)).mpr summable_omegaR_div_two_pow).mul_left ((2:ℝ) ^ k)
  refine this.congr (fun i => ?_)
  rw [show i + (k + 1) = k + i + 1 by ring, pow_add, pow_add]
  field_simp
  ring

/-- The dilated tail `∑_{j ≥ 1} 2^{-j} ω(d(k + j))`. -/
noncomputable def dilatedTail (d k : ℕ) : ℝ := ∑' i : ℕ, omegaR (d * (k + i + 1)) / 2 ^ (i + 1)

lemma summable_dilatedTail (d k : ℕ) (hd : d ≠ 0) :
    Summable (fun i : ℕ => omegaR (d * (k + i + 1)) / 2 ^ (i + 1)) := by
  have h : ∀ i : ℕ, omegaR (d * (k + i + 1)) / 2 ^ (i + 1) =
      omegaR (k + i + 1) / 2 ^ (i + 1) + omegaR d * (1 / 2 ^ (i + 1))
        - (overlap d (k + i + 1) : ℝ) / 2 ^ (i + 1) := by
    intro i
    rw [omegaR_mul_eq d _ hd (by omega)]
    ring
  refine Summable.congr ?_ (fun i => (h i).symm)
  exact ((summable_tailT k).add (summable_geom_shift.mul_left _)).sub (summable_transportCorr d k)

/-- **Exact transport**: `∑_{j≥1} 2^{-j} ω(d(k+j)) = T(k) + ω(d) − E_d(k)` for `d ≥ 1`. -/
theorem dilatedTail_eq (d k : ℕ) (hd : d ≠ 0) :
    dilatedTail d k = tailT k + omegaR d - transportCorr d k := by
  have h : ∀ i : ℕ, omegaR (d * (k + i + 1)) / 2 ^ (i + 1) =
      omegaR (k + i + 1) / 2 ^ (i + 1) + omegaR d * (1 / 2 ^ (i + 1))
        - (overlap d (k + i + 1) : ℝ) / 2 ^ (i + 1) := by
    intro i
    rw [omegaR_mul_eq d _ hd (by omega)]
    ring
  rw [dilatedTail, tsum_congr h, Summable.tsum_sub, Summable.tsum_add, tsum_mul_left,
    tsum_geom_shift, mul_one, tailT, transportCorr]
  · exact summable_tailT k
  · exact summable_geom_shift.mul_left _
  · exact (summable_tailT k).add (summable_geom_shift.mul_left _)
  · exact summable_transportCorr d k

/-- The overlap count depends only on `m mod p` for `p ∣ d`. -/
lemma overlap_congr (d m m' : ℕ) (h : ∀ p ∈ d.primeFactors, m ≡ m' [MOD p]) :
    overlap d m = overlap d m' := by
  unfold overlap
  congr 1
  refine Finset.filter_congr (fun p hp => ?_)
  have := h p hp
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, this]

/-- **Exact periodicity**: `E_d(k) = E_d(k')` whenever `k ≡ k'` modulo every prime dividing `d`
(i.e. modulo `rad d`). -/
theorem transportCorr_congr (d k k' : ℕ) (h : ∀ p ∈ d.primeFactors, k ≡ k' [MOD p]) :
    transportCorr d k = transportCorr d k' := by
  unfold transportCorr
  refine tsum_congr (fun i => ?_)
  rw [overlap_congr d (k + i + 1) (k' + i + 1) (fun p hp => ((h p hp).add_right i).add_right 1)]

end NormalNumbers.PrimeLambert
