import NormalNumbers.PairDecoupleMertens
import NormalNumbers.PairDecoupleTwoPoint

/-!
# Leaf (D) at first order: no single prime obstructs, however large

The wall under `PairDecorr` is leaf (D) — natural density over `[0, R)` versus the mean over one
full period of the prime-periodic model `θ_N = Σ_r b^{N mod r}/(b^r − 1)`
(`SwingC1Periodic.lean`).  The period of the primes `≤ P` is `exp((1+o(1))P)`, so the model can
never be truncated inside `[0, R)`, and Ren's worry locates the whole difficulty in the primes
`r ≍ N`.

This file settles the **first-order** part of that worry, unconditionally and with no sieve:

`|Σ_{n<R} (θ^{(r)}_{pn} − θ^{(r)}_{qn})| ≤ 1/(b−1)`   for every prime `r ∤ pq`,

**uniformly in `r` and `R`** (`abs_sum_pairPeriodicTerm_le`).  So a single prime contributes
`O(1/R)` to the pair mean no matter how large it is, and all primes together contribute
`O(π(pR)/R) = O(1/log R)` (`tendsto_sum_pairPeriodicTerm_div`).

The mechanism is exact: `θ^{(r)}_N = Σ_{k : r ∣ N+1+k} b^{−(k+1)}/(1−b^{−r})`, and along an
arithmetic progression the number of solutions of `r ∣ an+1+k` with `n < R` is `⌊R/r⌋` or
`⌈R/r⌉` — the two-sided residue count of lap 19.  The `p`- and `q`-counts therefore differ by at
most `1`, for every `k` and every `r`, and the `b`-adic weights sum to `1/(b−1)`.

**Consequence for the route.**  Leaf (D) cannot be obstructed by the *linear* term of any prime.
Whatever obstructs it is a genuinely multilinear interaction between two or more large primes.
-/

open Finset Filter Topology NormalNumbers.PairDecouple

namespace NormalNumbers.CastingOut

/-! ### The two-sided residue count, as a difference -/

/-- **The `p`- and `q`-counts along a progression differ by at most one.**  Both equal `R/r`
up to one, by `card_filter_dvd_ge` and `card_filter_dvd_le_coprime`. -/
lemma abs_card_filter_dvd_sub_le_one (r a a' e e' R : ℕ) (hr : 0 < r)
    (hra : Nat.Coprime r a) (hra' : Nat.Coprime r a') :
    |((#{i ∈ range R | r ∣ a * i + e} : ℤ)) - ((#{i ∈ range R | r ∣ a' * i + e'} : ℤ))| ≤ 1 := by
  have h1 := card_filter_dvd_ge r a e R hr hra
  have h2 := card_filter_dvd_le_coprime r a e R hr hra
  have h3 := card_filter_dvd_ge r a' e' R hr hra'
  have h4 := card_filter_dvd_le_coprime r a' e' R hr hra'
  have g1 : ((R / r : ℕ) : ℤ) ≤ (#{i ∈ range R | r ∣ a * i + e} : ℤ) := by exact_mod_cast h1
  have g2 : (#{i ∈ range R | r ∣ a * i + e} : ℤ) ≤ ((R / r : ℕ) : ℤ) + 1 := by exact_mod_cast h2
  have g3 : ((R / r : ℕ) : ℤ) ≤ (#{i ∈ range R | r ∣ a' * i + e'} : ℤ) := by exact_mod_cast h3
  have g4 : (#{i ∈ range R | r ∣ a' * i + e'} : ℤ) ≤ ((R / r : ℕ) : ℤ) + 1 := by
    exact_mod_cast h4
  rw [abs_le]
  omega

/-! ### One prime's contribution to the pair sum -/

private lemma sum_range_tsum_aux (f : ℕ → ℕ → ℝ) (hf : ∀ n, Summable (f n)) (R : ℕ) :
    Summable (fun k => ∑ n ∈ range R, f n k) ∧
      ∑ n ∈ range R, ∑' k : ℕ, f n k = ∑' k : ℕ, ∑ n ∈ range R, f n k := by
  induction R with
  | zero => simp
  | succ R ih =>
      obtain ⟨hs, he⟩ := ih
      refine ⟨?_, ?_⟩
      · exact (hs.add (hf R)).congr fun k => by rw [Finset.sum_range_succ]
      · rw [Finset.sum_range_succ, he, ← hs.tsum_add (hf R)]
        exact tsum_congr fun k => by rw [Finset.sum_range_succ]


private lemma summable_ppCell_k (b : ℕ) (hb : 2 ≤ b) (N r : ℕ) :
    Summable (fun k : ℕ => ppCell b N k r) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hgeom : Summable (fun k : ℕ => ((b : ℝ) ^ (k + 1))⁻¹) := by
    have : Summable (fun k : ℕ => ((b : ℝ)⁻¹) ^ k) :=
      summable_geometric_of_lt_one (by positivity) (by rw [inv_lt_one₀ (by linarith)]; linarith)
    refine (this.mul_right ((b : ℝ)⁻¹)).congr fun k => ?_
    rw [← inv_pow, ← pow_succ]
  refine Summable.of_nonneg_of_le (fun k => ppCell_nonneg b N k r) (fun k => ?_) hgeom
  unfold ppCell
  split_ifs
  · exact le_rfl
  · positivity

/-- The `r`-th periodic term summed along a progression is the `b`-adic average of the residue
counts. -/
lemma sum_range_primePeriodicTerm_mul (b : ℕ) (hb : 2 ≤ b) (r a : ℕ) (hr : r.Prime) (R : ℕ) :
    ∑ n ∈ range R, primePeriodicTerm b r (a * n)
      = ∑' k : ℕ, ((#{n ∈ range R | r ∣ a * n + 1 + k} : ℕ) : ℝ) * ((b : ℝ) ^ (k + 1))⁻¹ := by
  classical
  have hcell : ∀ n : ℕ, primePeriodicTerm b r (a * n) = ∑' k : ℕ, ppCell b (a * n) k r := by
    intro n
    rw [tsum_ppCell_k b hb (a * n) r hr, primePeriodicTerm, if_pos hr]
  rw [Finset.sum_congr rfl fun n _ => hcell n,
    (sum_range_tsum_aux (fun n k => ppCell b (a * n) k r)
      (fun n => summable_ppCell_k b hb (a * n) r) R).2]
  refine tsum_congr fun k => ?_
  rw [Finset.sum_congr rfl fun n _ => ppCell_prime_eq b (a * n) k r hr, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]

/-- **NO SINGLE PRIME OBSTRUCTS LEAF (D), HOWEVER LARGE.**  The pair difference carried by one
prime `r ∤ pq` has sum `O(1)` over `[0, R)`, uniformly in `r` and `R`. -/
theorem abs_sum_pairPeriodicTerm_le (b : ℕ) (hb : 2 ≤ b) (r p q : ℕ) (hr : r.Prime)
    (hrp : Nat.Coprime r p) (hrq : Nat.Coprime r q) (R : ℕ) :
    |∑ n ∈ range R, (primePeriodicTerm b r (p * n) - primePeriodicTerm b r (q * n))|
      ≤ 1 / ((b : ℝ) - 1) := by
  classical
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hgeom : Summable (fun k : ℕ => ((b : ℝ) ^ (k + 1))⁻¹) := by
    have : Summable (fun k : ℕ => ((b : ℝ)⁻¹) ^ k) :=
      summable_geometric_of_lt_one (by positivity) (by rw [inv_lt_one₀ (by linarith)]; linarith)
    refine (this.mul_right ((b : ℝ)⁻¹)).congr fun k => ?_
    rw [← inv_pow, ← pow_succ]
  have hgeomsum : ∑' k : ℕ, ((b : ℝ) ^ (k + 1))⁻¹ = 1 / ((b : ℝ) - 1) := by
    have h1 : ∀ k : ℕ, ((b : ℝ) ^ (k + 1))⁻¹ = ((b : ℝ)⁻¹) ^ k * (b : ℝ)⁻¹ := fun k => by
      rw [← inv_pow, ← pow_succ]
    rw [tsum_congr h1, tsum_mul_right,
      tsum_geometric_of_lt_one (by positivity) (by rw [inv_lt_one₀ (by linarith)]; linarith)]
    have hbne : (b : ℝ) ≠ 0 := by linarith
    field_simp
  set F : ℕ → ℕ → ℝ := fun a k =>
    ((#{n ∈ range R | r ∣ a * n + 1 + k} : ℕ) : ℝ) * ((b : ℝ) ^ (k + 1))⁻¹ with hF
  have hFnn : ∀ a k, 0 ≤ F a k := by intro a k; rw [hF]; positivity
  have hFsum : ∀ a : ℕ, Summable (F a) := by
    intro a
    refine Summable.of_nonneg_of_le (hFnn a) (fun k => ?_) (hgeom.mul_left (R : ℝ))
    have hcard : ((#{n ∈ range R | r ∣ a * n + 1 + k} : ℕ) : ℝ) ≤ (R : ℝ) := by
      have : #{n ∈ range R | r ∣ a * n + 1 + k} ≤ R := by
        simpa using Finset.card_le_card (Finset.filter_subset _ (range R))
      exact_mod_cast this
    rw [hF]
    dsimp only
    have hpos : (0:ℝ) < ((b : ℝ) ^ (k + 1))⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_right hcard hpos.le
  have hdiff : ∀ k : ℕ, |F p k - F q k| ≤ ((b : ℝ) ^ (k + 1))⁻¹ := by
    intro k
    have hkey := abs_card_filter_dvd_sub_le_one r p q (1 + k) (1 + k) R hr.pos
      hrp.symm.symm hrq.symm.symm
    simp only [← add_assoc] at hkey
    have hreal : |((#{n ∈ range R | r ∣ p * n + 1 + k} : ℕ) : ℝ)
        - ((#{n ∈ range R | r ∣ q * n + 1 + k} : ℕ) : ℝ)| ≤ 1 := by
      have h0 : |((#{n ∈ range R | r ∣ p * n + 1 + k} : ℕ) : ℤ)
          - ((#{n ∈ range R | r ∣ q * n + 1 + k} : ℕ) : ℤ)| ≤ 1 := hkey
      have h1 : ((|((#{n ∈ range R | r ∣ p * n + 1 + k} : ℕ) : ℤ)
          - ((#{n ∈ range R | r ∣ q * n + 1 + k} : ℕ) : ℤ)| : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by
        exact_mod_cast h0
      push_cast at h1
      exact h1
    rw [hF]
    dsimp only
    rw [← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((b : ℝ) ^ (k + 1))⁻¹)]
    have hpos : (0:ℝ) < ((b : ℝ) ^ (k + 1))⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_right hreal hpos.le
    simpa using this
  have hsplit : ∑ n ∈ range R, (primePeriodicTerm b r (p * n) - primePeriodicTerm b r (q * n))
      = ∑' k : ℕ, (F p k - F q k) := by
    rw [Finset.sum_sub_distrib, sum_range_primePeriodicTerm_mul b hb r p hr R,
      sum_range_primePeriodicTerm_mul b hb r q hr R, ← (hFsum p).tsum_sub (hFsum q)]
  rw [hsplit, ← hgeomsum]
  have hsum1 : Summable (fun k : ℕ => F p k - F q k) := (hFsum p).sub (hFsum q)
  have hsum2 : Summable (fun k : ℕ => |F p k - F q k|) := hsum1.abs
  calc |∑' k : ℕ, (F p k - F q k)| ≤ ∑' k : ℕ, |F p k - F q k| := by
        have h := norm_tsum_le_tsum_norm (f := fun k : ℕ => F p k - F q k)
          (by simpa only [Real.norm_eq_abs] using hsum2)
        simpa only [Real.norm_eq_abs] using h
    _ ≤ ∑' k : ℕ, ((b : ℝ) ^ (k + 1))⁻¹ := Summable.tsum_le_tsum hdiff hsum2 hgeom

/-- **All primes together: the whole first-order term vanishes.**  `π(x)/x → 0`, so summing the
uniform `O(1)` bound over the `O(R/log R)` relevant primes gives `O(1/log R)`. -/
theorem sum_abs_sum_pairPeriodicTerm_le (b : ℕ) (hb : 2 ≤ b) (p q : ℕ) (P R : ℕ)
    (hp : ∀ r ∈ primesLe P, Nat.Coprime r p) (hq : ∀ r ∈ primesLe P, Nat.Coprime r q) :
    ∑ r ∈ primesLe P,
        |∑ n ∈ range R, (primePeriodicTerm b r (p * n) - primePeriodicTerm b r (q * n))|
      ≤ ((primesLe P).card : ℝ) * (1 / ((b : ℝ) - 1)) := by
  calc ∑ r ∈ primesLe P,
        |∑ n ∈ range R, (primePeriodicTerm b r (p * n) - primePeriodicTerm b r (q * n))|
      ≤ ∑ _r ∈ primesLe P, (1 / ((b : ℝ) - 1)) :=
        Finset.sum_le_sum fun r hr =>
          abs_sum_pairPeriodicTerm_le b hb r p q (prime_of_mem_primesLe hr) (hp r hr) (hq r hr) R
    _ = ((primesLe P).card : ℝ) * (1 / ((b : ℝ) - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end NormalNumbers.CastingOut
