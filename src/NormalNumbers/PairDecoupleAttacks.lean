import NormalNumbers.PairDecoupleLower

/-!
# The refutation checklist, discharged

`KICKOFF-2026-09-24-pd-refute.md` lists the local obstructions a counterexample to
`PairDecouple` might exploit.  This file turns each of them into a *theorem* saying it cannot
work, so the refutation search is narrowed rather than merely reported on.

The vehicle is `classDeviation B Q R`, the mean over residue classes of the deviation of `B`'s
progression mean from its overall mean — `pairDefect` with its arithmetic stripped
(`pairDefect_eq_classDeviation`).

| attack | why it fails | theorem |
|---|---|---|
| the shifts `k ≡ −1 (mod p)`, where `p ∣ pn+1+k` for EVERY `n` | `p`'s own contribution to `omegaTail b (pn)` is the CONSTANT `1/(b^p−1)`, and a constant summand in the exponent is invisible to the class deviation | `primePeriodicTerm_mul_self`, `classDeviation_phase_add_primePeriodicTerm_self` |
| the `n = 0` term (`pairRemainder = 0` there, so `B 0 = 1` regardless of `b, t, p, q`) | perturbing finitely many terms moves the defect by `O(n₀/(QR))` | `pairRemainder_zero`, `classDeviation_perturb` |
| a prime shared by `pn+k` and `qn+k'` for every `n` in a class | such a prime satisfies `r ∣ p` or `r ≤ P`, so it is not in the remainder at all: this is the CRT reason | `no_prime_dvd_class_beyond_cut` |
| `p ≤ P` (`p ∣ Q`), and the vanishing of the small-prime model | already handled in `PairDecoupleLower.lean`: `p ≡ q` mod the small primes makes the model term exactly `1`, which relocates the content but creates no bias |
| the `R`-indexing of `progMean` against `fullMean` | no mismatch: `fullMean B (Q·R)` IS the mean of the `Q` progression means (`fullMean_eq_periodMean_progMean`), so `classDeviation` is a genuine mean absolute deviation | — |

The numerics agree (`probes/data-2026-09-24-pair-defect*.txt`): the band decomposition shows the
class deviation of the remainder restricted to primes in `(P, y]` decaying like `R^{-1/2}`…`R^{-1}`
for every fixed `y` — exactly the CRT rate `O(y/R)` — and *no* excess surviving in the `y → ∞`
limit beyond a slowly (`≈ (log N)^{-1/2}`) decaying residue.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-! ### The arithmetic-free defect -/

/-- `pairDefect` with the arithmetic stripped: the mean over the `Q` residue classes of the
deviation of `B`'s progression mean from its mean over `[0, QR)`. -/
noncomputable def classDeviation (B : ℕ → ℂ) (Q R : ℕ) : ℝ :=
  (∑ c ∈ range Q, ‖progMean B Q R c - fullMean B (Q * R)‖) / Q

lemma pairDefect_eq_classDeviation (b P p q : ℕ) (t : ℝ) (R : ℕ) :
    pairDefect b P p q t R
      = classDeviation (fun n => phase (t * pairRemainder b P p q n)) (primorialLe P) R := rfl

lemma classDeviation_nonneg (B : ℕ → ℂ) (Q R : ℕ) : 0 ≤ classDeviation B Q R := by
  rw [classDeviation]; positivity

/-! ### A unimodular constant is invisible -/

lemma progMean_const_mul (B : ℕ → ℂ) (z : ℂ) (Q R c : ℕ) :
    progMean (fun n => z * B n) Q R c = z * progMean B Q R c := by
  rw [progMean, progMean, ← Finset.mul_sum, mul_div_assoc]

lemma fullMean_const_mul (B : ℕ → ℂ) (z : ℂ) (N : ℕ) :
    fullMean (fun n => z * B n) N = z * fullMean B N := by
  rw [fullMean, fullMean, ← Finset.mul_sum, mul_div_assoc]

theorem classDeviation_const_mul (B : ℕ → ℂ) (z : ℂ) (Q R : ℕ) :
    classDeviation (fun n => z * B n) Q R = ‖z‖ * classDeviation B Q R := by
  rw [classDeviation, classDeviation, ← mul_div_assoc, Finset.mul_sum]
  refine congrArg (· / (Q : ℝ)) (Finset.sum_congr rfl fun c _ => ?_)
  rw [progMean_const_mul, fullMean_const_mul, ← mul_sub, norm_mul]

/-- **A constant summand in the exponent leaves the class deviation untouched.** -/
theorem classDeviation_phase_add_const (x : ℕ → ℝ) (κ : ℝ) (Q R : ℕ) :
    classDeviation (fun n => phase (x n + κ)) Q R = classDeviation (fun n => phase (x n)) Q R := by
  have hrw : (fun n => phase (x n + κ)) = fun n => phase κ * phase (x n) := by
    funext n; rw [add_comm, phase_add]
  rw [hrw, classDeviation_const_mul, norm_phase, one_mul]

/-! ### Attack 1: the shifts `k ≡ −1 (mod p)` -/

/-- **`p ∣ pn + k ⟺ p ∣ k`, so the prime `p`'s own contribution to `omegaTail b (p n)` is the
CONSTANT `1/(b^p − 1)`.**  The shifts `k` with `p ∣ 1 + k` of the refutation checklist are
exactly the `k`'s that contribute to it, and they contribute for every `n` alike. -/
lemma primePeriodicTerm_mul_self (b p n : ℕ) (hp : p.Prime) :
    primePeriodicTerm b p (p * n) = 1 / ((b : ℝ) ^ p - 1) := by
  rw [primePeriodicTerm, if_pos hp, Nat.mul_mod_right, pow_zero]

/-- **Attack 1 fails.**  The always-dividing prime contributes a constant phase, which cancels
between every progression mean and the full mean. -/
theorem classDeviation_phase_add_primePeriodicTerm_self
    (x : ℕ → ℝ) (b p : ℕ) (hp : p.Prime) (Q R : ℕ) :
    classDeviation (fun n => phase (x n + primePeriodicTerm b p (p * n))) Q R
      = classDeviation (fun n => phase (x n)) Q R := by
  have hrw : (fun n => phase (x n + primePeriodicTerm b p (p * n)))
      = fun n => phase (x n + 1 / ((b : ℝ) ^ p - 1)) := by
    funext n; rw [primePeriodicTerm_mul_self b p n hp]
  rw [hrw, classDeviation_phase_add_const]

/-! ### Attack 2: the `n = 0` term -/

lemma pairTail_zero (b p q : ℕ) : pairTail b p q 0 = 0 := by
  rw [pairTail, Nat.mul_zero, Nat.mul_zero, sub_self]

lemma truncPairTail_zero (b P p q : ℕ) : truncPairTail b P p q 0 = 0 := by
  rw [truncPairTail]
  exact Finset.sum_eq_zero fun r _ => by rw [Nat.mul_zero, Nat.mul_zero, sub_self]

/-- The frozen statement's `n = 0` term is the harmless value `1`, for every `b, t, p, q, P`. -/
lemma pairRemainder_zero (b P p q : ℕ) : pairRemainder b P p q 0 = 0 := by
  rw [pairRemainder, pairTail_zero, truncPairTail_zero, sub_self]

set_option maxHeartbeats 800000 in
/-- **Attack 2 fails.**  Changing `B` only on `[0, n₀)` moves the class deviation by at most
`4 n₀/(Q R)`.  So no finite set of exceptional indices — in particular not `n = 0` — can keep
`pairDefect` away from `0`. -/
theorem classDeviation_perturb (B B' : ℕ → ℂ) (Q R n₀ : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (hB : ∀ n, ‖B n‖ ≤ 1) (hB' : ∀ n, ‖B' n‖ ≤ 1) (hne : ∀ n, n₀ ≤ n → B n = B' n) :
    |classDeviation B Q R - classDeviation B' Q R| ≤ 4 * n₀ / (Q * R) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  set D : ℕ → ℝ := fun n => ‖B n - B' n‖ with hD
  have hDle : ∀ n, D n ≤ 2 := fun n =>
    (norm_sub_le _ _).trans (by linarith [hB n, hB' n])
  have hDzero : ∀ n, n₀ ≤ n → D n = 0 := by
    intro n hn; rw [hD]; simp [hne n hn]
  set S : ℝ := ∑ m ∈ range (Q * R), D m with hS
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg fun m _ => norm_nonneg _
  have hmass : S ≤ 2 * n₀ := by
    rw [hS]
    calc ∑ m ∈ range (Q * R), D m
        ≤ ∑ m ∈ range (Q * R), (if m < n₀ then (2 : ℝ) else 0) := by
          refine Finset.sum_le_sum fun m _ => ?_
          by_cases hm : m < n₀
          · simp only [hm, if_true]; exact hDle m
          · simp only [hm, if_false]; exact le_of_eq (hDzero m (by omega))
      _ ≤ 2 * n₀ := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hcard : ((range (Q * R)).filter (fun m => m < n₀)).card ≤ n₀ := by
            refine le_trans (Finset.card_le_card ?_) (Finset.card_range n₀).le
            intro m hm
            simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
            exact hm.2
          have hc : (((range (Q * R)).filter (fun m => m < n₀)).card : ℝ) ≤ n₀ := by
            exact_mod_cast hcard
          linarith
  -- progression means
  have hprog : ∑ c ∈ range Q, ‖progMean B Q R c - progMean B' Q R c‖ ≤ S / R := by
    rw [hS, sum_range_mul_split D Q R, Finset.sum_div]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [progMean, progMean, div_sub_div_same, norm_div, Complex.norm_natCast,
      div_le_div_iff_of_pos_right hRr]
    calc ‖∑ r ∈ range R, B (c + r * Q) - ∑ r ∈ range R, B' (c + r * Q)‖
        = ‖∑ r ∈ range R, (B (c + r * Q) - B' (c + r * Q))‖ := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ r ∈ range R, D (c + r * Q) := norm_sum_le _ _
  -- full mean
  have hfull : ‖fullMean B (Q * R) - fullMean B' (Q * R)‖ ≤ S / (Q * R) := by
    have hQRr : (0 : ℝ) < ((Q * R : ℕ) : ℝ) := by
      have : 0 < Q * R := Nat.mul_pos hQ hR
      exact_mod_cast this
    have hEq : (S : ℝ) / ((Q : ℝ) * R) = S / ((Q * R : ℕ) : ℝ) := by push_cast; ring
    rw [fullMean, fullMean, div_sub_div_same, norm_div, Complex.norm_natCast, hEq, hS,
      div_le_div_iff_of_pos_right hQRr]
    calc ‖∑ m ∈ range (Q * R), B m - ∑ m ∈ range (Q * R), B' m‖
        = ‖∑ m ∈ range (Q * R), (B m - B' m)‖ := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ m ∈ range (Q * R), D m := norm_sum_le _ _
  -- assemble
  have hstep : |classDeviation B Q R - classDeviation B' Q R|
      ≤ (∑ c ∈ range Q, ‖(progMean B Q R c - fullMean B (Q * R))
          - (progMean B' Q R c - fullMean B' (Q * R))‖) / Q := by
    rw [classDeviation, classDeviation, div_sub_div_same, abs_div, abs_of_pos hQr,
      div_le_div_iff_of_pos_right hQr]
    calc |∑ c ∈ range Q, ‖progMean B Q R c - fullMean B (Q * R)‖
            - ∑ c ∈ range Q, ‖progMean B' Q R c - fullMean B' (Q * R)‖|
        = |∑ c ∈ range Q, (‖progMean B Q R c - fullMean B (Q * R)‖
            - ‖progMean B' Q R c - fullMean B' (Q * R)‖)| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ c ∈ range Q, |‖progMean B Q R c - fullMean B (Q * R)‖
            - ‖progMean B' Q R c - fullMean B' (Q * R)‖| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun c _ => abs_norm_sub_norm_le _ _
  have hsplit : (∑ c ∈ range Q, ‖(progMean B Q R c - fullMean B (Q * R))
      - (progMean B' Q R c - fullMean B' (Q * R))‖) / Q
      ≤ (S / R + Q * (S / ((Q : ℝ) * R))) / Q := by
    rw [div_le_div_iff_of_pos_right hQr]
    have hterm : ∀ c ∈ range Q, ‖(progMean B Q R c - fullMean B (Q * R))
        - (progMean B' Q R c - fullMean B' (Q * R))‖
        ≤ ‖progMean B Q R c - progMean B' Q R c‖
          + ‖fullMean B (Q * R) - fullMean B' (Q * R)‖ := by
      intro c _
      calc ‖(progMean B Q R c - fullMean B (Q * R)) - (progMean B' Q R c - fullMean B' (Q * R))‖
          = ‖(progMean B Q R c - progMean B' Q R c)
              - (fullMean B (Q * R) - fullMean B' (Q * R))‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    calc ∑ c ∈ range Q, ‖(progMean B Q R c - fullMean B (Q * R))
            - (progMean B' Q R c - fullMean B' (Q * R))‖
        ≤ ∑ c ∈ range Q, (‖progMean B Q R c - progMean B' Q R c‖
            + ‖fullMean B (Q * R) - fullMean B' (Q * R)‖) := Finset.sum_le_sum hterm
      _ = (∑ c ∈ range Q, ‖progMean B Q R c - progMean B' Q R c‖)
            + Q * ‖fullMean B (Q * R) - fullMean B' (Q * R)‖ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ S / R + Q * (S / ((Q : ℝ) * R)) := by
          have h1 := hprog
          have h2 : ‖fullMean B (Q * R) - fullMean B' (Q * R)‖ ≤ S / ((Q : ℝ) * R) := hfull
          nlinarith [hQr.le]
  have hfin : (S / R + (Q : ℝ) * (S / ((Q : ℝ) * R))) / Q ≤ 4 * n₀ / ((Q : ℝ) * R) := by
    have e : (S / R + (Q : ℝ) * (S / ((Q : ℝ) * R))) / Q = 2 * S / ((Q : ℝ) * R) := by
      field_simp; ring
    rw [e, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (Q : ℝ) * R)]
    linarith
  have hgoal : (4 : ℝ) * n₀ / ((Q : ℝ) * R) = 4 * n₀ / ((Q * R : ℕ) : ℝ) := by push_cast; ring
  rw [hgoal] at hfin
  linarith [hstep.trans hsplit]

/-! ### Attack 3: a prime pinned on a residue class -/

/-- Two members of the class `c mod Q` force `r ∣ p·Q`. -/
lemma dvd_mul_of_dvd_class {r p k c Q : ℕ} (h : ∀ n : ℕ, r ∣ p * (c + n * Q) + k) :
    r ∣ p * Q := by
  have h0 := h 0
  have h1 := h 1
  have e : p * (c + 1 * Q) + k = (p * (c + 0 * Q) + k) + p * Q := by ring
  rw [e] at h1
  exact (Nat.dvd_add_right h0).mp h1

lemma mem_primesLe_of_prime_dvd_primorialLe {r P : ℕ} (hr : r.Prime)
    (h : r ∣ primorialLe P) : r ∈ primesLe P := by
  rw [primorialLe] at h
  obtain ⟨s, hs, hdvd⟩ := hr.prime.exists_mem_finset_dvd h
  have hsp : s.Prime := prime_of_mem_primesLe hs
  exact ((Nat.prime_dvd_prime_iff_eq hr hsp).mp hdvd) ▸ hs

lemma le_of_mem_primesLe {r P : ℕ} (hr : r ∈ primesLe P) : r ≤ P := by
  rw [primesLe, Finset.mem_filter, Finset.mem_range] at hr
  omega

/-- **Attack 3 fails: no prime beyond the cut is pinned by a residue class.**  If the prime `r`
divides `p·n + k` for EVERY `n` in the class `c mod primorialLe P`, then `r = p` or `r ≤ P`.  So
for the primes actually carrying `pairRemainder` — those `> P`, other than `p` itself — the
divisibility pattern is never forced by `n mod Q`: by CRT their residues are free.  This is the
exact sense in which the small-prime modulus cannot see the large primes. -/
theorem no_prime_dvd_class_beyond_cut {r p k c P : ℕ} (hr : r.Prime) (hp : p.Prime)
    (hrp : r ≠ p) (hrP : P < r) :
    ¬ (∀ n : ℕ, r ∣ p * (c + n * primorialLe P) + k) := by
  intro h
  rcases (Nat.Prime.dvd_mul hr).mp (dvd_mul_of_dvd_class h) with h1 | h2
  · exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp h1)
  · have := le_of_mem_primesLe (mem_primesLe_of_prime_dvd_primorialLe hr h2)
    omega

/-- The `n = 0` instance of attack 2, spelled out: the single exceptional term of the frozen
statement costs at most `4/(Q·R)`. -/
theorem classDeviation_perturb_zero (B B' : ℕ → ℂ) (Q R : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (hB : ∀ n, ‖B n‖ ≤ 1) (hB' : ∀ n, ‖B' n‖ ≤ 1) (hne : ∀ n, n ≠ 0 → B n = B' n) :
    |classDeviation B Q R - classDeviation B' Q R| ≤ 4 / (Q * R) := by
  have := classDeviation_perturb B B' Q R 1 hQ hR hB hB' (fun n hn => hne n (by omega))
  simpa using this

end NormalNumbers.CastingOut
