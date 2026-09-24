import NormalNumbers.SwingC1

/-!
# The prime-periodic form of the `b`-adic tail of `G₄_b`

The swing's crux (`hAutoCorrAll` in `SwingC1.lean`) is a statement about the orbit
`t_n = fract(b^n · G₄_b)`, equivalently about the `b`-adic tail

`θ_n = omegaTail b n = Σ_{k ≥ 1} ω(n+k) b^{−k}`.

This file proves the **exact** identity

`θ_n = Σ_{p prime} b^{(n mod p)} / (b^p − 1)`               (`omegaTail_eq_tsum_primePeriodic`)

obtained by exchanging the two summations in `ω(m) = Σ_p [p ∣ m]` and summing each prime's
contribution as a geometric series along the arithmetic progression `{k : p ∣ n+k}`.

The point is structural: **the `p`-th summand depends on `n` only through `n mod p`**, so `θ`
is an infinite sum of periodic functions of `n` — a Besicovitch almost-periodic sequence with
the primes as periods.  Two immediate consequences are recorded here:

* `primePeriodicTerm_add_period` — each summand is exactly `p`-periodic;
* `sum_primePeriodicTerm_period` — the mean of the `p`-th summand over one full period is
  exactly `1/(p(b−1))`, with no error term.

The second is the quantitative form of the obstruction recorded in
`OBSTRUCTION-2026-09-24-periodic-approximant.md`: summing `1/(p(b−1))` over `p ≤ P` is Mertens,
so the mass of `θ` carried by the primes `≤ P` is `≍ (log log P)/(b−1)`, while the joint period
of those primes is `exp((1+o(1))P)`.  The two requirements — period `≤ N`, and captured mass
`= (1−o(1))` of the total — are incompatible, and now quantitatively so.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-! ### The double expansion -/

/-- The `(k, p)` cell of the double expansion `ω(m) = Σ_p [p ∣ m]` inside `omegaTail`. -/
noncomputable def ppCell (b N k p : ℕ) : ℝ :=
  if p ∈ (N + 1 + k).primeFactors then ((b : ℝ) ^ (k + 1))⁻¹ else 0

lemma ppCell_nonneg (b N k p : ℕ) : 0 ≤ ppCell b N k p := by
  unfold ppCell; split_ifs with h
  · positivity
  · exact le_rfl

lemma ppCell_eq_zero_of_not_prime (b N k p : ℕ) (hp : ¬ p.Prime) : ppCell b N k p = 0 := by
  unfold ppCell
  rw [if_neg]
  intro hmem
  exact hp (Nat.prime_of_mem_primeFactors hmem)

lemma ppCell_prime_eq (b N k p : ℕ) (hp : p.Prime) :
    ppCell b N k p = if p ∣ N + 1 + k then ((b : ℝ) ^ (k + 1))⁻¹ else 0 := by
  have hne : N + 1 + k ≠ 0 := by omega
  unfold ppCell
  by_cases h : p ∣ N + 1 + k
  · rw [if_pos h, if_pos (Nat.mem_primeFactors.mpr ⟨hp, h, hne⟩)]
  · rw [if_neg h, if_neg]
    intro hmem
    exact h (Nat.mem_primeFactors.mp hmem).2.1

/-- Summing the cell over the primes recovers one term of `omegaTail`. -/
lemma tsum_ppCell_p (b N k : ℕ) :
    ∑' p : ℕ, ppCell b N k p = (omegaNat (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1) := by
  classical
  rw [tsum_eq_sum (s := (N + 1 + k).primeFactors)
    (fun p hp => by unfold ppCell; rw [if_neg hp])]
  rw [Finset.sum_congr rfl (g := fun _ => ((b : ℝ) ^ (k + 1))⁻¹)
    (fun p hp => by unfold ppCell; rw [if_pos hp])]
  rw [Finset.sum_const, nsmul_eq_mul, omegaNat, div_eq_mul_inv]

/-! ### The arithmetic progression carrying one prime -/

/-- `p ∣ N + 1 + k` is a condition on `N mod p` and `k mod p` only. -/
lemma dvd_shift_iff (N p k : ℕ) (hp : 2 ≤ p) :
    p ∣ N + 1 + k ↔ N % p + 1 + k % p = p := by
  have hp0 : 0 < p := by omega
  have hN : N % p < p := Nat.mod_lt _ hp0
  have hk : k % p < p := Nat.mod_lt _ hp0
  have heq : (N % p + 1 + k % p) % p = (N + 1 + k) % p :=
    ((Nat.mod_modEq N p).add_right 1).add (Nat.mod_modEq k p)
  constructor
  · rintro ⟨c, hc⟩
    have h0 : (N + 1 + k) % p = 0 := by rw [hc]; exact Nat.mul_mod_right p c
    rw [h0] at heq
    set u := N % p with hu
    set v := k % p with hv
    rcases Nat.lt_or_ge (u + 1 + v) p with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at heq; omega
    · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at heq; omega
  · intro h
    refine Nat.dvd_of_mod_eq_zero ?_
    rw [← heq, h, Nat.mod_self]

/-- The residue of `k` forced by `p ∣ N + 1 + k`. -/
lemma dvd_shift_iff_mod (N p k : ℕ) (hp : 2 ≤ p) :
    p ∣ N + 1 + k ↔ k % p = p - 1 - N % p := by
  have hp0 : 0 < p := by omega
  have hN : N % p < p := Nat.mod_lt _ hp0
  have hk : k % p < p := Nat.mod_lt _ hp0
  rw [dvd_shift_iff N p k hp]
  set u := N % p with hu
  set v := k % p with hv
  omega

/-! ### Summing one prime's contribution -/

/-- `b^{N mod p} / (b^p − 1)`: the `p`-periodic contribution of the prime `p` to the tail. -/
noncomputable def primePeriodicTerm (b p N : ℕ) : ℝ :=
  if p.Prime then (b : ℝ) ^ (N % p) / ((b : ℝ) ^ p - 1) else 0

lemma tsum_ppCell_k (b : ℕ) (hb : 2 ≤ b) (N p : ℕ) (hp : p.Prime) :
    ∑' k : ℕ, ppCell b N k p = (b : ℝ) ^ (N % p) / ((b : ℝ) ^ p - 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := by omega
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hBpos : (0 : ℝ) < (b : ℝ) ^ p := by positivity
  have hB1 : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ hb1 (by omega)
  have hr : N % p < p := Nat.mod_lt _ hp0
  set r := N % p with hrdef
  set k₀ := p - 1 - r with hk0def
  have hk0p : k₀ < p := by omega
  -- the index map
  have hginj : Function.Injective (fun i : ℕ => k₀ + i * p) := by
    intro i j hij
    simp only at hij
    have : i * p = j * p := by omega
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  have hhit : ∀ i : ℕ, p ∣ N + 1 + (k₀ + i * p) := by
    intro i
    rw [dvd_shift_iff_mod N p _ hp2, ← hrdef, ← hk0def]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk0p]
  have hsupp : Function.support (fun k => ppCell b N k p) ⊆ Set.range (fun i : ℕ => k₀ + i * p) := by
    intro k hk
    have hdvd : p ∣ N + 1 + k := by
      by_contra hcon
      apply hk
      show ppCell b N k p = 0
      rw [ppCell_prime_eq b N k p hp, if_neg hcon]
    have hmod : k % p = k₀ := (dvd_shift_iff_mod N p k hp2).mp hdvd
    refine ⟨k / p, ?_⟩
    have hdm := Nat.div_add_mod k p
    rw [hmod] at hdm
    show k₀ + k / p * p = k
    rw [Nat.mul_comm (k / p) p]
    omega
  have hkey := hginj.tsum_eq (f := fun k => ppCell b N k p) hsupp
  rw [← hkey]
  -- each term is geometric
  have hterm : ∀ i : ℕ, ppCell b N (k₀ + i * p) p
      = ((b : ℝ) ^ (k₀ + 1))⁻¹ * (((b : ℝ) ^ p)⁻¹) ^ i := by
    intro i
    rw [ppCell_prime_eq b N _ p hp, if_pos (hhit i)]
    have e : k₀ + i * p + 1 = (k₀ + 1) + p * i := by ring
    rw [e, pow_add, pow_mul, mul_inv, inv_pow]
  rw [tsum_congr hterm, tsum_mul_left,
    tsum_geometric_of_lt_one (by positivity) (by
      rw [inv_lt_one₀ hBpos]; exact hB1)]
  -- final algebra
  have hBne : ((b : ℝ) ^ p) ≠ 0 := ne_of_gt hBpos
  have hB1ne : ((b : ℝ) ^ p - 1) ≠ 0 := by linarith
  have hsplit : (b : ℝ) ^ (k₀ + 1) * (b : ℝ) ^ r = (b : ℝ) ^ p := by
    rw [← pow_add]; congr 1; omega
  have hk0ne : ((b : ℝ) ^ (k₀ + 1)) ≠ 0 := by positivity
  field_simp
  nlinarith [hsplit, hBpos, hB1]

/-! ### The identity -/

lemma summable_ppCell_p (b N k : ℕ) : Summable (fun p : ℕ => ppCell b N k p) :=
  summable_of_ne_finset_zero (s := (N + 1 + k).primeFactors)
    (fun p hp => by unfold ppCell; rw [if_neg hp])

lemma summable_ppCell_uncurry (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    Summable (Function.uncurry (fun k p => ppCell b N k p)) := by
  refine (summable_prod_of_nonneg (fun x => ppCell_nonneg b N x.1 x.2)).mpr ⟨?_, ?_⟩
  · intro k; exact summable_ppCell_p b N k
  · refine (summable_omegaTail b hb N).congr (fun k => ?_)
    exact (tsum_ppCell_p b N k).symm

/-- **The prime-periodic form of the `b`-adic tail.**  `Σ_{k ≥ 1} ω(N+k) b^{−k}` equals
`Σ_p b^{(N mod p)} / (b^p − 1)`: an infinite sum of functions of `N` that are *periodic*, with
the primes as periods. -/
theorem omegaTail_eq_tsum_primePeriodic (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    omegaTail b N = ∑' p : ℕ, primePeriodicTerm b p N := by
  have h1 : omegaTail b N = ∑' k : ℕ, ∑' p : ℕ, ppCell b N k p := by
    rw [omegaTail]
    exact tsum_congr (fun k => (tsum_ppCell_p b N k).symm)
  rw [h1, ← (summable_ppCell_uncurry b hb N).tsum_comm]
  refine tsum_congr (fun p => ?_)
  by_cases hp : p.Prime
  · rw [tsum_ppCell_k b hb N p hp, primePeriodicTerm, if_pos hp]
  · rw [primePeriodicTerm, if_neg hp, tsum_congr (fun k => ppCell_eq_zero_of_not_prime b N k p hp),
      tsum_zero]

/-! ### Periodicity, and the exact mean over one period -/

lemma primePeriodicTerm_nonneg (b : ℕ) (hb : 2 ≤ b) (p N : ℕ) : 0 ≤ primePeriodicTerm b p N := by
  unfold primePeriodicTerm
  split_ifs with hp
  · have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    have : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ hb1 (by have := hp.two_le; omega)
    have h2 : (0 : ℝ) ≤ (b : ℝ) ^ (N % p) := by positivity
    exact div_nonneg h2 (by linarith)
  · exact le_rfl

/-- **Each summand is exactly `p`-periodic in `N`.** -/
theorem primePeriodicTerm_add_period (b p N : ℕ) :
    primePeriodicTerm b p (N + p) = primePeriodicTerm b p N := by
  unfold primePeriodicTerm
  rw [Nat.add_mod_right]

/-- **The mean of the `p`-th summand over one full period is exactly `1/(p(b−1))`.**
(Stated without the `1/p`: the sum over a period is `1/(b−1)`.)  Summing this over
`p ≤ P` is Mertens: the mass of `θ` seen by the primes `≤ P` is `≍ (log log P)/(b−1)`. -/
theorem sum_primePeriodicTerm_period (b : ℕ) (hb : 2 ≤ b) (p : ℕ) (hp : p.Prime) :
    ∑ s ∈ range p, primePeriodicTerm b p s = 1 / ((b : ℝ) - 1) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hp2 : 2 ≤ p := hp.two_le
  have hB1 : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ hb1 (by omega)
  have hB1ne : ((b : ℝ) ^ p - 1) ≠ 0 := by linarith
  have hbne : ((b : ℝ) - 1) ≠ 0 := by linarith
  have hgeom : ∑ s ∈ range p, (b : ℝ) ^ s = ((b : ℝ) ^ p - 1) / ((b : ℝ) - 1) := by
    rw [geom_sum_eq (by linarith)]
  have hterm : ∀ s ∈ range p, primePeriodicTerm b p s = (b : ℝ) ^ s / ((b : ℝ) ^ p - 1) := by
    intro s hs
    rw [Finset.mem_range] at hs
    rw [primePeriodicTerm, if_pos hp, Nat.mod_eq_of_lt hs]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, hgeom]
  field_simp

/-! ### The orbit of `G₄_b` is an explicit almost-periodic sequence -/

lemma omegaTail_zero (b : ℕ) (hb : 2 ≤ b) : omegaTail b 0 = primeLambertAtBase b := by
  have hs := summable_lambert b hb omegaNat omegaNat_le
  have h1 : primeLambertAtBase b = ∑' m : ℕ, (omegaNat m : ℝ) / (b : ℝ) ^ m := by
    rw [primeLambertAtBase_eq_lambertVal_omegaNat, lambertVal]
  have h0 : (omegaNat 0 : ℝ) / (b : ℝ) ^ (0 : ℕ) = 0 := by simp [omegaNat]
  have hshift : ∀ k : ℕ, (omegaNat (0 + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)
      = (omegaNat (k + 1) : ℝ) / (b : ℝ) ^ (k + 1) := by
    intro k; rw [show 0 + 1 + k = k + 1 by omega]
  rw [h1, hs.tsum_eq_zero_add, h0, zero_add, omegaTail]
  exact tsum_congr hshift

/-- `fract(bⁿ · G₄_b) = fract(tail_n)`: the orbit point is the fractional part of the tail. -/
theorem fract_orbit_eq_fract_omegaTail (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    Int.fract (primeLambertAtBase b * (b : ℝ) ^ n) = Int.fract (omegaTail b n) := by
  have h := omegaTail_pow b hb n 0
  rw [omegaTail_zero b hb, zero_add] at h
  rw [mul_comm (primeLambertAtBase b) ((b : ℝ) ^ n), h, Int.fract_intCast_add]

/-- **The `×b`-orbit of `G₄_b` is explicitly almost periodic.**  Modulo `1`,
`bⁿ · G₄_b = Σ_p b^{(n mod p)} / (b^p − 1)`: a convergent sum of functions of `n` each of which
is periodic, with the primes as periods.  Every form of the C1 crux (`HOrbit`, `HFloorCorr`,
`HAutoCorr`, …) is a statement about *this* sequence — no `ω`, no carry, no real number left. -/
theorem fract_orbit_eq_fract_tsum (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    Int.fract (primeLambertAtBase b * (b : ℝ) ^ n)
      = Int.fract (∑' p : ℕ, primePeriodicTerm b p n) := by
  rw [fract_orbit_eq_fract_omegaTail b hb n, omegaTail_eq_tsum_primePeriodic b hb n]

/-- The crux (`HOrbit` form) rewritten on the prime-periodic sequence. -/
theorem orbitCorrSum_eq_primePeriodic (b : ℕ) (hb : 2 ≤ b) (j L N : ℕ) :
    orbitCorrSum b j L N
      = (∑ n ∈ range N, zetaRoot (b - 1) ^
          ((j : ℤ) * ⌊(b : ℝ) ^ L * Int.fract (∑' p : ℕ, primePeriodicTerm b p n)⌋)) / N := by
  rw [orbitCorrSum]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by rw [fract_orbit_eq_fract_tsum b hb n]

/-! ### The truncation to the primes `≤ P`, and the exact Mertens mass it carries -/

lemma primePeriodicTerm_add_mul (b p N t : ℕ) :
    primePeriodicTerm b p (N + p * t) = primePeriodicTerm b p N := by
  unfold primePeriodicTerm
  rw [Nat.add_mul_mod_self_left]

/-- `θ^{(P)}`: the part of the tail carried by the primes `≤ P`.  Purely periodic. -/
noncomputable def truncTail (b P N : ℕ) : ℝ := ∑ p ∈ range (P + 1), primePeriodicTerm b p N

/-- **`θ^{(P)}` is periodic with any common period of the primes `≤ P`.** -/
theorem truncTail_add_period (b P N M : ℕ) (hM : ∀ p, p ≤ P → p.Prime → p ∣ M) :
    truncTail b P (N + M) = truncTail b P N := by
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  by_cases hpp : p.Prime
  · obtain ⟨t, ht⟩ := hM p (by omega) hpp
    rw [ht, primePeriodicTerm_add_mul]
  · unfold primePeriodicTerm; rw [if_neg hpp, if_neg hpp]

/-- **The exact mass of one prime over `t` full periods.**  No error term. -/
theorem sum_primePeriodicTerm_range_mul (b : ℕ) (hb : 2 ≤ b) (p : ℕ) (hp : p.Prime) (t : ℕ) :
    ∑ n ∈ range (p * t), primePeriodicTerm b p n = (t : ℝ) * (1 / ((b : ℝ) - 1)) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hsplit : p * (t + 1) = p * t + p := by ring
      have hIco : ∑ n ∈ Finset.Ico (p * t) (p * t + p), primePeriodicTerm b p n
          = ∑ s ∈ range p, primePeriodicTerm b p s := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        exact Finset.sum_congr rfl fun s _ => by
          rw [show p * t + s = s + p * t by ring, primePeriodicTerm_add_mul]
      rw [hsplit, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le (p * t)) (Nat.le_add_right (p * t) p),
        ← Finset.range_eq_Ico, ih, hIco, sum_primePeriodicTerm_period b hb p hp]
      push_cast
      ring

end NormalNumbers.CastingOut
