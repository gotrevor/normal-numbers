import NormalNumbers.TwoPointMoebiusPNT

/-!
# The Levin–Fainleib/Wirsing scale equation for `z^ω`, and `DelangeMean` for ALL `t ∉ ℤ`

`TwoPointDelangeScale.lean` proved `DelangeMean t` for `‖phase t − 1‖ < 1` (i.e. `‖t‖ < 1/6`) by
an integrating-factor argument run on the *kernel* sum `S(N) = ∑_{n ≤ N} h_z(n)/n`, where
`h_z = (z−1)^{ω}μ²`.  That route is capped at `‖z − 1‖ < 1` for a structural reason: the `ℓ¹` mass
`A(N) = ∑_{n≤N}‖h_z(n)‖/n ≍ (log N)^{‖z−1‖}` is the error term, and it must be `o(log N)`.
`TwoPointDelangeParity.lean` + `TwoPointMoebiusPNT.lean` then added the single point `t = 1/2`
by a *finite convolution* down to Möbius, and proved that finite convolution reaches no other
point (the exponent in `(1 − zX)^{-1}(1 − X)^w` is an integer only at `z = −1`).

## The move this file makes

Run the Levin–Fainleib identity on `f = z^ω` **itself** rather than on its kernel.  `f` has modulus
one, so every error term is `O(N)` with no `(log N)^{‖z−1‖}` blow-up.  The mechanism:

* `ω(d·m) = ω(m) + [p ∤ m]` whenever `d` is a power of the prime `p` — so `f(d·m) = f(m)·z` off the
  multiples of `p`, uniformly in the exponent.  Hence, with `M(N) = ∑_{n≤N} f(n)`,

      ∑_{n≤N} f(n) log n  =  z·∑_{d≤N} Λ(d)·M(N/d)  −  (z−1)·∑_{d≤N} Λ(d)·G(d.minFac, N/d) ,

  where `G(p, y) = ∑_{m≤y, p∣m} f(m)` obeys `‖G(p,y)‖ ≤ y/p`, so the second sum is `O(N)` by
  `∑_p log p/p² < ∞` (`sum_log_div_sq_prime_le`) — **no Mertens' second theorem**.
* `∑_{d≤N} Λ(d) M(N/d) = ∑_{m≤N} f(m)·ψ(N/m) = N·∑_{m≤N} f(m)/m + O(N)`, the `O(N)` being exactly
  `DelangeSlot.exists_sum_abs_deltaN_le` — the hyperbola-averaged quantitative PNT already in tree.
* `∑_{n≤N} f(n) log n = M(N) log N + O(N)` by `log_factorial_ge`.

Together: `‖M(N)·log N − z·N·T(N)‖ ≤ C·N` with `T(N) = ∑_{m≤N} f(m)/m`, and Abel summation turns
`T` into `M(N)/N + Ũ(N)`, `Ũ(N) = ∑_{m<N} M(m)/(m(m+1))`.  The recursion
`Ũ(N+1) = Ũ(N)(1 + z s_N) + s_N·E_N`, `s_N = 1/((N+1) log N)`, `‖E_N‖ ≤ C`, is then closed by the
same discrete integrating factor as brick 3 of the scale route, giving `‖Ũ(N)‖ ≪ (log N)^θ` for any
`θ ∈ (max(Re z, 0), 1)` and hence `M(N)/N ≪ (log N)^{θ−1} → 0` for **every** `z` on the unit circle
with `z ≠ 1` (`Re z < 1` is automatic).
-/

open Finset Filter Topology ArithmeticFunction

namespace NormalNumbers.CastingOut

/-! ### The multiplicative function `f = z^ω` and its partial sums -/

/-- `f_z(n) = z^{ω(n)}` for `n ≥ 1`, and `0` at `n = 0`. -/
noncomputable def fOm (z : ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else z ^ omegaNat n

lemma fOm_zero (z : ℂ) : fOm z 0 = 0 := by simp [fOm]

lemma fOm_of_pos {z : ℂ} {n : ℕ} (hn : n ≠ 0) : fOm z n = z ^ omegaNat n := by
  simp [fOm, hn]

lemma norm_fOm_le {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) : ‖fOm z n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fOm]
  · rw [fOm_of_pos hn, norm_pow, hz, one_pow]

/-- `M(N) = ∑_{n ≤ N} z^{ω(n)}`. -/
noncomputable def mOm (z : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.Ioc 0 N, fOm z n

lemma norm_mOm_le {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) : ‖mOm z N‖ ≤ (N : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n _ => norm_fOm_le hz n) ?_
  simp

/-! ### `ω` against multiplication by a prime power -/

/-- If `d` is a power of the prime `p` then `ω(d·m) = ω(m) + [p ∤ m]` for `m ≠ 0`. -/
lemma omegaNat_primePow_mul {p k m : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hm : m ≠ 0) :
    omegaNat (p ^ k * m) = omegaNat m + (if p ∣ m then 0 else 1) := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hpf : (p ^ k * m).primeFactors = insert p m.primeFactors := by
    rw [Nat.primeFactors_mul hpk hm, Nat.primeFactors_pow _ hk, hp.primeFactors]
    rw [Finset.insert_eq]
  rw [omegaNat, omegaNat, hpf]
  by_cases h : p ∣ m
  · have : p ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨hp, h, hm⟩
    rw [Finset.insert_eq_self.2 this, if_pos h, add_zero]
  · have : p ∉ m.primeFactors := fun hmem => h (Nat.dvd_of_mem_primeFactors hmem)
    rw [Finset.card_insert_of_notMem this, if_neg h]

/-- The corresponding factorisation of `f = z^ω`. -/
lemma fOm_primePow_mul {z : ℂ} {p k m : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hm : m ≠ 0) :
    fOm z (p ^ k * m) = z * fOm z m - (z - 1) * (if p ∣ m then fOm z m else 0) := by
  have hne : p ^ k * m ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hp.pos.ne') hm
  rw [fOm_of_pos hne, fOm_of_pos hm, omegaNat_primePow_mul hp hk hm]
  by_cases h : p ∣ m <;> simp [h, pow_succ] <;> ring


/-! ### The Levin–Fainleib identity for `f = z^ω` -/

/-- Hyperbola summation for a summand depending on both `d` and `n/d`. -/
theorem sum_conv_gen {R : Type*} [AddCommMonoid R] (F : ℕ → ℕ → R) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, F d (n / d)
      = ∑ d ∈ Finset.Ioc 0 N, ∑ e ∈ Finset.Ioc 0 (N / d), F d e := by
  classical
  have hstep : ∀ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, F d (n / d)
      = ∑ d ∈ Finset.Ioc 0 N, if d ∣ n then F d (n / d) else 0 := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hdvd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hn.1, le_trans (Nat.le_of_dvd hn.1 hdvd) hn.2⟩, hdvd⟩
    · rintro ⟨_, hdvd⟩
      exact ⟨hdvd, by omega⟩
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_Ioc] at hd
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun n => n / d) (fun e => d * e) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    obtain ⟨⟨hn0, hnN⟩, hdvd⟩ := hn
    refine ⟨Nat.div_pos (Nat.le_of_dvd hn0 hdvd) hd.1, ?_⟩
    exact Nat.div_le_div_right hnN
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_Ioc] at he ⊢
    refine ⟨⟨Nat.mul_pos hd.1 he.1, ?_⟩, Dvd.intro e rfl⟩
    calc d * e ≤ d * (N / d) := Nat.mul_le_mul_left d he.2
      _ = (N / d) * d := by ring
      _ ≤ N := Nat.div_mul_le_self N d
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro e he
    exact Nat.mul_div_cancel_left e hd.1
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    rfl

/-- `G(p, y) = ∑_{m ≤ y, p ∣ m} f(m)`, the defect in the prime-power factorisation. -/
noncomputable def gOm (z : ℂ) (p y : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc 0 y, if p ∣ m then fOm z m else 0

/-- **The Levin–Fainleib identity for `z^ω`**, exactly. -/
theorem sum_fOm_log_eq (z : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, fOm z n * ((Real.log n : ℝ) : ℂ)
      = ∑ d ∈ Finset.Ioc 0 N,
          ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * (z * mOm z (N / d) - (z - 1) * gOm z d.minFac (N / d)) := by
  classical
  have hlhs : ∀ n ∈ Finset.Ioc 0 N, fOm z n * ((Real.log n : ℝ) : ℂ)
      = ∑ d ∈ n.divisors, ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * fOm z (d * (n / d)) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have : ∀ d ∈ n.divisors, ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * fOm z (d * (n / d))
        = ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * fOm z n := by
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.1 hd).1]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← Complex.ofReal_sum, vonMangoldt_sum]
    ring
  rw [Finset.sum_congr rfl hlhs,
    sum_conv_gen (fun d e => ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * fOm z (d * e)) N]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_Ioc] at hd
  by_cases hpp : IsPrimePow d
  · obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    rw [(Nat.prime_iff.2 hp).pow_minFac (by omega : k ≠ 0)]
    rw [← Finset.mul_sum, mOm, gOm]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [Finset.mem_Ioc] at hm
    exact fOm_primePow_mul (Nat.prime_iff.2 hp) (by omega) (by omega)
  · have : ArithmeticFunction.vonMangoldt d = 0 := vonMangoldt_eq_zero_iff.2 hpp
    simp [this]

end NormalNumbers.CastingOut
