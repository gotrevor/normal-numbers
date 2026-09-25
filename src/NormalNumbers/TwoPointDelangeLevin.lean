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


/-! ### The defect sum is `O(N)` -/

/-- `‖G(p,y)‖ ≤ y/p`: only the multiples of `p` contribute, each of modulus one. -/
lemma norm_gOm_le {z : ℂ} (hz : ‖z‖ = 1) (p y : ℕ) (hp : 0 < p) :
    ‖gOm z p y‖ ≤ (y : ℝ) / p := by
  classical
  have h1 : ‖gOm z p y‖ ≤ ∑ m ∈ Finset.Ioc 0 y, ‖(if p ∣ m then fOm z m else 0 : ℂ)‖ :=
    norm_sum_le _ _
  have h2 : ∀ m ∈ Finset.Ioc 0 y, ‖(if p ∣ m then fOm z m else 0 : ℂ)‖
      ≤ (if p ∣ m then (1:ℝ) else 0) := by
    intro m _
    by_cases h : p ∣ m
    · simpa [h] using norm_fOm_le hz m
    · simp [h]
  have h3 : ∑ m ∈ Finset.Ioc 0 y, (if p ∣ m then (1:ℝ) else 0)
      = (((Finset.Ioc 0 y).filter (p ∣ ·)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  have h4 : ((Finset.Ioc 0 y).filter (p ∣ ·)).card ≤ y / p := by
    have : (Finset.Ioc 0 y).filter (p ∣ ·) ⊆ (Finset.Ioc 0 (y / p)).image (fun j => p * j) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hm
      obtain ⟨⟨hm0, hmy⟩, j, rfl⟩ := hm
      refine Finset.mem_image.2 ⟨j, ?_, rfl⟩
      simp only [Finset.mem_Ioc]
      refine ⟨Nat.pos_of_mul_pos_left (by omega : 0 < p * j) , ?_⟩
      exact (Nat.le_div_iff_mul_le hp).2 (by rw [Nat.mul_comm] at hmy; omega)
    calc ((Finset.Ioc 0 y).filter (p ∣ ·)).card
        ≤ ((Finset.Ioc 0 (y / p)).image (fun j => p * j)).card := Finset.card_le_card this
      _ ≤ (Finset.Ioc 0 (y / p)).card := Finset.card_image_le
      _ = y / p := by simp
  calc ‖gOm z p y‖ ≤ _ := h1
    _ ≤ ∑ m ∈ Finset.Ioc 0 y, (if p ∣ m then (1:ℝ) else 0) := Finset.sum_le_sum h2
    _ = _ := h3
    _ ≤ ((y / p : ℕ) : ℝ) := by exact_mod_cast h4
    _ ≤ (y : ℝ) / p := Nat.cast_div_le


/-- `log p / (p^k · p)`, the term of the prime-power regrouping. -/
noncomputable def ppTerm (q : ℕ × ℕ) : ℝ :=
  Real.log q.1 / ((q.1 : ℝ) ^ q.2 * (q.1 : ℝ))

/-- `d ↦ (minFac d, v_{minFac d}(d))`, a bijection on the prime powers. -/
def ppPair (d : ℕ) : ℕ × ℕ := (d.minFac, d.factorization d.minFac)

lemma ppTerm_nonneg (q : ℕ × ℕ) : 0 ≤ ppTerm q := by
  rcases Nat.eq_zero_or_pos q.1 with h | h
  · simp [ppTerm, h]
  · have h1 : (1:ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast h
    have h0 : (0:ℝ) < (q.1 : ℝ) := by linarith
    have hl : 0 ≤ Real.log q.1 := Real.log_nonneg h1
    rw [ppTerm]
    positivity

/-- The prime-power regrouping bound `∑_{d ≤ N} Λ(d)/(d·minFac d) ≤ 16`, the only arithmetic
input to the defect estimate.  No Mertens' second theorem: the convergent series is
`∑_p log p/p²` (`sum_log_div_sq_prime_le`, constant `8`). -/
theorem sum_vonMangoldt_div_mul_minFac_le (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt d / ((d : ℝ) * (d.minFac : ℝ)) ≤ 16 := by
  classical
  have hstep1 : ∑ d ∈ Finset.Ioc 0 N,
      ArithmeticFunction.vonMangoldt d / ((d : ℝ) * (d.minFac : ℝ))
      = ∑ d ∈ (Finset.Ioc 0 N).filter IsPrimePow,
          ArithmeticFunction.vonMangoldt d / ((d : ℝ) * (d.minFac : ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : IsPrimePow d
    · simp [h]
    · simp [h, vonMangoldt_eq_zero_iff.2 h]
  have hpow : ∀ d ∈ (Finset.Ioc 0 N).filter IsPrimePow,
      (d.minFac) ^ (d.factorization d.minFac) = d := fun d hd =>
    IsPrimePow.minFac_pow_factorization_eq (Finset.mem_filter.1 hd).2
  have hinj : Set.InjOn ppPair ((Finset.Ioc 0 N).filter IsPrimePow) := by
    intro a ha b hb hab
    simp only [ppPair, Prod.mk.injEq] at hab
    rw [← hpow a ha, ← hpow b hb, hab.2, hab.1]
  have hstep2 : ∑ d ∈ (Finset.Ioc 0 N).filter IsPrimePow,
        ArithmeticFunction.vonMangoldt d / ((d : ℝ) * (d.minFac : ℝ))
      = ∑ q ∈ ((Finset.Ioc 0 N).filter IsPrimePow).image ppPair, ppTerm q := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hpp : IsPrimePow d := (Finset.mem_filter.1 hd).2
    have hc : ((d.minFac : ℝ)) ^ (d.factorization d.minFac) = (d:ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (hpow d hd)
    rw [ppTerm, ppPair, vonMangoldt_apply, if_pos hpp]
    simp only
    rw [hc]
  have hsub : ((Finset.Ioc 0 N).filter IsPrimePow).image ppPair
      ⊆ primesLe N ×ˢ Finset.Ioc 0 N := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hq
    have hpp : IsPrimePow d := (Finset.mem_filter.1 hd).2
    have hdN : 0 < d ∧ d ≤ N := Finset.mem_Ioc.1 (Finset.mem_filter.1 hd).1
    have hd1 : d ≠ 1 := hpp.ne_one
    have hp : (d.minFac).Prime := Nat.minFac_prime hd1
    have hk : 0 < d.factorization d.minFac := by
      by_contra hc
      have h0 : d.factorization d.minFac = 0 := by omega
      rw [← hpow d hd, h0, pow_zero] at hd1
      exact hd1 rfl
    have h2 : 2 ^ (d.factorization d.minFac) ≤ d := by
      calc 2 ^ (d.factorization d.minFac) ≤ (d.minFac) ^ (d.factorization d.minFac) :=
            Nat.pow_le_pow_left hp.two_le _
        _ = d := hpow d hd
    have hlt := Nat.lt_two_pow_self (n := d.factorization d.minFac)
    have hmf := Nat.minFac_le hdN.1
    refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hp⟩,
      Finset.mem_Ioc.2 ⟨hk, ?_⟩⟩
    · simp only [ppPair]; omega
    · simp only [ppPair]; omega
  have hprod : ∑ q ∈ primesLe N ×ˢ Finset.Ioc 0 N, ppTerm q ≤ 16 := by
    rw [Finset.sum_product]
    have hinner : ∀ p ∈ primesLe N, ∑ k ∈ Finset.Ioc 0 N, ppTerm (p, k)
        ≤ 2 * (Real.log p / (p : ℝ) ^ 2) := by
      intro p hp
      have hpp : p.Prime := prime_of_mem_primesLe hp
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
      have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      have hterm : ∀ k ∈ Finset.Ioc 0 N,
          ppTerm (p, k) ≤ (Real.log p / (p:ℝ) ^ 2) * (1/2 : ℝ) ^ (k - 1) := by
        intro k hk
        obtain ⟨hk0, _⟩ := Finset.mem_Ioc.1 hk
        have hpk : (p:ℝ) ^ 2 * 2 ^ (k - 1) ≤ (p:ℝ) ^ k * (p:ℝ) := by
          have he : (p:ℝ) ^ k = (p:ℝ) * (p:ℝ) ^ (k - 1) := by
            rw [← pow_succ']; congr 1; omega
          have h2p : (2:ℝ) ^ (k-1) ≤ (p:ℝ) ^ (k-1) :=
            pow_le_pow_left₀ (by norm_num) hp2 _
          rw [he]
          nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (k-1), sq_nonneg ((p:ℝ))]
        have hRHS : Real.log p / (p:ℝ)^2 * (1/2:ℝ)^(k-1)
            = Real.log p / ((p:ℝ)^2 * 2^(k-1)) := by
          rw [div_pow, one_pow]
          field_simp
        rw [ppTerm, hRHS]
        simp only
        gcongr
        all_goals first | exact hlog | positivity
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.mul_sum]
      have hgeo : ∑ k ∈ Finset.Ioc 0 N, (1/2 : ℝ) ^ (k - 1) ≤ 2 := by
        have heq : ∑ k ∈ Finset.Ioc 0 N, (1/2 : ℝ) ^ (k - 1)
            = ∑ j ∈ Finset.range N, (1/2 : ℝ) ^ j := by
          refine Finset.sum_nbij' (fun k => k - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
          · intro k hk; simp only [Finset.mem_Ioc] at hk; simp only [Finset.mem_range]; omega
          · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Ioc]; omega
          · intro k hk; simp only [Finset.mem_Ioc] at hk; omega
          · intro j _; omega
          · intro k _; rfl
        rw [heq]; exact sum_geometric_two_le N
      have hnn : 0 ≤ Real.log p / (p:ℝ) ^ 2 := by positivity
      nlinarith [hnn, hgeo]
    refine le_trans (Finset.sum_le_sum hinner) ?_
    rw [← Finset.mul_sum]
    have := sum_log_div_sq_prime_le N
    linarith
  calc ∑ d ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt d / ((d : ℝ) * (d.minFac : ℝ)) = _ := hstep1
    _ = _ := hstep2
    _ ≤ ∑ q ∈ primesLe N ×ˢ Finset.Ioc 0 N, ppTerm q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => ppTerm_nonneg q)
    _ ≤ 16 := hprod


/-! ### The hyperbola swap -/

/-- `∑_{d ≤ N} k(d)·∑_{e ≤ N/d} T(e) = ∑_{e ≤ N} T(e)·∑_{d ≤ N/e} k(d)`: both sides count the
lattice points `d·e ≤ N`. -/
theorem sum_hyperbola_swap {R : Type*} [CommRing R] (k T : ℕ → R) (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N, k d * ∑ e ∈ Finset.Ioc 0 (N / d), T e
      = ∑ e ∈ Finset.Ioc 0 N, T e * ∑ d ∈ Finset.Ioc 0 (N / e), k d := by
  classical
  have hsplit : ∀ (a : ℕ), 0 < a → ∀ (g : ℕ → R),
      ∑ b ∈ Finset.Ioc 0 (N / a), g b
        = ∑ b ∈ Finset.Ioc 0 N, if a * b ≤ N then g b else 0 := by
    intro a ha g
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext b
    simp only [Finset.mem_Ioc, Finset.mem_filter]
    constructor
    · rintro ⟨hb0, hb⟩
      have h1 : a * b ≤ N := by
        have h := (Nat.le_div_iff_mul_le ha).1 hb
        rw [Nat.mul_comm]; exact h
      have h2 : b ≤ a * b := Nat.le_mul_of_pos_left b ha
      exact ⟨⟨hb0, le_trans h2 h1⟩, h1⟩
    · rintro ⟨⟨hb0, _⟩, hab⟩
      refine ⟨hb0, (Nat.le_div_iff_mul_le ha).2 ?_⟩
      rw [Nat.mul_comm]; exact hab
  have hL : ∑ d ∈ Finset.Ioc 0 N, k d * ∑ e ∈ Finset.Ioc 0 (N / d), T e
      = ∑ d ∈ Finset.Ioc 0 N, ∑ e ∈ Finset.Ioc 0 N,
          (if d * e ≤ N then k d * T e else 0) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_Ioc] at hd
    rw [hsplit d hd.1 T, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : d * e ≤ N <;> simp [h]
  have hR : ∑ e ∈ Finset.Ioc 0 N, T e * ∑ d ∈ Finset.Ioc 0 (N / e), k d
      = ∑ e ∈ Finset.Ioc 0 N, ∑ d ∈ Finset.Ioc 0 N,
          (if d * e ≤ N then k d * T e else 0) := by
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [Finset.mem_Ioc] at he
    rw [hsplit e he.1 k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hc : e * d = d * e := Nat.mul_comm e d
    rw [hc]
    by_cases h : d * e ≤ N
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hL, hR, Finset.sum_comm]

/-! ### The scale equation `‖M(N) log N − z·N·T(N)‖ ≤ C·N` -/

/-- `T(N) = ∑_{m ≤ N} z^{ω(m)}/m`. -/
noncomputable def tOm (z : ℂ) (N : ℕ) : ℂ := ∑ m ∈ Finset.Ioc 0 N, fOm z m / (m : ℂ)

/-- **(A) The defect sum is `O(N)`**, with the absolute constant `32`. -/
theorem norm_defect_le {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖∑ d ∈ Finset.Ioc 0 N,
        ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * ((z - 1) * gOm z d.minFac (N / d))‖
      ≤ 32 * N := by
  have hz1 : ‖z - 1‖ ≤ 2 := by
    calc ‖z - 1‖ ≤ ‖z‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hz]; norm_num
  have hterm : ∀ d ∈ Finset.Ioc 0 N,
      ‖((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * ((z - 1) * gOm z d.minFac (N / d))‖
        ≤ 2 * (N : ℝ) * (ArithmeticFunction.vonMangoldt d / ((d:ℝ) * (d.minFac : ℝ))) := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd.1
    have hmf : 0 < d.minFac := Nat.minFac_pos d
    have hmf0 : (0:ℝ) < (d.minFac : ℝ) := by exact_mod_cast hmf
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d := vonMangoldt_nonneg
    have hg : ‖gOm z d.minFac (N / d)‖ ≤ ((N / d : ℕ) : ℝ) / (d.minFac : ℝ) :=
      norm_gOm_le hz _ _ hmf
    have hND : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
    have h1 : ‖z - 1‖ * ‖gOm z d.minFac (N / d)‖
        ≤ 2 * ((N : ℝ) / (d : ℝ) / (d.minFac : ℝ)) := by
      have hgnn : 0 ≤ ‖gOm z d.minFac (N / d)‖ := norm_nonneg _
      have h2 : ‖gOm z d.minFac (N / d)‖ ≤ (N : ℝ) / (d:ℝ) / (d.minFac : ℝ) := by
        refine hg.trans ?_
        gcongr
      nlinarith [norm_nonneg (z - 1)]
    calc ArithmeticFunction.vonMangoldt d * (‖z - 1‖ * ‖gOm z d.minFac (N / d)‖)
        ≤ ArithmeticFunction.vonMangoldt d * (2 * ((N : ℝ) / (d : ℝ) / (d.minFac : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 hΛ
      _ = 2 * (N : ℝ) * (ArithmeticFunction.vonMangoldt d / ((d:ℝ) * (d.minFac : ℝ))) := by
          field_simp
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have := sum_vonMangoldt_div_mul_minFac_le N
  nlinarith

/-- **(B) The `ψ`-replacement**, on the hyperbola-averaged quantitative PNT. -/
theorem exists_norm_psi_replace_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ), ‖z‖ = 1 → ∀ N : ℕ,
      ‖(∑ d ∈ Finset.Ioc 0 N, ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * mOm z (N / d))
          - (N : ℂ) * tOm z N‖ ≤ C * N := by
  obtain ⟨C₀, hC₀, hC⟩ := NormalNumbers.DelangeSlot.exists_sum_abs_deltaN_le
  refine ⟨C₀ + 1, by linarith, fun z hz N => ?_⟩
  have hswap : ∑ d ∈ Finset.Ioc 0 N, ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * mOm z (N / d)
      = ∑ m ∈ Finset.Ioc 0 N, fOm z m * ((NormalNumbers.DelangeSlot.psiN (N / m) : ℝ) : ℂ) := by
    simp only [mOm]
    rw [sum_hyperbola_swap (fun d => ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ)) (fOm z) N]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    rw [NormalNumbers.DelangeSlot.psiN, Complex.ofReal_sum]
  have hT : (N : ℂ) * tOm z N
      = ∑ m ∈ Finset.Ioc 0 N, fOm z m * (((N : ℝ) / (m : ℝ) : ℝ) : ℂ) := by
    rw [tOm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [Finset.mem_Ioc] at hm
    have hm0 : (m : ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    push_cast
    field_simp
  rw [hswap, hT, ← Finset.sum_sub_distrib]
  have hbound : ∀ m ∈ Finset.Ioc 0 N,
      ‖fOm z m * ((NormalNumbers.DelangeSlot.psiN (N / m) : ℝ) : ℂ)
        - fOm z m * (((N : ℝ) / (m : ℝ) : ℝ) : ℂ)‖
      ≤ |NormalNumbers.DelangeSlot.deltaN (N / m)| + 1 := by
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    have hm0 : 0 < m := hm.1
    rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hsplit : NormalNumbers.DelangeSlot.psiN (N / m) - (N : ℝ) / (m : ℝ)
        = NormalNumbers.DelangeSlot.deltaN (N / m) + (((N / m : ℕ) : ℝ) - (N : ℝ) / (m : ℝ)) := by
      rw [NormalNumbers.DelangeSlot.deltaN]; ring
    have hfl : |((N / m : ℕ) : ℝ) - (N : ℝ) / (m : ℝ)| ≤ 1 := by
      have h1 : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := Nat.cast_div_le
      have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
      have h2 : (N : ℝ) / (m : ℝ) < ((N / m : ℕ) : ℝ) + 1 := by
        have hlt : N < (N / m + 1) * m := by
          have hd1 := Nat.div_add_mod N m
          have hd2 : N % m < m := Nat.mod_lt _ hm0
          have hd3 : (N / m + 1) * m = m * (N / m) + m := by ring
          omega
        have : (N:ℝ) < (((N / m : ℕ) : ℝ) + 1) * (m:ℝ) := by exact_mod_cast hlt
        rw [div_lt_iff₀ hmR]; exact this
      rw [abs_le]; constructor <;> linarith
    calc ‖fOm z m‖ * |NormalNumbers.DelangeSlot.psiN (N / m) - (N : ℝ) / (m : ℝ)|
        ≤ 1 * |NormalNumbers.DelangeSlot.psiN (N / m) - (N : ℝ) / (m : ℝ)| := by
          have := norm_fOm_le hz m
          have := abs_nonneg (NormalNumbers.DelangeSlot.psiN (N / m) - (N : ℝ) / (m : ℝ))
          nlinarith
      _ = |NormalNumbers.DelangeSlot.deltaN (N / m) + (((N / m : ℕ) : ℝ) - (N : ℝ) / (m : ℝ))| := by
          rw [one_mul, hsplit]
      _ ≤ |NormalNumbers.DelangeSlot.deltaN (N / m)| + 1 :=
          le_trans (abs_add_le _ _) (by linarith)
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  have h1 := hC N
  have hc0 : ((N - 0 : ℕ) : ℝ) = (N:ℝ) := by simp
  rw [hc0]
  linarith

/-- **(C) The log shift.** -/
theorem norm_log_shift_le {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖mOm z N * ((Real.log N : ℝ) : ℂ)
      - ∑ n ∈ Finset.Ioc 0 N, fOm z n * ((Real.log n : ℝ) : ℂ)‖ ≤ (N : ℝ) := by
  have hrw : mOm z N * ((Real.log N : ℝ) : ℂ)
      - ∑ n ∈ Finset.Ioc 0 N, fOm z n * ((Real.log n : ℝ) : ℂ)
      = ∑ n ∈ Finset.Ioc 0 N, fOm z n * (((Real.log N - Real.log n : ℝ)) : ℂ) := by
    rw [mOm, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  rw [hrw]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum ?_) (sum_log_div_le N)
  intro n hn
  simp only [Finset.mem_Ioc] at hn
  have hlog : 0 ≤ Real.log N - Real.log n := by
    have h1 : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
    have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have := Real.log_le_log h2 h1
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  have := norm_fOm_le hz n
  nlinarith

/-- **The Levin–Fainleib scale equation for `z^ω`.**  With `M(N) = ∑_{n≤N} z^{ω(n)}` and
`T(N) = ∑_{n≤N} z^{ω(n)}/n`,

    ‖M(N)·log N − z·N·T(N)‖ ≤ C·N ,

with an ABSOLUTE constant `C` — no `(log N)^{‖z−1‖}` anywhere, because `f = z^ω` has modulus one.
This is the statement the `‖z−1‖ < 1` scale route could not reach. -/
theorem exists_levin_scale_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ), ‖z‖ = 1 → ∀ N : ℕ,
      ‖mOm z N * ((Real.log N : ℝ) : ℂ) - z * (N : ℂ) * tOm z N‖ ≤ C * N := by
  obtain ⟨CB, hCB0, hCB⟩ := exists_norm_psi_replace_le
  refine ⟨CB + 33, by linarith, fun z hz N => ?_⟩
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  -- split the Levin–Fainleib identity
  have hsplit : ∑ n ∈ Finset.Ioc 0 N, fOm z n * ((Real.log n : ℝ) : ℂ)
      = z * (∑ d ∈ Finset.Ioc 0 N,
              ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * mOm z (N / d))
        - ∑ d ∈ Finset.Ioc 0 N,
            ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * ((z - 1) * gOm z d.minFac (N / d)) := by
    rw [sum_fOm_log_eq z N, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hB := hCB z hz N
  have hA := norm_defect_le hz N
  have hC := norm_log_shift_le hz N
  have hkey : mOm z N * ((Real.log N : ℝ) : ℂ) - z * (N : ℂ) * tOm z N
      = (mOm z N * ((Real.log N : ℝ) : ℂ)
          - ∑ n ∈ Finset.Ioc 0 N, fOm z n * ((Real.log n : ℝ) : ℂ))
        + z * ((∑ d ∈ Finset.Ioc 0 N,
              ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * mOm z (N / d)) - (N : ℂ) * tOm z N)
        - ∑ d ∈ Finset.Ioc 0 N,
            ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * ((z - 1) * gOm z d.minFac (N / d)) := by
    rw [hsplit]; ring
  rw [hkey]
  have hz' : ‖z‖ = 1 := hz
  calc ‖(mOm z N * ((Real.log N : ℝ) : ℂ)
          - ∑ n ∈ Finset.Ioc 0 N, fOm z n * ((Real.log n : ℝ) : ℂ))
        + z * ((∑ d ∈ Finset.Ioc 0 N,
              ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * mOm z (N / d)) - (N : ℂ) * tOm z N)
        - ∑ d ∈ Finset.Ioc 0 N,
            ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * ((z - 1) * gOm z d.minFac (N / d))‖
      ≤ ‖(mOm z N * ((Real.log N : ℝ) : ℂ)
          - ∑ n ∈ Finset.Ioc 0 N, fOm z n * ((Real.log n : ℝ) : ℂ))
        + z * ((∑ d ∈ Finset.Ioc 0 N,
              ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * mOm z (N / d)) - (N : ℂ) * tOm z N)‖
        + ‖∑ d ∈ Finset.Ioc 0 N,
            ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ)
              * ((z - 1) * gOm z d.minFac (N / d))‖ := norm_sub_le _ _
    _ ≤ ((N:ℝ) + 1 * (CB * N)) + 32 * N := by
        have h1 := norm_add_le (mOm z N * ((Real.log N : ℝ) : ℂ)
          - ∑ n ∈ Finset.Ioc 0 N, fOm z n * ((Real.log n : ℝ) : ℂ))
          (z * ((∑ d ∈ Finset.Ioc 0 N,
              ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * mOm z (N / d)) - (N : ℂ) * tOm z N))
        have h2 : ‖z * ((∑ d ∈ Finset.Ioc 0 N,
              ((ArithmeticFunction.vonMangoldt d : ℝ) : ℂ) * mOm z (N / d))
                - (N : ℂ) * tOm z N)‖ ≤ 1 * (CB * N) := by
          rw [norm_mul, hz']
          linarith
        linarith
    _ ≤ (CB + 33) * N := by ring_nf; linarith

/-! ### Abel summation: `T(N) = M(N)/N + Ũ(N)` -/

/-- `Ũ(N) = ∑_{1 ≤ m < N} M(m)/(m(m+1))`, the discrete `∫ m(σ) dσ`. -/
noncomputable def uOm (z : ℂ) (N : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ico 1 N, mOm z m / ((m : ℂ) * ((m : ℂ) + 1))

lemma uOm_succ (z : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    uOm z (N + 1) = uOm z N + mOm z N / ((N : ℂ) * ((N : ℂ) + 1)) := by
  rw [uOm, uOm, Finset.sum_Ico_succ_top hN]

lemma mOm_succ (z : ℂ) (N : ℕ) : mOm z (N + 1) = mOm z N + fOm z (N + 1) := by
  rw [mOm, mOm, Finset.sum_Ioc_succ_top (Nat.zero_le N)]

/-- **Abel summation.** -/
theorem tOm_eq_of_pos (z : ℂ) : ∀ N : ℕ, 1 ≤ N → tOm z N = mOm z N / (N : ℂ) + uOm z N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp [tOm, mOm, uOm]
  | succ N hN ih =>
      have hN0 : (N : ℂ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]; omega
      have hN1 : ((N : ℂ) + 1) ≠ 0 := by
        have : ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [this]
        simp only [ne_eq, Nat.cast_eq_zero]; omega
      have htsucc : tOm z (N + 1) = tOm z N + fOm z (N + 1) / ((N : ℂ) + 1) := by
        rw [tOm, tOm, Finset.sum_Ioc_succ_top (Nat.zero_le N)]
        push_cast
        ring
      rw [htsucc, ih, uOm_succ z hN, mOm_succ]
      push_cast
      field_simp
      ring

/-! ### The recursion `Ũ(N+1) = Ũ(N)(1 + z·s_N) + s_N·E_N` -/

/-- `s_N = 1/((N+1)·log N)`. -/
noncomputable def invStep (N : ℕ) : ℝ := 1 / (((N : ℝ) + 1) * Real.log (N : ℝ))

lemma invStep_nonneg {N : ℕ} (hN : 3 ≤ N) : 0 ≤ invStep N := by
  have hL := one_le_log_cast hN
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  rw [invStep]
  positivity

/-- `s_N ≤ σ_N`: `1/(N+1) ≤ log(N+1) − log N`, from `log x ≤ x − 1` at `x = N/(N+1)`. -/
lemma invStep_le_logRatioStep {N : ℕ} (hN : 3 ≤ N) : invStep N ≤ logRatioStep N := by
  have hL := one_le_log_cast hN
  have hNR : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hkey : 1 / ((N:ℝ) + 1) ≤ Real.log ((N:ℝ) + 1) - Real.log (N:ℝ) := by
    have hpos : (0:ℝ) < (N:ℝ) / ((N:ℝ) + 1) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by linarith) (by linarith)] at h
    have hrw : (N:ℝ) / ((N:ℝ) + 1) - 1 = -(1 / ((N:ℝ) + 1)) := by
      field_simp
      ring
    rw [hrw] at h
    linarith
  rw [invStep, logRatioStep, div_le_div_iff₀ (by positivity) (by linarith)]
  have h1 : 0 ≤ Real.log ((N:ℝ)+1) - Real.log (N:ℝ) := by
    have := Real.log_le_log (by linarith : (0:ℝ) < (N:ℝ)) (by linarith : (N:ℝ) ≤ (N:ℝ)+1)
    linarith
  calc (1:ℝ) * Real.log (N:ℝ)
      = Real.log (N:ℝ) := by ring
    _ ≤ (Real.log ((N:ℝ)+1) - Real.log (N:ℝ)) * (((N:ℝ)+1) * Real.log (N:ℝ)) := by
        have h2 : 1 / ((N:ℝ)+1) * (((N:ℝ)+1) * Real.log (N:ℝ)) = Real.log (N:ℝ) := by
          field_simp
        nlinarith [mul_le_mul_of_nonneg_right hkey
          (show (0:ℝ) ≤ ((N:ℝ)+1) * Real.log (N:ℝ) by positivity)]

/-- **The normalised scale equation.**  `‖m(N)·log N − z·Ũ(N)‖ ≤ C` with `m(N) = M(N)/N`. -/
theorem exists_mOm_scale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ), ‖z‖ = 1 → ∀ N : ℕ, 3 ≤ N →
      ‖mOm z N / (N : ℂ) * ((Real.log (N:ℝ) : ℝ) : ℂ) - z * uOm z N‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_levin_scale_bound
  refine ⟨C + 1, by linarith, fun z hz N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNR : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hid : mOm z N / (N : ℂ) * ((Real.log (N:ℝ) : ℝ) : ℂ) - z * uOm z N
      = (mOm z N * ((Real.log (N:ℝ) : ℝ) : ℂ) - z * (N:ℂ) * tOm z N) / (N:ℂ)
          + z * (mOm z N / (N:ℂ)) := by
    rw [tOm_eq_of_pos z N hN1]
    field_simp
    ring
  rw [hid]
  have hb1 : ‖(mOm z N * ((Real.log (N:ℝ) : ℝ) : ℂ) - z * (N:ℂ) * tOm z N) / (N:ℂ)‖ ≤ C := by
    rw [norm_div, Complex.norm_natCast]
    have hNpos : (0:ℝ) < (N:ℝ) := by linarith
    rw [div_le_iff₀ hNpos]
    exact hC z hz N
  have hb2 : ‖z * (mOm z N / (N:ℂ))‖ ≤ 1 := by
    rw [norm_mul, hz, one_mul, norm_div, Complex.norm_natCast]
    have hNpos : (0:ℝ) < (N:ℝ) := by linarith
    rw [div_le_one hNpos]
    exact norm_mOm_le hz N
  exact le_trans (norm_add_le _ _) (by linarith)

/-- **The recursion.**  `Ũ(N+1) − Ũ(N)(1 + z·s_N)` has norm `≤ s_N·C` with `C` absolute. -/
theorem exists_uOm_step :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ), ‖z‖ = 1 → ∀ N : ℕ, 3 ≤ N →
      ‖uOm z (N + 1) - uOm z N * (1 + z * ((invStep N : ℝ) : ℂ))‖ ≤ invStep N * C := by
  obtain ⟨C, hC0, hC⟩ := exists_mOm_scale
  refine ⟨C, hC0, fun z hz N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hL := one_le_log_cast hN
  have hNR : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hLC : ((Real.log (N:ℝ) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hN1C : ((N : ℂ) + 1) ≠ 0 := by
    intro h
    have h2 : (N : ℂ) = -1 := by linear_combination h
    have hre : ((N : ℝ)) = -1 := by exact_mod_cast congrArg Complex.re h2
    linarith
  have hsC : ((invStep N : ℝ) : ℂ) = 1 / (((N:ℂ) + 1) * ((Real.log (N:ℝ) : ℝ) : ℂ)) := by
    rw [invStep]
    push_cast
    ring
  have hid : uOm z (N + 1) - uOm z N * (1 + z * ((invStep N : ℝ) : ℂ))
      = ((invStep N : ℝ) : ℂ)
        * (mOm z N / (N : ℂ) * ((Real.log (N:ℝ) : ℝ) : ℂ) - z * uOm z N) := by
    rw [uOm_succ z hN1, hsC]
    field_simp
    ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (invStep_nonneg hN)]
  exact mul_le_mul_of_nonneg_left (hC z hz N hN) (invStep_nonneg hN)

end NormalNumbers.CastingOut
