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

end NormalNumbers.CastingOut
