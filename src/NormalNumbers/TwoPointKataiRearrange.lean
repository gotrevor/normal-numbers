import NormalNumbers.TwoPointTuranKubilius

/-!
# The rearrangement step of the Kátai/BSZ inequality

Obligation 2 of `KataiQuantSharp`.  Weighting by `ω_w(n) = #{p ≤ w : p ∣ n}` and summing over
`n ≤ N` is the same as summing over pairs `(p, m)` with `p ≤ w` prime and `pm ≤ N`:

    Σ_{n ≤ N} ω_w(n) · F(n)  =  Σ_{p ≤ w} Σ_{m ≤ N/p} F(p·m) .

Exact, for any `F`.  The inner reindexing is the bijection `m ↦ p·m` from `(0, ⌊N/p⌋]` onto the
multiples of `p` in `(0, N]`.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The multiples of `p` in `(0, N]` are the image of `(0, ⌊N/p⌋]` under `m ↦ p·m`. -/
lemma sum_multiples_reindex {M : Type*} [AddCommMonoid M] (p N : ℕ) (hp : 0 < p) (F : ℕ → M) :
    ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => p ∣ n), F n
      = ∑ m ∈ Finset.Ioc 0 (N / p), F (p * m) := by
  classical
  refine (Finset.sum_nbij' (i := fun m => p * m) (j := fun n => n / p) ?_ ?_ ?_ ?_ ?_).symm
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.mp hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by positivity, ?_⟩, Dvd.intro m rfl⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hp).mp hm2
  · intro n hn
    obtain ⟨hn1, hdvd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn2, hn3⟩ := Finset.mem_Ioc.mp hn1
    refine Finset.mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hn3⟩
    exact Nat.div_pos (Nat.le_of_dvd hn2 hdvd) hp
  · intro m _
    exact Nat.mul_div_cancel_left m hp
  · intro n hn
    obtain ⟨_, hdvd⟩ := Finset.mem_filter.mp hn
    exact Nat.mul_div_cancel' hdvd
  · intro m _; rfl

/-- **The rearrangement.**  Exact, for any `F`. -/
theorem sum_kataiOmega_mul_complex (w N : ℕ) (F : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc 0 N, (kataiOmega w n : ℂ) * F n
      = ∑ p ∈ primesLe w, ∑ m ∈ Finset.Ioc 0 (N / p), F (p * m) := by
  classical
  have hstep : ∀ n : ℕ, (kataiOmega w n : ℂ) * F n
      = ∑ p ∈ primesLe w, if p ∣ n then F n else 0 := by
    intro n
    rw [kataiOmega, Finset.card_filter]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p ∣ n <;> simp [hp]
  rw [Finset.sum_congr rfl fun n _ => hstep n, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_filter]
  exact sum_multiples_reindex p N (prime_of_mem_primesLe hp).pos F


/-! ### Obligation 3: peeling `f(pm) = f(p) f(m)`

The identity holds whenever `p ∤ m`, so the error is supported on the multiples of `p` inside
`(0, ⌊N/p⌋]`, of which there are `⌊N/p²⌋`.  Since `Σ_{p ≤ w} 1/p² ≤ Σ_{n ≥ 2} 1/n² ≤ 1`, the
total error is at most `2N` — an `O(N)` term, harmless after dividing by `N·L(w)`. -/

lemma sum_inv_sq_primes_le_one (w : ℕ) : ∑ p ∈ primesLe w, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
  classical
  have hfilter : (primesLe w).filter (fun p => 1 < p) = primesLe w := by
    refine Finset.filter_true_of_mem fun p hp => ?_
    exact (prime_of_mem_primesLe hp).one_lt
  have := sum_inv_sq_primes_tail_le 1 w le_rfl
  rw [hfilter] at this
  simpa using this

theorem kataiMultiplicativeError (w N : ℕ) (a f : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) :
    ‖(∑ p ∈ primesLe w, ∑ m ∈ Finset.Ioc 0 (N / p), f (p * m) * a (p * m))
      - ∑ p ∈ primesLe w, f p * ∑ m ∈ Finset.Ioc 0 (N / p), f m * a (p * m)‖
      ≤ 2 * (N : ℝ) := by
  classical
  have hdiff : (∑ p ∈ primesLe w, ∑ m ∈ Finset.Ioc 0 (N / p), f (p * m) * a (p * m))
      - ∑ p ∈ primesLe w, f p * ∑ m ∈ Finset.Ioc 0 (N / p), f m * a (p * m)
      = ∑ p ∈ primesLe w, ∑ m ∈ Finset.Ioc 0 (N / p),
          (f (p * m) - f p * f m) * a (p * m) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hdiff]
  -- pointwise: zero off the multiples of `p`, at most `2` on them
  have hpt : ∀ p ∈ primesLe w, ∀ m : ℕ,
      ‖(f (p * m) - f p * f m) * a (p * m)‖ ≤ if p ∣ m then (2 : ℝ) else 0 := by
    intro p hp m
    by_cases hdvd : p ∣ m
    · rw [if_pos hdvd, norm_mul]
      have h1 : ‖f (p * m) - f p * f m‖ ≤ 2 := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul]
        nlinarith [hf (p * m), hf p, hf m, norm_nonneg (f p), norm_nonneg (f m)]
      nlinarith [h1, ha (p * m), norm_nonneg (a (p * m)), norm_nonneg (f (p * m) - f p * f m)]
    · rw [if_neg hdvd]
      have hco : Nat.Coprime p m :=
        (Nat.Prime.coprime_iff_not_dvd (prime_of_mem_primesLe hp)).mpr hdvd
      rw [hmul p m hco, sub_self, zero_mul, norm_zero]
  calc ‖∑ p ∈ primesLe w, ∑ m ∈ Finset.Ioc 0 (N / p), (f (p * m) - f p * f m) * a (p * m)‖
      ≤ ∑ p ∈ primesLe w, ∑ m ∈ Finset.Ioc 0 (N / p),
          ‖(f (p * m) - f p * f m) * a (p * m)‖ :=
        le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => norm_sum_le _ _)
    _ ≤ ∑ p ∈ primesLe w, ∑ m ∈ Finset.Ioc 0 (N / p), (if p ∣ m then (2 : ℝ) else 0) :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun m _ => hpt p hp m
    _ = ∑ p ∈ primesLe w, 2 * ((((N / p) / p : ℕ)) : ℝ) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          Nat.Ioc_filter_dvd_card_eq_div]
        ring
    _ ≤ 2 * (N : ℝ) := by
        have hbound : ∀ p ∈ primesLe w, 2 * ((((N / p) / p : ℕ)) : ℝ)
            ≤ 2 * (N : ℝ) * ((1 : ℝ) / (p : ℝ) ^ 2) := by
          intro p hp
          have hppos : 0 < p := (prime_of_mem_primesLe hp).pos
          have hdd : (N / p) / p = N / (p * p) := Nat.div_div_eq_div_mul N p p
          have h1 : (((N / (p * p) : ℕ)) : ℝ) ≤ (N : ℝ) / ((p * p : ℕ) : ℝ) := Nat.cast_div_le
          have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
          rw [hdd]
          have h2 : (N : ℝ) / ((p * p : ℕ) : ℝ) = (N : ℝ) * ((1 : ℝ) / (p : ℝ) ^ 2) := by
            push_cast; rw [sq]; field_simp
          rw [h2] at h1
          linarith
        calc ∑ p ∈ primesLe w, 2 * ((((N / p) / p : ℕ)) : ℝ)
            ≤ ∑ p ∈ primesLe w, 2 * (N : ℝ) * ((1 : ℝ) / (p : ℝ) ^ 2) :=
              Finset.sum_le_sum hbound
          _ = 2 * (N : ℝ) * ∑ p ∈ primesLe w, (1 : ℝ) / (p : ℝ) ^ 2 := by
              rw [Finset.mul_sum]
          _ ≤ 2 * (N : ℝ) * 1 := by
              have hNnn : (0 : ℝ) ≤ 2 * (N : ℝ) := by positivity
              exact mul_le_mul_of_nonneg_left (sum_inv_sq_primes_le_one w) hNnn
          _ = 2 * (N : ℝ) := by ring

end NormalNumbers.CastingOut
