import NormalNumbers.PrimeLambertAnalytic

/-!
# Exact pieces of the analytic chain: frozen bad primes and the binary-tail bound

* `badPrimeFrozen_of_residue`: if the sample is frozen modulo every bad prime
  (`p ∣ n − n'`), then `BadPrimeFrozen` holds.  Exact.
* `phaseSum_sub_truncPhase`: the truncation error `F − F_J` is exactly `phaseSum c J n`
  (the tail beyond `J`).
* `omegaR_le_log`: `ω(m) ≤ log₂ m`; `omegaR_mul_le`: `ω(dm) ≤ ω(d) + ω(m)`.
* `abs_atomTail_le`: on the progression `n = d k + s`,
  `|∑_{j>J} 2^{-j} ω(d(k+j))| ≤ (ω(d) + log₂(k+1) + J + 1) / 2^J`.
* `abs_truncation_error_le`: hence
  `|F − F_J| ≤ ∑_a |c a| (ω(d_a) + log₂(k_a+1) + J + 1) / 2^J`
  — draft (20) in exact form; `TailTruncation` follows from any parameter choice making the
  right side tend to zero uniformly on the sample (`tailTruncation_of_bound`).
-/

open Filter Topology Finset
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-! ### Frozen bad primes -/

lemma primePart_congr (c : TConfig) (K J p : ℕ) (n n' : ℤ) (h : (p : ℤ) ∣ n - n') :
    primePart c K J p n = primePart c K J p n' := by
  unfold primePart
  refine Finsupp.sum_congr (fun a _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2 ↔ (p : ℤ) ∣ n' + ((i : ℤ) + 1) * a.1 - a.2 := by
    constructor
    · intro hd
      have := dvd_sub hd h
      rwa [show n + ((i : ℤ) + 1) * a.1 - a.2 - (n - n') = n' + ((i : ℤ) + 1) * a.1 - a.2 by ring]
        at this
    · intro hd
      have := dvd_add hd h
      rwa [show n' + ((i : ℤ) + 1) * a.1 - a.2 + (n - n') = n + ((i : ℤ) + 1) * a.1 - a.2 by ring]
        at this
  simp only [this]

/-- **Exact freezing**: a sample frozen modulo every bad prime has constant bad-class sum. -/
theorem badPrimeFrozen_of_residue {q : ℤ} (C : Chain q)
    (h : ∀ N, ∀ n ∈ (C.D N).P, ∀ n' ∈ (C.D N).P, ∀ p ∈ (C.S N).bad, (p : ℤ) ∣ n - n') :
    BadPrimeFrozen C := by
  intro N n hn n' hn'
  unfold classSum
  exact Finset.sum_congr rfl (fun p hp => primePart_congr _ _ _ p n n' (h N n hn n' hn' p hp))

/-! ### The truncation error is the tail beyond `J` -/

lemma atomTail_sub_finite {d : ℕ} {s : ℤ} {n : ℤ} {k : ℕ} (hd : d ≠ 0) (hn : n = (d : ℤ) * k + s)
    (K J : ℕ) (hKJ : K ≤ J) :
    atomTail K (d, s) n - ∑ i ∈ Ico K J, omegaZ (n + ((i : ℤ) + 1) * d - s) / 2 ^ (i + 1)
      = atomTail J (d, s) n := by
  have : ∀ i : ℕ, omegaZ (n + ((i : ℤ) + 1) * d - s) / 2 ^ (i + 1)
      = omegaR (d * (k + i + 1)) / 2 ^ (i + 1) := by
    intro i
    rw [arg_eq hn i, omegaZ_natCast]
  rw [Finset.sum_congr rfl (fun i _ => this i)]
  rw [atomTail_eq hd hn K, atomTail_eq hd hn J, Finset.sum_Ico_eq_sub _ hKJ]
  ring

/-- `F − F_J = phaseSum c J n` on the progression. -/
theorem phaseSum_sub_truncPhase (c : TConfig) (K J : ℕ) (hKJ : K ≤ J) (k : ℤ → ℕ × ℤ → ℕ)
    (n : ℤ) (hn : OnProgression c k n) :
    phaseSum c K n - truncPhase c K J n = phaseSum c J n := by
  unfold phaseSum truncPhase
  rw [← Finsupp.sum_sub]
  refine Finsupp.sum_congr (fun a ha => ?_)
  rw [← mul_sub]
  congr 1
  exact atomTail_sub_finite (hn.pos a ha) (hn.quot a ha) K J hKJ

/-! ### `ω` bounds -/

lemma card_primeFactors_le_log (m : ℕ) (hm : m ≠ 0) : m.primeFactors.card ≤ Nat.log 2 m := by
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  calc 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

lemma omegaR_le_log (m : ℕ) : omegaR m ≤ Nat.log 2 m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [omegaR_eq]
  · rw [omegaR_eq]; exact_mod_cast card_primeFactors_le_log m hm

lemma omegaR_mul_le (d m : ℕ) : omegaR (d * m) ≤ omegaR d + omegaR m := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [omegaR_eq]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [omegaR_eq]
  simp only [omegaR_eq]
  rw [Nat.primeFactors_mul hd hm]
  exact_mod_cast Finset.card_union_le _ _

/-- `log₂(k + i + 1) ≤ log₂(k + 1) + i`. -/
lemma log_add_le (k i : ℕ) : Nat.log 2 (k + i + 1) ≤ Nat.log 2 (k + 1) + i := by
  have h1 : k + i + 1 < 2 ^ (Nat.log 2 (k + 1) + 1 + i) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (k + 1)
    have h2 : (1 : ℕ) + i ≤ 2 ^ i := by
      have := Nat.lt_two_pow_self (n := i); omega
    have h3 : 1 ≤ 2 ^ (Nat.log 2 (k + 1) + 1) := Nat.one_le_two_pow
    calc k + i + 1 = (k + 1) + i := by ring
      _ < 2 ^ (Nat.log 2 (k + 1) + 1) + i := by omega
      _ ≤ 2 ^ (Nat.log 2 (k + 1) + 1) * 2 ^ i := by
          calc 2 ^ (Nat.log 2 (k + 1) + 1) + i
              ≤ 2 ^ (Nat.log 2 (k + 1) + 1) + 2 ^ (Nat.log 2 (k + 1) + 1) * i :=
                Nat.add_le_add_left (Nat.le_mul_of_pos_left i (by omega)) _
            _ = 2 ^ (Nat.log 2 (k + 1) + 1) * (1 + i) := by ring
            _ ≤ 2 ^ (Nat.log 2 (k + 1) + 1) * 2 ^ i := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (Nat.log 2 (k + 1) + 1 + i) := by rw [pow_add _ (Nat.log 2 (k + 1) + 1) i]
  have := Nat.log_lt_of_lt_pow (by omega) h1
  omega

/-! ### Geometric tails -/

lemma tsum_shift_geom (J : ℕ) : ∑' i : ℕ, (1 : ℝ) / 2 ^ (i + J + 1) = 1 / 2 ^ J := by
  have : ∀ i : ℕ, (1 : ℝ) / 2 ^ (i + J + 1) = (1 / 2 ^ J) * (1 / 2 ^ (i + 1)) := by
    intro i; rw [show i + J + 1 = J + (i + 1) by ring, pow_add]; field_simp
  rw [tsum_congr this, tsum_mul_left, tsum_geom_shift, mul_one]

lemma summable_i_geom : Summable (fun i : ℕ => (i : ℝ) / 2 ^ (i + 1)) := by
  have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1/2 : ℝ)) (by
    rw [Real.norm_eq_abs]; norm_num)
  refine (this.mul_left (1/2)).congr (fun i => ?_)
  rw [pow_one, pow_succ, one_div_pow]; field_simp

lemma tsum_i_geom : ∑' i : ℕ, (i : ℝ) / 2 ^ (i + 1) = 1 := by
  have h := tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := (1/2 : ℝ)) (by
    rw [Real.norm_eq_abs]; norm_num)
  have : ∀ i : ℕ, (i : ℝ) / 2 ^ (i + 1) = (1 / 2) * ((i : ℝ) * (1 / 2) ^ i) := by
    intro i; rw [pow_succ, one_div_pow]; field_simp
  rw [tsum_congr this, tsum_mul_left, h]; norm_num

/-- The majorant tail `∑_{i ≥ J} (A + i) / 2^{i+1} = (A + J + 1) / 2^J`. -/
lemma tsum_majorant (A : ℝ) (J : ℕ) :
    ∑' i : ℕ, (if J ≤ i then (A + i) / 2 ^ (i + 1) else 0) = (A + J + 1) / 2 ^ J := by
  have hs : Summable (fun i : ℕ => (if J ≤ i then (A + i) / 2 ^ (i + 1) else 0)) := by
    have h1 : Summable (fun i : ℕ => (A + i) / 2 ^ (i + 1)) := by
      have := (summable_geom_shift.mul_left A).add summable_i_geom
      refine this.congr (fun i => ?_); ring
    refine h1.norm.of_norm_bounded (fun i => ?_)
    split_ifs <;> simp <;> positivity
  rw [← hs.sum_add_tsum_nat_add J, Finset.sum_eq_zero (fun i hi => by
    rw [Finset.mem_range] at hi; simp [not_le.mpr hi]), zero_add]
  have : ∀ i : ℕ, (if J ≤ i + J then (A + ((i + J : ℕ) : ℝ)) / 2 ^ (i + J + 1) else 0)
      = (A + J) * (1 / 2 ^ (i + J + 1)) + (1 / 2 ^ J) * ((i : ℝ) / 2 ^ (i + 1)) := by
    intro i
    rw [if_pos (by omega), show i + J + 1 = J + (i + 1) by ring, pow_add]
    push_cast; field_simp; ring
  have hs1 : Summable (fun i : ℕ => (A + J) * (1 / 2 ^ (i + J + 1) : ℝ)) := by
    have h0 : Summable (fun i : ℕ => (1 : ℝ) / 2 ^ (i + J + 1)) := by
      have := (summable_nat_add_iff J).mpr summable_geom_shift
      refine this.congr (fun i => ?_)
      simp only
    exact h0.mul_left _
  rw [tsum_congr this, Summable.tsum_add hs1 (summable_i_geom.mul_left _), tsum_mul_left,
    tsum_mul_left, tsum_shift_geom, tsum_i_geom]
  field_simp

/-- **Exact tail bound** for one atom on the progression. -/
theorem abs_atomTail_le {d : ℕ} {s : ℤ} {n : ℤ} {k : ℕ} (_hd : d ≠ 0) (hn : n = (d : ℤ) * k + s)
    (J : ℕ) :
    |atomTail J (d, s) n| ≤ (omegaR d + Nat.log 2 (k + 1) + J + 1) / 2 ^ J := by
  have hterm : ∀ i : ℕ, (if J ≤ i then omegaZ (n + ((i : ℤ) + 1) * d - s) / 2 ^ (i + 1) else 0)
      = (if J ≤ i then omegaR (d * (k + i + 1)) / 2 ^ (i + 1) else 0) := by
    intro i; rw [arg_eq hn i, omegaZ_natCast]
  have hnn : ∀ i : ℕ, 0 ≤ (if J ≤ i then omegaR (d * (k + i + 1)) / 2 ^ (i + 1) else 0) := by
    intro i; split_ifs
    · have := omegaR_nonneg (d * (k + i + 1)); positivity
    · exact le_rfl
  have hle : ∀ i : ℕ, (if J ≤ i then omegaR (d * (k + i + 1)) / 2 ^ (i + 1) else 0)
      ≤ (if J ≤ i then ((omegaR d + Nat.log 2 (k + 1)) + i) / 2 ^ (i + 1) else 0) := by
    intro i; split_ifs
    · gcongr
      calc omegaR (d * (k + i + 1)) ≤ omegaR d + omegaR (k + i + 1) := omegaR_mul_le _ _
        _ ≤ omegaR d + Nat.log 2 (k + i + 1) := by gcongr; exact omegaR_le_log _
        _ ≤ omegaR d + (Nat.log 2 (k + 1) + i) := by gcongr; exact_mod_cast log_add_le k i
        _ = omegaR d + Nat.log 2 (k + 1) + i := by ring
    · exact le_rfl
  have hsum2 : Summable (fun i : ℕ =>
      (if J ≤ i then ((omegaR d + Nat.log 2 (k + 1)) + i) / 2 ^ (i + 1) else 0)) := by
    have h1 : Summable (fun i : ℕ => ((omegaR d + Nat.log 2 (k + 1)) + i) / 2 ^ (i + 1)) := by
      have := (summable_geom_shift.mul_left (omegaR d + Nat.log 2 (k + 1))).add summable_i_geom
      refine this.congr (fun i => ?_); ring
    refine h1.norm.of_norm_bounded (fun i => ?_)
    split_ifs <;> simp <;> positivity
  unfold atomTail
  rw [tsum_congr hterm, abs_of_nonneg (tsum_nonneg hnn)]
  calc ∑' i : ℕ, (if J ≤ i then omegaR (d * (k + i + 1)) / 2 ^ (i + 1) else 0)
      ≤ ∑' i : ℕ, (if J ≤ i then ((omegaR d + Nat.log 2 (k + 1)) + i) / 2 ^ (i + 1) else 0) :=
        Summable.tsum_le_tsum hle
          (Summable.of_nonneg_of_le hnn hle hsum2) hsum2
    _ = (omegaR d + Nat.log 2 (k + 1) + J + 1) / 2 ^ J := by
        rw [tsum_majorant]

/-- **Draft (20), exact form**: the truncation error on the progression. -/
theorem abs_truncation_error_le (c : TConfig) (K J : ℕ) (hKJ : K ≤ J) (k : ℤ → ℕ × ℤ → ℕ)
    (n : ℤ) (hn : OnProgression c k n) :
    |phaseSum c K n - truncPhase c K J n|
      ≤ (∑ a ∈ c.support, |(c a : ℝ)| * (omegaR a.1 + Nat.log 2 (k n a + 1) + J + 1)) / 2 ^ J := by
  rw [phaseSum_sub_truncPhase c K J hKJ k n hn, phaseSum, Finsupp.sum, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a ha => ?_))
  rw [abs_mul, mul_div_assoc]
  gcongr
  exact abs_atomTail_le (hn.pos a ha) (hn.quot a ha) J

/-- `TailTruncation` follows from any bound tending to zero on the sample. -/
theorem tailTruncation_of_bound {q : ℤ} (C : Chain q) (hKJ : ∀ N, C.K N ≤ (C.S N).J)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ N, ∀ n ∈ (C.D N).P,
      (∑ a ∈ (C.c N).support, |((C.c N) a : ℝ)| *
        (omegaR a.1 + Nat.log 2 ((C.D N).k n a + 1) + (C.S N).J + 1)) / 2 ^ (C.S N).J ≤ ε N) :
    TailTruncation C := by
  refine ⟨ε, hε, fun N n hn => ?_⟩
  exact (abs_truncation_error_le _ _ _ (hKJ N) _ n ((C.D N).onProg n hn)).trans (hb N n hn)

end NormalNumbers.PrimeLambert
