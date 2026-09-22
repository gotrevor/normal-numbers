import NormalNumbers.PrimeModelPhaseAlgebra
import NormalNumbers.PrimeModelRadicalState

/-!
# Prime model, assembly part B: factorising the window phase

`papers/prime-model-assembly-2026-09-22.md`, "Decomposition", "E1" and "Phase factorisation".

The window term `e(h · truncTailS S k n) = ∏_{j<k} z_j^{ω_S(n+j+1)}` with `z_j = e(h/4^{j+1})`.
Split `ω_S(m) = ω_{≤y}(m) + ω_{>y}(m)` at the sieve cutoff `y`:

* **E1** (`windowMean_sub_windowMeanLe_le`): dropping the primes above `y` costs at most
  `4k · recipSumIoc S y x + 2k²/x` in the window mean (each `p ∈ (y, x]` divides at most
  `x/p + 1 ≤ 2x/p` of the `n+j+1 < x + k`, and there are at most `k` primes in `(x, x+k]`).
* **Phase factorisation** (`phase_factorisation`): for `p ≤ k` the indicator `[p ∣ n+j+1]`
  depends only on `n mod k#`; for `k < p ≤ y` at most one `j` hits, recorded by `hitShift`.
  So the `y`-truncated term is `residuePhase (n mod k#) · statePhase (actualState k P n)`,
  `P` the `S`-primes in `(k, y]`.  This needs `k ≤ y`: otherwise `residuePhase` carries the
  `S`-primes in `(y, k]`, which `omegaLe` does not count, and the identity fails (e.g.
  `k = 2, y = 1, h = 1, n = 1, S = ⊤`: left side `1`, right side `i`).

Shift convention `n + j + 1` throughout, matching `truncTailS` and `hitShift`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.PhaseFactor

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.Radical NormalNumbers.PrimeModel.RadicalState
open NormalNumbers.PrimeModel.PhaseAlgebra

variable (S : ℕ → Prop) [DecidablePred S]

/-! ### Elementary `ePhase` algebra -/

private lemma ePhase_zero' : ePhase 0 = 1 := by
  simp [ePhase]

private lemma ePhase_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ePhase (∑ i ∈ s, f i) = ∏ i ∈ s, ePhase (f i) := by
  classical
  refine Finset.induction_on s (by simp [ePhase_zero']) ?_
  intro a t ha ih
  rw [Finset.sum_insert ha, ePhase_add, ih, Finset.prod_insert ha]

private lemma ePhase_nat_mul (w : ℕ) (t : ℝ) : ePhase ((w : ℝ) * t) = ePhase t ^ w := by
  induction w with
  | zero => simpa using ePhase_zero'
  | succ m ih =>
      have : ((m + 1 : ℕ) : ℝ) * t = (m : ℝ) * t + t := by push_cast; ring
      rw [this, ePhase_add, ih, pow_succ]

/-- `#{p ∈ S prime : p ≤ y, p ∣ m}`. -/
def omegaLe (y m : ℕ) : ℕ := ((m.primeFactors.filter S).filter (fun p => p ≤ y)).card

/-- `#{p ∈ S prime : y < p, p ∣ m}`. -/
def omegaGt (y m : ℕ) : ℕ := ((m.primeFactors.filter S).filter (fun p => y < p)).card

lemma omegaSN_eq_omegaLe_add_omegaGt (y m : ℕ) :
    omegaSN S m = omegaLe S y m + omegaGt S y m := by
  classical
  rw [omegaLe, omegaGt, omegaSN]
  have h := Finset.card_filter_add_card_filter_not
    (s := m.primeFactors.filter S) (p := fun p => p ≤ y)
  have h2 : (m.primeFactors.filter S).filter (fun p => ¬ p ≤ y)
      = (m.primeFactors.filter S).filter (fun p => y < p) := by
    apply Finset.filter_congr
    intro p _
    simp [not_le]
  rw [h2] at h
  omega

/-- The window term as a product of site phases raised to `ω_S`. -/
theorem window_term_eq (k : ℕ) (h : ℤ) (n : ℕ) :
    ePhase ((h : ℝ) * truncTailS S k n)
      = ∏ j : Fin k, zPhase h k j ^ omegaSN S (n + j.val + 1) := by
  have hR : ∏ j : Fin k, zPhase h k j ^ omegaSN S (n + j.val + 1)
      = ∏ j ∈ Finset.range k,
          ePhase ((h : ℝ) / (4 : ℝ) ^ (j + 1)) ^ omegaSN S (n + j + 1) := by
    rw [Finset.prod_range (fun j => ePhase ((h : ℝ) / (4 : ℝ) ^ (j + 1)) ^ omegaSN S (n + j + 1))]
    rfl
  rw [hR, truncTailS, Finset.mul_sum, ePhase_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [omegaS,
    show (h : ℝ) * ((omegaSN S (n + j + 1) : ℝ) / (4 : ℝ) ^ (j + 1))
      = (omegaSN S (n + j + 1) : ℝ) * ((h : ℝ) / (4 : ℝ) ^ (j + 1)) from by ring,
    ePhase_nat_mul]

/-- The window mean with the primes above `y` removed from every `ω_S`. -/
noncomputable def windowMeanLe (y k : ℕ) (h : ℤ) (x : ℕ) : ℂ :=
  prefixMean (fun n => ∏ j : Fin k, zPhase h k j ^ omegaLe S y (n + j.val + 1)) x

/-! ### Counting the primes above `y` -/

private lemma card_filter_dvd_shift_eq_one {p : ℕ} (hp : 0 < p) (j : ℕ) :
    ((Finset.range p).filter (fun c => p ∣ c + j + 1)).card = 1 := by
  classical
  have hmodj : ∀ c : ℕ, p ∣ c + j % p + 1 ↔ p ∣ c + j + 1 := by
    intro c
    have h1 : c + j % p + 1 ≡ c + j + 1 [MOD p] :=
      ((Nat.mod_modEq j p).add_left c).add_right 1
    rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
    exact ⟨fun hd => h1.symm.trans hd, fun hd => h1.trans hd⟩
  have hb := Radical.card_filter_shift p {j % p}
    (by intro t ht; rw [Finset.mem_singleton] at ht; subst ht; exact Nat.mod_lt _ hp)
  rw [Finset.card_singleton] at hb
  have hset : (Finset.range p).filter (fun c => ∃ t ∈ ({j % p} : Finset ℕ), p ∣ c + t + 1)
      = (Finset.range p).filter (fun c => p ∣ c + j + 1) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_singleton, exists_eq_left]
    exact and_congr_right fun _ => hmodj c
  rw [hset] at hb
  exact hb

private lemma card_filter_dvd_le {p : ℕ} (hp : 0 < p) (j x : ℕ) :
    ((((Finset.range x).filter (fun n => p ∣ n + j + 1)).card : ℝ)) ≤ (x : ℝ) / p + 1 := by
  classical
  have hper : ∀ n : ℕ, (p ∣ n + j + 1) ↔ (p ∣ n % p + j + 1) :=
    fun n => (Radical.dvd_mod_add_succ_iff p n j).symm
  have hbase := Radical.abs_card_filter_periodic_sub_le hp x (fun n => p ∣ n + j + 1) hper
  rw [card_filter_dvd_shift_eq_one hp j] at hbase
  have h2 := (abs_le.mp hbase).2
  push_cast at h2 ⊢
  rw [one_mul] at h2
  linarith

/-- For each shift `j < k`, the total number of `S`-prime factors above `y` of the `x` values
`n + j + 1` (`n < x`) is at most `2x ∑_{y<p≤x} 1/p + k`. -/
lemma sum_omegaGt_shift_le (y k x j : ℕ) (hj : j < k) :
    (∑ n ∈ Finset.range x, (omegaGt S y (n + j + 1) : ℝ))
      ≤ 2 * x * recipSumIoc S y x + k := by
  classical
  set T : Finset ℕ := (Finset.Ioc y (x + k)).filter (fun p => p.Prime ∧ S p) with hT
  -- rewrite `omegaGt` as a count over the fixed superset `T`
  have hcard : ∀ n ∈ Finset.range x,
      omegaGt S y (n + j + 1) = (T.filter (fun p => p ∣ n + j + 1)).card := by
    intro n hn
    have hnx : n < x := Finset.mem_range.mp hn
    rw [omegaGt]
    congr 1
    ext p
    simp only [hT, Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hp, hdvd, hne⟩, hSp⟩, hy⟩
      have hple : p ≤ n + j + 1 := Nat.le_of_dvd (by omega) hdvd
      exact ⟨⟨⟨hy, by omega⟩, hp, hSp⟩, hdvd⟩
    · rintro ⟨⟨⟨hy, hle⟩, hp, hSp⟩, hdvd⟩
      exact ⟨⟨⟨hp, hdvd, by omega⟩, hSp⟩, hy⟩
  rw [Finset.sum_congr rfl (fun n hn => by rw [hcard n hn])]
  -- swap the order of summation
  have hswapN : ∑ n ∈ Finset.range x, (T.filter (fun p => p ∣ n + j + 1)).card
      = ∑ p ∈ T, ((Finset.range x).filter (fun n => p ∣ n + j + 1)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hswap : ∑ n ∈ Finset.range x, ((T.filter (fun p => p ∣ n + j + 1)).card : ℝ)
      = ∑ p ∈ T, (((Finset.range x).filter (fun n => p ∣ n + j + 1)).card : ℝ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hswapN
  rw [hswap]
  set cnt : ℕ → ℕ := fun p => ((Finset.range x).filter (fun n => p ∣ n + j + 1)).card with hcnt
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    rw [hT, Finset.mem_filter] at hp
    exact hp.2.1
  -- split at `p ≤ x`
  rw [← Finset.sum_filter_add_sum_filter_not T (fun p => p ≤ x) (fun p => (cnt p : ℝ))]
  have hlow : ∑ p ∈ T.filter (fun p => p ≤ x), (cnt p : ℝ) ≤ 2 * x * recipSumIoc S y x := by
    have hset : T.filter (fun p => p ≤ x)
        = (Finset.Ioc y x).filter (fun p => p.Prime ∧ S p) := by
      ext p
      simp only [hT, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨⟨hy, -⟩, hp, hSp⟩, hle⟩; exact ⟨⟨hy, hle⟩, hp, hSp⟩
      · rintro ⟨⟨hy, hle⟩, hp, hSp⟩; exact ⟨⟨⟨hy, by omega⟩, hp, hSp⟩, hle⟩
    rw [hset, recipSumIoc, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hple : p ≤ x := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
    have hp2 : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hppos : (0 : ℝ) < p := by exact_mod_cast hp2.pos
    have hb := card_filter_dvd_le (p := p) hp2.pos j x
    have hxp : (1 : ℝ) ≤ (x : ℝ) / p := by
      rw [le_div_iff₀ hppos]
      simpa using (by exact_mod_cast hple : (p : ℝ) ≤ (x : ℝ))
    have : (cnt p : ℝ) ≤ 2 * ((x : ℝ) / p) := by rw [hcnt]; linarith
    calc (cnt p : ℝ) ≤ 2 * ((x : ℝ) / p) := this
      _ = 2 * (x : ℝ) * (1 / p) := by ring
  have hhigh : ∑ p ∈ T.filter (fun p => ¬ p ≤ x), (cnt p : ℝ) ≤ k := by
    have hone : ∀ p ∈ T.filter (fun p => ¬ p ≤ x), (cnt p : ℝ) ≤ 1 := by
      intro p hp
      have hpx : x < p := by
        have := (Finset.mem_filter.mp hp).2
        omega
      have hp2 : p.Prime := hTprime p (Finset.mem_filter.mp hp).1
      have hppos : (0 : ℝ) < p := by exact_mod_cast hp2.pos
      have hb := card_filter_dvd_le (p := p) hp2.pos j x
      have hlt : (x : ℝ) / p < 1 := by
        rw [div_lt_one hppos]; exact_mod_cast hpx
      have h2 : (cnt p : ℝ) < 2 := by rw [hcnt]; linarith
      have : cnt p < 2 := by exact_mod_cast h2
      have : cnt p ≤ 1 := by omega
      exact_mod_cast this
    have hcardle : (T.filter (fun p => ¬ p ≤ x)).card ≤ k := by
      have hsub : T.filter (fun p => ¬ p ≤ x) ⊆ Finset.Ioc x (x + k) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        have h1 := hp.1
        rw [hT, Finset.mem_filter, Finset.mem_Ioc] at h1
        rw [Finset.mem_Ioc]
        exact ⟨by omega, h1.1.2⟩
      have := Finset.card_le_card hsub
      simpa using this
    calc ∑ p ∈ T.filter (fun p => ¬ p ≤ x), (cnt p : ℝ)
        ≤ ∑ p ∈ T.filter (fun p => ¬ p ≤ x), (1 : ℝ) := Finset.sum_le_sum hone
      _ = ((T.filter (fun p => ¬ p ≤ x)).card : ℝ) := by simp
      _ ≤ (k : ℝ) := by exact_mod_cast hcardle
  linarith

/-- **E1.**  `‖W − W_y‖ ≤ 4k · ∑_{y<p≤x, p∈S} 1/p + 2k²/x`. -/
theorem windowMean_sub_windowMeanLe_le (y k : ℕ) (h : ℤ) (x : ℕ) (hx : 1 ≤ x) :
    ‖windowMeanS S k h x - windowMeanLe S y k h x‖
      ≤ 4 * k * recipSumIoc S y x + 2 * (k : ℝ) ^ 2 / x := by
  classical
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  -- pointwise bound
  have key : ∀ n : ℕ,
      ‖ePhase ((h : ℝ) * truncTailS S k n)
        - ∏ j : Fin k, zPhase h k j ^ omegaLe S y (n + j.val + 1)‖
        ≤ ∑ j : Fin k, 2 * (omegaGt S y (n + j.val + 1) : ℝ) := by
    intro n
    rw [window_term_eq]
    refine le_trans (norm_prod_sub_prod_le Finset.univ _ _ ?_ ?_) ?_
    · intro i _
      rw [norm_pow, norm_zPhase, one_pow]
    · intro i _
      rw [norm_pow, norm_zPhase, one_pow]
    · refine Finset.sum_le_sum fun i _ => ?_
      rw [omegaSN_eq_omegaLe_add_omegaGt S y]
      exact norm_pow_sub_pow_le _ (norm_zPhase h k i) _ _
  rw [windowMeanS, windowMeanLe, prefixMean, prefixMean, div_sub_div_same, norm_div,
    Complex.norm_natCast, ← Finset.sum_sub_distrib]
  have hnum : ‖∑ n ∈ Finset.range x,
      (ePhase ((h : ℝ) * truncTailS S k n)
        - ∏ j : Fin k, zPhase h k j ^ omegaLe S y (n + j.val + 1))‖
      ≤ 4 * k * recipSumIoc S y x * x + 2 * (k : ℝ) ^ 2 := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun n _ => key n) ?_
    rw [Finset.sum_comm]
    have hj : ∀ j : Fin k, ∑ n ∈ Finset.range x, 2 * (omegaGt S y (n + j.val + 1) : ℝ)
        ≤ 2 * (2 * x * recipSumIoc S y x + k) := by
      intro j
      rw [← Finset.mul_sum]
      have := sum_omegaGt_shift_le S y k x j.val j.isLt
      linarith
    refine le_trans (Finset.sum_le_sum fun j _ => hj j) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    nlinarith [sq_nonneg ((k : ℝ))]
  rw [div_le_iff₀ hx0]
  have hrw : (4 * k * recipSumIoc S y x + 2 * (k : ℝ) ^ 2 / x) * x
      = 4 * k * recipSumIoc S y x * x + 2 * (k : ℝ) ^ 2 := by
    field_simp
  rw [hrw]
  exact hnum

/-- The `S`-primes in `(k, y]`: the index set of the radical model. -/
def midPrimes (k y : ℕ) : Finset ℕ := (Finset.Iic y).filter (fun p => p.Prime ∧ S p ∧ k < p)

/-- The `S`-primes `≤ k`, handled by the residue modulo `k#`. -/
def smallPrimes (k : ℕ) : Finset ℕ := (Finset.Iic k).filter (fun p => p.Prime ∧ S p)

lemma mem_midPrimes {k y p : ℕ} : p ∈ midPrimes S k y ↔ p.Prime ∧ S p ∧ k < p ∧ p ≤ y := by
  simp only [midPrimes, Finset.mem_filter, Finset.mem_Iic]
  tauto

/-- The residue factor: the phase contribution of the `S`-primes `≤ k`, a function of `n mod k#`. -/
noncomputable def residuePhase (k : ℕ) (h : ℤ) (r : ℕ) : ℂ :=
  ∏ p ∈ smallPrimes S k, ∏ j : Fin k, if p ∣ r + j.val + 1 then zPhase h k j else 1

private lemma norm_prod_ite_zPhase_le (k : ℕ) (h : ℤ) (P : Fin k → Prop) [DecidablePred P] :
    ‖∏ j : Fin k, if P j then zPhase h k j else 1‖ ≤ 1 := by
  rw [norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ?_
  by_cases hi : P i <;> simp [hi]

lemma norm_residuePhase_le (k : ℕ) (h : ℤ) (r : ℕ) : ‖residuePhase S k h r‖ ≤ 1 := by
  rw [residuePhase, norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun p _ => ?_
  exact norm_prod_ite_zPhase_le k h _

/-- The state factor: `∏_{p ∈ P} localPhase (state p)`. -/
noncomputable def statePhase (k y : ℕ) (h : ℤ)
    (s : {q // q ∈ midPrimes S k y} → Option (Fin k)) : ℂ :=
  ∏ i, localPhase k (zPhase h k) (s i)

lemma norm_statePhase_le (k y : ℕ) (h : ℤ) (s : {q // q ∈ midPrimes S k y} → Option (Fin k)) :
    ‖statePhase S k y h s‖ ≤ 1 := by
  rw [statePhase, norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ?_
  cases hsi : s i with
  | none => simp [localPhase]
  | some t => simp [localPhase]

/-! ### The factorisation -/

private lemma prod_ite_eq_pow_card (A : Finset ℕ) (z : ℂ) (P : ℕ → Prop)
    [DecidablePred P] :
    ∏ p ∈ A, (if P p then z else 1) = z ^ (A.filter P).card := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

private lemma dvd_mod_of_dvd {p Q n a : ℕ} (hpQ : p ∣ Q) :
    p ∣ n % Q + a + 1 ↔ p ∣ n + a + 1 := by
  have h1 : n % Q + a + 1 ≡ n + a + 1 [MOD p] :=
    (((Nat.mod_modEq n Q).of_dvd hpQ).add_right a).add_right 1
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨fun hd => h1.symm.trans hd, fun hd => h1.trans hd⟩

/-- A modulus exceeding `k` hits at most one shift, so the indicator product over the window is
the local phase at the recorded hit. -/
private lemma prod_ite_eq_localPhase {k p n : ℕ} (hp : k < p) (z : Fin k → ℂ) :
    ∏ j : Fin k, (if p ∣ n + j.val + 1 then z j else 1) = localPhase k z (hitShift k p n) := by
  classical
  cases hs : hitShift k p n with
  | none =>
      have hnone := hitShift_eq_none_iff.mp hs
      simp only [localPhase]
      exact Finset.prod_eq_one fun j _ => if_neg (hnone j)
  | some t =>
      have ht := (hitShift_eq_some_iff hp t).mp hs
      have hsingle : ∏ j : Fin k, (if p ∣ n + j.val + 1 then z j else 1)
          = if p ∣ n + t.val + 1 then z t else 1 :=
        Finset.prod_eq_single t
          (fun j _ hjt => if_neg (fun hd => hjt (hit_unique hp hd ht)))
          (fun hmem => absurd (Finset.mem_univ t) hmem)
      simp only [localPhase]
      rw [hsingle, if_pos ht]

/-- **Phase factorisation.**  The `y`-truncated window term is the residue factor at `n mod k#`
times the state factor at the actual radical state. -/
theorem phase_factorisation (k y : ℕ) (hk : 1 ≤ k) (hky : k ≤ y) (h : ℤ) (n : ℕ) :
    ∏ j : Fin k, zPhase h k j ^ omegaLe S y (n + j.val + 1)
      = residuePhase S k h (n % primorial k)
          * statePhase S k y h (actualState k (midPrimes S k y) n) := by
  classical
  -- split `omegaLe` at `k`
  have hsplit : ∀ j : Fin k,
      omegaLe S y (n + j.val + 1)
        = ((smallPrimes S k).filter (fun p => p ∣ n + j.val + 1)).card
          + ((midPrimes S k y).filter (fun p => p ∣ n + j.val + 1)).card := by
    intro j
    rw [omegaLe]
    have hunion : ((n + j.val + 1).primeFactors.filter S).filter (fun p => p ≤ y)
        = ((smallPrimes S k).filter (fun p => p ∣ n + j.val + 1))
          ∪ ((midPrimes S k y).filter (fun p => p ∣ n + j.val + 1)) := by
      ext p
      simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_union, smallPrimes,
        midPrimes, Finset.mem_Iic]
      constructor
      · rintro ⟨⟨⟨hp, hdvd, -⟩, hSp⟩, hpy⟩
        by_cases hpk : p ≤ k
        · exact Or.inl ⟨⟨hpk, hp, hSp⟩, hdvd⟩
        · exact Or.inr ⟨⟨hpy, hp, hSp, by omega⟩, hdvd⟩
      · rintro (⟨⟨hpk, hp, hSp⟩, hdvd⟩ | ⟨⟨hpy, hp, hSp, hkp⟩, hdvd⟩)
        · exact ⟨⟨⟨hp, hdvd, by omega⟩, hSp⟩, by omega⟩
        · exact ⟨⟨⟨hp, hdvd, by omega⟩, hSp⟩, hpy⟩
    rw [hunion, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_filter, smallPrimes, Finset.mem_filter, Finset.mem_Iic] at hp
    rw [Finset.mem_filter, midPrimes, Finset.mem_filter, Finset.mem_Iic] at hp'
    omega
  have hprod : ∏ j : Fin k, zPhase h k j ^ omegaLe S y (n + j.val + 1)
      = (∏ j : Fin k, zPhase h k j ^ ((smallPrimes S k).filter (fun p => p ∣ n + j.val + 1)).card)
        * ∏ j : Fin k,
            zPhase h k j ^ ((midPrimes S k y).filter (fun p => p ∣ n + j.val + 1)).card := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hsplit j, pow_add]
  rw [hprod]
  congr 1
  · -- the small primes: residue factor
    rw [residuePhase, Finset.prod_comm]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [prod_ite_eq_pow_card]
    congr 2
    apply Finset.filter_congr
    intro p hp
    have hpQ : p ∣ primorial k := by
      rw [smallPrimes, Finset.mem_filter, Finset.mem_Iic] at hp
      exact (Nat.Prime.dvd_primorial_iff hp.2.1).mpr hp.1
    simpa using (dvd_mod_of_dvd (n := n) (a := j.val) hpQ).symm
  · -- the mid primes: state factor
    rw [statePhase]
    have hRHS : (∏ i : {q // q ∈ midPrimes S k y},
        localPhase k (zPhase h k) (actualState k (midPrimes S k y) n i))
        = ∏ p ∈ midPrimes S k y, localPhase k (zPhase h k) (hitShift k p n) :=
      Finset.prod_coe_sort (midPrimes S k y)
        (fun p => localPhase k (zPhase h k) (hitShift k p n))
    rw [hRHS]
    have hL : ∀ j : Fin k,
        zPhase h k j ^ ((midPrimes S k y).filter (fun p => p ∣ n + j.val + 1)).card
          = ∏ p ∈ midPrimes S k y, (if p ∣ n + j.val + 1 then zPhase h k j else 1) :=
      fun j => (prod_ite_eq_pow_card _ _ _).symm
    rw [Finset.prod_congr rfl (fun j (_ : j ∈ Finset.univ) => hL j), Finset.prod_comm]
    refine Finset.prod_congr rfl fun p hp => ?_
    exact prod_ite_eq_localPhase ((mem_midPrimes S).mp hp).2.2.1 (zPhase h k)

/-- The `S`-reciprocal sum up to `y` is the `midPrimes` sum plus at most `k` (one term `≤ 1/2`
per small prime, and there are at most `k` of them). -/
theorem recipSumLe_le_sum_midPrimes (k y : ℕ) :
    recipSumLe S y ≤ (∑ i : {q // q ∈ midPrimes S k y}, (1 : ℝ) / ((i : ℕ) : ℝ)) + k := by
  classical
  have hmid : (∑ i : {q // q ∈ midPrimes S k y}, (1 : ℝ) / ((i : ℕ) : ℝ))
      = ∑ p ∈ midPrimes S k y, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_coe_sort (midPrimes S k y) (fun p => (1 : ℝ) / (p : ℝ))
  rw [hmid, recipSumLe]
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Iic y).filter (fun p => p.Prime ∧ S p))
    (fun p => k < p) (fun p => (1 : ℝ) / p)]
  have heq : ((Finset.Iic y).filter (fun p => p.Prime ∧ S p)).filter (fun p => k < p)
      = midPrimes S k y := by
    ext p
    simp only [midPrimes, Finset.mem_filter, Finset.mem_Iic]
    tauto
  rw [heq]
  have hsmall : ∑ p ∈ ((Finset.Iic y).filter (fun p => p.Prime ∧ S p)).filter
      (fun p => ¬ k < p), (1 : ℝ) / p ≤ k := by
    set A := ((Finset.Iic y).filter (fun p => p.Prime ∧ S p)).filter (fun p => ¬ k < p) with hA
    have hsub : A ⊆ Finset.Icc 2 k := by
      intro p hp
      rw [hA, Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.1.2.1.two_le, by omega⟩
    have hbound : ∀ p ∈ A, (1 : ℝ) / p ≤ 1 / 2 := by
      intro p hp
      rw [hA, Finset.mem_filter, Finset.mem_filter] at hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.2.1.two_le
      apply one_div_le_one_div_of_le (by norm_num) h2
    have hcard : (A.card : ℝ) ≤ k := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      have h2 : A.card ≤ k := by omega
      exact_mod_cast h2
    calc ∑ p ∈ A, (1 : ℝ) / p ≤ ∑ p ∈ A, (1 : ℝ) / 2 := Finset.sum_le_sum hbound
      _ = (A.card : ℝ) * (1 / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) * (1 / 2) := by
          have : (0:ℝ) ≤ 1/2 := by norm_num
          nlinarith [hcard]
      _ ≤ (k : ℝ) := by
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
  linarith

end NormalNumbers.PrimeModel.PhaseFactor
