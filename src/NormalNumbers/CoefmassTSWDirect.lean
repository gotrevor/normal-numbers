/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CPrimeSiteFactorization
import ErdosProblems.Erdos67b.PrimeEstimates

/-!
# `TwistedSiegelWalfisz` from prime Siegel–Walfisz: the largest-prime transfer

The paper proof is `docs/notes/tsw-y-uniformity-2026-10-11.md`, "Primary route" (Astra
2026-10-11, checked by Opus).  It needs no cutoff-free TSW and no Selberg–Delange input.

* `Literature.PrimeCharacterSW`: Siegel–Walfisz for prime sums of a nonprincipal character, at
  moduli up to a power of `log X`.  Classical, with an ineffective constant.
* `largestPrimeTransfer`: an elementary lemma.  Let `f` be multiplicative on coprime arguments with
  `|f| ≤ 1`, and suppose every prime interval above `W` has a small sum.  Then `|Σ_{n≤X} f(n)|` is
  at most the `W`-smooth count, plus `X/(W−1)` for the `n` whose largest prime is repeated, plus
  the harmonic sum of the interval bounds.
* `smoothCount_rankin`: an elementary lemma.  At `W = ⌈exp √log X⌉`, the `W`-smooth integers up to
  `X` are fewer than `X/(log X)^A`, by Rankin and the proved Mertens bound of the
  `Erdos67b.PrimeEstimates` dependency.
* `uniformZTSW_of_primeSW`: the assembly.  On primes,
  `f(p) = χ(p)[1 + (z−1)·1_{p≡a (q₀)}·1_{p≤y}]`.  Expanding the residue-class indicator in
  characters mod `q₀` turns each interval sum into prime sums of the nonprincipal `χψ` mod `r q₀`.
  This gives a bound uniform in `z`, which is stronger than frozen `TwistedSiegelWalfisz`.
* `twistedSiegelWalfisz_of_primeSW`: the frozen target, from SW alone.

The frozen `twistedSiegelWalfisz` (no hypotheses) is unchanged.
-/

namespace NormalNumbers.Literature

/-- **Siegel–Walfisz for prime character sums** (classical; ineffective constant via Siegel's
theorem).  For every `A, B` there is `C` such that every nonprincipal `χ` mod `r ≤ (log X)^B` has
`|Σ_{p≤X} χ(p)| ≤ C X/(log X)^A`.  This is the Siegel–Walfisz theorem for `ψ(x, χ)`, moved to the
unweighted prime sum by partial summation.  ⚠️ No textbook theorem number has been checked yet;
pin one before this is upstreamed. -/
def PrimeCharacterSW : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ C : ℝ, 0 < C ∧
    ∀ X r : ℕ, 3 ≤ X → 1 ≤ r → (r : ℝ) ≤ Real.log X ^ B →
    ∀ χ : DirichletCharacter ℂ r, χ ≠ 1 →
      ‖∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, χ (p : ZMod r)‖ ≤ C * X / Real.log X ^ A

end NormalNumbers.Literature

namespace NormalNumbers.PrimeModel.SiteFactor

open NormalNumbers.Literature Finset

/-- `Ψ(X, W)`: the integers in `[1, X]` all of whose prime factors are at most `W` (`1` included). -/
noncomputable def smoothCount (X W : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n => ∀ p ∈ n.primeFactors, p ≤ W)).card

/-- The largest prime factor `P⁺(n)` (`0` for `n ≤ 1`). -/
def topPrime (n : ℕ) : ℕ := n.primeFactors.sup id

lemma le_topPrime {n p : ℕ} (h : p ∈ n.primeFactors) : p ≤ topPrime n := Finset.le_sup (f := id) h

lemma topPrime_mem {n : ℕ} (h : n.primeFactors.Nonempty) : topPrime n ∈ n.primeFactors := by
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_sup _ h id
  simpa [topPrime, he] using hp

lemma topPrime_mul {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hlt : topPrime m < p) : topPrime (m * p) = p := by
  unfold topPrime at *
  rw [Nat.primeFactors_mul hm hp.ne_zero, hp.primeFactors, Finset.sup_union,
    Finset.sup_singleton]
  simp [le_of_lt hlt]

lemma sum_inv_sq_le_tsw (W N : ℕ) (hW : 1 ≤ W) :
    ∑ k ∈ Ioc W (W + N), (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / W - 1 / (W + N : ℕ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show W + (N + 1) = (W + N) + 1 by ring, Finset.sum_Ioc_succ_top (by omega)]
    have h1 : (1 : ℝ) ≤ (W + N : ℕ) := by exact_mod_cast (by omega : 1 ≤ W + N)
    have key : (1 : ℝ) / ((W + N + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (W + N : ℕ) - 1 / (W + N + 1 : ℕ) := by
      push_cast at h1 ⊢
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma card_sq_dvd_tsw (X k : ℕ) : ((Icc 1 X).filter (fun n => k ^ 2 ∣ n)).card = X / k ^ 2 := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  rfl

lemma harmonic_Icc_le (X : ℕ) : ∑ m ∈ Icc 1 X, (1 : ℝ) / m ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log X
  have : (harmonic X : ℝ) = ∑ m ∈ Icc 1 X, (1 : ℝ) / m := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp
  linarith

/-- The largest-prime transfer, as a statement. -/
def LargestPrimeTransfer : Prop :=
  ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) →
    (∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) →
    ∀ X W : ℕ, 3 ≤ X → 2 ≤ W → W ≤ X → ∀ η : ℝ, 0 ≤ η →
      (∀ U V : ℕ, W ≤ U → U ≤ V → V ≤ X →
        ‖∑ p ∈ (Finset.Ioc U V).filter Nat.Prime, f p‖ ≤ η * V) →
      ‖∑ n ∈ Finset.Icc 1 X, f n‖ ≤
        (smoothCount X W : ℝ) + X / ((W : ℝ) - 1) + η * X * (1 + Real.log X)

/-- Elementary; no analytic input.  Paper proof: split `n ≤ X` by its largest prime `p`.
- `p ≤ W`: `n` is counted by `smoothCount X W`.
- `p > W` and `p² ∣ n`: at most `X Σ_{p>W} p⁻² ≤ X/(W−1)` such `n`.
- Otherwise `n = m p` uniquely, with `p > max(W, P⁺(m))` and `Coprime m p`.  That block equals
  `Σ_{m ≤ X/W} f(m) Σ_{max(W,P⁺(m)) < p ≤ X/m} f(p)`.  Empty intervals are dropped; each remaining
  interval is bounded by `η X/m`, and `Σ_{m≤X} 1/m ≤ 1 + log X`.
The partition was checked exactly (`X ≤ 2500`); dropping the repeated-prime block breaks it. -/
theorem largestPrimeTransfer : LargestPrimeTransfer := by
  intro f hf1 hmul X W hX hW hWX η hη hint
  set P : ℕ → Prop := fun n => ∀ p ∈ n.primeFactors, p ≤ W with hPdef
  have hnP : ∀ n, ¬ P n → W < topPrime n ∧ topPrime n ∈ n.primeFactors := by
    intro n hn
    simp only [hPdef, not_forall, not_le] at hn
    obtain ⟨p, hp, hpW⟩ := hn
    exact ⟨lt_of_lt_of_le hpW (le_topPrime hp), topPrime_mem ⟨p, hp⟩⟩
  rw [← sum_filter_add_sum_filter_not (Icc 1 X) P,
    ← sum_filter_add_sum_filter_not ((Icc 1 X).filter (fun n => ¬ P n)) (fun n => topPrime n ^ 2 ∣ n)]
  -- smooth block
  have h1 : ‖∑ n ∈ (Icc 1 X).filter P, f n‖ ≤ smoothCount X W := by
    refine (norm_sum_le _ _).trans ?_
    unfold smoothCount
    refine (sum_le_sum (fun n _ => hf1 n)).trans ?_
    simp only [sum_const, nsmul_eq_mul, mul_one]
    exact le_rfl
  -- repeated topPrime prime
  have h2 : ‖∑ n ∈ ((Icc 1 X).filter (fun n => ¬ P n)).filter (fun n => topPrime n ^ 2 ∣ n), f n‖
      ≤ X / ((W : ℝ) - 1) := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum (fun n _ => hf1 n)).trans ?_
    rw [sum_const, nsmul_one]
    have hsub : ((Icc 1 X).filter (fun n => ¬ P n)).filter (fun n => topPrime n ^ 2 ∣ n) ⊆
        (Ioc W X).biUnion (fun k => (Icc 1 X).filter (fun n => k ^ 2 ∣ n)) := by
      intro n hn
      simp only [mem_filter, mem_Icc] at hn
      obtain ⟨⟨⟨hn1, hnX⟩, hP⟩, hd⟩ := hn
      obtain ⟨hWt, hmem⟩ := hnP n hP
      simp only [mem_biUnion, mem_Ioc, mem_filter, mem_Icc]
      exact ⟨topPrime n, ⟨hWt, (Nat.le_of_mem_primeFactors hmem).trans hnX⟩, ⟨hn1, hnX⟩, hd⟩
    have hc := (card_le_card hsub).trans card_biUnion_le
    simp only [card_sq_dvd_tsw] at hc
    have hc' : ((((Icc 1 X).filter (fun n => ¬ P n)).filter (fun n => topPrime n ^ 2 ∣ n)).card : ℝ)
        ≤ ∑ k ∈ Ioc W X, (X : ℝ) * (1 / (k : ℝ) ^ 2) := by
      refine (Nat.cast_le.mpr hc).trans ?_
      push_cast
      refine sum_le_sum (fun k hk => ?_)
      rw [mul_one_div]
      have := Nat.cast_div_le (α := ℝ) (m := X) (n := k ^ 2)
      push_cast at this
      exact this
    rw [← mul_sum] at hc'
    have hs := sum_inv_sq_le_tsw W (X - W) (by omega)
    rw [show W + (X - W) = X by omega] at hs
    have hW1 : (1 : ℝ) < W := by exact_mod_cast (by omega : 1 < W)
    have hX0 : (0 : ℝ) ≤ X := by positivity
    have : (1 : ℝ) / W - 1 / (X : ℕ) ≤ 1 / ((W : ℝ) - 1) := by
      have : (0 : ℝ) ≤ 1 / (X : ℕ) := by positivity
      have : (1 : ℝ) / W ≤ 1 / ((W : ℝ) - 1) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      linarith
    calc _ ≤ _ := hc'
      _ ≤ (X : ℝ) * (1 / ((W : ℝ) - 1)) := mul_le_mul_of_nonneg_left (hs.trans this) hX0
      _ = _ := by ring
  -- simple topPrime prime
  set T := ((Icc 1 X).filter (fun n => ¬ P n)).filter (fun n => ¬ topPrime n ^ 2 ∣ n) with hT
  have hTmem : ∀ n ∈ T, 1 ≤ n ∧ n ≤ X ∧ W < topPrime n ∧ topPrime n ∈ n.primeFactors ∧
      ¬ topPrime n ^ 2 ∣ n := by
    intro n hn
    simp only [hT, mem_filter, mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnX⟩, hP⟩, hd⟩ := hn
    exact ⟨hn1, hnX, (hnP n hP).1, (hnP n hP).2, hd⟩
  have hmaps : ∀ n ∈ T, n / topPrime n ∈ Icc 1 X := by
    intro n hn
    obtain ⟨hn1, hnX, -, hmem, -⟩ := hTmem n hn
    have hp := Nat.prime_of_mem_primeFactors hmem
    have hpd := Nat.dvd_of_mem_primeFactors hmem
    have hle := Nat.le_of_mem_primeFactors hmem
    rw [mem_Icc]
    exact ⟨(Nat.one_le_div_iff hp.pos).mpr hle, (Nat.div_le_self _ _).trans hnX⟩
  have hinner : ∀ m ∈ Icc 1 X, ∑ n ∈ T with n / topPrime n = m, f n =
      f m * ∑ p ∈ (Ioc (max W (topPrime m)) (X / m)).filter Nat.Prime, f p := by
    intro m hm
    rw [mem_Icc] at hm
    rw [mul_sum]
    apply sum_nbij' topPrime (fun p => m * p)
    · intro n hn
      rw [mem_filter] at hn
      obtain ⟨hnT, hnm⟩ := hn
      obtain ⟨hn1, hnX, hWt, hmem, hd⟩ := hTmem n hnT
      have hp := Nat.prime_of_mem_primeFactors hmem
      have hpd := Nat.dvd_of_mem_primeFactors hmem
      have hn : m * topPrime n = n := by rw [← hnm]; exact Nat.div_mul_cancel hpd
      have hndvd : ¬ topPrime n ∣ m := by
        intro h
        have := Nat.mul_dvd_mul_right h (topPrime n)
        rw [hn] at this
        exact hd (by rwa [pow_two])
      have htm : topPrime m < topPrime n := by
        apply (Finset.sup_lt_iff (f := id) (s := m.primeFactors) hp.pos).mpr
        intro q hq
        have hqn : q ∈ n.primeFactors :=
          Nat.primeFactors_mono ⟨topPrime n, hn.symm⟩ (by omega) hq
        have := le_topPrime hqn
        have hne : q ≠ topPrime n := by
          rintro rfl; exact hndvd (Nat.dvd_of_mem_primeFactors hq)
        simp only [id]; omega
      simp only [mem_filter, mem_Ioc, max_lt_iff]
      refine ⟨⟨⟨hWt, htm⟩, ?_⟩, hp⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      rw [mul_comm]; omega
    · intro p hp
      simp only [mem_filter, mem_Ioc, max_lt_iff] at hp
      obtain ⟨⟨⟨hWp, htp⟩, hpX⟩, hpr⟩ := hp
      have htop := topPrime_mul (by omega : m ≠ 0) hpr htp
      have hmX : m * p ≤ X := by
        rw [Nat.le_div_iff_mul_le (by omega)] at hpX; rw [mul_comm]; exact hpX
      rw [mem_filter, hT, mem_filter, mem_filter, mem_Icc, htop]
      refine ⟨⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hpr.ne_zero), hmX⟩,
        fun hP => ?_⟩, fun hd => ?_⟩, Nat.mul_div_cancel _ hpr.pos⟩
      · have := hP p (Nat.mem_primeFactors.mpr ⟨hpr, dvd_mul_left _ _, by
          exact Nat.mul_ne_zero (by omega) hpr.ne_zero⟩)
        omega
      · rw [pow_two] at hd
        have hpm : p ∣ m := Nat.dvd_of_mul_dvd_mul_right hpr.pos hd
        have := le_topPrime (Nat.mem_primeFactors.mpr ⟨hpr, hpm, by omega⟩)
        omega
    · intro n hn
      rw [mem_filter] at hn
      obtain ⟨hnT, hnm⟩ := hn
      obtain ⟨-, -, -, hmem, -⟩ := hTmem n hnT
      rw [← hnm]; exact Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hmem)
    · intro p hp
      simp only [mem_filter, mem_Ioc, max_lt_iff] at hp
      exact topPrime_mul (by omega) hp.2 hp.1.1.2
    · intro n hn
      rw [mem_filter] at hn
      obtain ⟨hnT, hnm⟩ := hn
      obtain ⟨-, -, -, hmem, hd⟩ := hTmem n hnT
      have hp := Nat.prime_of_mem_primeFactors hmem
      have hpd := Nat.dvd_of_mem_primeFactors hmem
      have hn : m * topPrime n = n := by rw [← hnm]; exact Nat.div_mul_cancel hpd
      have hndvd : ¬ topPrime n ∣ m := by
        intro h
        have := Nat.mul_dvd_mul_right h (topPrime n)
        rw [hn] at this
        exact hd (by rwa [pow_two])
      conv_lhs => rw [← hn]
      exact hmul _ _ ((Nat.coprime_comm).mp ((hp.coprime_iff_not_dvd).mpr hndvd))
  have h3 : ‖∑ n ∈ T, f n‖ ≤ η * X * (1 + Real.log X) := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine (norm_sum_le _ _).trans ?_
    have hm : ∀ m ∈ Icc 1 X, ‖∑ n ∈ T with n / topPrime n = m, f n‖ ≤ η * X * (1 / (m : ℝ)) := by
      intro m hm'
      rw [hinner m hm', norm_mul]
      have hm1 : 1 ≤ m := (mem_Icc.mp hm').1
      have hb : ‖∑ p ∈ (Ioc (max W (topPrime m)) (X / m)).filter Nat.Prime, f p‖
          ≤ η * X * (1 / (m : ℝ)) := by
        by_cases hc : max W (topPrime m) ≤ X / m
        · refine (hint _ _ (le_max_left _ _) hc (Nat.div_le_self _ _)).trans ?_
          rw [mul_assoc, mul_one_div]
          exact mul_le_mul_of_nonneg_left Nat.cast_div_le hη
        · rw [Ioc_eq_empty (by omega), filter_empty, sum_empty, norm_zero]
          positivity
      calc _ ≤ 1 * ‖∑ p ∈ (Ioc (max W (topPrime m)) (X / m)).filter Nat.Prime, f p‖ :=
            mul_le_mul_of_nonneg_right (hf1 m) (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hb
    refine (sum_le_sum hm).trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (harmonic_Icc_le X) (by positivity)
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le
    (∑ n ∈ ((Icc 1 X).filter (fun n => ¬ P n)).filter (fun n => topPrime n ^ 2 ∣ n), f n)
    (∑ n ∈ T, f n)
  linarith

lemma rpow_geom_tsw {p : ℕ} (_hp : p.Prime) (σ : ℝ) (n : ℕ) :
    (((p ^ n : ℕ) : ℝ)) ^ (-σ) = ((p : ℝ) ^ (-σ)) ^ n := by
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), mul_comm]

lemma rpow_neg_lt_one_tsw {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 < σ) : (p : ℝ) ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- Rankin's trick through Mathlib's Euler product over smooth numbers. -/
lemma rankin_euler (X W : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (smoothCount X W : ℝ) ≤
      (X : ℝ) ^ σ * ∏ p ∈ (W + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  set f : ℕ → ℝ := fun n => (n : ℝ) ^ (-σ) with hf
  have hf1 : f 1 = 1 := by simp [hf]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n _
    simp only [hf, Nat.cast_mul]
    exact Real.mul_rpow (by positivity) (by positivity)
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖f (p ^ n)‖) := by
    intro p hp
    simp only [hf, rpow_geom_tsw hp, norm_pow, Real.norm_eq_abs]
    exact summable_geometric_of_lt_one (abs_nonneg _)
      (by rw [abs_of_nonneg (by positivity)]; exact rpow_neg_lt_one_tsw hp hσ)
  obtain ⟨-, hHas⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hsum (W + 1)
  have hval : ∏ p ∈ (W + 1).primesBelow, ∑' n : ℕ, f (p ^ n)
      = ∏ p ∈ (W + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    refine prod_congr rfl (fun p hp => ?_)
    have hpp := (Nat.mem_primesBelow.mp hp).2
    simp only [hf, rpow_geom_tsw hpp]
    exact tsum_geometric_of_lt_one (by positivity) (rpow_neg_lt_one_tsw hpp hσ)
  rw [hval] at hHas
  set S := (Icc 1 X).filter (fun n => ∀ p ∈ n.primeFactors, p ≤ W) with hS
  have hSsm : ∀ n ∈ S, n ∈ (W + 1).smoothNumbers := by
    intro n hn
    rw [hS, mem_filter, mem_Icc] at hn
    rw [Nat.mem_smoothNumbers']
    intro p hp hpn
    have := hn.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩)
    omega
  have hle : ∑ n ∈ S, f n ≤ ∏ p ∈ (W + 1).primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    have := sum_le_hasSum (S.subtype (· ∈ (W + 1).smoothNumbers))
      (fun i _ => by simp only [hf]; positivity) hHas
    rw [Finset.sum_subtype_of_mem (f := f) hSsm] at this
    exact this
  unfold smoothCount
  rw [← hS]
  calc (S.card : ℝ) = ∑ n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, (X : ℝ) ^ σ * f n := by
      refine sum_le_sum (fun n hn => ?_)
      rw [hS, mem_filter, mem_Icc] at hn
      simp only [hf]
      rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv,
        le_div_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _), one_mul]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn.1.2) hσ.le
    _ = (X : ℝ) ^ σ * ∑ n ∈ S, f n := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (by positivity)

lemma one_sub_inv_le_exp_tsw {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 3 / 4) : (1 - x)⁻¹ ≤ Real.exp (4 * x) := by
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  have := Real.add_one_le_exp (4 * x)
  nlinarith

lemma exp_half_le_two_tsw : Real.exp (1 / 2) ≤ 2 := by
  have h : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos (1 / 2)]

lemma euler_prod_le (W : ℕ) (hW : 3 ≤ W) :
    ∏ p ∈ (W + 1).primesBelow, (1 - (p : ℝ) ^ (-(1 - 1 / (2 * Real.log W))))⁻¹ ≤
      Real.exp (8 * Erdos67b.PrimeEstimates.primeReciprocals W) := by
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; have := Real.exp_one_lt_d9; linarith
  have hlW : 1 < Real.log W := lt_of_lt_of_le hlog3
    (Real.log_le_log (by norm_num) (by exact_mod_cast hW))
  set η := 1 / (2 * Real.log W) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 2 := by
    rw [hη, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have key : ∀ p ∈ (W + 1).primesBelow,
      (1 - (p : ℝ) ^ (-(1 - η)))⁻¹ ≤ Real.exp (8 * (p : ℝ)⁻¹) := by
    intro p hp
    obtain ⟨hpW, hpp⟩ := Nat.mem_primesBelow.mp hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    set x := (p : ℝ) ^ (-(1 - η)) with hx
    have hx0 : 0 ≤ x := by positivity
    have hxa : x ≤ 2 * (p : ℝ)⁻¹ := by
      rw [hx, show -(1 - η) = η + (-1) by ring, Real.rpow_add hp0, Real.rpow_neg_one]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [Real.rpow_def_of_pos hp0]
      refine le_trans (Real.exp_le_exp.mpr ?_) exp_half_le_two_tsw
      have : Real.log p ≤ Real.log W :=
        Real.log_le_log hp0 (by exact_mod_cast (by omega : p ≤ W))
      rw [hη, mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    have hxb : x ≤ 3 / 4 := by
      have hsq : x ^ 2 ≤ (p : ℝ) ^ (-1 : ℝ) := by
        rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
        exact Real.rpow_le_rpow_of_exponent_le hp1.le (by push_cast; linarith)
      have h2 : (p : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 := by
        rw [Real.rpow_neg_one, ← one_div]
        exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hpp.two_le)
      nlinarith
    refine (one_sub_inv_le_exp_tsw hx0 hxb).trans (Real.exp_le_exp.mpr (by linarith))
  refine (prod_le_prod (fun p hp => by
    have hpp := (Nat.mem_primesBelow.mp hp).2
    have : (p : ℝ) ^ (-(1 - η)) < 1 := rpow_neg_lt_one_tsw hpp (by linarith)
    exact inv_nonneg.mpr (by linarith)) key).trans ?_
  rw [← Real.exp_sum, ← mul_sum]
  apply le_of_eq
  congr 2

/-- Smooth numbers below `exp √log X` are negligible. -/
def SmoothCountRankin : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 3 ≤ X →
    (smoothCount X ⌈Real.exp (Real.sqrt (Real.log X))⌉₊ : ℝ) ≤ C * X / Real.log X ^ A

/-- Elementary.  Rankin with `η = 1/log W`:
`Ψ(X, W) ≤ X^{1−η} Π_{p≤W} (1 − p^{−1+η})⁻¹`.  For `p ≤ W`, `p^η ≤ e` and `p^{−1+η} ≤ 2^{−1/2}`, so
the product is at most `exp(C Σ_{p≤W} 1/p) ≤ C′ (log W)^C` by
`Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le`.  Then
`Ψ ≤ C′ X e^{−log X/log W} (log W)^C`, and `log W ≈ √log X`, so this beats every `(log X)^{−A}`. -/
theorem smoothCount_rankin : SmoothCountRankin := by
  intro A hA
  set M := Erdos67b.PrimeEstimates.mertensBound
  set k : ℕ := ⌈2 * A⌉₊ + 8 with hk
  refine ⟨Real.exp (8 * M) * 2 ^ 8 * (4 ^ k * k.factorial), by positivity, ?_⟩
  intro X hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  set L := Real.log X with hL
  have hL1 : 1 < L := by
    rw [hL, Real.lt_log_iff_exp_lt hX0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ X := by exact_mod_cast hX
    linarith
  set t := Real.sqrt L with ht
  have ht1 : 1 ≤ t := by rw [ht, Real.one_le_sqrt]; linarith
  have htL : t ^ 2 = L := Real.sq_sqrt (by linarith)
  set W := ⌈Real.exp t⌉₊ with hW
  have hWe : Real.exp t ≤ W := Nat.le_ceil _
  have he2 : (2 : ℝ) < Real.exp t := by
    have := Real.add_one_lt_exp (show t ≠ 0 by linarith); linarith
  have hW3 : 3 ≤ W := by
    have : (2 : ℝ) < W := by linarith
    exact_mod_cast (show 2 < W by exact_mod_cast this)
  have hWpos : (0 : ℝ) < W := by linarith
  have hlogW_ge : t ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hWpos]; exact hWe
  have hlogW_le : Real.log W ≤ 2 * t := by
    have h1 : (W : ℝ) < Real.exp t + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : Real.exp t + 1 ≤ Real.exp (t + 1) := by
      rw [Real.exp_add]
      have := Real.add_one_le_exp (1 : ℝ)
      have : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp (by linarith)
      nlinarith
    have : Real.log W ≤ t + 1 := by
      rw [Real.log_le_iff_le_exp hWpos]; linarith
    linarith
  have hlW0 : 0 < 2 * Real.log W := by linarith
  -- Rankin
  set η := 1 / (2 * Real.log W) with hη
  have hR := rankin_euler X W (σ := 1 - η) (by
    have : η ≤ 1 / 2 := by
      rw [hη, div_le_div_iff₀ hlW0 (by norm_num)]; linarith
    linarith)
  have hE := euler_prod_le W hW3
  have hMert := Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le (X := W) (by omega)
  rw [abs_le] at hMert
  have hll : Real.log (Real.log W) ≤ Real.log (2 * t) :=
    Real.log_le_log (by linarith) hlogW_le
  have hexp8 : Real.exp (8 * Erdos67b.PrimeEstimates.primeReciprocals W)
      ≤ Real.exp (8 * M) * (2 * t) ^ 8 := by
    calc _ ≤ Real.exp (8 * M + (8 : ℕ) * Real.log (2 * t)) := by
            apply Real.exp_le_exp.mpr; push_cast; linarith
      _ = _ := by rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by linarith)]
  have hXs : (X : ℝ) ^ (1 - η) ≤ X * Real.exp (-(t / 4)) := by
    rw [Real.rpow_sub hX0, Real.rpow_one, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hX0.le
    rw [Real.rpow_def_of_pos hX0, ← Real.exp_neg, Real.exp_le_exp, neg_le_neg_iff, ← hL]
    rw [hη, mul_one_div, le_div_iff₀ hlW0, ← htL]
    nlinarith
  have hS : (smoothCount X W : ℝ) ≤ X * Real.exp (-(t / 4)) * (Real.exp (8 * M) * (2 * t) ^ 8) :=
    hR.trans ((mul_le_mul_of_nonneg_left (hE.trans hexp8) (by positivity)).trans
      (mul_le_mul_of_nonneg_right hXs (by positivity)))
  -- L^A ≤ t^(k-8)
  have hLA : L ^ A ≤ t ^ (k - 8) := by
    rw [← htL, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    refine Real.rpow_le_rpow_of_exponent_le ht1 ?_
    rw [hk, Nat.add_sub_cancel]; push_cast
    have := Nat.le_ceil (2 * A); linarith
  -- t^k e^{-t/4} ≤ 4^k k!
  have hpk : t ^ k * Real.exp (-(t / 4)) ≤ 4 ^ k * k.factorial := by
    have h := Real.pow_div_factorial_le_exp (x := t / 4) (by linarith) k
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    nlinarith [Real.exp_pos (t / 4)]
  have hLpos : 0 < L ^ A := Real.rpow_pos_of_pos (by linarith) _
  rw [le_div_iff₀ hLpos]
  have htk : t ^ (k - 8) * t ^ 8 = t ^ k := by
    rw [← pow_add]; congr 1
  calc (smoothCount X W : ℝ) * L ^ A
      ≤ (X * Real.exp (-(t / 4)) * (Real.exp (8 * M) * (2 * t) ^ 8)) * t ^ (k - 8) :=
        mul_le_mul hS hLA hLpos.le (by positivity)
    _ = X * Real.exp (8 * M) * 2 ^ 8 * (t ^ k * Real.exp (-(t / 4))) := by
        rw [← htk]; ring
    _ ≤ X * Real.exp (8 * M) * 2 ^ 8 * (4 ^ k * k.factorial) :=
        mul_le_mul_of_nonneg_left hpk (by positivity)
    _ = _ := by ring

/-- `TwistedSiegelWalfisz` with the constant uniform in the unit `z`. -/
def UniformZTSW : Prop :=
  ∀ q₀ a : ℕ, 3 ≤ q₀ → Nat.Coprime a q₀ → ∀ A B : ℝ, 0 < A → 0 < B →
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ = 1 →
    ∀ x y r : ℕ, 3 ≤ x → 1 ≤ r → (r : ℝ) ≤ Real.log x ^ B → Nat.Coprime r q₀ →
    ∀ χ : DirichletCharacter ℂ r, χ ≠ 1 →
      ‖∑ n ∈ Finset.Icc 1 x, z ^ omegaMultLe (residueClass q₀ a) y n * χ (n : ZMod r)‖
        ≤ C * x / Real.log x ^ A

/-- The assembly, from SW alone.  `f(n) = z^{Ω_{P,≤y}(n)} χ(n)` is completely multiplicative with
`|f| ≤ 1`.  Apply `largestPrimeTransfer` with `W = ⌈exp √log x⌉` (large `x`; small `x` is
absorbed in `C`).  Interval sums: `f(p) = χ(p)[1 + (z−1)·1_{p≡a (q₀)}·1_{p≤y}]`.  The second
part lives on `(U, min(V, y)]`, which is dropped if empty.  For `p > W > q₀`,
`1_{p≡a} = φ(q₀)⁻¹ Σ_ψ ψ̄(a) ψ(p)`, and `χψ` is nonprincipal mod `r q₀` (CRT; `χ ≠ 1`,
`Coprime r q₀`).  Both endpoints are at least `W`, so `r q₀ ≤ q₀ (log x)^B ≤ (log t)^{2B+2}`.
`PrimeCharacterSW` with `A₁ = 2A + 4` then gives `η ≤ C (log x)^{−A−2}`.  The smooth block is
`smoothCount_rankin`, and the repeated-prime block is `x/(W−1)`. -/
theorem uniformZTSW_of_primeSW (hSW : PrimeCharacterSW) : UniformZTSW := sorry

/-- Quantifier plumbing: the uniform-in-`z` form implies the frozen statement. -/
theorem twistedSiegelWalfisz_of_uniformZ (h : UniformZTSW) : TwistedSiegelWalfisz := by
  intro q₀ a hq ha z hz A B hA hB
  obtain ⟨C, hC, hbound⟩ := h q₀ a hq ha A B hA hB
  exact ⟨C, hC, hbound z hz⟩

/-- **`TwistedSiegelWalfisz` from prime Siegel–Walfisz.**  Paper proof refereed both ways
(Astra `20261011T224341Z`, Opus `20261011T224511Z`). -/
theorem twistedSiegelWalfisz_of_primeSW (hSW : PrimeCharacterSW) : TwistedSiegelWalfisz :=
  twistedSiegelWalfisz_of_uniformZ (uniformZTSW_of_primeSW hSW)

end NormalNumbers.PrimeModel.SiteFactor
