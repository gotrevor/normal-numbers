/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The first moment of the divisor function along an arithmetic progression

This file supplies the *elementary* half of `SwingC2.CarryLeaf`: the hyperbola bound

  `Σ_{n ≤ X, n ≡ r (mod M)} τ(n) ≤ 2 (X/M · Σ_{d ≤ √X} 1/d + √X)`

for `r` coprime to `M`.  No sieve is used: every divisor `d ≤ √n` of an `n` coprime to `M` is
itself coprime to `M`, so `{n ≤ X : n ≡ r (M), d ∣ n}` is contained in a single residue class
modulo `d·M` and therefore has at most `X/(dM) + 1` elements.

The sum over `d` is left in the exact natural-number form `Σ_{d ∈ [1,√X]} (X/M/d + 1)`; the
conversion to `log` is a separate (purely analytic) step.
-/

namespace SwingC2Moment

open Finset

/-- A finset of naturals lying in `[0, X]` all of whose elements are congruent modulo `m`
has at most `X/m + 1` elements. -/
theorem card_le_of_mod_eq {m X : ℕ} (_hm : 0 < m) (S : Finset ℕ)
    (hX : ∀ x ∈ S, x ≤ X) (hmod : ∀ x ∈ S, ∀ y ∈ S, x % m = y % m) :
    S.card ≤ X / m + 1 := by
  classical
  have h : S.card ≤ (Finset.range (X / m + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun x => x / m) ?_ ?_
    · intro x hx
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (hX x hx))
    · intro x hx y hy hxy
      have hmm := hmod x hx y hy
      have hx1 := Nat.div_add_mod x m
      have hy1 := Nat.div_add_mod y m
      simp only at hxy
      rw [hxy, hmm] at hx1
      exact hx1.symm.trans hy1
  simpa using h

/-- Half of the divisors of `n` are at most `√n`. -/
theorem card_divisors_le_two_mul_small (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ≤ 2 * (n.divisors.filter (fun d => d ≤ Nat.sqrt n)).card := by
  classical
  set S := n.divisors.filter (fun d => d ≤ Nat.sqrt n) with hS
  set L := n.divisors.filter (fun d => ¬ d ≤ Nat.sqrt n) with hL
  have hsplit : S.card + L.card = n.divisors.card :=
    Finset.card_filter_add_card_filter_not _
  have hLS : L.card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun d => n / d) ?_ ?_
    · intro d hd
      simp only [hL, Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hd
      obtain ⟨⟨hdvd, -⟩, hgt⟩ := hd
      simp only [hS, Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors]
      refine ⟨⟨?_, hn⟩, ?_⟩
      · exact Nat.div_dvd_of_dvd hdvd
      · have h1 : Nat.sqrt n + 1 ≤ d := by omega
        have h2 : n / d ≤ n / (Nat.sqrt n + 1) := Nat.div_le_div_left h1 (by omega)
        have h3 : n / (Nat.sqrt n + 1) < Nat.sqrt n + 1 :=
          Nat.div_lt_of_lt_mul (Nat.lt_succ_sqrt n)
        omega
    · intro x hx y hy hxy
      simp only [hL, Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hx hy
      have := Nat.div_div_self hx.1.1 hn
      have h2 := Nat.div_div_self hy.1.1 hn
      simp only at hxy
      rw [← this, hxy, h2]
  omega

/-- The set of `n ≤ X` in the residue class `r` mod `M`. -/
def apSet (M r X : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter (fun n => n % M = r % M)

/-- **First moment of `τ` along a progression with `gcd(r,M)=1`.**  Purely elementary
(hyperbola method plus the observation that a divisor of an `M`-coprime number is `M`-coprime). -/
theorem tau_sum_AP_le (M r X : ℕ) (hM : 0 < M) (hr : Nat.Coprime r M) :
    ∑ n ∈ apSet M r X, n.divisors.card
      ≤ 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (X / M / d + 1) := by
  classical
  -- Step 1: pointwise, τ(n) ≤ 2 · #{d ∈ [1,√X] : d ∣ n}.
  have step1 : ∀ n ∈ apSet M r X,
      n.divisors.card ≤ 2 * ((Finset.Icc 1 (Nat.sqrt X)).filter (fun d => d ∣ n)).card := by
    intro n hn
    rw [apSet, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnX⟩, -⟩ := hn
    refine le_trans (card_divisors_le_two_mul_small n (by omega)) ?_
    refine Nat.mul_le_mul_left 2 (Finset.card_le_card ?_)
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, -⟩, hle⟩ := hd
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hdvd⟩
    · exact Nat.one_le_iff_ne_zero.2 (fun h => by simp [h] at hdvd; omega)
    · exact le_trans hle (Nat.sqrt_le_sqrt hnX)
  -- Step 2: swap the order of summation.
  have step2 :
      ∑ n ∈ apSet M r X, ((Finset.Icc 1 (Nat.sqrt X)).filter (fun d => d ∣ n)).card
        = ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), ((apSet M r X).filter (fun n => d ∣ n)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  -- Step 3: each inner count is at most X/(dM) + 1.
  have step3 : ∀ d ∈ Finset.Icc 1 (Nat.sqrt X),
      ((apSet M r X).filter (fun n => d ∣ n)).card ≤ X / M / d + 1 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd0 : 0 < d := hd.1
    have hdM : 0 < d * M := Nat.mul_pos hd0 hM
    rcases Finset.eq_empty_or_nonempty ((apSet M r X).filter (fun n => d ∣ n)) with he | hne
    · simp [he]
    obtain ⟨n₁, hn₁⟩ := hne
    have hmem : ∀ x ∈ (apSet M r X).filter (fun n => d ∣ n),
        (1 ≤ x ∧ x ≤ X) ∧ x % M = r % M ∧ d ∣ x := by
      intro x hx
      rw [Finset.mem_filter, apSet, Finset.mem_filter, Finset.mem_Icc] at hx
      exact ⟨hx.1.1, hx.1.2, hx.2⟩
    have hcop : Nat.Coprime d M := by
      obtain ⟨⟨hn11, -⟩, hmod, hdvd⟩ := hmem n₁ hn₁
      have hnM : Nat.Coprime n₁ M := by
        have e1 : Nat.gcd M n₁ = Nat.gcd (n₁ % M) M := Nat.gcd_rec M n₁
        have e2 : Nat.gcd M r = Nat.gcd (r % M) M := Nat.gcd_rec M r
        have heq : Nat.gcd M n₁ = Nat.gcd M r := by rw [e1, e2, hmod]
        have hrM : Nat.gcd M r = 1 := by rw [Nat.gcd_comm]; exact hr
        show Nat.gcd n₁ M = 1
        rw [Nat.gcd_comm, heq, hrM]
      exact Nat.Coprime.coprime_dvd_left hdvd hnM
    have key : ∀ x ∈ (apSet M r X).filter (fun n => d ∣ n),
        ∀ y ∈ (apSet M r X).filter (fun n => d ∣ n), x % (d * M) = y % (d * M) := by
      intro x hx y hy
      obtain ⟨-, hxm, hxd⟩ := hmem x hx
      obtain ⟨-, hym, hyd⟩ := hmem y hy
      refine (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨?_, ?_⟩
      · show x % d = y % d
        rw [Nat.mod_eq_zero_of_dvd hxd, Nat.mod_eq_zero_of_dvd hyd]
      · show x % M = y % M
        rw [hxm, hym]
    have hbnd := card_le_of_mod_eq hdM ((apSet M r X).filter (fun n => d ∣ n))
      (fun x hx => (hmem x hx).1.2) key
    have hdiv : X / M / d = X / (d * M) := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm M d]
    rw [hdiv]
    exact hbnd
  calc ∑ n ∈ apSet M r X, n.divisors.card
      ≤ ∑ n ∈ apSet M r X, 2 * ((Finset.Icc 1 (Nat.sqrt X)).filter (fun d => d ∣ n)).card :=
        Finset.sum_le_sum step1
    _ = 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), ((apSet M r X).filter (fun n => d ∣ n)).card := by
        rw [← Finset.mul_sum, step2]
    _ ≤ 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), (X / M / d + 1) :=
        Nat.mul_le_mul_left 2 (Finset.sum_le_sum step3)

/-! ### The harmonic factor

`Σ_{d ≤ D} ⌊Y/d⌋ ≤ Y·(log₂ D + 2)`, by the dyadic blocking argument.  This is what turns
`tau_sum_AP_le` into a bound of the shape `X·log X/M + √X`. -/

theorem Icc_one_eq_Ioc (D : ℕ) : Finset.Icc 1 D = Finset.Ioc 0 D := by
  ext x; simp [Nat.lt_iff_add_one_le]

/-- Dyadic harmonic bound at a power of two. -/
theorem sum_div_Ioc_two_pow (Y : ℕ) : ∀ k : ℕ,
    ∑ d ∈ Finset.Ioc 0 (2 ^ k), Y / d ≤ Y * (k + 1) := by
  intro k
  induction k with
  | zero =>
      rw [pow_zero, show Finset.Ioc 0 1 = {1} from rfl]
      simp

  | succ k ih =>
    have hsplit : (∑ d ∈ Finset.Ioc 0 (2 ^ k), Y / d)
        + (∑ d ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), Y / d)
        = ∑ d ∈ Finset.Ioc 0 (2 ^ (k + 1)), Y / d := by
      refine Finset.sum_Ioc_consecutive _ (Nat.zero_le _) ?_
      exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)
    have hblock : (∑ d ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), Y / d) ≤ Y := by
      have hterm : ∀ d ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), Y / d ≤ Y / 2 ^ k := by
        intro d hd
        rw [Finset.mem_Ioc] at hd
        exact Nat.div_le_div_left hd.1.le (Nat.pow_pos (by norm_num : 0 < 2))
      calc (∑ d ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), Y / d)
          ≤ ∑ _d ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), Y / 2 ^ k :=
            Finset.sum_le_sum hterm
        _ = (2 ^ k) * (Y / 2 ^ k) := by
            have h2 : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by
              rw [pow_succ]
              generalize (2 : ℕ) ^ k = z
              omega
            rw [Finset.sum_const, Nat.card_Ioc, smul_eq_mul, h2]
        _ ≤ Y := by
            rw [Nat.mul_comm]; exact Nat.div_mul_le_self Y (2 ^ k)
    calc ∑ d ∈ Finset.Ioc 0 (2 ^ (k + 1)), Y / d
        = (∑ d ∈ Finset.Ioc 0 (2 ^ k), Y / d)
            + (∑ d ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), Y / d) := hsplit.symm
      _ ≤ Y * (k + 1) + Y := Nat.add_le_add ih hblock
      _ = Y * (k + 1 + 1) := by ring

theorem sum_div_le_log (Y D : ℕ) :
    ∑ d ∈ Finset.Icc 1 D, Y / d ≤ Y * (Nat.log 2 D + 2) := by
  rw [Icc_one_eq_Ioc]
  set k := Nat.log 2 D + 1 with hk
  have hD : D ≤ 2 ^ k := by
    rw [hk]
    exact le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) D)
  have hmono : (∑ d ∈ Finset.Ioc 0 D, Y / d) ≤ ∑ d ∈ Finset.Ioc 0 (2 ^ k), Y / d :=
    Finset.sum_le_sum_of_subset (Finset.Ioc_subset_Ioc_right hD)
  have h2 := sum_div_Ioc_two_pow Y k
  have heq : Y * (k + 1) = Y * (Nat.log 2 D + 2) := by rw [hk]
  omega

/-- **The first moment of `τ` along a progression, in closed form.**
`Σ_{n ≤ X, n ≡ r (M)} τ(n) ≤ 2·( (X/M)·(log₂ √X + 2) + √X )` for `gcd(r,M) = 1`.

This is the elementary half of `SwingC2.CarryLeaf`: the average of `τ` over the progression is
`≪ log X`, so the set of `n` in the progression with `τ(n) ≥ T` has density `≪ log X / T`.
What `CarryLeaf` additionally needs is the same bound restricted to the PRIMES of the
progression (Brun–Titchmarsh / Selberg), which is NOT supplied here. -/
theorem tau_sum_AP_le_log (M r X : ℕ) (hM : 0 < M) (hr : Nat.Coprime r M) :
    ∑ n ∈ apSet M r X, n.divisors.card
      ≤ 2 * ((X / M) * (Nat.log 2 (Nat.sqrt X) + 2) + Nat.sqrt X) := by
  refine le_trans (tau_sum_AP_le M r X hM hr) ?_
  refine Nat.mul_le_mul_left 2 ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
  have h1 : ∑ d ∈ Finset.Icc 1 (Nat.sqrt X), X / M / d
      ≤ (X / M) * (Nat.log 2 (Nat.sqrt X) + 2) := sum_div_le_log _ _
  omega

/-! ### The shifted, sparse hyperbola reduction

`tau_sum_AP_le` above is the special case `c = 1, e = 0, P = ` the whole progression.  For
`SwingC2.TauMomentPrimes` the argument of `τ` is `c·p + e` with `c = 2^a` and `p` running over
the PRIMES of a progression, so the sum is over a sparse set and the shift is nonzero.  The
hyperbola step survives verbatim and is proved here for an arbitrary index set `P`; the sieve
enters afterwards, and only as a bound on the inner counts
`#{n ∈ P : d ∣ c·n + e}` — which for `P` the primes of a class mod `M` is exactly
`π(Y; lcm(d,M), ·)`, i.e. Brun–Titchmarsh. -/
theorem tau_shift_sum_le (c e Y : ℕ) (P : Finset ℕ) (hP : ∀ n ∈ P, n ≤ Y) :
    ∑ n ∈ P, (c * n + e).divisors.card
      ≤ 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (c * Y + e)),
          (P.filter (fun n => d ∣ c * n + e)).card := by
  classical
  have step1 : ∀ n ∈ P, (c * n + e).divisors.card
      ≤ 2 * ((Finset.Icc 1 (Nat.sqrt (c * Y + e))).filter (fun d => d ∣ c * n + e)).card := by
    intro n hn
    rcases Nat.eq_zero_or_pos (c * n + e) with h0 | hpos
    · simp [h0]
    refine le_trans (card_divisors_le_two_mul_small _ (by omega)) ?_
    refine Nat.mul_le_mul_left 2 (Finset.card_le_card ?_)
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, -⟩, hle⟩ := hd
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hdvd⟩
    · rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · rw [hd0] at hdvd
        exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by omega)
      · exact hd0
    · refine le_trans hle (Nat.sqrt_le_sqrt ?_)
      exact Nat.add_le_add_right (Nat.mul_le_mul_left c (hP n hn)) e
  have step2 :
      ∑ n ∈ P, ((Finset.Icc 1 (Nat.sqrt (c * Y + e))).filter (fun d => d ∣ c * n + e)).card
        = ∑ d ∈ Finset.Icc 1 (Nat.sqrt (c * Y + e)),
            (P.filter (fun n => d ∣ c * n + e)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  calc ∑ n ∈ P, (c * n + e).divisors.card
      ≤ ∑ n ∈ P, 2 * ((Finset.Icc 1 (Nat.sqrt (c * Y + e))).filter
          (fun d => d ∣ c * n + e)).card := Finset.sum_le_sum step1
    _ = 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (c * Y + e)),
          (P.filter (fun n => d ∣ c * n + e)).card := by rw [← Finset.mul_sum, step2]

/-! ### The integer count behind one divisor incidence

`#{n ≤ Y : n ≡ r (mod M), d ∣ c·n + e}` is at most `Y/(dM) + 1` whenever `gcd(c,d) = 1` and
`gcd(d,M) = 1`: two such `n` differ by a multiple of `d` (cancel `c`) and of `M`, hence of `dM`.
With `c = 2^a` the first condition says only that `d` is odd, and `d ∣ 2^a n + e` with
`gcd(n,M) = 1` forces the second whenever `gcd(e,M) = 1`.

This is the *integer* count.  Replacing it by the count of PRIMES in the same class is the
Brun–Titchmarsh step; the integer count alone is what a `ShiftedDivisorIncidence` proof would
use if the family `P` were all of the progression rather than its primes. -/
theorem card_shift_dvd_le (c e M r Y d : ℕ) (hd : 0 < d) (hM : 0 < M)
    (hcd : Nat.Coprime c d) (hdM : Nat.Coprime d M) :
    ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).card
      ≤ Y / (d * M) + 1 := by
  classical
  refine card_le_of_mod_eq (m := d * M) (X := Y) (Nat.mul_pos hd hM) _ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    exact hx.1.2
  · intro x hx y hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hx hy
    obtain ⟨-, hxm, hxd⟩ := hx
    obtain ⟨-, hym, hyd⟩ := hy
    refine (Nat.modEq_and_modEq_iff_modEq_mul hdM).1 ⟨?_, ?_⟩
    · -- `d ∣ c*x + e` and `d ∣ c*y + e` give `d ∣ c*(x-y)`, hence `x ≡ y [MOD d]`
      have hkey : ∀ u v : ℕ, u ≤ v → d ∣ c * u + e → d ∣ c * v + e → u % d = v % d := by
        intro u v huv hu hv
        have hsub : d ∣ (c * v + e) - (c * u + e) := Nat.dvd_sub hv hu
        have hmul : c * (v - u) = c * v - c * u := Nat.mul_sub c v u
        have hcuv : c * u ≤ c * v := Nat.mul_le_mul_left c huv
        have he : (c * v + e) - (c * u + e) = (v - u) * c := by
          rw [Nat.mul_comm (v - u) c, hmul]; omega
        rw [he] at hsub
        have hdvu : d ∣ v - u := Nat.Coprime.dvd_of_dvd_mul_right hcd.symm hsub
        exact (Nat.modEq_iff_dvd' huv).2 hdvu
      rcases Nat.le_total x y with hxy | hxy
      · exact hkey x y hxy hxd hyd
      · exact (hkey y x hxy hyd hxd).symm
    · show x % M = y % M
      rw [hxm, hym]

/-- Summing `card_shift_dvd_le` over `d ≤ D`: the crude incidence bound.  Valid only for the
divisors `d` coprime to `c` and to `M`; see the `SwingC2` docstring of
`ShiftedDivisorIncidence` for why the remaining divisors are the hard part. -/
theorem sum_card_shift_dvd_le (c e M r Y D : ℕ) (hM : 0 < M)
    (hcop : ∀ d ∈ Finset.Icc 1 D, Nat.Coprime c d ∧ Nat.Coprime d M) :
    ∑ d ∈ Finset.Icc 1 D,
        ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).card
      ≤ (Y / M) * (Nat.log 2 D + 2) + D := by
  classical
  have hstep : ∀ d ∈ Finset.Icc 1 D,
      ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).card
        ≤ Y / M / d + 1 := by
    intro d hd
    obtain ⟨h1, h2⟩ := hcop d hd
    have hd0 : 0 < d := (Finset.mem_Icc.1 hd).1
    have := card_shift_dvd_le c e M r Y d hd0 hM h1 h2
    have hdiv : Y / M / d = Y / (d * M) := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm M d]
    omega
  calc ∑ d ∈ Finset.Icc 1 D,
        ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).card
      ≤ ∑ d ∈ Finset.Icc 1 D, (Y / M / d + 1) := Finset.sum_le_sum hstep
    _ = (∑ d ∈ Finset.Icc 1 D, Y / M / d) + D := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
        omega
    _ ≤ (Y / M) * (Nat.log 2 D + 2) + D := by
        have := sum_div_le_log (Y / M) D
        omega

end SwingC2Moment
