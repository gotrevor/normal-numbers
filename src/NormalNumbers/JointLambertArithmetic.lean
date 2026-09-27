/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.SwingC2

/-!
# §4 of the joint Lambert paper: one common arithmetic progression

Paper: `papers/2026-09-26-joint-lambert-disjunctivity.md`, §4.

This file proves the **finite CRT theorem** behind the joint construction.  It is
purely elementary arithmetic: no analytic input, no AGP, no prime-density
hypothesis.  The supply of primes is *data* — the caller hands in `q` and the
families `p j t` — precisely so that the later exceptional-modulus avoidance can
choose them.  Nothing here fixes them to be consecutive primes.

## The contract (frozen across laps)

Given `c ≥ 2` (the joint exponent, to be `lcm(bases)`), `a ≥ 2`, slots
`1 ≤ r < k ≤ L`, a prime `q > L` with `q^(a-1) > r`, and for each killed slot
`j < k`, `j ≠ r` a family of `j+1` distinct primes `p j t > L`, all distinct from
`q` and from each other across slots, put

* `slotProd p j = ∏_{t < j+1} p j t`   (written `P_j` in the paper),
* `jointQ a q = q^(a-1)`               (`Q`),
* `killCore c k r p = ∏_{j < k, j ≠ r} (P_j)^c`,
* `jointA = q^a * killCore`            (`A`),
* `jointB = q * killCore`              (`B`).

`exists_joint_progression` produces `0 < R < A` and `1 ≤ u < B` with

* `R + r = Q * u`, `A = Q * B`, `u ≡ 1 [MOD q]`, `Nat.Coprime u B`;
* the exact CRT residues `R + r ≡ Q [MOD q^a]` and
  `R + j ≡ P_j^(c-1) [MOD P_j^c]`;
* `c^(j+1) ∣ τ(R + m*A + j)` at every killed slot, for **every** `m`;
* `τ(R + m*A + r) = 2*a` whenever `u + m*B` is prime;
* `Nat.Coprime (R + j) A` for every `k ≤ j < L` (the free tail).

`divisor_count_dvd_of_dvd` is the elementary corollary that `b ∣ c` transfers the
killed-slot divisibility to each base `b`, which is how `c = lcm(bases)` is used.

Divisor counts are `SwingC2.tau m = m.divisors.card` throughout — actual
cardinalities, not an abstract coefficient sequence.
-/

open Finset

namespace NormalNumbers.JointLambert

open NormalNumbers.SwingC2

/-! ### 0. Generic arithmetic helpers -/

/-- **Valuation pinned by a congruence to `P^e · unit`.**  Generalizes
`SwingC2.factorization_eq_of_modEq` from the residue `P^e` to `P^e * w` with
`P ∤ w`, which is what a CRT condition modulo a *product* of primes delivers. -/
theorem factorization_eq_of_modEq_unit {P e m w : ℕ} (hP : P.Prime) (hm : m ≠ 0)
    (hw : ¬ P ∣ w) (h : m ≡ P ^ e * w [MOD P ^ (e + 1)]) :
    m.factorization P = e := by
  have hZ : (P : ℤ) ^ (e + 1) ∣ (P : ℤ) ^ e * (w : ℤ) - (m : ℤ) := by
    have h0 := (Nat.modEq_iff_dvd).mp h
    push_cast at h0
    exact h0
  have hPe : (P ^ e : ℕ) ∣ m := by
    have h2 : (P : ℤ) ^ e ∣ (P : ℤ) ^ e * (w : ℤ) - (m : ℤ) :=
      dvd_trans (pow_dvd_pow _ (by omega)) hZ
    have h3 : (P : ℤ) ^ e ∣ (P : ℤ) ^ e * (w : ℤ) := Dvd.intro _ rfl
    have h4 : (P : ℤ) ^ e ∣ (m : ℤ) := by
      have h5 := dvd_sub h3 h2
      have h6 : (P : ℤ) ^ e * (w : ℤ) - ((P : ℤ) ^ e * (w : ℤ) - (m : ℤ)) = (m : ℤ) := by ring
      rwa [h6] at h5
    exact_mod_cast h4
  have h5 : ¬ (P ^ (e + 1) : ℕ) ∣ m := by
    intro hd
    have hdZ : (P : ℤ) ^ (e + 1) ∣ (m : ℤ) := by exact_mod_cast hd
    have h7 : (P : ℤ) ^ (e + 1) ∣ (P : ℤ) ^ e * (w : ℤ) := by
      have h8 := dvd_add hdZ hZ
      have h9 : (m : ℤ) + ((P : ℤ) ^ e * (w : ℤ) - (m : ℤ)) = (P : ℤ) ^ e * (w : ℤ) := by ring
      rwa [h9] at h8
    have hN : (P ^ (e + 1) : ℕ) ∣ P ^ e * w := by exact_mod_cast h7
    rw [pow_succ] at hN
    exact hw ((Nat.mul_dvd_mul_iff_left (Nat.pow_pos hP.pos : 0 < P ^ e)).mp hN)
  have hA := (Nat.Prime.pow_dvd_iff_le_factorization hP hm).mp hPe
  have hB : ¬ (e + 1 ≤ m.factorization P) := fun hc =>
    h5 ((Nat.Prime.pow_dvd_iff_le_factorization hP hm).mpr hc)
  omega

/-- **Shifted CRT.**  Pairwise coprime moduli `M j` and arbitrary shifts `s j`:
the conditions `n + s j ≡ T j [MOD M j]` hold simultaneously on a full residue
class modulo `∏_{j<N} M j`. -/
theorem exists_crt_shifted (N : ℕ) (M s T : ℕ → ℕ)
    (hMpos : ∀ j, j < N → 0 < M j)
    (hcop : ∀ i j, i < N → j < N → i ≠ j → Nat.Coprime (M i) (M j)) :
    ∃ R : ℕ, ∀ n : ℕ, n ≡ R [MOD ∏ j ∈ range N, M j] →
      ∀ j, j < N → n + s j ≡ T j [MOD M j] := by
  induction N with
  | zero => exact ⟨0, fun n _ j hj => absurd hj (by omega)⟩
  | succ N ih =>
    obtain ⟨R₀, hR₀⟩ := ih (fun j hj => hMpos j (by omega))
      (fun i j hi hj hij => hcop i j (by omega) (by omega) hij)
    have hMN : 0 < M N := hMpos N (by omega)
    have hn₁c : (T N + M N * (s N + 1) - s N) + s N = T N + M N * (s N + 1) := by
      have h1 : s N + 1 ≤ M N * (s N + 1) := Nat.le_mul_of_pos_left _ hMN
      omega
    have hcp : Nat.Coprime (∏ j ∈ range N, M j) (M N) := by
      refine Nat.Coprime.prod_left fun j hj => ?_
      have hjN : j < N := Finset.mem_range.mp hj
      exact hcop j N (by omega) (by omega) (by omega)
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hcp R₀ (T N + M N * (s N + 1) - s N)
    refine ⟨n, fun x hx j hj => ?_⟩
    rw [Finset.prod_range_succ] at hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · exact hR₀ x ((hx.of_dvd (dvd_mul_right _ _)).trans hn1) j hj'
    · subst hj'
      have h1 : x ≡ T j + M j * (s j + 1) - s j [MOD M j] :=
        (hx.of_dvd (dvd_mul_left _ _)).trans hn2
      have h2 : x + s j ≡ (T j + M j * (s j + 1) - s j) + s j [MOD M j] := h1.add_right _
      refine h2.trans ?_
      rw [hn₁c]
      exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mpr ⟨s j + 1, by omega⟩).symm

/-- Two window slots less than `P` apart cannot both be killed by the same prime `P`. -/
theorem prime_not_dvd_both {P R x y : ℕ} (hx : x < P) (hy : y < P) (hne : x ≠ y)
    (h1 : P ∣ R + x) (h2 : P ∣ R + y) : False := by
  rcases Nat.lt_or_ge x y with hlt | hge
  · have he : R + y = (R + x) + (y - x) := by omega
    rw [he] at h2
    have hd : P ∣ y - x := (Nat.dvd_add_right h1).mp h2
    have := Nat.le_of_dvd (by omega) hd
    omega
  · have hlt : y < x := by omega
    have he : R + x = (R + y) + (x - y) := by omega
    rw [he] at h1
    have hd : P ∣ x - y := (Nat.dvd_add_right h2).mp h1
    have := Nat.le_of_dvd (by omega) hd
    omega

/-- `τ(q^e) = e + 1`. -/
theorem tau_prime_pow {q : ℕ} (hq : q.Prime) (e : ℕ) : tau (q ^ e) = e + 1 := by
  rw [tau, Nat.divisors_prime_pow hq, Finset.card_map, Finset.card_range]

/-- **The survivor shape, general base prime.**  `τ(q^e · P) = 2(e+1)` for distinct primes. -/
theorem tau_prime_pow_mul_prime {q e P : ℕ} (hq : q.Prime) (hP : P.Prime) (hne : P ≠ q) :
    tau (q ^ e * P) = 2 * (e + 1) := by
  have hcop : Nat.Coprime (q ^ e) P :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hq hP).2 (Ne.symm hne))
  rw [tau_mul_coprime hcop, tau_prime_pow hq, tau_prime hP]
  ring

/-! ### 1. The data of §4 -/

/-- `P_j`: the product of the `j+1` primes assigned to killed slot `j`. -/
def slotProd (p : ℕ → ℕ → ℕ) (j : ℕ) : ℕ := ∏ t ∈ range (j + 1), p j t

/-- The killed slots: `{j < k} \ {r}`. -/
def killedIdx (k r : ℕ) : Finset ℕ := (range k).erase r

/-- `∏_{j killed} P_j^c`, the part of the modulus shared by `A` and `B`. -/
def killCore (c k r : ℕ) (p : ℕ → ℕ → ℕ) : ℕ := ∏ j ∈ killedIdx k r, slotProd p j ^ c

/-- `Q = q^(a-1)`. -/
def jointQ (a q : ℕ) : ℕ := q ^ (a - 1)

/-- `A = q^a ∏_{j killed} P_j^c`, the common difference of the progression. -/
def jointA (c a k r q : ℕ) (p : ℕ → ℕ → ℕ) : ℕ := q ^ a * killCore c k r p

/-- `B = A / Q = q ∏_{j killed} P_j^c`, the modulus the survivor prime runs in. -/
def jointB (c k r q : ℕ) (p : ℕ → ℕ → ℕ) : ℕ := q * killCore c k r p

theorem mem_killedIdx {k r j : ℕ} : j ∈ killedIdx k r ↔ j ≠ r ∧ j < k := by
  simp [killedIdx, Finset.mem_erase, Finset.mem_range]


/-! ### 2. The theorem of §4 -/

/-- **§4: one common arithmetic progression.**

The finite CRT core of the joint Lambert construction, with the prime supply
supplied as *data* (`q` and the families `p j t`), so that the later
exceptional-modulus avoidance is free to choose it.

Given `c ≥ 2`, `a ≥ 2`, `1 ≤ r < k ≤ L`, a prime `q > L` with `q^(a-1) > r`, and
for each killed slot `j < k`, `j ≠ r` a family of `j+1` primes `p j t > L`, all
distinct from each other and from `q`, there are `0 < R < A` and `1 ≤ u < B` with
`R + r = Q·u`, `A = Q·B`, `u ≡ 1 [MOD q]`, `(u,B) = 1`, the exact CRT residues,
`c^(j+1) ∣ τ(R + mA + j)` at every killed slot for every `m`, `τ(R + mA + r) = 2a`
whenever `u + mB` is prime, and `(R + j, A) = 1` on the free tail `k ≤ j < L`.

No analytic input: this is pure arithmetic. -/
theorem exists_joint_progression
    {c a k r L q : ℕ} {p : ℕ → ℕ → ℕ}
    (hc : 2 ≤ c) (ha : 2 ≤ a) (hr : 1 ≤ r) (hrk : r < k) (hkL : k ≤ L)
    (hq : q.Prime) (hqL : L < q) (hqr : r < jointQ a q)
    (hp : ∀ j t, j < k → j ≠ r → t < j + 1 → (p j t).Prime)
    (hpL : ∀ j t, j < k → j ≠ r → t < j + 1 → L < p j t)
    (hpq : ∀ j t, j < k → j ≠ r → t < j + 1 → p j t ≠ q)
    (hpinj : ∀ j t j' t', j < k → j ≠ r → t < j + 1 → j' < k → j' ≠ r → t' < j' + 1 →
      p j t = p j' t' → j = j' ∧ t = t') :
    ∃ R u : ℕ,
      0 < R ∧ R < jointA c a k r q p ∧ 1 ≤ u ∧ u < jointB c k r q p ∧
      R + r = jointQ a q * u ∧
      jointA c a k r q p = jointQ a q * jointB c k r q p ∧
      u ≡ 1 [MOD q] ∧ Nat.Coprime u (jointB c k r q p) ∧
      R + r ≡ jointQ a q [MOD q ^ a] ∧
      (∀ j, j < k → j ≠ r → R + j ≡ slotProd p j ^ (c - 1) [MOD slotProd p j ^ c]) ∧
      (∀ m j, j < k → j ≠ r → c ^ (j + 1) ∣ tau (R + m * jointA c a k r q p + j)) ∧
      (∀ m, (u + m * jointB c k r q p).Prime →
        tau (R + m * jointA c a k r q p + r) = 2 * a) ∧
      (∀ j, k ≤ j → j < L → Nat.Coprime (R + j) (jointA c a k r q p)) := by
  classical
  have hq2 : 2 ≤ q := hq.two_le
  -- ### slot products
  have hslot2 : ∀ j, j < k → j ≠ r → 2 ≤ slotProd p j := by
    intro j hjk hjr
    have h1 : p j 0 ≤ slotProd p j := by
      simp only [slotProd]
      exact Finset.single_le_prod' (fun i hi => (hp j i hjk hjr (Finset.mem_range.mp hi)).pos)
        (Finset.mem_range.mpr (by omega))
    have := (hp j 0 hjk hjr (by omega)).two_le
    omega
  have hcop_q_slot : ∀ j, j < k → j ≠ r → Nat.Coprime q (slotProd p j) := by
    intro j hjk hjr
    simp only [slotProd]
    refine Nat.Coprime.prod_right fun t ht => ?_
    have htr := Finset.mem_range.mp ht
    exact (Nat.coprime_primes hq (hp j t hjk hjr htr)).2 (Ne.symm (hpq j t hjk hjr htr))
  have hcop_slot : ∀ i j, i < k → i ≠ r → j < k → j ≠ r → i ≠ j →
      Nat.Coprime (slotProd p i) (slotProd p j) := by
    intro i j hik hir hjk hjr hij
    simp only [slotProd]
    refine Nat.Coprime.prod_left fun t ht => Nat.Coprime.prod_right fun t' ht' => ?_
    have htr := Finset.mem_range.mp ht
    have ht'r := Finset.mem_range.mp ht'
    refine (Nat.coprime_primes (hp i t hik hir htr) (hp j t' hjk hjr ht'r)).2 fun he => ?_
    exact hij (hpinj i t j t' hik hir htr hjk hjr ht'r he).1
  -- ### the CRT system
  set M : ℕ → ℕ := fun j => if j = r then q ^ a else slotProd p j ^ c with hMdef
  set T : ℕ → ℕ := fun j => if j = r then jointQ a q else slotProd p j ^ (c - 1) with hTdef
  have hMpos : ∀ j, j < k → 0 < M j := by
    intro j hjk
    by_cases hjr : j = r
    · simp [hMdef, hjr]; positivity
    · have := hslot2 j hjk hjr
      simp only [hMdef, if_neg hjr]
      exact Nat.pow_pos (by omega)
  have hMcop : ∀ i j, i < k → j < k → i ≠ j → Nat.Coprime (M i) (M j) := by
    intro i j hik hjk hij
    by_cases hir : i = r
    · have hjr : j ≠ r := by omega
      simp only [hMdef, if_pos hir, if_neg hjr, hir]
      exact Nat.Coprime.pow _ _ (hcop_q_slot j hjk hjr)
    · by_cases hjr : j = r
      · simp only [hMdef, if_neg hir, if_pos hjr, hjr]
        exact Nat.Coprime.pow _ _ (hcop_q_slot i hik hir).symm
      · simp only [hMdef, if_neg hir, if_neg hjr]
        exact Nat.Coprime.pow _ _ (hcop_slot i j hik hir hjk hjr hij)
  have hprodM : ∏ j ∈ range k, M j = jointA c a k r q p := by
    have hrmem : r ∈ range k := Finset.mem_range.mpr hrk
    rw [← Finset.mul_prod_erase _ M hrmem]
    have h1 : M r = q ^ a := by simp [hMdef]
    rw [h1]
    simp only [jointA, killCore, killedIdx]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjr : j ≠ r := (Finset.mem_erase.mp hj).1
    simp [hMdef, hjr]
  obtain ⟨R₀, hR₀⟩ := exists_crt_shifted k M (fun j => j) T hMpos hMcop
  have hApos : 0 < jointA c a k r q p := by
    rw [← hprodM]; exact Finset.prod_pos fun j hj => hMpos j (Finset.mem_range.mp hj)
  refine ⟨R₀ % jointA c a k r q p, ?_⟩
  set R := R₀ % jointA c a k r q p with hRdef
  have hRA : R < jointA c a k r q p := Nat.mod_lt _ hApos
  have hres : ∀ j, j < k → R + j ≡ T j [MOD M j] := by
    refine hR₀ R ?_
    rw [hprodM, hRdef]
    exact Nat.mod_modEq _ _
  have hres_r : R + r ≡ jointQ a q [MOD q ^ a] := by
    have := hres r hrk
    simpa [hMdef, hTdef] using this
  have hres_j : ∀ j, j < k → j ≠ r →
      R + j ≡ slotProd p j ^ (c - 1) [MOD slotProd p j ^ c] := by
    intro j hjk hjr
    have := hres j hjk
    simpa [hMdef, hTdef, hjr] using this
  -- ### the kill primes divide their own slot
  have hdvd_slot : ∀ j, j < k → j ≠ r → ∀ t, t < j + 1 → p j t ∣ R + j := by
    intro j hjk hjr t ht
    have hpS : p j t ∣ slotProd p j := by
      simp only [slotProd]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr ht)
    have h2 : R + j ≡ slotProd p j ^ (c - 1) [MOD p j t] :=
      (hres_j j hjk hjr).of_dvd (dvd_trans hpS (dvd_pow_self _ (by omega)))
    have h3 : p j t ∣ slotProd p j ^ (c - 1) := dvd_pow hpS (by omega)
    exact (Nat.modEq_zero_iff_dvd).mp (h2.trans ((Nat.modEq_zero_iff_dvd).mpr h3))
  have hqdvdRr : q ∣ R + r := by
    have h2 : R + r ≡ jointQ a q [MOD q] := hres_r.of_dvd (dvd_pow_self q (by omega))
    have h3 : q ∣ jointQ a q := by
      simp only [jointQ]; exact dvd_pow_self q (by omega)
    exact (Nat.modEq_zero_iff_dvd).mp (h2.trans ((Nat.modEq_zero_iff_dvd).mpr h3))
  -- ### positivity of R
  have hR0 : 0 < R := by
    rcases Nat.eq_zero_or_pos R with h0 | h
    · exfalso
      have h1 := hres_j 0 (by omega) (by omega)
      rw [h0] at h1
      have h2 : slotProd p 0 ^ c ∣ slotProd p 0 ^ (c - 1) :=
        (Nat.modEq_zero_iff_dvd).mp (by simpa using h1.symm)
      have hs2 : 2 ≤ slotProd p 0 := hslot2 0 (by omega) (by omega)
      have h4 := Nat.le_of_dvd (Nat.pow_pos (by omega)) h2
      have h5 : slotProd p 0 ^ (c - 1) < slotProd p 0 ^ c :=
        Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    · exact h
  -- ### A = Q · B
  have hQpow : jointQ a q * q = q ^ a := by
    simp only [jointQ]
    rw [← pow_succ]
    congr 1
    omega
  have hAQB : jointA c a k r q p = jointQ a q * jointB c k r q p := by
    simp only [jointA, jointB]
    rw [← mul_assoc, hQpow]
  -- ### the survivor cofactor u
  have hQdvd : jointQ a q ∣ R + r := by
    have h2 : R + r ≡ jointQ a q [MOD jointQ a q] := by
      refine hres_r.of_dvd ?_
      simp only [jointQ]
      exact pow_dvd_pow q (by omega)
    exact (Nat.modEq_zero_iff_dvd).mp (h2.trans ((Nat.modEq_zero_iff_dvd).mpr dvd_rfl))
  obtain ⟨u, hu⟩ := hQdvd
  have hQpos : 0 < jointQ a q := by simp only [jointQ]; positivity
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h
    · rw [h0, mul_zero] at hu; omega
    · exact h
  -- u ≡ 1 mod q
  have humod : u ≡ 1 [MOD q] := by
    refine (Nat.modEq_iff_dvd).mpr ?_
    have h1 : ((q : ℤ)) ^ a ∣ ((jointQ a q : ℕ) : ℤ) - ((R + r : ℕ) : ℤ) := by
      have := (Nat.modEq_iff_dvd).mp hres_r
      push_cast at this ⊢
      exact this
    rw [hu] at h1
    have h2 : ((q : ℤ)) ^ a = (jointQ a q : ℤ) * (q : ℤ) := by
      have := hQpow
      exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) this.symm
    rw [h2] at h1
    have h3 : ((jointQ a q : ℕ) : ℤ) - ((jointQ a q * u : ℕ) : ℤ)
        = (jointQ a q : ℤ) * (1 - (u : ℤ)) := by push_cast; ring
    rw [h3] at h1
    have hQne : ((jointQ a q : ℕ) : ℤ) ≠ 0 := by
      have h0 : jointQ a q ≠ 0 := by omega
      exact_mod_cast h0
    have h4 := (mul_dvd_mul_iff_left hQne).mp h1
    push_cast
    exact h4
  have hqu : ¬ q ∣ u := by
    intro hd
    have hdm : q ∣ u - 1 := (Nat.modEq_iff_dvd' hu1).mp humod.symm
    have he : u = (u - 1) + 1 := by omega
    rw [he] at hd
    have h1 : q ∣ 1 := (Nat.dvd_add_right hdm).mp hd
    have := Nat.le_of_dvd one_pos h1
    omega
  -- u < B
  have huB : u < jointB c k r q p := by
    by_contra hcon
    push_neg at hcon
    have h1 : jointA c a k r q p ≤ R + r := by
      rw [hu, hAQB]; exact Nat.mul_le_mul_left _ hcon
    have hqaK : jointA c a k r q p = q ^ a * killCore c k r p := by simp only [jointA]
    obtain ⟨d, hdeq⟩ : ∃ d, R + r = jointA c a k r q p + d := ⟨R + r - jointA c a k r q p, by omega⟩
    have hdlt : d < r := by omega
    have hQlt : jointQ a q < q ^ a := by
      simp only [jointQ]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    have hmod1 : (R + r) % q ^ a = d % q ^ a := by
      rw [hdeq, hqaK]; exact Nat.mul_add_mod _ _ _
    have hmod2 : (R + r) % q ^ a = jointQ a q % q ^ a := hres_r
    rw [Nat.mod_eq_of_lt hQlt] at hmod2
    rw [Nat.mod_eq_of_lt (show d < q ^ a by omega)] at hmod1
    omega
  -- (u, B) = 1
  have hcopuB : Nat.Coprime u (jointB c k r q p) := by
    simp only [jointB, killCore, killedIdx]
    refine Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqu).symm ?_
    refine Nat.Coprime.prod_right fun j hj => Nat.Coprime.pow_right _ ?_
    have hjr : j ≠ r := (Finset.mem_erase.mp hj).1
    have hjk : j < k := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    simp only [slotProd]
    refine Nat.Coprime.prod_right fun t ht => ?_
    have htr := Finset.mem_range.mp ht
    have hpp := hp j t hjk hjr htr
    refine ((Nat.Prime.coprime_iff_not_dvd hpp).mpr ?_).symm
    intro hdu
    have h1 : p j t ∣ R + r := by rw [hu]; exact Dvd.dvd.mul_left hdu _
    have hL := hpL j t hjk hjr htr
    exact prime_not_dvd_both (x := r) (y := j) (by omega) (by omega) (by omega) h1
      (hdvd_slot j hjk hjr t htr)
  -- ### killed slots
  have hkill : ∀ m j, j < k → j ≠ r →
      c ^ (j + 1) ∣ tau (R + m * jointA c a k r q p + j) := by
    intro m j hjk hjr
    have hn0 : R + m * jointA c a k r q p + j ≠ 0 := by omega
    have hScA : slotProd p j ^ c ∣ jointA c a k r q p := by
      simp only [jointA, killCore, killedIdx]
      exact Dvd.dvd.mul_left
        (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hjr, Finset.mem_range.mpr hjk⟩)) _
    have hnmod : R + m * jointA c a k r q p + j ≡ slotProd p j ^ (c - 1)
        [MOD slotProd p j ^ c] := by
      have e1 : R + m * jointA c a k r q p + j = (R + j) + m * jointA c a k r q p := by ring
      have h0 : (R + j) + m * jointA c a k r q p ≡ (R + j) + 0 [MOD slotProd p j ^ c] :=
        Nat.ModEq.add_left _ ((Nat.modEq_zero_iff_dvd).mpr (Dvd.dvd.mul_left hScA m))
      rw [e1]
      simpa using h0.trans (hres_j j hjk hjr)
    have hSprop : ∀ P ∈ (range (j + 1)).image (p j), P.Prime ∧
        (R + m * jointA c a k r q p + j).factorization P = c - 1 := by
      intro P hP
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hP
      have htr := Finset.mem_range.mp ht
      have hpp := hp j t hjk hjr htr
      refine ⟨hpp, ?_⟩
      have hSW : slotProd p j = p j t * ∏ t' ∈ (range (j + 1)).erase t, p j t' := by
        simp only [slotProd]
        exact (Finset.mul_prod_erase _ _ ht).symm
      have hcopW : Nat.Coprime (p j t) (∏ t' ∈ (range (j + 1)).erase t, p j t') := by
        refine Nat.Coprime.prod_right fun t' ht' => ?_
        have ht'r := Finset.mem_range.mp (Finset.mem_of_mem_erase ht')
        refine (Nat.coprime_primes hpp (hp j t' hjk hjr ht'r)).2 fun he => ?_
        exact (Finset.mem_erase.mp ht').1
          ((hpinj j t j t' hjk hjr htr hjk hjr ht'r he).2).symm
      have hPW : ¬ p j t ∣ (∏ t' ∈ (range (j + 1)).erase t, p j t') ^ (c - 1) := by
        intro hd
        exact (Nat.Prime.coprime_iff_not_dvd hpp).mp hcopW (hpp.prime.dvd_of_dvd_pow hd)
      have hdvdpow : p j t ^ c ∣ slotProd p j ^ c := by
        refine pow_dvd_pow_of_dvd ?_ c
        simp only [slotProd]
        exact Finset.dvd_prod_of_mem _ ht
      have hcong : R + m * jointA c a k r q p + j ≡
          p j t ^ (c - 1) * (∏ t' ∈ (range (j + 1)).erase t, p j t') ^ (c - 1)
          [MOD p j t ^ c] := by
        have h1 := hnmod.of_dvd hdvdpow
        rw [hSW, mul_pow] at h1
        exact h1
      refine factorization_eq_of_modEq_unit hpp hn0 hPW ?_
      rw [show c - 1 + 1 = c by omega]
      exact hcong
    have hcard : ((range (j + 1)).image (p j)).card = j + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro t ht t' ht' he
      exact (hpinj j t j t' hjk hjr (Finset.mem_range.mp ht) hjk hjr
        (Finset.mem_range.mp ht') he).2
    have := pow_card_dvd_tau (show 2 ≤ c by omega) hn0 _ hSprop
    rwa [hcard] at this
  -- ### the survivor
  have hsurv : ∀ m, (u + m * jointB c k r q p).Prime →
      tau (R + m * jointA c a k r q p + r) = 2 * a := by
    intro m hP
    have e1 : R + m * jointA c a k r q p + r
        = q ^ (a - 1) * (u + m * jointB c k r q p) := by
      have : R + m * jointA c a k r q p + r = (R + r) + m * jointA c a k r q p := by ring
      rw [this, hu, hAQB]
      simp only [jointQ]
      ring
    have hne : (u + m * jointB c k r q p) ≠ q := by
      intro he
      have h1 : q ∣ u + m * jointB c k r q p := ⟨1, by omega⟩
      have h2 : q ∣ m * jointB c k r q p := by
        refine Dvd.dvd.mul_left ?_ m
        simp only [jointB]
        exact Dvd.intro _ rfl
      exact hqu ((Nat.dvd_add_left h2).mp h1)
    rw [e1, tau_prime_pow_mul_prime hq hP hne]
    congr 1
    omega
  -- ### the free tail
  have htail : ∀ j, k ≤ j → j < L → Nat.Coprime (R + j) (jointA c a k r q p) := by
    intro j hkj hjL
    simp only [jointA, killCore, killedIdx]
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ?_) ?_
    · refine ((Nat.Prime.coprime_iff_not_dvd hq).mpr ?_).symm
      intro hd
      exact prime_not_dvd_both (x := r) (y := j) (by omega) (by omega) (by omega) hqdvdRr hd
    · refine Nat.Coprime.prod_right fun j' hj' => Nat.Coprime.pow_right _ ?_
      have hj'r : j' ≠ r := (Finset.mem_erase.mp hj').1
      have hj'k : j' < k := Finset.mem_range.mp (Finset.mem_of_mem_erase hj')
      simp only [slotProd]
      refine Nat.Coprime.prod_right fun t ht => ?_
      have htr := Finset.mem_range.mp ht
      have hpp := hp j' t hj'k hj'r htr
      have hL := hpL j' t hj'k hj'r htr
      refine ((Nat.Prime.coprime_iff_not_dvd hpp).mpr ?_).symm
      intro hd
      exact prime_not_dvd_both (x := j') (y := j) (by omega) (by omega) (by omega)
        (hdvd_slot j' hj'k hj'r t htr) hd
  exact ⟨u, hR0, hRA, hu1, huB, hu, hAQB, humod, hcopuB, hres_r, hres_j, hkill, hsurv, htail⟩

/-- **Elementary corollary preparing `c = lcm(bases)`.**  If `b ∣ c` then the killed-slot
divisibility descends to base `b`: `b^(j+1) ∣ τ(R + mA + j)`. -/
theorem divisor_count_dvd_of_dvd {b c j n : ℕ} (hbc : b ∣ c)
    (h : c ^ (j + 1) ∣ tau n) : b ^ (j + 1) ∣ tau n :=
  (pow_dvd_pow_of_dvd hbc _).trans h

/-- **Non-vacuity anchor.**  The hypothesis bundle of `exists_joint_progression` is
satisfiable: `c = a = 2`, `r = 1`, `k = L = 2`, `q = 3`, one killed slot `j = 0` with
the single prime `5`.  (Here `A = 225`, `B = 75`, `Q = 3`, and the CRT solution is
`R = 155`, `u = 52`.)  This guards the contract against an unsatisfiable-hypothesis
reading. -/
theorem exists_joint_progression_nonvacuous :
    ∃ R u : ℕ,
      0 < R ∧ R < jointA 2 2 2 1 3 (fun _ _ => 5) ∧ 1 ≤ u ∧
      u < jointB 2 2 1 3 (fun _ _ => 5) ∧
      R + 1 = jointQ 2 3 * u ∧
      jointA 2 2 2 1 3 (fun _ _ => 5) = jointQ 2 3 * jointB 2 2 1 3 (fun _ _ => 5) ∧
      u ≡ 1 [MOD 3] ∧ Nat.Coprime u (jointB 2 2 1 3 (fun _ _ => 5)) ∧
      R + 1 ≡ jointQ 2 3 [MOD 3 ^ 2] ∧
      (∀ j, j < 2 → j ≠ 1 →
        R + j ≡ slotProd (fun _ _ => 5) j ^ (2 - 1) [MOD slotProd (fun _ _ => 5) j ^ 2]) ∧
      (∀ m j, j < 2 → j ≠ 1 →
        2 ^ (j + 1) ∣ tau (R + m * jointA 2 2 2 1 3 (fun _ _ => 5) + j)) ∧
      (∀ m, (u + m * jointB 2 2 1 3 (fun _ _ => 5)).Prime →
        tau (R + m * jointA 2 2 2 1 3 (fun _ _ => 5) + 1) = 2 * 2) ∧
      (∀ j, 2 ≤ j → j < 2 → Nat.Coprime (R + j) (jointA 2 2 2 1 3 (fun _ _ => 5))) := by
  refine exists_joint_progression (L := 2) (p := fun _ _ => 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · simp [jointQ]
  · intro j t _ _ _; norm_num
  · intro j t _ _ _; norm_num
  · intro j t _ _ _; norm_num
  · intro j t j' t' hj _ ht hj' _ ht' _
    omega

end NormalNumbers.JointLambert
