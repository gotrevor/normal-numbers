/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CastingOut
import NormalNumbers.G4WeightInterface
import NormalNumbers.SwingC2Moment

/-!
# Swing at C2: the Erdős–Borwein constant is disjunctive

`ConjC2` (frozen in `CastingOut.lean`): `Σ_{n≥1} 1/(bⁿ−1) = Σ_m d(m)/bᵐ`
(`erdosBorweinAtBase_eq_lambertVal`) is disjunctive in every base `b ≥ 3`.  The G4 method proves
this for the ADDITIVE weight `ω`; `d = τ` is multiplicative.

## Contents of this file (the 2026-09-24 audit lap)

* **The window bridge** (`isDisjunctive_of_floorWindow`, `floorWindow_lambertVal`):
  disjunctivity of `lambertVal b w` is implied by the purely arithmetic
  `FloorWindow`, i.e. the prescribability of the window
  `Σ_{j=1}^{ℓ} w(N+j)·b^{ℓ−j} + carry` modulo `b^ℓ`.  This converts C2 from a statement about a
  real number into a statement about `τ` on short intervals.  `conjC2_of_tauWindow` is the
  resulting conditional theorem.
* **The audit verdict** on the G5 additive-weight interface (`G4WeightInterface`):  the class the
  existing §4C Fourier control covers is exactly `w(m) = Σ_{p∣m} (1 + c_p (v_p(m) − 1))`, whose
  value at a *prime* is forced to be `1` (`weightN_prime`).  `τ(p) = 2`, so `τ ∉` the class
  (`tau_ne_weightN`), and not by a normalisation: `τ` is not even additive on coprimes
  (`tau_not_additive`).  So `G4Transport`'s exact affine identity
  `ω(D·m) = ω(m) + ω(D) − overlap(D,m)` cannot be ported verbatim.
* **What replaces it** (`tau_transport_frozen`):  `τ` has an exact *multiplicative* transport
  identity along a progression that freezes the valuations at the primes of `D`:

      (∏_{p ∣ D} (e_p + 1)) · τ(D·m)  =  (∏_{p ∣ D} (v_p(D) + e_p + 1)) · τ(m)

  whenever `v_p(m) = e_p` for every `p ∣ D`.  In particular `τ(D·m) = τ(D)·τ(m)` for `m` coprime
  to `D` (`Nat.card_divisors_mul`).  Transport for `τ` is therefore multiplication by a fixed
  rational on the torus, not translation; and the freezing condition is a congruence modulo
  `rad(D)^T` (not `rad D`), with exceptional density `≤ Σ_{p ∣ D} p^{−T}`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.SwingC2

open NormalNumbers.CastingOut

/-! ### 1. The window bridge -/

/-- The divisor-count weight, as a function `ℕ → ℕ`. -/
def tau (m : ℕ) : ℕ := m.divisors.card

/-- **Window prescribability.**  Every residue `t < b^ℓ` occurs as the length-`ℓ` window of `x`
read at some position.  This is the arithmetic shadow of disjunctivity. -/
def FloorWindow (b : ℕ) (x : ℝ) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ t : ℤ, 0 ≤ t → t < (b : ℤ) ^ ℓ →
    ∃ n : ℕ, ⌊x * (b : ℝ) ^ (n + ℓ)⌋ % (b : ℤ) ^ ℓ = t

/-- Reading a window off the orbit: `⌊b^ℓ · {x·bⁿ}⌋ = ⌊x·b^{n+ℓ}⌋ mod b^ℓ`. -/
theorem floor_orbit_mul_pow (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (n ℓ : ℕ) :
    ⌊orbit b x n * (b : ℝ) ^ ℓ⌋ = ⌊x * (b : ℝ) ^ (n + ℓ)⌋ % (b : ℤ) ^ ℓ := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hpow : ((b : ℤ) ^ ℓ : ℤ) ≠ 0 := by positivity
  have hkey : ⌊x * (b : ℝ) ^ n⌋ = ⌊x * (b : ℝ) ^ (n + ℓ)⌋ / (b : ℤ) ^ ℓ := by
    have hne : ((b : ℝ) ^ ℓ) ≠ 0 := by positivity
    have : x * (b : ℝ) ^ n = (x * (b : ℝ) ^ (n + ℓ)) / ((b ^ ℓ : ℕ) : ℝ) := by
      push_cast
      rw [pow_add]
      field_simp
    rw [this, Int.floor_div_natCast]
    push_cast
    ring_nf
  have hfr : orbit b x n * (b : ℝ) ^ ℓ
      = x * (b : ℝ) ^ (n + ℓ) - ((⌊x * (b : ℝ) ^ n⌋ * (b : ℤ) ^ ℓ : ℤ) : ℝ) := by
    unfold orbit
    rw [← Int.self_sub_floor]
    push_cast
    rw [pow_add]
    ring
  rw [hfr, Int.floor_sub_intCast, Int.emod_def, hkey]
  ring

/-- The window bridge: window prescribability implies disjunctivity. -/
theorem isDisjunctive_of_floorWindow (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (h : FloorWindow b x) :
    IsDisjunctive b x := by
  intro a c ha hac hc
  have hbr : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  -- pick `ℓ` with `2/b^ℓ ≤ c − a`
  obtain ⟨ℓ₀, hℓ₀⟩ := pow_unbounded_of_one_lt (2 / (c - a)) hb1
  refine ?_
  set ℓ := ℓ₀ + 1 with hℓdef
  have hbpow : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have hwidth : 2 / ((b : ℝ) ^ ℓ) ≤ c - a := by
    have h1 : (b : ℝ) ^ ℓ₀ ≤ (b : ℝ) ^ ℓ := by
      apply pow_le_pow_right₀ (by linarith) (by omega)
    have : 2 / (c - a) < (b : ℝ) ^ ℓ := lt_of_lt_of_le hℓ₀ h1
    rw [div_le_iff₀ hbpow]
    rw [div_lt_iff₀ (by linarith)] at this
    linarith
  -- the target residue
  set t : ℤ := ⌈a * (b : ℝ) ^ ℓ⌉ with ht
  have ht0 : 0 ≤ t := by
    rw [ht]; positivity
  have hta : a * (b : ℝ) ^ ℓ ≤ (t : ℝ) := Int.le_ceil _
  have htb : (t : ℝ) < a * (b : ℝ) ^ ℓ + 1 := by
    rw [ht]; exact Int.ceil_lt_add_one _
  have htlt : t < (b : ℤ) ^ ℓ := by
    have : (t : ℝ) < ((b : ℝ) ^ ℓ) := by
      have hca : a + 2 / (b : ℝ) ^ ℓ ≤ c := by linarith
      have hc1 : a * (b : ℝ) ^ ℓ + 2 ≤ c * (b : ℝ) ^ ℓ := by
        have := mul_le_mul_of_nonneg_right hca (le_of_lt hbpow)
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hbpow)] at this
        linarith
      nlinarith
    exact_mod_cast (by exact_mod_cast this : ((t : ℝ)) < ((((b : ℤ) ^ ℓ : ℤ)) : ℝ))
  obtain ⟨n, hn⟩ := h ℓ (by omega) t ht0 htlt
  refine ⟨n, ?_, ?_⟩
  · -- `a ≤ orbit`
    have hfl : ⌊orbit b x n * (b : ℝ) ^ ℓ⌋ = t := by rw [floor_orbit_mul_pow b hb x n ℓ, hn]
    have := Int.floor_le (orbit b x n * (b : ℝ) ^ ℓ)
    rw [hfl] at this
    nlinarith [hta]
  · have hfl : ⌊orbit b x n * (b : ℝ) ^ ℓ⌋ = t := by rw [floor_orbit_mul_pow b hb x n ℓ, hn]
    have hlt := Int.lt_floor_add_one (orbit b x n * (b : ℝ) ^ ℓ)
    rw [hfl] at hlt
    have hca : a + 2 / (b : ℝ) ^ ℓ ≤ c := by linarith
    have hc1 : a * (b : ℝ) ^ ℓ + 2 ≤ c * (b : ℝ) ^ ℓ := by
      have := mul_le_mul_of_nonneg_right hca (le_of_lt hbpow)
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hbpow)] at this
      linarith
    nlinarith


/-! ### 1b. The window as a finite arithmetic expression -/

/-- The length-`ℓ` window of `Σ w(m)/bᵐ` read at position `n`, as an integer:
`Σ_{j<ℓ} w(n+1+j)·b^{ℓ−1−j}` plus the carry into position `n+ℓ`. -/
noncomputable def windowNum (b : ℕ) (w : ℕ → ℕ) (n ℓ : ℕ) : ℤ :=
  (∑ j ∈ range ℓ, (w (n + 1 + j) : ℤ) * (b : ℤ) ^ (ℓ - 1 - j)) + carry b w (n + ℓ)

/-- **The window identity.**  Only the `ℓ` weights inside the window, and the carry into its
right end, survive modulo `b^ℓ`.  Everything to the left of the window is killed. -/
theorem floor_lambertVal_emod (b : ℕ) (hb : 2 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m) (n ℓ : ℕ) :
    ⌊lambertVal b w * (b : ℝ) ^ (n + ℓ)⌋ % (b : ℤ) ^ ℓ = windowNum b w n ℓ % (b : ℤ) ^ ℓ := by
  rw [floor_lambertVal_mul_pow b hb w hw (n + ℓ)]
  unfold windowNum
  show Int.ModEq _ _ _
  have hsplit : (((∑ m ∈ range (n + ℓ + 1), w m * b ^ (n + ℓ - m) : ℕ)) : ℤ)
      = (∑ m ∈ range (n + 1), (w m : ℤ) * (b : ℤ) ^ (n + ℓ - m))
        + ∑ j ∈ range ℓ, (w (n + 1 + j) : ℤ) * (b : ℤ) ^ (ℓ - 1 - j) := by
    push_cast
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (n + 1)) (show n + 1 ≤ n + ℓ + 1 by omega)]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1; omega) fun j hj => ?_
    have hj' : j < ℓ := by
      have := Finset.mem_range.mp hj; omega
    congr 2
    omega
  rw [hsplit]
  have hdvd : ((b : ℤ) ^ ℓ) ∣ ∑ m ∈ range (n + 1), (w m : ℤ) * (b : ℤ) ^ (n + ℓ - m) := by
    refine Finset.dvd_sum fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    exact Dvd.dvd.mul_left (pow_dvd_pow (b : ℤ) (by omega)) _
  calc (∑ m ∈ range (n + 1), (w m : ℤ) * (b : ℤ) ^ (n + ℓ - m)
        + ∑ j ∈ range ℓ, (w (n + 1 + j) : ℤ) * (b : ℤ) ^ (ℓ - 1 - j)) + carry b w (n + ℓ)
      ≡ 0 + ∑ j ∈ range ℓ, (w (n + 1 + j) : ℤ) * (b : ℤ) ^ (ℓ - 1 - j) + carry b w (n + ℓ)
        [ZMOD (b : ℤ) ^ ℓ] := by
        exact Int.ModEq.add_right _ (Int.ModEq.add_right _ ((Int.modEq_zero_iff_dvd).2 hdvd))
    _ = _ := by ring


/-! ### 1c. The conditional theorem -/

/-- **The crux, as pure arithmetic.**  Every residue class mod `b^ℓ` is realised by some window
of the weight sequence `w` (together with the carry into the window's right end). -/
def WindowPrescribable (b : ℕ) (w : ℕ → ℕ) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ t : ℤ, 0 ≤ t → t < (b : ℤ) ^ ℓ →
    ∃ n : ℕ, windowNum b w n ℓ % (b : ℤ) ^ ℓ = t

theorem floorWindow_of_windowPrescribable (b : ℕ) (hb : 2 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m)
    (h : WindowPrescribable b w) : FloorWindow b (lambertVal b w) := by
  intro ℓ hℓ t ht0 htlt
  obtain ⟨n, hn⟩ := h ℓ hℓ t ht0 htlt
  exact ⟨n, by rw [floor_lambertVal_emod b hb w hw n ℓ, hn]⟩

theorem isDisjunctive_lambertVal_of_windowPrescribable (b : ℕ) (hb : 2 ≤ b) (w : ℕ → ℕ)
    (hw : ∀ m, w m ≤ m) (h : WindowPrescribable b w) : IsDisjunctive b (lambertVal b w) :=
  isDisjunctive_of_floorWindow b hb _ (floorWindow_of_windowPrescribable b hb w hw h)

theorem tau_le_self (m : ℕ) : tau m ≤ m := Nat.card_divisors_le_self m

/-- **`ConjC2` from the arithmetic crux.**  This is the swing's conditional theorem: the
Erdős–Borwein constant is disjunctive in every base `b ≥ 3` as soon as the divisor-count windows
`Σ_{j<ℓ} τ(n+1+j)·b^{ℓ−1−j}` (plus the carry) realise every residue mod `b^ℓ`. -/
theorem conjC2_of_windowPrescribable (h : ∀ b, 3 ≤ b → WindowPrescribable b tau) : ConjC2 := by
  intro b hb
  rw [erdosBorweinAtBase_eq_lambertVal b (by omega)]
  exact isDisjunctive_lambertVal_of_windowPrescribable b (by omega) tau tau_le_self (h b hb)

/-! ### 2. The audit verdict on the G5 additive class -/

open NormalNumbers.PrimeLambert in
/-- Every weight in the G5 interface class takes the value `1` at a prime: the coefficient `a_p`
is pinned to `1` by the §4C Fourier control.  `τ(p) = 2`. -/
theorem weightN_prime (c : ℕ → ℕ) {p : ℕ} (hp : p.Prime) : weightN c p = 1 := by
  unfold weightN
  rw [ArithmeticFunction.cardDistinctFactors_apply_prime hp, hp.primeFactors]
  simp [Nat.Prime.factorization_self hp]

open NormalNumbers.PrimeLambert in
/-- **The obstruction.**  `τ` is not a member of the G5 additive class, for any coefficients. -/
theorem tau_ne_weightN (c : ℕ → ℕ) : ∃ m, weightN c m ≠ tau m := by
  refine ⟨2, ?_⟩
  rw [weightN_prime c Nat.prime_two]
  decide

/-- `τ` is not additive on coprime arguments: `τ(4·9) = 9 ≠ 3 + 3`.  So the exact affine transport
identity of `G4Transport` has no analogue for `τ` in the additive category. -/
theorem tau_not_additive : ∃ m n : ℕ, Nat.Coprime m n ∧ tau (m * n) ≠ tau m + tau n := by
  refine ⟨4, 9, by decide, by decide⟩

/-! ### 3. What replaces it: exact multiplicative transport for `τ` -/

/-- `τ` is multiplicative: coprime transport is exact. -/
theorem tau_mul_coprime {D m : ℕ} (h : Nat.Coprime D m) : tau (D * m) = tau D * tau m :=
  h.card_divisors_mul

/-- **Exact transport for `τ` on a valuation-frozen progression.**  If the valuation of `m` at
every prime of `D` is frozen to `e p`, then `τ(D·m)` is the fixed rational multiple
`∏_{p ∣ D} (v_p(D) + e_p + 1)/(e_p + 1)` of `τ(m)` — stated multiplicatively to stay in `ℕ`.
This is the `τ`-analogue of `G4Transport.dilatedTailB_eq`: transport is multiplication by a
constant, not translation by one.  The freezing hypothesis is a congruence modulo `rad(D)^T`
once one truncates at `v_p(m) < T`. -/
theorem tau_transport_frozen {D m : ℕ} (hD : D ≠ 0) (hm : m ≠ 0) (e : ℕ → ℕ)
    (hfreeze : ∀ p ∈ D.primeFactors, m.factorization p = e p) :
    (∏ p ∈ D.primeFactors, (e p + 1)) * tau (D * m)
      = (∏ p ∈ D.primeFactors, (D.factorization p + e p + 1)) * tau m := by
  classical
  have hDm : D * m ≠ 0 := Nat.mul_ne_zero hD hm
  set Q : ℕ := ∏ p ∈ m.primeFactors \ D.primeFactors, (m.factorization p + 1) with hQ
  have hfact : ∀ p, (D * m).factorization p = D.factorization p + m.factorization p := by
    intro p; rw [Nat.factorization_mul hD hm]; rfl
  have hDzero : ∀ p ∉ D.primeFactors, D.factorization p = 0 := by
    intro p hp
    by_contra h
    exact hp (Nat.support_factorization (n := D) ▸ Finsupp.mem_support_iff.2 h)
  have hmzero : ∀ p ∉ m.primeFactors, m.factorization p = 0 := by
    intro p hp
    by_contra h
    exact hp (Nat.support_factorization (n := m) ▸ Finsupp.mem_support_iff.2 h)
  have hdisj : Disjoint D.primeFactors (m.primeFactors \ D.primeFactors) :=
    Finset.disjoint_left.2 fun p hp hp' => (Finset.mem_sdiff.mp hp').2 hp
  -- `τ(D·m)`
  have h1 : tau (D * m) = (∏ p ∈ D.primeFactors, (D.factorization p + e p + 1)) * Q := by
    rw [tau, Nat.card_divisors hDm, Nat.primeFactors_mul hD hm,
      show D.primeFactors ∪ m.primeFactors
          = D.primeFactors ∪ (m.primeFactors \ D.primeFactors) from
        (Finset.union_sdiff_self_eq_union).symm,
      Finset.prod_union hdisj]
    congr 1
    · exact Finset.prod_congr rfl fun p hp => by rw [hfact, hfreeze p hp]
    · refine Finset.prod_congr rfl fun p hp => ?_
      rw [hfact, hDzero p (Finset.mem_sdiff.mp hp).2, zero_add]
  -- `τ(m)`
  have h2 : tau m = (∏ p ∈ D.primeFactors, (e p + 1)) * Q := by
    have hsub : m.primeFactors ∩ D.primeFactors ⊆ D.primeFactors := Finset.inter_subset_right
    have hmsplit : m.primeFactors
        = (m.primeFactors ∩ D.primeFactors) ∪ (m.primeFactors \ D.primeFactors) := by
      ext p; by_cases h : p ∈ D.primeFactors <;> simp [h]
    have hdisj2 : Disjoint (m.primeFactors ∩ D.primeFactors) (m.primeFactors \ D.primeFactors) :=
      Finset.disjoint_left.2 fun p hp hp' => (Finset.mem_sdiff.mp hp').2 (Finset.mem_inter.mp hp).2
    rw [tau, Nat.card_divisors hm, hmsplit, Finset.prod_union hdisj2]
    congr 1
    rw [← Finset.prod_subset hsub]
    · exact Finset.prod_congr rfl fun p hp => by rw [hfreeze p (Finset.mem_inter.mp hp).2]
    · intro p hp hp'
      have : m.factorization p = 0 := hmzero p fun hc => hp' (Finset.mem_inter.mpr ⟨hc, hp⟩)
      rw [← hfreeze p hp, this]
      rfl
  rw [h1, h2]; ring


/-! ### 3b. The carry is small: `τ(m) ≤ 2√m` -/

/-- Divisors pair off across `√m`, so `τ(m) ≤ 2⌊√m⌋`. -/
theorem tau_le_two_mul_sqrt {m : ℕ} (hm : m ≠ 0) : tau m ≤ 2 * Nat.sqrt m := by
  classical
  set S : Finset ℕ := Finset.Icc 1 (Nat.sqrt m) with hS
  have hcover : m.divisors ⊆ S ∪ S.image (fun d => m / d) := by
    intro d hd
    rcases Nat.mem_divisors.mp hd with ⟨hdvd, -⟩
    have hd0 : d ≠ 0 := by
      rintro rfl; exact hm (Nat.eq_zero_of_zero_dvd hdvd)
    by_cases hle : d ≤ Nat.sqrt m
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd0, hle⟩)
    · -- then `m / d ≤ √m` and `d = m / (m / d)`
      have hq0 : m / d ≠ 0 := by
        have hdm : d ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd
        have := Nat.div_pos hdm (Nat.pos_of_ne_zero hd0)
        omega
      have hqle : m / d ≤ Nat.sqrt m := by
        by_contra hc
        push_neg at hc
        have h1 : Nat.sqrt m + 1 ≤ d := by omega
        have h2 : Nat.sqrt m + 1 ≤ m / d := by omega
        have hmul : d * (m / d) = m := Nat.mul_div_cancel' hdvd
        have : (Nat.sqrt m + 1) * (Nat.sqrt m + 1) ≤ m := by
          calc (Nat.sqrt m + 1) * (Nat.sqrt m + 1) ≤ d * (m / d) := Nat.mul_le_mul h1 h2
            _ = m := hmul
        have hlt := Nat.lt_succ_sqrt m
        simp only [Nat.succ_eq_add_one] at hlt
        omega
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m / d, ?_, ?_⟩)
      · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hq0, hqle⟩
      · exact Nat.div_div_self hdvd hm
  calc tau m ≤ (S ∪ S.image (fun d => m / d)).card := Finset.card_le_card hcover
    _ ≤ S.card + (S.image (fun d => m / d)).card := Finset.card_union_le _ _
    _ ≤ S.card + S.card := by
        exact Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * Nat.sqrt m := by rw [hS, Nat.card_Icc]; omega


/-- `√(N+j) ≤ √N + j`. -/
theorem sqrt_add_le (N j : ℕ) : Nat.sqrt (N + j) ≤ Nat.sqrt N + j := by
  have hN := Nat.lt_succ_sqrt N
  have h2 : N + j < (Nat.sqrt N + j + 1) ^ 2 := by nlinarith [Nat.zero_le j]
  exact Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr h2)

/-- **The carry is `O(√N)`.**  `τ(m) ≤ 2√m` makes the carry into position `N` at most
`2√N + 2` for every base `b ≥ 3`.  This is what lets a window be padded on the right with `K`
zero digits that absorb the carry, `K ≈ log_b √N`. -/
theorem carry_le_sqrt (b : ℕ) (hb : 3 ≤ b) (N : ℕ) :
    carry b tau N ≤ 2 * (Nat.sqrt N : ℤ) + 2 := by
  set s : ℕ := Nat.sqrt N with hs
  set r : ℝ := (b : ℝ)⁻¹ with hr
  have hb3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrlt : r < 1 := by rw [hr]; rw [inv_lt_one_iff₀]; right; linarith
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hrpos]
  -- the comparison series
  have hsum0 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    simpa using h
  have hshiftsum : Summable (fun k : ℕ => ((k : ℝ) + 1) * r ^ (k + 1)) := by
    have h := hsum0.comp_injective (add_left_injective 1)
    refine h.congr fun k => ?_
    simp [Function.comp]
  have hval : (∑' n : ℕ, (n : ℝ) * r ^ n) = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hshift : (∑' k : ℕ, ((k : ℝ) + 1) * r ^ (k + 1)) = r / (1 - r) ^ 2 := by
    rw [← hval, hsum0.tsum_eq_zero_add]
    simp
  -- the bound on the comparison sum
  have hcmp : r / (1 - r) ^ 2 ≤ 3 / 4 := by
    have h1 : (1 : ℝ) - r = 1 - (b : ℝ)⁻¹ := by rw [hr]
    have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
    have hone : (2 : ℝ) / 3 ≤ 1 - r := by
      rw [hr]
      have : (b : ℝ)⁻¹ ≤ 1 / 3 := by
        rw [inv_le_comm₀ hbpos (by norm_num)]; linarith
      linarith
    have hrle : r ≤ 1 / 3 := by
      rw [hr, inv_le_comm₀ hbpos (by norm_num)]; linarith
    have hsq : (2 / 3 : ℝ) ^ 2 ≤ (1 - r) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  -- termwise domination
  set T : ℝ := ∑' k : ℕ, (tau (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1) with hT
  have hdom : ∀ k : ℕ, (tau (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)
      ≤ (2 * (s : ℝ) + 2) * (((k : ℝ) + 1) * r ^ (k + 1)) := by
    intro k
    have h1 : tau (N + 1 + k) ≤ 2 * (s + (1 + k)) := by
      refine le_trans (tau_le_two_mul_sqrt (by omega)) ?_
      have h := sqrt_add_le N (1 + k)
      rw [show N + (1 + k) = N + 1 + k from by omega] at h
      omega
    have h2 : (tau (N + 1 + k) : ℝ) ≤ 2 * ((s : ℝ) + (1 + k)) := by exact_mod_cast h1
    have h3 : 2 * ((s : ℝ) + (1 + k)) ≤ (2 * (s : ℝ) + 2) * ((k : ℝ) + 1) := by
      have : (0 : ℝ) ≤ (s : ℝ) * k := by positivity
      nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) s]
    have hpow : (0 : ℝ) < (b : ℝ) ^ (k + 1) := by positivity
    have hrp : r ^ (k + 1) = ((b : ℝ) ^ (k + 1))⁻¹ := by rw [hr, inv_pow]
    rw [div_le_iff₀ hpow, hrp]
    field_simp
    nlinarith [h2, h3]
  have hsummableT : Summable (fun k : ℕ => (tau (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)) := by
    exact Summable.of_nonneg_of_le (fun k => by positivity) hdom (hshiftsum.mul_left _)
  have hTle : T ≤ 2 * (s : ℝ) + 2 := by
    have h := hsummableT.tsum_le_tsum hdom (hshiftsum.mul_left (2 * (s : ℝ) + 2))
    rw [hT]
    refine h.trans ?_
    rw [tsum_mul_left, hshift]
    nlinarith [hcmp, Nat.cast_nonneg (α := ℝ) s]
  have : carry b tau N ≤ ⌊(2 * (s : ℝ) + 2)⌋ := by
    unfold carry
    exact Int.floor_le_floor hTle
  refine this.trans ?_
  have : (2 * (s : ℝ) + 2) = ((2 * (s : ℤ) + 2 : ℤ) : ℝ) := by push_cast; ring
  rw [this, Int.floor_intCast]


/-- **The carry bound in its usable, pointwise form.**  If `τ(N+1+k) ≤ A·(k+1)` for every
`k`, then the carry into position `N` is at most `A` — in fact at most `3A/4`, which is why no
constant is lost.  `carry_le_sqrt` is the instance `A = 2√N + 2`.

This is the plumbing that turns a *family* of divisor bounds at the shifts `N+1+k` into the
single inequality `carry b tau N < b^K` that `CarryLeaf` asks for.  Note the shape of the
hypothesis: the threshold is allowed to GROW linearly in `k`, and since `τ(m) ≤ 2√m` the
hypothesis is automatic for every `k ≥ 2√N/A`.  So only `O(√N/A)` shifts need real input. -/
theorem carry_le_of_tau_le (b : ℕ) (hb : 3 ≤ b) (N A : ℕ)
    (h : ∀ k : ℕ, tau (N + 1 + k) ≤ A * (k + 1)) :
    4 * carry b tau N ≤ 3 * (A : ℤ) := by
  set r : ℝ := (b : ℝ)⁻¹ with hr
  have hb3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrlt : r < 1 := by rw [hr]; rw [inv_lt_one_iff₀]; right; linarith
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hrpos]
  have hsum0 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    simpa using h
  have hshiftsum : Summable (fun k : ℕ => ((k : ℝ) + 1) * r ^ (k + 1)) := by
    have h := hsum0.comp_injective (add_left_injective 1)
    refine h.congr fun k => ?_
    simp [Function.comp]
  have hval : (∑' n : ℕ, (n : ℝ) * r ^ n) = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hshift : (∑' k : ℕ, ((k : ℝ) + 1) * r ^ (k + 1)) = r / (1 - r) ^ 2 := by
    rw [← hval, hsum0.tsum_eq_zero_add]
    simp
  have hcmp : r / (1 - r) ^ 2 ≤ 3 / 4 := by
    have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
    have hone : (2 : ℝ) / 3 ≤ 1 - r := by
      rw [hr]
      have : (b : ℝ)⁻¹ ≤ 1 / 3 := by
        rw [inv_le_comm₀ hbpos (by norm_num)]; linarith
      linarith
    have hrle : r ≤ 1 / 3 := by
      rw [hr, inv_le_comm₀ hbpos (by norm_num)]; linarith
    have hsq : (2 / 3 : ℝ) ^ 2 ≤ (1 - r) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have hdom : ∀ k : ℕ, (tau (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)
      ≤ (A : ℝ) * (((k : ℝ) + 1) * r ^ (k + 1)) := by
    intro k
    have h2 : (tau (N + 1 + k) : ℝ) ≤ (A : ℝ) * ((k : ℝ) + 1) := by
      have := h k
      have : ((tau (N + 1 + k) : ℕ) : ℝ) ≤ ((A * (k + 1) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
    have hpow : (0 : ℝ) < (b : ℝ) ^ (k + 1) := by positivity
    have hrp : r ^ (k + 1) = ((b : ℝ) ^ (k + 1))⁻¹ := by rw [hr, inv_pow]
    rw [div_le_iff₀ hpow, hrp]
    field_simp
    linarith
  have hsummableT : Summable (fun k : ℕ => (tau (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hdom (hshiftsum.mul_left _)
  have hTle : (∑' k : ℕ, (tau (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)) ≤ 3 / 4 * (A : ℝ) := by
    have hle := hsummableT.tsum_le_tsum hdom (hshiftsum.mul_left (A : ℝ))
    refine hle.trans ?_
    rw [tsum_mul_left, hshift]
    nlinarith [hcmp, Nat.cast_nonneg (α := ℝ) A]
  have hfl : ((carry b tau N : ℤ) : ℝ)
      ≤ ∑' k : ℕ, (tau (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1) := by
    unfold carry
    exact Int.floor_le _
  have hreal : (4 : ℝ) * ((carry b tau N : ℤ) : ℝ) ≤ 3 * (A : ℝ) := by linarith
  exact_mod_cast hreal

/-- `carry ≤ A` form of `carry_le_of_tau_le`. -/
theorem carry_le_of_tau_le' (b : ℕ) (hb : 3 ≤ b) (N A : ℕ)
    (h : ∀ k : ℕ, tau (N + 1 + k) ≤ A * (k + 1)) :
    carry b tau N ≤ (A : ℤ) := by
  have h4 := carry_le_of_tau_le b hb N A h
  have hA : (0 : ℤ) ≤ (A : ℤ) := Int.natCast_nonneg A
  omega

/-- **Strict** form: the `3/4` slack in `carry_le_of_tau_le` makes the bound strict. -/
theorem carry_lt_of_tau_le (b : ℕ) (hb : 3 ≤ b) (N A : ℕ) (hA : 0 < A)
    (h : ∀ k : ℕ, tau (N + 1 + k) ≤ A * (k + 1)) :
    carry b tau N < (A : ℤ) := by
  have h4 := carry_le_of_tau_le b hb N A h
  have hA' : (1 : ℤ) ≤ (A : ℤ) := by exact_mod_cast hA
  omega

/-- **The carry bound with a GEOMETRIC threshold.**  If `τ(N+1+k) ≤ A·(k+1)·2^k` for every `k`,
then `carry b τ N ≤ 3A` (for `b ≥ 3`; the constant is `b/(b−2)² ≤ 3`, attained at `b = 3`).

This is the form the crux actually needs.  With the *linear* threshold of `carry_le_of_tau_le`
the trivial bound `τ(m) ≤ 2√m` only takes over at `k ≈ √N`, so a union bound over shifts costs a
factor `√N` and destroys the budget.  With the geometric threshold it takes over at
`k ≈ log₂ √N`, and — more importantly — the *per-shift* exceptional densities may be allowed to
decay like `2^{-k}`, so the union bound over shifts converges and costs nothing at all. -/
theorem carry_le_of_tau_geom (b : ℕ) (hb : 3 ≤ b) (N A : ℕ)
    (h : ∀ k : ℕ, tau (N + 1 + k) ≤ A * (k + 1) * 2 ^ k) :
    carry b tau N ≤ 3 * (A : ℤ) := by
  set s : ℝ := 2 / (b : ℝ) with hs
  have hb3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hspos : 0 < s := by rw [hs]; positivity
  have hslt : s < 1 := by rw [hs, div_lt_one hbpos]; linarith
  have hnorm : ‖s‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hspos]
  have hsum0 : Summable (fun n : ℕ => (n : ℝ) * s ^ n) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    simpa using h
  have hgsum : Summable (fun k : ℕ => ((k : ℝ) + 1) * s ^ k) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    have h2 : Summable (fun k : ℕ => s ^ k) := summable_geometric_of_norm_lt_one hnorm
    have := h.add h2
    refine this.congr fun k => ?_
    simp [add_mul]
  have hval : (∑' n : ℕ, (n : ℝ) * s ^ n) = s / (1 - s) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hshift : (∑' k : ℕ, ((k : ℝ) + 1) * s ^ (k + 1)) = s / (1 - s) ^ 2 := by
    rw [← hval, hsum0.tsum_eq_zero_add]
    simp
  have hgval : (∑' k : ℕ, ((k : ℝ) + 1) * s ^ k) = 1 / (1 - s) ^ 2 := by
    have hfac : (∑' k : ℕ, ((k : ℝ) + 1) * s ^ (k + 1))
        = s * ∑' k : ℕ, ((k : ℝ) + 1) * s ^ k := by
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      ring
    rw [hfac] at hshift
    have hne : (1 : ℝ) - s ≠ 0 := by
      have : (0 : ℝ) < 1 - s := by linarith
      exact ne_of_gt this
    refine mul_left_cancel₀ (ne_of_gt hspos) ?_
    rw [hshift]
    field_simp
  have hdom : ∀ k : ℕ, (tau (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)
      ≤ ((A : ℝ) / (b : ℝ)) * (((k : ℝ) + 1) * s ^ k) := by
    intro k
    have h2 : (tau (N + 1 + k) : ℝ) ≤ (A : ℝ) * ((k : ℝ) + 1) * 2 ^ k := by
      have h1 := h k
      have : ((tau (N + 1 + k) : ℕ) : ℝ) ≤ ((A * (k + 1) * 2 ^ k : ℕ) : ℝ) := by
        exact_mod_cast h1
      push_cast at this
      linarith
    have hpow : (0 : ℝ) < (b : ℝ) ^ (k + 1) := by positivity
    have hsk : s ^ k = 2 ^ k / (b : ℝ) ^ k := by rw [hs, div_pow]
    rw [div_le_iff₀ hpow, hsk]
    have hbk : (0 : ℝ) < (b : ℝ) ^ k := by positivity
    have hexp : (b : ℝ) ^ (k + 1) = (b : ℝ) ^ k * (b : ℝ) := by ring
    field_simp [hexp]
    nlinarith [h2, hbk, Nat.cast_nonneg (α := ℝ) A]
  have hsummableT : Summable (fun k : ℕ => (tau (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hdom (hgsum.mul_left _)
  have hTle : (∑' k : ℕ, (tau (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)) ≤ 3 * (A : ℝ) := by
    have hle := hsummableT.tsum_le_tsum hdom (hgsum.mul_left ((A : ℝ) / (b : ℝ)))
    refine hle.trans ?_
    rw [tsum_mul_left, hgval]
    have h1s : (1 : ℝ) - s = ((b : ℝ) - 2) / (b : ℝ) := by
      rw [hs]; field_simp
    have hb2 : (0 : ℝ) < (b : ℝ) - 2 := by linarith
    have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    have heq : (A : ℝ) / (b : ℝ) * (1 / (1 - s) ^ 2)
        = (A : ℝ) * (b : ℝ) / ((b : ℝ) - 2) ^ 2 := by
      rw [h1s]
      field_simp
    rw [heq, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hAnn (mul_nonneg (by linarith : (0:ℝ) ≤ (b : ℝ) - 3)
      (by linarith : (0:ℝ) ≤ 3 * (b : ℝ) - 4))]
  have hfl : ((carry b tau N : ℤ) : ℝ)
      ≤ ∑' k : ℕ, (tau (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1) := by
    unfold carry
    exact Int.floor_le _
  have : ((carry b tau N : ℤ) : ℝ) ≤ ((3 * (A : ℤ) : ℤ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-- The shifts `k` at which `carry_le_of_tau_le` needs real input are only those with
`2·√(N+1+k) > A·(k+1)`; everywhere else `τ(m) ≤ 2√m` already gives the hypothesis. -/
theorem tau_le_of_sqrt_small (N A k : ℕ) (h : 2 * Nat.sqrt (N + 1 + k) ≤ A * (k + 1)) :
    tau (N + 1 + k) ≤ A * (k + 1) :=
  le_trans (tau_le_two_mul_sqrt (by omega)) h

/-! ### 3c. The padding reduction: the crux becomes a congruence on `τ` -/

/-- The in-window part of `windowNum`. -/
def paddedSum (b : ℕ) (w : ℕ → ℕ) (n L : ℕ) : ℤ :=
  ∑ j ∈ range L, (w (n + 1 + j) : ℤ) * (b : ℤ) ^ (L - 1 - j)

theorem windowNum_eq (b : ℕ) (w : ℕ → ℕ) (n L : ℕ) :
    windowNum b w n L = paddedSum b w n L + carry b w (n + L) := rfl

/-- Dropping the last `K` digits of a floor is integer division by `b^K`. -/
theorem floor_mul_pow_div (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (m K : ℕ) :
    ⌊x * (b : ℝ) ^ m⌋ = ⌊x * (b : ℝ) ^ (m + K)⌋ / (b : ℤ) ^ K := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hne : ((b : ℝ) ^ K) ≠ 0 := by positivity
  have h : x * (b : ℝ) ^ m = (x * (b : ℝ) ^ (m + K)) / ((b ^ K : ℕ) : ℝ) := by
    push_cast
    rw [pow_add]
    field_simp
  rw [h, Int.floor_div_natCast]
  push_cast
  ring_nf

/-- The carry is nonnegative. -/
theorem carry_nonneg (b : ℕ) (hb : 2 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m) (N : ℕ) :
    0 ≤ carry b w N := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  refine Int.le_floor.mpr ?_
  have hs := ((summable_lambert b hb w hw).mul_right ((b : ℝ) ^ (N + 1))).comp_injective
    (add_left_injective 0)
  push_cast
  refine tsum_nonneg fun k => by positivity

/-- **Sub-leaf A.**  The purely congruential residue of the crux: for every target `t < b^ℓ`
there is a position `n` and a pad length `K`, long enough to swallow the carry
(`2√(n+ℓ+K) + 2 < b^K`, cf. `carry_le_sqrt`), at which the `ℓ+K` divisor counts
`τ(n+1), …, τ(n+ℓ+K)` weight-sum to `t·b^K` modulo `b^{ℓ+K}`.

No real analysis, no carries: this is a statement about the divisor function on an interval of
length `ℓ+K` in residue classes modulo powers of `b`. -/
def SubLeafA (b : ℕ) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ t : ℕ, t < b ^ ℓ → ∃ n K : ℕ,
    carry b tau (n + (ℓ + K)) < (b : ℤ) ^ K ∧
    paddedSum b tau n (ℓ + K) % (b : ℤ) ^ (ℓ + K) = (t : ℤ) * (b : ℤ) ^ K

/-- **What the padding argument actually needs.**  Only that the length-`ℓ+K` window value is
`t·b^K + c` for SOME `c ∈ [0, b^K)` — no bound on the carry, and no condition on `paddedSum`
separately.  `SubLeafA` is the special case `c = carry` (`windowShape_of_subLeafA`), which is
strictly stronger; an analytic proof may target this weaker statement instead. -/
def WindowShape (b : ℕ) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ t : ℕ, t < b ^ ℓ → ∃ n K : ℕ, ∃ c : ℤ, 0 ≤ c ∧ c < (b : ℤ) ^ K ∧
    windowNum b tau n (ℓ + K) % (b : ℤ) ^ (ℓ + K) = (t : ℤ) * (b : ℤ) ^ K + c

theorem windowPrescribable_of_windowShape (b : ℕ) (hb : 3 ≤ b) (h : WindowShape b) :
    WindowPrescribable b tau := by
  have hb2 : 2 ≤ b := by omega
  have hbpos : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (show 0 < b by omega)
  intro ℓ hℓ t ht0 htlt
  lift t to ℕ using ht0 with t₀
  have ht₀ : t₀ < b ^ ℓ := by exact_mod_cast htlt
  obtain ⟨n, K, C, hC0, hCK, hW⟩ := h ℓ hℓ t₀ ht₀
  set L := ℓ + K with hL
  set x : ℝ := lambertVal b tau with hx
  have hbK : (0 : ℤ) < (b : ℤ) ^ K := by positivity
  have hbL : (0 : ℤ) < (b : ℤ) ^ L := by positivity
  have hV : ⌊x * (b : ℝ) ^ (n + L)⌋ % (b : ℤ) ^ L = (t₀ : ℤ) * (b : ℤ) ^ K + C := by
    rw [floor_lambertVal_emod b hb2 tau tau_le_self n L]; exact hW
  refine ⟨n, ?_⟩
  rw [← floor_lambertVal_emod b hb2 tau tau_le_self n ℓ]
  rw [floor_mul_pow_div b hb2 x (n + ℓ) K, show n + ℓ + K = n + L from by omega]
  obtain ⟨q, hq⟩ : ∃ q : ℤ, ⌊x * (b : ℝ) ^ (n + L)⌋
      = (b : ℤ) ^ L * q + ((t₀ : ℤ) * (b : ℤ) ^ K + C) := by
    refine ⟨⌊x * (b : ℝ) ^ (n + L)⌋ / (b : ℤ) ^ L, ?_⟩
    have hmd := Int.emod_def ⌊x * (b : ℝ) ^ (n + L)⌋ ((b : ℤ) ^ L)
    rw [hV] at hmd
    omega
  rw [hq]
  have hdivK : ((b : ℤ) ^ L * q + ((t₀ : ℤ) * (b : ℤ) ^ K + C)) / (b : ℤ) ^ K
      = (b : ℤ) ^ ℓ * q + (t₀ : ℤ) := by
    have hrw : (b : ℤ) ^ L * q + ((t₀ : ℤ) * (b : ℤ) ^ K + C)
        = C + (b : ℤ) ^ K * ((b : ℤ) ^ ℓ * q + (t₀ : ℤ)) := by
      rw [hL, pow_add]; ring
    rw [hrw, Int.add_mul_ediv_left _ _ (ne_of_gt hbK), Int.ediv_eq_zero_of_lt hC0 hCK, zero_add]
  rw [hdivK, add_comm, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ht₀)

/-- `SubLeafA` is the `c = carry` case of `WindowShape`. -/
theorem windowShape_of_subLeafA (b : ℕ) (hb : 3 ≤ b) (h : SubLeafA b) : WindowShape b := by
  have hb2 : 2 ≤ b := by omega
  have hbpos : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (show 0 < b by omega)
  intro ℓ hℓ t₀ ht₀
  obtain ⟨n, K, hK, hP⟩ := h ℓ hℓ t₀ ht₀
  set L := ℓ + K with hL
  have hbK : (0 : ℤ) < (b : ℤ) ^ K := by positivity
  refine ⟨n, K, carry b tau (n + L), carry_nonneg b hb2 tau tau_le_self _, hK, ?_⟩
  set C : ℤ := carry b tau (n + L) with hC
  have hC0 : 0 ≤ C := carry_nonneg b hb2 tau tau_le_self _
  rw [windowNum_eq]
  have hsmall : 0 ≤ (t₀ : ℤ) * (b : ℤ) ^ K + C ∧ (t₀ : ℤ) * (b : ℤ) ^ K + C < (b : ℤ) ^ L := by
    constructor
    · positivity
    · have h1 : (t₀ : ℤ) ≤ (b : ℤ) ^ ℓ - 1 := by
        have : (t₀ : ℤ) < (b : ℤ) ^ ℓ := by exact_mod_cast ht₀
        omega
      have h2 : (t₀ : ℤ) * (b : ℤ) ^ K ≤ ((b : ℤ) ^ ℓ - 1) * (b : ℤ) ^ K :=
        mul_le_mul_of_nonneg_right h1 hbK.le
      have h3 : ((b : ℤ) ^ ℓ - 1) * (b : ℤ) ^ K = (b : ℤ) ^ L - (b : ℤ) ^ K := by
        rw [hL, pow_add]; ring
      omega
  calc (paddedSum b tau n L + C) % (b : ℤ) ^ L
      = ((paddedSum b tau n L % (b : ℤ) ^ L) + C) % (b : ℤ) ^ L :=
        (Int.emod_add_emod _ _ _).symm
    _ = ((t₀ : ℤ) * (b : ℤ) ^ K + C) % (b : ℤ) ^ L := by rw [hP]
    _ = (t₀ : ℤ) * (b : ℤ) ^ K + C := Int.emod_eq_of_lt hsmall.1 hsmall.2

theorem windowPrescribable_of_subLeafA (b : ℕ) (hb : 3 ≤ b) (h : SubLeafA b) :
    WindowPrescribable b tau :=
  windowPrescribable_of_windowShape b hb (windowShape_of_subLeafA b hb h)


/-! ### 3d. The route back to an ADDITIVE weight: `τ = (a+1)·2^ω` on the squarefree locus

The audit verdict (§2) is that `τ` is multiplicative and so falls outside the additive class the
G4 Fourier control covers.  The escape is that `τ` *restricted to a structured locus* is an
exponential of an additive weight.  If `n = p^a · s` with `s` squarefree and `p ∤ s`, then

    τ(n) = (a+1) · 2^{ω(s)},

so `τ(n) mod b^L` is determined by `a` and by `ω(s) mod ord_{b^L}(2)` — and `ω` IS additive, which
is exactly the weight `G4Transport`/`G4WeightInterface` handle.  The free factor `(a+1)` supplies
the residues (such as `0 mod b`) that the cyclic group generated by `2` cannot reach.  This is the
proposed replacement for the broken transport identity. -/

/-- On a squarefree number the divisor count is `2^ω`. -/
theorem tau_of_squarefree {s : ℕ} (hs : Squarefree s) :
    tau s = 2 ^ s.primeFactors.card := by
  have hs0 : s ≠ 0 := hs.ne_zero
  rw [tau, Nat.card_divisors hs0]
  rw [Finset.prod_congr rfl (fun p hp => ?_), Finset.prod_const]
  rw [Nat.factorization_eq_one_of_squarefree hs (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)]

/-- **The structured form of `τ`.**  `τ(p^a · s) = (a+1)·2^{ω(s)}` for `s` squarefree, `p ∤ s`. -/
theorem tau_primePow_mul_squarefree {p a s : ℕ} (hp : p.Prime) (hs : Squarefree s)
    (hps : ¬ p ∣ s) : tau (p ^ a * s) = (a + 1) * 2 ^ s.primeFactors.card := by
  have hcop : Nat.Coprime (p ^ a) s := (Nat.Prime.coprime_iff_not_dvd hp).2 hps |>.pow_left a
  rw [tau_mul_coprime hcop, tau_of_squarefree hs]
  congr 1
  rw [tau, Nat.card_divisors (pow_ne_zero a hp.ne_zero)]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [Nat.primeFactors_prime_pow (by omega) hp, Finset.prod_singleton,
      Nat.Prime.factorization_pow hp]
    simp


/-! ### 3e. `SubLeafB`: the crux inside the ADDITIVE category -/

/-- `m = q^a · s` with `q` prime, `s` squarefree and `q ∤ s`: the locus on which
`τ(m) = (a+1)·2^{ω(s)}` (`tau_primePow_mul_squarefree`).  Every `m` whose non-squarefree part is
supported at a single prime is of this shape; such `m` have positive density. -/
def Structured (m q a s : ℕ) : Prop :=
  q.Prime ∧ Squarefree s ∧ ¬ q ∣ s ∧ m = q ^ a * s

theorem tau_of_structured {m q a s : ℕ} (h : Structured m q a s) :
    tau m = (a + 1) * 2 ^ s.primeFactors.card := by
  obtain ⟨hq, hs, hqs, rfl⟩ := h
  exact tau_primePow_mul_squarefree hq hs hqs

/-- **`SubLeafB`.**  `SubLeafA` with the divisor counts replaced by their structured form: the
window is prescribed using only the exponents `a_j` and the ADDITIVE weights `ω(s_j)`.  No
multiplicative weight appears — the unknown is a vector of `ω`-values on `L` consecutive
integers, which is the category `G4Transport` / `G4WeightInterface` were built for. -/
def SubLeafB (b : ℕ) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ t : ℕ, t < b ^ ℓ → ∃ n K : ℕ, ∃ q a s : ℕ → ℕ,
    carry b tau (n + (ℓ + K)) < (b : ℤ) ^ K ∧
    (∀ j < ℓ + K, Structured (n + 1 + j) (q j) (a j) (s j)) ∧
    (∑ j ∈ range (ℓ + K),
        (((a j + 1) * 2 ^ ((s j).primeFactors.card) : ℕ) : ℤ) * (b : ℤ) ^ (ℓ + K - 1 - j))
        % (b : ℤ) ^ (ℓ + K) = (t : ℤ) * (b : ℤ) ^ K

/-- The structured window computes the padded divisor window. -/
theorem subLeafA_of_subLeafB (b : ℕ) (h : SubLeafB b) : SubLeafA b := by
  intro ℓ hℓ t ht
  obtain ⟨n, K, q, a, s, hK, hstruct, hsum⟩ := h ℓ hℓ t ht
  refine ⟨n, K, hK, ?_⟩
  rw [show paddedSum b tau n (ℓ + K)
      = ∑ j ∈ range (ℓ + K),
          (((a j + 1) * 2 ^ ((s j).primeFactors.card) : ℕ) : ℤ) * (b : ℤ) ^ (ℓ + K - 1 - j) from ?_]
  · exact hsum
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [tau_of_structured (hstruct j (Finset.mem_range.mp hj))]


/-! ### 3f. No LOCAL obstruction: the structured target system is algebraically free -/

/-- **The structured window system has no algebraic obstruction.**  For every base `b ≥ 2`, every
window length `L ≥ 1` and every target `t`, the shape `Σ_j (a_j+1)·2^{e_j}·b^{L−1−j}` realises `t`
modulo `b^L` — already with all `e_j = 0` and a single free exponent in the last slot.

Consequence for the swing: **nothing in `SubLeafB` is blocked by congruence algebra.**  The whole
difficulty is *arithmetic realisability* — making one window of `L` CONSECUTIVE integers carry the
required exponent vector — not the residues themselves.  In particular a proof needs only ONE slot
whose prime-power exponent is free; the other `L−1` slots may contribute whatever they like. -/
theorem structuredTarget_unobstructed (b : ℕ) (hb : 2 ≤ b) (L : ℕ) (hL : 1 ≤ L) (t : ℤ) :
    ∃ a e : ℕ → ℕ,
      (∑ j ∈ range L, (((a j + 1) * 2 ^ (e j) : ℕ) : ℤ) * (b : ℤ) ^ (L - 1 - j))
        % (b : ℤ) ^ L = t % (b : ℤ) ^ L := by
  classical
  have hbL : (0 : ℤ) < (b : ℤ) ^ L := by
    have : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (show 0 < b by omega)
    positivity
  set S₀ : ℤ := ∑ j ∈ range L, (b : ℤ) ^ (L - 1 - j) with hS₀
  set A : ℕ := ((t - S₀) % (b : ℤ) ^ L).toNat with hA
  have hAcast : (A : ℤ) = (t - S₀) % (b : ℤ) ^ L :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hbL))
  refine ⟨fun j => if j = L - 1 then A else 0, fun _ => 0, ?_⟩
  have hterm : ∀ j ∈ range L,
      ((((if j = L - 1 then A else 0) + 1) * 2 ^ (0 : ℕ) : ℕ) : ℤ) * (b : ℤ) ^ (L - 1 - j)
        = (if j = L - 1 then (A : ℤ) else 0) * (b : ℤ) ^ (L - 1 - j) + (b : ℤ) ^ (L - 1 - j) := by
    intro j _
    by_cases h : j = L - 1 <;> simp [h] <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← hS₀]
  have hpick : (∑ j ∈ range L, (if j = L - 1 then (A : ℤ) else 0) * (b : ℤ) ^ (L - 1 - j))
      = (A : ℤ) := by
    rw [Finset.sum_eq_single (L - 1)]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [hpick]
  have hmod : (A : ℤ) % (b : ℤ) ^ L = (t - S₀) % (b : ℤ) ^ L := by
    rw [hAcast, Int.emod_emod_of_dvd _ dvd_rfl]
  have : (A : ℤ) + S₀ ≡ (t - S₀) + S₀ [ZMOD (b : ℤ) ^ L] := Int.ModEq.add_right S₀ hmod
  have h2 : S₀ + (A : ℤ) ≡ t [ZMOD (b : ℤ) ^ L] := by
    simpa [add_comm, sub_add_cancel] using this
  rw [add_comm]
  exact h2


/-! ### 3g. The pad constraint is a SEARCH BOUND — and it refutes the CRT route

The carry-free form of the crux buys its cleanliness at a price: `2√(n+L)+2 < b^K` bounds the
window position by the square of the modulus.  So `SubLeafA`/`SubLeafB` are not "find `n` anywhere";
they are "find `n` in `[0, b^{2K})`", a *finite* search whose size is only the square of the number
of targets' modulus.  This kills the obvious construction (recorded here so it is not retried). -/

/-- **The search bound.**  The pad hypothesis of `SubLeafA` forces `n + L < (b^K)^2`. -/
theorem lt_pow_two_mul_of_pad {b K m : ℕ} (h : 2 * (Nat.sqrt m : ℤ) + 2 < (b : ℤ) ^ K) :
    m < b ^ (2 * K) := by
  have hN : (2 : ℕ) * Nat.sqrt m + 2 < b ^ K := by
    have hcast : ((2 * Nat.sqrt m + 2 : ℕ) : ℤ) < ((b ^ K : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast hcast
  have h1 : Nat.sqrt m + 1 ≤ b ^ K := by omega
  have h2 : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := by
    have := Nat.lt_succ_sqrt m
    simpa [Nat.succ_eq_add_one] using this
  calc m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := h2
    _ ≤ b ^ K * b ^ K := Nat.mul_le_mul h1 h1
    _ = b ^ (2 * K) := by rw [← pow_add]; ring_nf


/-! ### 3h. `SubLeafA` is monotone in the word length -/

/-- `SubLeafA` at one fixed word length `ℓ`. -/
def SubLeafAAt (b ℓ : ℕ) : Prop :=
  ∀ t : ℕ, t < b ^ ℓ → ∃ n K : ℕ,
    carry b tau (n + (ℓ + K)) < (b : ℤ) ^ K ∧
    paddedSum b tau n (ℓ + K) % (b : ℤ) ^ (ℓ + K) = (t : ℤ) * (b : ℤ) ^ K

theorem subLeafA_iff (b : ℕ) : SubLeafA b ↔ ∀ ℓ, 1 ≤ ℓ → SubLeafAAt b ℓ := Iff.rfl

/-- **Longer words are harder.**  A witness for a word of length `ℓ` also witnesses every shorter
word: enlarge the pad by `ℓ − ℓ'` and the same window works.  So `SubLeafA b` follows from
`SubLeafAAt b ℓ` along ANY sequence `ℓ → ∞` — one never has to treat small `ℓ` separately, and a
proof may choose whichever `ℓ` (e.g. `ℓ` a power of `b`) is most convenient. -/
theorem subLeafAAt_mono (b : ℕ) (hb : 1 ≤ b) {ℓ ℓ' : ℕ} (hle : ℓ' ≤ ℓ)
    (h : SubLeafAAt b ℓ) : SubLeafAAt b ℓ' := by
  intro t' ht'
  have hbpos : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (show 0 < b by omega)
  have ht : t' * b ^ (ℓ - ℓ') < b ^ ℓ := by
    have hbp : 0 < b ^ (ℓ - ℓ') := Nat.pow_pos (by omega)
    calc t' * b ^ (ℓ - ℓ') < b ^ ℓ' * b ^ (ℓ - ℓ') := by
          exact Nat.mul_lt_mul_of_lt_of_le ht' le_rfl hbp
      _ = b ^ ℓ := by rw [← pow_add]; congr 1; omega
  obtain ⟨n, K, hcarry, hsum⟩ := h _ ht
  refine ⟨n, K + (ℓ - ℓ'), ?_, ?_⟩
  · rw [show ℓ' + (K + (ℓ - ℓ')) = ℓ + K from by omega]
    refine hcarry.trans_le (pow_le_pow_right₀ (by exact_mod_cast hb) (by omega))
  · rw [show ℓ' + (K + (ℓ - ℓ')) = ℓ + K from by omega, hsum]
    push_cast
    rw [pow_add]
    ring


/-! ### 3i. Killing slots: the single-surviving-slot identity

If the divisor count in slot `j` is divisible by `b^{j+1}`, that slot contributes nothing modulo
`b^L` (its weight is `b^{L−1−j}`, and `b^{j+1}·b^{L−1−j} = b^L`).  Since the exponent `a` in
`q^a ‖ m` contributes the factor `a+1` to `τ(m)`, such a slot is produced by a CRT condition
`a_j + 1 ≡ 0 (mod b^{j+1})`.  This is the algebraic core of the construction described in the
handoff: kill every slot but one, and let the survivor carry the target. -/
theorem paddedSum_single (b n L j₀ : ℕ) (hj₀ : j₀ < L)
    (h : ∀ j, j < L → j ≠ j₀ → ((b : ℤ) ^ (j + 1) ∣ (tau (n + 1 + j) : ℤ))) :
    paddedSum b tau n L % (b : ℤ) ^ L
      = ((tau (n + 1 + j₀) : ℤ) * (b : ℤ) ^ (L - 1 - j₀)) % (b : ℤ) ^ L := by
  have hdvd : ((b : ℤ) ^ L) ∣
      (paddedSum b tau n L - (tau (n + 1 + j₀) : ℤ) * (b : ℤ) ^ (L - 1 - j₀)) := by
    unfold paddedSum
    rw [← Finset.sum_erase_add (range L) _ (Finset.mem_range.mpr hj₀)]
    simp only [add_sub_cancel_right]
    refine Finset.dvd_sum fun j hj => ?_
    have hmem := Finset.mem_erase.mp hj
    have hne : j ≠ j₀ := hmem.1
    have hlt : j < L := Finset.mem_range.mp hmem.2
    obtain ⟨k, hk⟩ := h j hlt hne
    have hL : (j + 1) + (L - 1 - j) = L := by omega
    refine ⟨k, ?_⟩
    rw [hk, mul_right_comm, ← pow_add, hL]
  have hmod : paddedSum b tau n L ≡ (tau (n + 1 + j₀) : ℤ) * (b : ℤ) ^ (L - 1 - j₀)
      [ZMOD (b : ℤ) ^ L] := Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using hdvd))
  exact hmod


/-! ### 3j. The construction lemma: ONE Dirichlet condition suffices

Put the surviving slot at `j₀ = ℓ − 1`, whose weight is exactly `b^{L−1−(ℓ−1)} = b^K`.  Then the
whole target is carried by a SINGLE divisor count:

    paddedSum ≡ τ(n+ℓ)·b^K  (mod b^L),   and   τ(n+ℓ) ≡ t (mod b^ℓ)  suffices.

This is what makes the construction feasible: it needs *one* integer of controlled shape
(`n+ℓ = r^e·p`, giving `τ = 2(e+1)`, solvable for every `t` when `b` is odd since `2` is then
invertible mod `b^ℓ`), not `ℓ` simultaneous ones — so Dirichlet suffices and Dickson is not needed.
-/
theorem paddedSum_of_construction (b ℓ K t : ℕ) (hb : 2 ≤ b) (hℓ : 1 ≤ ℓ) (n : ℕ)
    (ht : t < b ^ ℓ)
    (hkill : ∀ j, j < ℓ + K → j ≠ ℓ - 1 → ((b : ℤ) ^ (j + 1) ∣ (tau (n + 1 + j) : ℤ)))
    (hsurv : (tau (n + ℓ) : ℤ) ≡ (t : ℤ) [ZMOD (b : ℤ) ^ ℓ]) :
    paddedSum b tau n (ℓ + K) % (b : ℤ) ^ (ℓ + K) = (t : ℤ) * (b : ℤ) ^ K := by
  have hbpos : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (show 0 < b by omega)
  set L := ℓ + K with hL
  have hj₀ : ℓ - 1 < L := by omega
  have hidx : n + 1 + (ℓ - 1) = n + ℓ := by omega
  have hw : L - 1 - (ℓ - 1) = K := by omega
  have h1 := paddedSum_single b n L (ℓ - 1) hj₀ hkill
  rw [hidx, hw] at h1
  rw [h1]
  -- `τ(n+ℓ)·b^K ≡ t·b^K (mod b^{ℓ+K})`
  have h2 : (tau (n + ℓ) : ℤ) * (b : ℤ) ^ K ≡ (t : ℤ) * (b : ℤ) ^ K [ZMOD (b : ℤ) ^ L] := by
    obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.mp hsurv
    refine Int.modEq_iff_dvd.mpr ⟨d, ?_⟩
    have : (t : ℤ) * (b : ℤ) ^ K - (tau (n + ℓ) : ℤ) * (b : ℤ) ^ K
        = ((t : ℤ) - (tau (n + ℓ) : ℤ)) * (b : ℤ) ^ K := by ring
    rw [this, hd, hL, pow_add]
    ring
  rw [h2]
  refine Int.emod_eq_of_lt (by positivity) ?_
  have h3 : (t : ℤ) ≤ (b : ℤ) ^ ℓ - 1 := by
    have : (t : ℤ) < (b : ℤ) ^ ℓ := by exact_mod_cast ht
    omega
  have hbK : (0 : ℤ) < (b : ℤ) ^ K := by positivity
  have h4 : (t : ℤ) * (b : ℤ) ^ K ≤ ((b : ℤ) ^ ℓ - 1) * (b : ℤ) ^ K :=
    mul_le_mul_of_nonneg_right h3 hbK.le
  have h5 : ((b : ℤ) ^ ℓ - 1) * (b : ℤ) ^ K = (b : ℤ) ^ L - (b : ℤ) ^ K := by
    rw [hL, pow_add]; ring
  omega


/-- **The three construction conditions.**  `(K1)` kill every slot but `ℓ−1` by a CRT choice of
prime-power valuations; `(K2)` make the surviving divisor count hit the target; `(K3)` keep the
carry inside the pad.  `subLeafA_of_constructionInputs` shows these suffice for `SubLeafA`, hence
for `ConjC2`. -/
def ConstructionInputs (b : ℕ) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ t : ℕ, t < b ^ ℓ → ∃ n K : ℕ,
    (∀ j, j < ℓ + K → j ≠ ℓ - 1 → ((b : ℤ) ^ (j + 1) ∣ (tau (n + 1 + j) : ℤ))) ∧
    ((tau (n + ℓ) : ℤ) ≡ (t : ℤ) [ZMOD (b : ℤ) ^ ℓ]) ∧
    carry b tau (n + (ℓ + K)) < (b : ℤ) ^ K

theorem subLeafA_of_constructionInputs (b : ℕ) (hb : 3 ≤ b) (h : ConstructionInputs b) :
    SubLeafA b := by
  intro ℓ hℓ t ht
  obtain ⟨n, K, hkill, hsurv, hcarry⟩ := h ℓ hℓ t ht
  exact ⟨n, K, hcarry, paddedSum_of_construction b ℓ K t (by omega) hℓ n ht hkill hsurv⟩


/-! ### 3k. (K1) pointwise: the valuation at one prime divides `τ` -/

/-- If `q^a ‖ m` then `a + 1 ∣ τ(m)`.  This is the mechanism behind condition (K1): a CRT choice
of `a` with `b^{j+1} ∣ a + 1` forces `b^{j+1} ∣ τ(n+1+j)`, killing that slot
(`paddedSum_single`). -/
theorem succ_factorization_dvd_tau {q m : ℕ} (hq : q.Prime) (hm : m ≠ 0) :
    (m.factorization q + 1) ∣ tau m := by
  classical
  rcases Nat.eq_zero_or_pos (m.factorization q) with h0 | hpos
  · simp [h0]
  · have hmem : q ∈ m.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.2 (by omega)
    rw [tau, Nat.card_divisors hm]
    exact Finset.dvd_prod_of_mem (fun p => m.factorization p + 1) hmem

/-- The (K1) slot condition in the form the CRT step will supply it. -/
theorem pow_dvd_tau_of_factorization {b j q m : ℕ} (hq : q.Prime) (hm : m ≠ 0)
    (h : b ^ (j + 1) ∣ (m.factorization q + 1)) : (b : ℤ) ^ (j + 1) ∣ (tau m : ℤ) := by
  have : b ^ (j + 1) ∣ tau m := h.trans (succ_factorization_dvd_tau hq hm)
  exact_mod_cast Int.natCast_dvd_natCast.2 this


/-- `m ≡ q^a (mod q^{a+1})` pins the valuation: `v_q(m) = a`.  This is how the CRT step delivers
the exponents of (K1). -/
theorem factorization_eq_of_modEq {q a m : ℕ} (hq : q.Prime) (hm : m ≠ 0)
    (h : m ≡ q ^ a [MOD q ^ (a + 1)]) : m.factorization q = a := by
  have hq2 : 2 ≤ q := hq.two_le
  have hqa : 0 < q ^ a := Nat.pow_pos (by omega)
  have hlt : q ^ a < q ^ (a + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hmod : m % q ^ (a + 1) = q ^ a := by
    rw [Nat.ModEq] at h
    rw [h, Nat.mod_eq_of_lt hlt]
  obtain ⟨w, hw⟩ : ∃ w, m = q ^ a * (q * w + 1) := by
    refine ⟨m / q ^ (a + 1), ?_⟩
    have := Nat.div_add_mod m (q ^ (a + 1))
    rw [hmod] at this
    calc m = q ^ (a + 1) * (m / q ^ (a + 1)) + q ^ a := this.symm
      _ = q ^ a * (q * (m / q ^ (a + 1)) + 1) := by rw [pow_succ]; ring
  have hu : ¬ q ∣ (q * w + 1) := by
    intro hdvd
    have : q ∣ 1 := (Nat.dvd_add_right ⟨w, rfl⟩).mp hdvd
    exact absurd (Nat.le_of_dvd one_pos this) (by omega)
  have hune : q * w + 1 ≠ 0 := by omega
  rw [hw, Nat.factorization_mul (by positivity) hune]
  simp [Nat.Prime.factorization_pow hq, Nat.factorization_eq_zero_of_not_dvd hu]



/-! ### 3m. (K2): the survivor value is a theorem

The survivor entry is taken of the shape `n + ℓ = 2^a·p` with `p` an odd prime, so that
`τ(n+ℓ) = 2(a+1)` — which runs over every residue mod `b^ℓ` when `b` is odd and over every EVEN
residue when `b` is even.  The modulus `M` being odd makes `2^a` invertible mod `M` (explicitly:
`(M+1)/2` inverts `2`), so the progression condition `n ≡ n₀ (mod M)` collapses to a single
congruence on `p` — one application of Dirichlet's theorem on primes in arithmetic progressions.
-/

/-- `τ(2^a) = a + 1`. -/
theorem tau_two_pow (a : ℕ) : tau (2 ^ a) = a + 1 := by
  rw [tau, Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]

/-- `τ(p) = 2` for a prime `p`. -/
theorem tau_prime {p : ℕ} (hp : p.Prime) : tau p = 2 := by
  rw [tau, Nat.Prime.divisors hp, Finset.card_pair (Ne.symm hp.ne_one)]

/-- **The survivor shape.**  `τ(2^a·p) = 2(a+1)` for an odd prime `p`. -/
theorem tau_two_pow_mul_prime {a p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    tau (2 ^ a * p) = 2 * (a + 1) := by
  have hcop : Nat.Coprime (2 ^ a) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  rw [tau_mul_coprime hcop, tau_two_pow, tau_prime hp]
  ring

/-- **The exponent equation.**  `2(a+1) ≡ t (mod b^ℓ)` is solvable with `a < b^ℓ` exactly when
`t` is even or `b` is odd — the parity condition of `SurvivorLeaf`. -/
theorem exists_survivor_exponent (b ℓ t : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) (ht : t < b ^ ℓ)
    (hpar : 2 ∣ b → 2 ∣ t) :
    ∃ a : ℕ, a < b ^ ℓ ∧ (2 * ((a : ℤ) + 1)) ≡ (t : ℤ) [ZMOD (b : ℤ) ^ ℓ] := by
  have hN3 : 3 ≤ b ^ ℓ := by
    calc 3 ≤ b := hb
      _ = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ ℓ := Nat.pow_le_pow_right (by omega) hℓ
  have hcast : (b : ℤ) ^ ℓ = ((b ^ ℓ : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨T, hT2, hTle, hTeven, hTmod⟩ :
      ∃ T : ℕ, 2 ≤ T ∧ T ≤ 2 * b ^ ℓ ∧ 2 ∣ T ∧
        (T : ℤ) ≡ (t : ℤ) [ZMOD ((b ^ ℓ : ℕ) : ℤ)] := by
    by_cases h0 : t = 0
    · refine ⟨2 * b ^ ℓ, by omega, by omega, ⟨b ^ ℓ, rfl⟩, ?_⟩
      rw [h0]
      push_cast
      exact Int.modEq_iff_dvd.mpr ⟨-2, by ring⟩
    · by_cases he : 2 ∣ t
      · exact ⟨t, by omega, by omega, he, Int.ModEq.refl _⟩
      · have hbo : ¬ 2 ∣ b := fun hb2 => he (hpar hb2)
        have hNo : ¬ 2 ∣ b ^ ℓ := fun hd => hbo (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd)
        refine ⟨t + b ^ ℓ, by omega, by omega, by omega, ?_⟩
        push_cast
        exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
  refine ⟨T / 2 - 1, by omega, ?_⟩
  have hAT : 2 * ((T / 2 - 1) + 1) = T := by omega
  rw [hcast]
  have hcastT : (2 * (((T / 2 - 1 : ℕ) : ℤ) + 1)) = (T : ℤ) := by exact_mod_cast hAT
  rw [hcastT]
  exact hTmod

/-- **The exponent is free to be LARGE.**  The exponent equation `2(a+1) ≡ t (mod b^ℓ)` only
pins `a` modulo `b^ℓ`, so `a` may be pushed above any prescribed bound `A` at the cost of
`a < (A+1)·b^ℓ`.  This matters for the 2-adic reduction `tau_shift_two_adic`: the shifts
`e = K+1+k` must satisfy `e < 2^a`, which fails outright for the small exponents the bare
equation returns.  The budget `a ≤ b^{K/4}` leaves room for `A` as large as `b^{K/4 − ℓ − 1}`. -/
theorem exists_survivor_exponent_large (b ℓ t A : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) (ht : t < b ^ ℓ)
    (hpar : 2 ∣ b → 2 ∣ t) :
    ∃ a : ℕ, A ≤ a ∧ a < (A + 1) * b ^ ℓ ∧
      (2 * ((a : ℤ) + 1)) ≡ (t : ℤ) [ZMOD (b : ℤ) ^ ℓ] := by
  obtain ⟨a₀, ha₀, hmod⟩ := exists_survivor_exponent b ℓ t hb hℓ ht hpar
  have hbl : 1 ≤ b ^ ℓ := Nat.one_le_pow _ _ (by omega)
  refine ⟨a₀ + A * b ^ ℓ, ?_, ?_, ?_⟩
  · have : A * 1 ≤ A * b ^ ℓ := Nat.mul_le_mul_left A hbl
    omega
  · have : (A + 1) * b ^ ℓ = A * b ^ ℓ + b ^ ℓ := by ring
    omega
  · have hcast : ((a₀ + A * b ^ ℓ : ℕ) : ℤ) = (a₀ : ℤ) + (A : ℤ) * (b : ℤ) ^ ℓ := by
      push_cast; ring
    rw [hcast]
    refine Int.ModEq.trans ?_ hmod
    refine Int.ModEq.symm ?_
    refine Int.modEq_iff_dvd.2 ⟨2 * (A : ℤ), ?_⟩
    ring

/-- **(K2), discharged.**  In an odd progression `n ≡ n₀ (mod M)` whose survivor entry is coprime
to `M`, there are an exponent `a < b^ℓ` and a residue `r` coprime to `M` such that EVERY odd
prime `p ≡ r (mod M)` makes `2^a·p` land in the progression with `τ(2^a·p) ≡ t (mod b^ℓ)`.
Dirichlet then supplies arbitrarily large such `p`; choosing one with a small tail carry is all
that `SurvivorLeaf` still needs (`CarryLeaf`). -/
theorem exists_survivor_data (b ℓ M n₀ t : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) (hM : 0 < M)
    (h2M : Nat.Coprime 2 M) (hcop : Nat.Coprime (n₀ + ℓ) M) (ht : t < b ^ ℓ)
    (hpar : 2 ∣ b → 2 ∣ t) :
    ∃ a r : ℕ, a < b ^ ℓ ∧ Nat.Coprime r M ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ≡ r [MOD M] →
        (2 ^ a * p ≡ n₀ + ℓ [MOD M]) ∧
        ((tau (2 ^ a * p) : ℤ) ≡ (t : ℤ) [ZMOD (b : ℤ) ^ ℓ]) := by
  obtain ⟨a, ha, haT⟩ := exists_survivor_exponent b ℓ t hb hℓ ht hpar
  have hModd : ¬ 2 ∣ M := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h2M
  set c := (M + 1) / 2 with hc
  have h2cM : 2 * c = M + 1 := by omega
  have hccop : Nat.Coprime c M := by
    have hd1 : Nat.gcd c M ∣ M + 1 := by
      rw [← h2cM]; exact Dvd.dvd.mul_left (Nat.gcd_dvd_left c M) 2
    have hd2 : Nat.gcd c M ∣ M := Nat.gcd_dvd_right c M
    have : Nat.gcd c M ∣ 1 := by
      have := Nat.dvd_sub hd1 hd2
      simpa using this
    exact Nat.dvd_one.mp this
  have h2c : 2 * c ≡ 1 [MOD M] := by
    rw [h2cM]
    exact ((Nat.modEq_iff_dvd' (by omega)).mpr ⟨1, by omega⟩).symm
  have hpowc : 2 ^ a * c ^ a ≡ 1 [MOD M] := by
    have := h2c.pow a
    rwa [mul_pow, one_pow] at this
  set X := (n₀ + ℓ) * c ^ a with hX
  have hXcop : Nat.Coprime X M := Nat.Coprime.mul_left hcop (Nat.Coprime.pow_left _ hccop)
  refine ⟨a, X % M, ha, ?_, ?_⟩
  · have h1 : Nat.gcd M X = 1 := (Nat.coprime_comm.mp hXcop)
    rw [Nat.gcd_rec] at h1
    exact h1
  · intro p hp hp2 hpr
    constructor
    · calc 2 ^ a * p ≡ 2 ^ a * (X % M) [MOD M] := Nat.ModEq.mul_left _ hpr
        _ ≡ 2 ^ a * X [MOD M] := Nat.ModEq.mul_left _ (Nat.mod_modEq X M)
        _ = (n₀ + ℓ) * (2 ^ a * c ^ a) := by rw [hX]; ring
        _ ≡ (n₀ + ℓ) * 1 [MOD M] := Nat.ModEq.mul_left _ hpowc
        _ = n₀ + ℓ := by ring
    · rw [tau_two_pow_mul_prime hp hp2]
      push_cast
      exact haT

/-- **(K2) with a large exponent.**  Same as `exists_survivor_data`, but the exponent `a` may
be pushed above any prescribed `A` — which is what the 2-adic reduction of the shifts needs
(`exists_survivor_exponent_large`). -/
theorem exists_survivor_data_large (b ℓ M n₀ t A : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) (hM : 0 < M)
    (h2M : Nat.Coprime 2 M) (hcop : Nat.Coprime (n₀ + ℓ) M) (ht : t < b ^ ℓ)
    (hpar : 2 ∣ b → 2 ∣ t) :
    ∃ a r : ℕ, A ≤ a ∧ a < (A + 1) * b ^ ℓ ∧ Nat.Coprime r M ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ≡ r [MOD M] →
        (2 ^ a * p ≡ n₀ + ℓ [MOD M]) ∧
        ((tau (2 ^ a * p) : ℤ) ≡ (t : ℤ) [ZMOD (b : ℤ) ^ ℓ]) := by
  obtain ⟨a, haA, ha, haT⟩ := exists_survivor_exponent_large b ℓ t A hb hℓ ht hpar
  have hModd : ¬ 2 ∣ M := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h2M
  set c := (M + 1) / 2 with hc
  have h2cM : 2 * c = M + 1 := by omega
  have hccop : Nat.Coprime c M := by
    have hd1 : Nat.gcd c M ∣ M + 1 := by
      rw [← h2cM]; exact Dvd.dvd.mul_left (Nat.gcd_dvd_left c M) 2
    have hd2 : Nat.gcd c M ∣ M := Nat.gcd_dvd_right c M
    have : Nat.gcd c M ∣ 1 := by
      have := Nat.dvd_sub hd1 hd2
      simpa using this
    exact Nat.dvd_one.mp this
  have h2c : 2 * c ≡ 1 [MOD M] := by
    rw [h2cM]
    exact ((Nat.modEq_iff_dvd' (by omega)).mpr ⟨1, by omega⟩).symm
  have hpowc : 2 ^ a * c ^ a ≡ 1 [MOD M] := by
    have := h2c.pow a
    rwa [mul_pow, one_pow] at this
  set X := (n₀ + ℓ) * c ^ a with hX
  have hXcop : Nat.Coprime X M := Nat.Coprime.mul_left hcop (Nat.Coprime.pow_left _ hccop)
  refine ⟨a, X % M, haA, ha, ?_, ?_⟩
  · have h1 : Nat.gcd M X = 1 := (Nat.coprime_comm.mp hXcop)
    rw [Nat.gcd_rec] at h1
    exact h1
  · intro p hp hp2 hpr
    constructor
    · calc 2 ^ a * p ≡ 2 ^ a * (X % M) [MOD M] := Nat.ModEq.mul_left _ hpr
        _ ≡ 2 ^ a * X [MOD M] := Nat.ModEq.mul_left _ (Nat.mod_modEq X M)
        _ = (n₀ + ℓ) * (2 ^ a * c ^ a) := by rw [hX]; ring
        _ ≡ (n₀ + ℓ) * 1 [MOD M] := Nat.ModEq.mul_left _ hpowc
        _ = n₀ + ℓ := by ring
    · rw [tau_two_pow_mul_prime hp hp2]
      push_cast
      exact haT


/-! ### 3l. (K1): the kill progression is a single residue class

The slot-killing conditions of `ConstructionInputs` are pure congruences.  For each slot `j` we
pin the valuation of `n+1+j` at `L` *distinct* primes to be exactly `b−1`; each such prime
contributes a factor `(b−1)+1 = b` to `τ(n+1+j)`, so `b^L ∣ τ(n+1+j)`, which is more than the
`b^{j+1}` that slot needs.  Every condition is a congruence to a prime-power modulus `q^b`, the
moduli are pairwise coprime, so CRT collapses the whole system to one residue class.

**The design point (2026-09-24).**  Using `L` primes at exponent `b−1` rather than ONE prime at
exponent `b^{j+1}−1` keeps the modulus at `exp(O(b L⁴))` instead of `exp(b^{L+1})`.  Since the
pad budget `b^K` is itself exponential in `L`, this is what makes the remaining analytic
condition (K3) a statement about the *average* of `τ` (which is `≍ log M = poly(L) ≪ b^K`)
rather than about its normal order. -/

/-- If `m` has valuation exactly `b−1` at each of the primes of a finset `S`, then `b^{|S|}`
divides `τ(m)`: each such prime contributes the factor `(b−1)+1 = b` to `τ(m) = ∏ (v_p+1)`. -/
theorem pow_card_dvd_tau {b m : ℕ} (hb : 2 ≤ b) (hm : m ≠ 0) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ m.factorization q = b - 1) :
    b ^ S.card ∣ tau m := by
  classical
  have hsub : S ⊆ m.primeFactors := by
    intro q hq
    have hqv := (hS q hq).2
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.2 (by omega)
  have hprod : ∏ q ∈ S, (m.factorization q + 1) = b ^ S.card := by
    rw [Finset.prod_congr rfl (fun q hq => by rw [(hS q hq).2]; omega : ∀ q ∈ S,
      m.factorization q + 1 = b), Finset.prod_const]
  rw [tau, Nat.card_divisors hm, ← hprod]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

/-- The next prime after `x`, from Bertrand's postulate: `x < nextPrime x ≤ 2x + 2`. -/
noncomputable def nextPrime (x : ℕ) : ℕ :=
  (Nat.exists_prime_lt_and_le_two_mul (x + 1) (Nat.succ_ne_zero x)).choose

theorem nextPrime_prime (x : ℕ) : (nextPrime x).Prime :=
  (Nat.exists_prime_lt_and_le_two_mul (x + 1) (Nat.succ_ne_zero x)).choose_spec.1

theorem lt_nextPrime (x : ℕ) : x < nextPrime x :=
  lt_trans (Nat.lt_succ_self x)
    (Nat.exists_prime_lt_and_le_two_mul (x + 1) (Nat.succ_ne_zero x)).choose_spec.2.1

theorem nextPrime_le (x : ℕ) : nextPrime x ≤ 2 * x + 2 := by
  have h := (Nat.exists_prime_lt_and_le_two_mul (x + 1) (Nat.succ_ne_zero x)).choose_spec.2.2
  have he : nextPrime x
      = (Nat.exists_prime_lt_and_le_two_mul (x + 1) (Nat.succ_ne_zero x)).choose := rfl
  rw [he]; omega

/-- A strictly increasing sequence of primes, all greater than `B`. -/
noncomputable def bigPrime (B : ℕ) : ℕ → ℕ
  | 0 => nextPrime B
  | k + 1 => nextPrime (bigPrime B k)

theorem bigPrime_prime (B k : ℕ) : (bigPrime B k).Prime := by
  cases k <;> exact nextPrime_prime _

theorem lt_bigPrime (B k : ℕ) : B < bigPrime B k := by
  induction k with
  | zero => exact lt_nextPrime B
  | succ k ih => exact ih.trans (lt_nextPrime _)

theorem bigPrime_strictMono (B : ℕ) : StrictMono (bigPrime B) :=
  strictMono_nat_of_lt_succ fun _ => lt_nextPrime _

theorem bigPrime_injective (B : ℕ) : Function.Injective (bigPrime B) :=
  (bigPrime_strictMono B).injective

/-- The Bertrand recursion doubles at each step: `bigPrime B k + 2 ≤ 2^{k+1}·(B+2)`. -/
theorem bigPrime_le (B k : ℕ) : bigPrime B k + 2 ≤ 2 ^ (k + 1) * (B + 2) := by
  induction k with
  | zero =>
    have := nextPrime_le B
    simp only [bigPrime, pow_one]
    omega
  | succ k ih =>
    have h := nextPrime_le (bigPrime B k)
    have : bigPrime B (k + 1) = nextPrime (bigPrime B k) := rfl
    rw [this]
    calc nextPrime (bigPrime B k) + 2 ≤ 2 * (bigPrime B k + 2) := by omega
      _ ≤ 2 * (2 ^ (k + 1) * (B + 2)) := by omega
      _ = 2 ^ (k + 1 + 1) * (B + 2) := by ring


/-- Pinning a valuation is a congruence: `n + c ≡ q^{b−1} (mod q^b)` forces `v_q(n+c) = b−1`. -/
theorem factorization_shift_of_modEq {b q c n : ℕ} (hb : 2 ≤ b) (hq : q.Prime)
    (h : n + c ≡ q ^ (b - 1) [MOD q ^ b]) : (n + c).factorization q = b - 1 := by
  have hb1 : b - 1 + 1 = b := by omega
  have hq2 : 2 ≤ q := hq.two_le
  have hpos : 0 < q ^ (b - 1) := Nat.pow_pos (by omega)
  have hne : n + c ≠ 0 := by
    intro h0
    rw [h0] at h
    have hlt : q ^ (b - 1) < q ^ b := Nat.pow_lt_pow_right (by omega) (by omega)
    have h2 : (0 : ℕ) % q ^ b = q ^ (b - 1) % q ^ b := h
    rw [Nat.zero_mod, Nat.mod_eq_of_lt hlt] at h2
    omega
  exact factorization_eq_of_modEq hq hne (by rw [hb1]; exact h)

/-- **The CRT core of (K1).**  For a sequence of distinct primes `Q` and arbitrary shifts `c`,
the conditions `v_{Q k}(n + c k) = b − 1` for `k < N` hold simultaneously on a full residue
class modulo `∏_{k<N} (Q k)^b`. -/
theorem exists_pin_progression {b : ℕ} (hb : 2 ≤ b) (Q c : ℕ → ℕ)
    (hQp : ∀ k, (Q k).Prime) (hQinj : Function.Injective Q) (N : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≡ n₀ [MOD ∏ k ∈ range N, Q k ^ b] →
      ∀ k, k < N → (n + c k).factorization (Q k) = b - 1 := by
  induction N with
  | zero => exact ⟨0, fun n _ k hk => absurd hk (by omega)⟩
  | succ N ih =>
    obtain ⟨n₀, hn₀⟩ := ih
    set q := Q N with hq
    have hqp : q.Prime := hQp N
    have hq2 : 2 ≤ q := hqp.two_le
    have hqb : 0 < q ^ b := Nat.pow_pos (by omega)
    set n₁ := q ^ (b - 1) + q ^ b * (c N + 1) - c N with hn₁
    have hn₁c : n₁ + c N = q ^ (b - 1) + q ^ b * (c N + 1) := by
      have h1 : c N + 1 ≤ q ^ b * (c N + 1) := Nat.le_mul_of_pos_left _ hqb
      omega
    have hcop : Nat.Coprime (∏ k ∈ range N, Q k ^ b) (q ^ b) := by
      refine Nat.Coprime.prod_left (fun k hk => ?_)
      have hkN : k < N := Finset.mem_range.mp hk
      have hne : Q k ≠ q := by
        intro hcon
        have := hQinj (hcon.trans hq)
        omega
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hQp k) hqp).2 hne)
    obtain ⟨m, hm1, hm2⟩ := Nat.chineseRemainder hcop n₀ n₁
    refine ⟨m, fun n hn k hk => ?_⟩
    rw [Finset.prod_range_succ] at hn
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
    · exact hn₀ n ((hn.of_dvd (dvd_mul_right _ _)).trans hm1) k hk'
    · subst hk'
      refine factorization_shift_of_modEq hb hqp ?_
      have h1 : n ≡ n₁ [MOD q ^ b] := (hn.of_dvd (dvd_mul_left _ _)).trans hm2
      have h2 : n + c k ≡ n₁ + c k [MOD q ^ b] := h1.add_right _
      refine h2.trans ?_
      rw [hn₁c]
      exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mpr ⟨c k + 1, by omega⟩).symm



/-- The primes used by the kill progression for a window of `L` slots: distinct primes above
`L+2`, so none of them divides two different window entries, nor the survivor. -/
noncomputable def killPrime (L k : ℕ) : ℕ := bigPrime (L + 2) k

theorem killPrime_prime (L k : ℕ) : (killPrime L k).Prime := bigPrime_prime _ _

theorem lt_killPrime (L k : ℕ) : L + 2 < killPrime L k := lt_bigPrime _ _

theorem killPrime_injective (L : ℕ) : Function.Injective (killPrime L) := bigPrime_injective _

/-- The CRT modulus of the kill progression: one prime power `q^b` for each of the `(L−1)·L`
pinned valuations (`L` primes for each of the `L−1` killed slots). -/
noncomputable def killModulus (b L : ℕ) : ℕ := ∏ k ∈ range ((L - 1) * L), killPrime L k ^ b

theorem killModulus_pos (b L : ℕ) : 0 < killModulus b L :=
  Finset.prod_pos fun k _ => Nat.pow_pos (killPrime_prime L k).pos

theorem coprime_two_killModulus (b L : ℕ) : Nat.Coprime 2 (killModulus b L) := by
  refine Nat.Coprime.prod_right fun k _ => Nat.Coprime.pow_right _ ?_
  refine (Nat.coprime_primes Nat.prime_two (killPrime_prime L k)).2 ?_
  have := lt_killPrime L k
  omega

/-- **(K1): the slot-killing conditions hold on a full residue class.**  For a window of `L`
slots with survivor `j₀` there is a residue `n₀` modulo `killModulus b L` such that *every* `n`
in that class kills every slot except `j₀` — and the survivor entry `n + 1 + j₀` is coprime to
the modulus, so it remains free to be prescribed by a Dirichlet prime.

Mechanism: at slot `j ≠ j₀` we pin `v_q(n+1+j) = b−1` at `L` distinct primes `q`, so
`b^L ∣ τ(n+1+j)` (`pow_card_dvd_tau`), which is more than the `b^{j+1}` the slot needs; all the
pinning conditions are congruences to pairwise coprime moduli `q^b` (`exists_pin_progression`). -/
theorem exists_kill_progression' (b L j₀ : ℕ) (hb : 2 ≤ b) (hL : 1 ≤ L) (hj₀ : j₀ < L) :
    ∃ n₀ : ℕ, Nat.Coprime (n₀ + 1 + j₀) (killModulus b L) ∧
      (∀ n : ℕ, n ≡ n₀ [MOD killModulus b L] →
        ∀ j, j < L → j ≠ j₀ → ((b : ℤ) ^ (j + 1) ∣ (tau (n + 1 + j) : ℤ))) ∧
      (∀ n : ℕ, n ≡ n₀ [MOD killModulus b L] → ∀ e : ℕ, L < 1 + j₀ + e →
        ∀ q : ℕ, q.Prime → q ∣ killModulus b L → q ∣ n + 1 + j₀ + e → q ≤ j₀ + e) ∧
      (3 ≤ b → ∀ n : ℕ, n ≡ n₀ [MOD killModulus b L] → ∀ e : ℕ, L < 1 + j₀ + e →
        ∀ q : ℕ, q.Prime → q ∣ killModulus b L → j₀ + e < q * q →
          ¬ (q * q ∣ n + 1 + j₀ + e)) ∧
      (∀ n : ℕ, n ≡ n₀ [MOD killModulus b L] → ∀ e : ℕ, L < 1 + j₀ + e →
        ∀ q : ℕ, q.Prime → q ∣ killModulus b L →
          ∃ c : ℕ, 1 ≤ c ∧ c ≤ L ∧
            ∀ j : ℕ, j ≤ b - 1 → q ^ j ∣ n + 1 + j₀ + e →
              q ^ j ∣ (1 + j₀ + e) - c) := by
  classical
  set sl : ℕ → ℕ := fun s => if s < j₀ then s else s + 1 with hsl
  set c : ℕ → ℕ := fun k => 1 + sl (k / L) with hc
  obtain ⟨n₀, hn₀⟩ :=
    exists_pin_progression hb (killPrime L) c (killPrime_prime L) (killPrime_injective L)
      ((L - 1) * L)
  have hmod : killModulus b L = ∏ k ∈ range ((L - 1) * L), killPrime L k ^ b := rfl
  have hck : ∀ k, k < (L - 1) * L → 1 ≤ c k ∧ c k ≤ L ∧ c k ≠ 1 + j₀ := by
    intro k hk
    have hdiv : k / L < L - 1 := by
      by_contra hcon
      push_neg at hcon
      have h1 : (L - 1) * L ≤ k / L * L := Nat.mul_le_mul_right _ hcon
      have h2 : k / L * L ≤ k := Nat.div_mul_le_self k L
      omega
    have key : ∀ d : ℕ, d < L - 1 → 1 ≤ 1 + sl d ∧ 1 + sl d ≤ L ∧ 1 + sl d ≠ 1 + j₀ := by
      intro d hd
      simp only [hsl]
      split <;> omega
    exact key (k / L) hdiv
  refine ⟨n₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmod]
    refine Nat.Coprime.prod_right fun k hk => Nat.Coprime.pow_right _ ?_
    have hkN : k < (L - 1) * L := Finset.mem_range.mp hk
    obtain ⟨hc1, hcL, hcne⟩ := hck k hkN
    have hqp : (killPrime L k).Prime := killPrime_prime L k
    have hqL : L + 2 < killPrime L k := lt_killPrime L k
    have hpin : (n₀ + c k).factorization (killPrime L k) = b - 1 :=
      hn₀ n₀ (Nat.ModEq.refl _) k hkN
    have hne0 : n₀ + c k ≠ 0 := by omega
    have hqdvd : killPrime L k ∣ n₀ + c k :=
      (Nat.Prime.dvd_iff_one_le_factorization hqp hne0).2 (by omega)
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hqp).2 fun hdvd => ?_
    have hdvd' : killPrime L k ∣ n₀ + (1 + j₀) := by rwa [← add_assoc]
    rcases Nat.lt_or_ge (c k) (1 + j₀) with hlt | hge
    · have hd : killPrime L k ∣ (n₀ + (1 + j₀)) - (n₀ + c k) := Nat.dvd_sub hdvd' hqdvd
      rw [Nat.add_sub_add_left] at hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    · have hd : killPrime L k ∣ (n₀ + c k) - (n₀ + (1 + j₀)) := Nat.dvd_sub hqdvd hdvd'
      rw [Nat.add_sub_add_left] at hd
      have := Nat.le_of_dvd (by omega) hd
      omega
  · intro n hn j hj hjne
    obtain ⟨s, hsL, hslj⟩ : ∃ s, s < L - 1 ∧ sl s = j := by
      by_cases h : j < j₀
      · exact ⟨j, by omega, by simp only [hsl, if_pos h]⟩
      · refine ⟨j - 1, by omega, ?_⟩
        have h1 : ¬ (j - 1 < j₀) := by omega
        simp only [hsl, if_neg h1]
        omega
    set S : Finset ℕ := (range L).image (fun i => killPrime L (s * L + i)) with hS
    have hcard : S.card = L := by
      rw [hS, Finset.card_image_of_injective _ (fun i i' hii => by
        have := killPrime_injective L hii; omega), Finset.card_range]
    have hne0 : n + 1 + j ≠ 0 := by omega
    have hmem : ∀ q ∈ S, q.Prime ∧ (n + 1 + j).factorization q = b - 1 := by
      intro q hqS
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hqS
      have hi' : i < L := Finset.mem_range.mp hi
      have hkN : s * L + i < (L - 1) * L := by
        have h1 : (s + 1) * L ≤ (L - 1) * L := Nat.mul_le_mul_right _ (by omega)
        have h2 : (s + 1) * L = s * L + L := by ring
        omega
      have hdiv : (s * L + i) / L = s := by
        have he : s * L + i = i + L * s := by ring
        rw [he, Nat.add_mul_div_left _ _ (by omega : 0 < L), Nat.div_eq_of_lt hi', Nat.zero_add]
      have hcv : c (s * L + i) = 1 + j := by simp only [hc, hdiv, hslj]
      have hpin := hn₀ n hn (s * L + i) hkN
      rw [hcv] at hpin
      refine ⟨killPrime_prime L _, ?_⟩
      rw [show n + 1 + j = n + (1 + j) by ring]
      exact hpin
    have hdvdL : b ^ L ∣ tau (n + 1 + j) := by
      have := pow_card_dvd_tau hb hne0 S hmem
      rwa [hcard] at this
    have hstep : b ^ (j + 1) ∣ b ^ L := pow_dvd_pow b (by omega)
    exact_mod_cast Int.natCast_dvd_natCast.2 (hstep.trans hdvdL)
  · intro n hn e he q hqp hqM hqd
    rw [hmod] at hqM
    obtain ⟨k, hk, hqk⟩ := (Nat.Prime.prime hqp).exists_mem_finset_dvd hqM
    have hkN : k < (L - 1) * L := Finset.mem_range.mp hk
    have hq_eq : q = killPrime L k :=
      (Nat.prime_dvd_prime_iff_eq hqp (killPrime_prime L k)).1
        (Nat.Prime.dvd_of_dvd_pow hqp hqk)
    obtain ⟨hc1, hcL, -⟩ := hck k hkN
    have hpin : (n + c k).factorization (killPrime L k) = b - 1 := hn₀ n hn k hkN
    have hne0 : n + c k ≠ 0 := by omega
    have hqdvd : killPrime L k ∣ n + c k :=
      (Nat.Prime.dvd_iff_one_le_factorization (killPrime_prime L k) hne0).2 (by omega)
    have hqd' : killPrime L k ∣ n + (1 + j₀ + e) := by
      rw [hq_eq] at hqd
      rw [show n + (1 + j₀ + e) = n + 1 + j₀ + e by ring]
      exact hqd
    have hd : killPrime L k ∣ (n + (1 + j₀ + e)) - (n + c k) := Nat.dvd_sub hqd' hqdvd
    rw [Nat.add_sub_add_left] at hd
    have hle := Nat.le_of_dvd (by omega) hd
    rw [hq_eq]
    omega
  · intro hb3 n hn e he q hqp hqM hqsq hcon
    rw [hmod] at hqM
    obtain ⟨k, hk, hqk⟩ := (Nat.Prime.prime hqp).exists_mem_finset_dvd hqM
    have hkN : k < (L - 1) * L := Finset.mem_range.mp hk
    have hq_eq : q = killPrime L k :=
      (Nat.prime_dvd_prime_iff_eq hqp (killPrime_prime L k)).1
        (Nat.Prime.dvd_of_dvd_pow hqp hqk)
    obtain ⟨hc1, hcL, -⟩ := hck k hkN
    have hpin : (n + c k).factorization (killPrime L k) = b - 1 := hn₀ n hn k hkN
    have hne0 : n + c k ≠ 0 := by omega
    -- `q^2 ∣ n + c k`, because the valuation there is `b − 1 ≥ 2`
    have hsq : killPrime L k ^ 2 ∣ n + c k := by
      refine (Nat.Prime.pow_dvd_iff_le_factorization (killPrime_prime L k) hne0).2 ?_
      rw [hpin]; omega
    have hsq' : q * q ∣ n + c k := by
      rw [hq_eq, show killPrime L k * killPrime L k = killPrime L k ^ 2 by ring]
      exact hsq
    have hqd' : q * q ∣ n + (1 + j₀ + e) := by
      rw [show n + (1 + j₀ + e) = n + 1 + j₀ + e by ring]; exact hcon
    have hd : q * q ∣ (n + (1 + j₀ + e)) - (n + c k) := Nat.dvd_sub hqd' hsq'
    rw [Nat.add_sub_add_left] at hd
    have hle := Nat.le_of_dvd (by omega) hd
    omega
  · intro n hn e he q hqp hqM
    rw [hmod] at hqM
    obtain ⟨k, hk, hqk⟩ := (Nat.Prime.prime hqp).exists_mem_finset_dvd hqM
    have hkN : k < (L - 1) * L := Finset.mem_range.mp hk
    have hq_eq : q = killPrime L k :=
      (Nat.prime_dvd_prime_iff_eq hqp (killPrime_prime L k)).1
        (Nat.Prime.dvd_of_dvd_pow hqp hqk)
    obtain ⟨hc1, hcL, -⟩ := hck k hkN
    have hpin : (n + c k).factorization (killPrime L k) = b - 1 := hn₀ n hn k hkN
    have hne0 : n + c k ≠ 0 := by omega
    refine ⟨c k, hc1, hcL, fun j hj hdvd => ?_⟩
    have hjp : q ^ j ∣ n + c k := by
      rw [hq_eq]
      refine (Nat.Prime.pow_dvd_iff_le_factorization (killPrime_prime L k) hne0).2 ?_
      rw [hpin]; exact hj
    have hdvd' : q ^ j ∣ n + (1 + j₀ + e) := by
      rw [show n + (1 + j₀ + e) = n + 1 + j₀ + e by ring]; exact hdvd
    have hd : q ^ j ∣ (n + (1 + j₀ + e)) - (n + c k) := Nat.dvd_sub hdvd' hjp
    rwa [Nat.add_sub_add_left] at hd

/-- **The kill progression, in the form the rest of the file consumes.** -/
theorem exists_kill_progression (b L j₀ : ℕ) (hb : 2 ≤ b) (hL : 1 ≤ L) (hj₀ : j₀ < L) :
    ∃ n₀ : ℕ, Nat.Coprime (n₀ + 1 + j₀) (killModulus b L) ∧
      ∀ n : ℕ, n ≡ n₀ [MOD killModulus b L] →
        ∀ j, j < L → j ≠ j₀ → ((b : ℤ) ^ (j + 1) ∣ (tau (n + 1 + j) : ℤ)) := by
  obtain ⟨n₀, h1, h2, -, -, -⟩ := exists_kill_progression' b L j₀ hb hL hj₀
  exact ⟨n₀, h1, h2⟩

/-- Every prime factor of the kill modulus exceeds `L + 2`. -/
theorem lt_of_prime_dvd_killModulus {b L q : ℕ} (hqp : q.Prime) (hq : q ∣ killModulus b L) :
    L + 2 < q := by
  classical
  obtain ⟨k, -, hqk⟩ := (Nat.Prime.prime hqp).exists_mem_finset_dvd hq
  have hq_eq : q = killPrime L k :=
    (Nat.prime_dvd_prime_iff_eq hqp (killPrime_prime L k)).1
      (Nat.Prime.dvd_of_dvd_pow hqp hqk)
  rw [hq_eq]
  exact lt_killPrime L k

/-- **The near shifts are coprime to the kill modulus.**  This is the structural fact that
rescues the incidence sum from the `2^{ω(M)}` gcd loss (lap-18j finding 6): with `M` the kill
modulus and `n` in the kill class, `gcd(M, n+1+j₀+e) = 1` for every shift `e` with
`L < 1+j₀+e` and `j₀+e ≤ L+2`.  The point is that a kill prime `q` assigned to slot `c k ≤ L`
divides `n + c k`, so if it also divided `n+1+j₀+e` it would divide the *positive* difference
`1+j₀+e − c k ≤ j₀+e`, forcing `q ≤ j₀+e ≤ L+2` — impossible, since every kill prime
exceeds `L+2`.  For larger `e` the same argument caps the prime factors of the gcd by `j₀+e`,
which is what bounds the divisor loss by a function of the shift alone. -/
theorem coprime_killModulus_shift {b L j₀ n e : ℕ}
    (h : ∀ q : ℕ, q.Prime → q ∣ killModulus b L → q ∣ n + 1 + j₀ + e → q ≤ j₀ + e)
    (hsmall : j₀ + e ≤ L + 2) : Nat.Coprime (killModulus b L) (n + 1 + j₀ + e) := by
  by_contra hcon
  obtain ⟨q, hqp, hq1, hq2⟩ := Nat.Prime.not_coprime_iff_dvd.1 hcon
  have h1 := h q hqp hq1 hq2
  have h2 := lt_of_prime_dvd_killModulus (b := b) hqp hq1
  omega


/-- The kill modulus carries each prime to exponent at most `b`. -/
theorem factorization_killModulus_le (b L q : ℕ) :
    (killModulus b L).factorization q ≤ b := by
  classical
  set N : ℕ := (L - 1) * L with hN
  by_cases hq : q.Prime
  · have hne : ∀ k ∈ Finset.range N, killPrime L k ^ b ≠ 0 := by
      intro k _
      have := Nat.pow_pos (n := b) (killPrime_prime L k).pos
      omega
    have hfac : (killModulus b L).factorization q
        = ∑ k ∈ Finset.range N, (killPrime L k ^ b).factorization q := by
      rw [killModulus, Nat.factorization_prod hne]
      simp
    have hterm : ∀ k ∈ Finset.range N,
        (killPrime L k ^ b).factorization q = if killPrime L k = q then b else 0 := by
      intro k _
      rw [Nat.factorization_pow]
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [Nat.Prime.factorization (killPrime_prime L k)]
      by_cases h : killPrime L k = q
      · simp [h]
      · simp [Finsupp.single_apply, h]
    have hcard : ((Finset.range N).filter (fun k => killPrime L k = q)).card ≤ 1 := by
      refine Finset.card_le_one.2 (fun x hx y hy => ?_)
      simp only [Finset.mem_filter] at hx hy
      exact killPrime_injective L (hx.2.trans hy.2.symm)
    rw [hfac, Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const,
      smul_eq_mul]
    calc ((Finset.range N).filter (fun k => killPrime L k = q)).card * b
        ≤ 1 * b := Nat.mul_le_mul_right b hcard
      _ = b := by ring
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
    exact Nat.zero_le _

/-- **The gcd of a shift divides the SQUARE of the window product.**  The `b`-free bound, valid
at every shift: `v_q(gcd) ≤ v_q(M) = b` and, for `j ≤ b−1`, `q^j` dividing the shifted value
already divides the window value `(1+j₀+e) − c`, so `v_q(gcd) ≤ v_q((1+j₀+e)−c) + 1`, hence
`≤ 2·v_q((1+j₀+e)−c)`.  Consequently `τ(gcd) ≤ gcd ≤ (∏_{c≤L} ((1+j₀+e)−c))²`. -/
theorem gcd_shift_dvd_window_sq (b L j₀ n e : ℕ) (hb : 2 ≤ b) (hle : L < 1 + j₀ + e)
    (hcon : ∀ q : ℕ, q.Prime → q ∣ killModulus b L →
      ∃ c : ℕ, 1 ≤ c ∧ c ≤ L ∧ ∀ j : ℕ, j ≤ b - 1 → q ^ j ∣ n + 1 + j₀ + e →
        q ^ j ∣ (1 + j₀ + e) - c) :
    Nat.gcd (killModulus b L) (n + 1 + j₀ + e)
      ∣ (∏ c ∈ Finset.Icc 1 L, ((1 + j₀ + e) - c)) ^ 2 := by
  classical
  set M : ℕ := killModulus b L with hM
  set S : ℕ := n + 1 + j₀ + e with hS
  set G : ℕ := Nat.gcd M S with hG
  set P : ℕ := ∏ c ∈ Finset.Icc 1 L, ((1 + j₀ + e) - c) with hP
  have hMpos : 0 < M := killModulus_pos b L
  have hGpos : 0 < G := Nat.gcd_pos_of_pos_left _ hMpos
  have hPpos : 0 < P := by
    refine Finset.prod_pos fun c hc => ?_
    have := (Finset.mem_Icc.1 hc).2
    omega
  refine (Nat.factorization_le_iff_dvd (by omega) (by positivity)).1 ?_
  intro q
  by_cases hq : q.Prime
  · by_cases hv : G.factorization q = 0
    · rw [hv]; exact Nat.zero_le _
    · -- `q ∣ G`, so `q ∣ M`
      have hqG : q ∣ G := by
        by_contra hcon2
        exact hv (Nat.factorization_eq_zero_of_not_dvd hcon2)
      have hqM : q ∣ M := hqG.trans (Nat.gcd_dvd_left _ _)
      obtain ⟨c, hc1, hcL, hcj⟩ := hcon q hq hqM
      set D : ℕ := (1 + j₀ + e) - c with hD
      have hDpos : 0 < D := by omega
      set v : ℕ := G.factorization q with hvdef
      have hvb : v ≤ b := le_trans
        (Nat.factorization_le_iff_dvd (by omega) (by omega) |>.2 (Nat.gcd_dvd_left _ _) q)
        (factorization_killModulus_le b L q)
      have hqS : q ^ v ∣ S := (Nat.Prime.pow_dvd_iff_le_factorization hq (by omega)).2
        (le_trans (le_of_eq hvdef.symm) (by
          exact (Nat.factorization_le_iff_dvd (by omega) (by omega) |>.2
            (Nat.gcd_dvd_right _ _) q)))
      have hw : v ≤ 2 * D.factorization q := by
        rcases Nat.lt_or_ge v b with hlt | hge
        · have h1 : q ^ v ∣ D := hcj v (by omega) hqS
          have h2 : v ≤ D.factorization q :=
            (Nat.Prime.pow_dvd_iff_le_factorization hq (by omega)).1 h1
          omega
        · have hb1 : q ^ (b - 1) ∣ S :=
            dvd_trans (pow_dvd_pow q (by omega)) hqS
          have h1 : q ^ (b - 1) ∣ D := hcj (b - 1) (by omega) hb1
          have h2 : b - 1 ≤ D.factorization q :=
            (Nat.Prime.pow_dvd_iff_le_factorization hq (by omega)).1 h1
          omega
      -- `v_q(D) ≤ v_q(P)` since `D` is one of the factors
      have hDP : D ∣ P := by
        rw [hP, hD]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨hc1, hcL⟩)
      have hDPf : D.factorization q ≤ P.factorization q :=
        (Nat.factorization_le_iff_dvd (by omega) (by omega) |>.2 hDP) q
      have hPsq : (P ^ 2).factorization q = 2 * P.factorization q := by
        rw [Nat.factorization_pow]
        simp [Nat.mul_comm]
      rw [hPsq]
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
    exact Nat.zero_le _

/-- If every prime of `G` occurs to the first power, `τ(G) ≤ 2^{ω(G)}`. -/
theorem card_divisors_le_two_pow {G : ℕ} (hG : G ≠ 0)
    (h : ∀ q ∈ G.primeFactors, G.factorization q ≤ 1) :
    G.divisors.card ≤ 2 ^ G.primeFactors.card := by
  rw [Nat.card_divisors hG]
  calc ∏ q ∈ G.primeFactors, (G.factorization q + 1)
      ≤ ∏ _q ∈ G.primeFactors, 2 :=
        Finset.prod_le_prod' (fun q hq => by have := h q hq; omega)
    _ = 2 ^ G.primeFactors.card := by rw [Finset.prod_const]

/-- **The gcd loss of one shift, evaluated for the kill modulus.**  Combining the third and
fourth conclusions of `exists_kill_progression'`: every prime of `gcd(M, n+1+j₀+e)` lies in
`(L+2, j₀+e]`, and each occurs to the first power (as long as `j₀+e < (L+3)²`), so

    `τ(gcd(M, n+1+j₀+e)) ≤ 2^{(j₀+e) − (L+2)}`.

For the survivor datum `j₀ = ℓ−1`, `e = K+1+k`, `L = ℓ+K` this reads `τ ≤ 2^{k−2}` — strictly
less than the `2^k` that the geometric threshold of `TauMomentPrimesShift` already carries.
This is the exact form of the loss that laps 18i–18j could only bound by `τ(M)` or `2^{ω(M)}`. -/
theorem card_divisors_gcd_shift_le (b L j₀ n e : ℕ)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ killModulus b L → q ∣ n + 1 + j₀ + e → q ≤ j₀ + e)
    (hsq : ∀ q : ℕ, q.Prime → q ∣ killModulus b L → j₀ + e < q * q →
      ¬ (q * q ∣ n + 1 + j₀ + e))
    (hlt : j₀ + e < (L + 3) * (L + 3)) :
    (Nat.gcd (killModulus b L) (n + 1 + j₀ + e)).divisors.card
      ≤ 2 ^ (j₀ + e - (L + 2)) := by
  classical
  set M : ℕ := killModulus b L with hM
  set G : ℕ := Nat.gcd M (n + 1 + j₀ + e) with hG
  have hMpos : 0 < M := killModulus_pos b L
  have hGpos : 0 < G := Nat.gcd_pos_of_pos_left _ hMpos
  have hGne : G ≠ 0 := by omega
  have hGM : G ∣ M := Nat.gcd_dvd_left _ _
  have hGs : G ∣ n + 1 + j₀ + e := Nat.gcd_dvd_right _ _
  -- every prime of `G` lies in `(L+2, j₀+e]`
  have hmem : ∀ q ∈ G.primeFactors, q ∈ Finset.Icc (L + 3) (j₀ + e) := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqG : q ∣ G := Nat.dvd_of_mem_primeFactors hq
    have h1 : L + 2 < q := lt_of_prime_dvd_killModulus (b := b) hqp (hqG.trans hGM)
    have h2 : q ≤ j₀ + e := hprime q hqp (hqG.trans hGM) (hqG.trans hGs)
    exact Finset.mem_Icc.2 ⟨by omega, h2⟩
  have hcard : G.primeFactors.card ≤ j₀ + e - (L + 2) := by
    have h1 : G.primeFactors.card ≤ (Finset.Icc (L + 3) (j₀ + e)).card :=
      Finset.card_le_card hmem
    rw [Nat.card_Icc] at h1
    omega
  -- each prime occurs to the first power
  have hv : ∀ q ∈ G.primeFactors, G.factorization q ≤ 1 := by
    intro q hq
    by_contra hcon
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqG : q ∣ G := Nat.dvd_of_mem_primeFactors hq
    have h1 : L + 2 < q := lt_of_prime_dvd_killModulus (b := b) hqp (hqG.trans hGM)
    have hsq2 : q ^ 2 ∣ G :=
      (Nat.Prime.pow_dvd_iff_le_factorization hqp hGne).2 (by omega)
    have hsq3 : q * q ∣ n + 1 + j₀ + e := by
      have : q * q ∣ G := by rw [show q * q = q ^ 2 by ring]; exact hsq2
      exact this.trans hGs
    have hq2 : (L + 3) * (L + 3) ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
    exact hsq q hqp (hqG.trans hGM) (by omega) hsq3
  exact le_trans (card_divisors_le_two_pow hGne hv) (Nat.pow_le_pow_right (by norm_num) hcard)

/-- `8t² + 12t ≤ 2^t` for `t ≥ 20`: the crossover estimate for the large-shift regime. -/
theorem eight_sq_add_le_two_pow : ∀ t : ℕ, 20 ≤ t → 8 * t * t + 12 * t ≤ 2 ^ t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hstep : 16 * n + 20 ≤ 8 * n * n + 12 * n := by nlinarith
    have hpow : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    have hexp : 8 * (n + 1) * (n + 1) + 12 * (n + 1) = (8 * n * n + 12 * n) + (16 * n + 20) := by
      ring
    omega

/-- **The gcd loss at EVERY shift, in one inequality.**  Writing the shift as `j₀+e = L+k`,

    `τ(gcd(killModulus b L, n+1+j₀+e)) ≤ 2^k`.

Two regimes: for `k ≤ L²` the gcd is squarefree with `≤ k−2` prime factors
(`card_divisors_gcd_shift_le`); beyond that it divides the square of the window product
(`gcd_shift_dvd_window_sq`), so `τ ≤ (L+k)^{2L}`, and `2L(log₂(L+k)+1) ≤ k` there.  Both are
below the `2^k` that the geometric threshold of `TauMomentPrimesShift` already carries. -/
theorem card_divisors_gcd_shift_le_two_pow (b L j₀ n e : ℕ) (hb : 2 ≤ b) (hL : 64 ≤ L)
    (hle : L < 1 + j₀ + e)
    (h3 : ∀ q : ℕ, q.Prime → q ∣ killModulus b L → q ∣ n + 1 + j₀ + e → q ≤ j₀ + e)
    (h4 : ∀ q : ℕ, q.Prime → q ∣ killModulus b L → j₀ + e < q * q →
      ¬ (q * q ∣ n + 1 + j₀ + e))
    (h5 : ∀ q : ℕ, q.Prime → q ∣ killModulus b L →
      ∃ c : ℕ, 1 ≤ c ∧ c ≤ L ∧ ∀ j : ℕ, j ≤ b - 1 → q ^ j ∣ n + 1 + j₀ + e →
        q ^ j ∣ (1 + j₀ + e) - c) :
    (Nat.gcd (killModulus b L) (n + 1 + j₀ + e)).divisors.card ≤ 2 ^ (j₀ + e - L) := by
  classical
  set m : ℕ := j₀ + e with hm
  rcases Nat.lt_or_ge m ((L + 3) * (L + 3)) with hcase | hcase
  · -- squarefree regime
    refine le_trans (card_divisors_gcd_shift_le b L j₀ n e h3 h4 (by omega)) ?_
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · -- window-square regime
    set G : ℕ := Nat.gcd (killModulus b L) (n + 1 + j₀ + e) with hG
    set P : ℕ := ∏ c ∈ Finset.Icc 1 L, ((1 + j₀ + e) - c) with hP
    have hGpos : 0 < G := Nat.gcd_pos_of_pos_left _ (killModulus_pos b L)
    have hPpos : 0 < P := by
      refine Finset.prod_pos fun c hc => ?_
      have := (Finset.mem_Icc.1 hc).2
      omega
    have hdvd : G ∣ P ^ 2 := gcd_shift_dvd_window_sq b L j₀ n e hb (by omega) h5
    have hGle : G ≤ P ^ 2 := Nat.le_of_dvd (by positivity) hdvd
    -- `P ≤ m ^ L`
    have hPle : P ≤ m ^ L := by
      calc P ≤ ∏ _c ∈ Finset.Icc 1 L, m := by
            refine Finset.prod_le_prod' fun c hc => ?_
            have := (Finset.mem_Icc.1 hc).1
            omega
        _ = m ^ L := by rw [Finset.prod_const, Nat.card_Icc]; simp
    set t : ℕ := Nat.log 2 m with ht
    have hmpos : 0 < m := by nlinarith
    have hmlt : m < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    have hkey : 2 * L * (t + 1) ≤ m - L := by
      rcases Nat.lt_or_ge (2 * (t + 1)) L with hsmall | hbig
      · -- `t+1 < L/2`: then `2L(t+1) < L²`
        have h1 : 2 * L * (t + 1) = L * (2 * (t + 1)) := by ring
        have h2 : L * (2 * (t + 1)) ≤ L * L := Nat.mul_le_mul_left _ (by omega)
        have h3 : (L + 3) * (L + 3) = L * L + 6 * L + 9 := by ring
        omega
      · -- `t+1 ≥ L/2`, so `t ≥ 20` and `L ≤ 4t`
        have ht20 : 20 ≤ t := by omega
        have hL4t : L ≤ 4 * t := by omega
        have hpow := eight_sq_add_le_two_pow t ht20
        have hmge : 2 ^ t ≤ m := Nat.pow_log_le_self 2 (by omega)
        have h1 : 2 * L * (t + 1) + L ≤ 8 * t * t + 12 * t := by nlinarith
        omega
    calc G.divisors.card ≤ G := Nat.card_divisors_le_self G
      _ ≤ P ^ 2 := hGle
      _ ≤ (m ^ L) ^ 2 := Nat.pow_le_pow_left hPle 2
      _ = m ^ (2 * L) := by rw [← pow_mul]; ring_nf
      _ ≤ (2 ^ (t + 1)) ^ (2 * L) := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ ((t + 1) * (2 * L)) := by rw [← pow_mul]
      _ ≤ 2 ^ (m - L) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- **The kill modulus is only exponential in a polynomial**: `log₂ (killModulus b L) ≤ b(L+5)⁴`.
This is the quantitative payoff of using many small exponents: with one prime per slot at
exponent `b^{j+1}−1` the modulus would be `exp(b^{L+1})`, which exceeds every pad budget `b^K`,
`K ≤ L`.  Here `log M` is polynomial in `L` while `b^K` is exponential, so the budget wins. -/
theorem killModulus_le (b L : ℕ) : killModulus b L ≤ 2 ^ (b * (L + 5) ^ 4) := by
  have hkp : ∀ k, killPrime L k ≤ 2 ^ (k + L + 5) := by
    intro k
    have h1 : bigPrime (L + 2) k + 2 ≤ 2 ^ (k + 1) * (L + 4) := by
      have h := bigPrime_le (L + 2) k
      have he : L + 2 + 2 = L + 4 := by omega
      rwa [he] at h
    have hkpe : killPrime L k = bigPrime (L + 2) k := rfl
    have h2 : L + 4 ≤ 2 ^ (L + 4) := (Nat.lt_pow_self (by norm_num)).le
    calc killPrime L k ≤ 2 ^ (k + 1) * (L + 4) := by rw [hkpe]; omega
      _ ≤ 2 ^ (k + 1) * 2 ^ (L + 4) := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (k + L + 5) := by rw [← pow_add]; ring_nf
  set N := (L - 1) * L with hN
  have hstep : killModulus b L ≤ 2 ^ (∑ k ∈ range N, (k + L + 5) * b) := by
    calc killModulus b L = ∏ k ∈ range N, killPrime L k ^ b := rfl
      _ ≤ ∏ k ∈ range N, (2 ^ (k + L + 5)) ^ b :=
          Finset.prod_le_prod' fun k _ => Nat.pow_le_pow_left (hkp k) b
      _ = ∏ k ∈ range N, 2 ^ ((k + L + 5) * b) := by
          exact Finset.prod_congr rfl fun k _ => by rw [← pow_mul]
      _ = 2 ^ (∑ k ∈ range N, (k + L + 5) * b) := Finset.prod_pow_eq_pow_sum _ _ _
  refine hstep.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  -- the exponent: `∑_{k<N} (k+L+5)·b ≤ N·(N+L+5)·b ≤ (L+5)⁴·b`
  have hsum : ∑ k ∈ range N, (k + L + 5) * b ≤ N * ((N + L + 5) * b) := by
    refine (Finset.sum_le_card_nsmul _ _ ((N + L + 5) * b) fun k hk => ?_).trans_eq ?_
    · have : k < N := Finset.mem_range.mp hk
      exact Nat.mul_le_mul_right _ (by omega)
    · simp [Finset.card_range, smul_eq_mul]
  refine hsum.trans ?_
  have hNL : N ≤ (L + 5) ^ 2 := by
    have h1 : N ≤ L * L := by rw [hN]; exact Nat.mul_le_mul_right _ (by omega)
    have h2 : (L + 5) ^ 2 = L * L + 10 * L + 25 := by ring
    omega
  have hNL2 : N + L + 5 ≤ (L + 5) ^ 2 := by
    have h1 : N ≤ L * L := by rw [hN]; exact Nat.mul_le_mul_right _ (by omega)
    have h2 : (L + 5) ^ 2 = L * L + 10 * L + 25 := by ring
    omega
  calc N * ((N + L + 5) * b) = (N * (N + L + 5)) * b := by ring
    _ ≤ ((L + 5) ^ 2 * (L + 5) ^ 2) * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul hNL hNL2)
    _ = b * (L + 5) ^ 4 := by ring

/-- **A pad length that beats the modulus.**  `K = 10ℓ + 100` makes the budget `b^{K/4}` exceed
`log₂` of the kill modulus for the window length `L = ℓ + K`.  The square-root in the exponent is
slack the analytic leaf needs: it must place a Dirichlet prime of size `M^{O(1)}` inside the
progression, so it needs `log M` to be a *small power* of the budget, not merely below it. -/
theorem exists_pad_budget (b ℓ : ℕ) (hb : 3 ≤ b) :
    ∃ K : ℕ, 10 * ℓ + 100 ≤ K ∧ killModulus b (ℓ + K) ≤ 2 ^ (b ^ (K / 4)) := by
  refine ⟨20 * ℓ + 200, by omega,
    (killModulus_le b _).trans (Nat.pow_le_pow_right (by norm_num) ?_)⟩
  have hrw : ℓ + (20 * ℓ + 200) + 5 = 21 * ℓ + 205 := by omega
  have hK2 : (20 * ℓ + 200) / 4 = 5 * ℓ + 50 := by omega
  rw [hrw, hK2]
  have h4 : (ℓ + 1) < 3 ^ (ℓ + 1) := Nat.lt_pow_self (by norm_num)
  have hchain : (21 * ℓ + 205) ^ 4 ≤ 3 ^ (5 * ℓ + 49) := by
    calc (21 * ℓ + 205) ^ 4 ≤ (205 * (ℓ + 1)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ = 205 ^ 4 * (ℓ + 1) ^ 4 := by ring
      _ ≤ 3 ^ 20 * (3 ^ (ℓ + 1)) ^ 4 :=
          Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left h4.le 4)
      _ = 3 ^ (4 * ℓ + 24) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ 3 ^ (5 * ℓ + 49) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb3 : (3 : ℕ) ^ (5 * ℓ + 49) ≤ b ^ (5 * ℓ + 49) := Nat.pow_le_pow_left (by omega) _
  calc b * (21 * ℓ + 205) ^ 4 ≤ b * b ^ (5 * ℓ + 49) :=
        Nat.mul_le_mul_left _ (hchain.trans hb3)
    _ = b ^ (5 * ℓ + 50) := by rw [← pow_succ']

/-! ### 4. The crux leaf -/

/-- **The parity of the window is the parity of the survivor.**  For an EVEN base every slot but
`ℓ−1` carries a weight divisible by `b`, so the window value is `≡ τ(n+ℓ) (mod 2)`; and `τ(m)` is
odd exactly when `m` is a perfect square.  So for even `b` a construction with a single survivor
can only reach an ODD target `t` if the survivor entry `n+ℓ` is a square — a quadratic-residue
condition on the kill progression.

This is *not* an obstruction to `ConjC2`: a target `t` of length `ℓ` is the target `t·b` of
length `ℓ+1` (`subLeafA_of_constructionInputsB`), and `t·b` is even.  So it suffices to realise
the targets divisible by `b`, which is what `ConstructionInputsB` asks. -/
def ConstructionInputsB (b : ℕ) : Prop :=
  ∀ ℓ, 1 ≤ ℓ → ∀ t : ℕ, t < b ^ ℓ → b ∣ t → ∃ n K : ℕ,
    (∀ j, j < ℓ + K → j ≠ ℓ - 1 → ((b : ℤ) ^ (j + 1) ∣ (tau (n + 1 + j) : ℤ))) ∧
    ((tau (n + ℓ) : ℤ) ≡ (t : ℤ) [ZMOD (b : ℤ) ^ ℓ]) ∧
    carry b tau (n + (ℓ + K)) < (b : ℤ) ^ K

theorem constructionInputsB_of_constructionInputs (b : ℕ) (h : ConstructionInputs b) :
    ConstructionInputsB b := fun ℓ hℓ t ht _ => h ℓ hℓ t ht

/-- **One extra digit removes the parity constraint.**  Realising the length-`ℓ+1` target `t·b`
realises the length-`ℓ` target `t`, because `(t·b)·b^{K} = t·b^{K+1}` and the window lengths agree:
`(ℓ+1)+K = ℓ+(K+1)`.  The carry bound even improves (`b^K ≤ b^{K+1}`). -/
theorem subLeafA_of_constructionInputsB (b : ℕ) (hb : 3 ≤ b) (h : ConstructionInputsB b) :
    SubLeafA b := by
  intro ℓ hℓ t ht
  have hb2 : 2 ≤ b := by omega
  have hbz : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (show 0 < b by omega)
  have htb : t * b < b ^ (ℓ + 1) := by
    have h1 : t * b < b ^ ℓ * b := mul_lt_mul_of_pos_right ht (by omega : 0 < b)
    calc t * b < b ^ ℓ * b := h1
      _ = b ^ (ℓ + 1) := (pow_succ b ℓ).symm
  obtain ⟨n, K, hkill, hsurv, hcarry⟩ := h (ℓ + 1) (by omega) (t * b) htb ⟨t, by ring⟩
  have he : ℓ + (K + 1) = (ℓ + 1) + K := by omega
  refine ⟨n, K + 1, ?_, ?_⟩
  · rw [he]
    refine hcarry.trans_le ?_
    rw [pow_succ]
    nlinarith [pow_pos hbz K]
  · have hp := paddedSum_of_construction b (ℓ + 1) K (t * b) hb2 (by omega) n htb hkill hsurv
    rw [he, hp]
    push_cast
    ring

/-- **THE CRUX (2026-09-24, after (K1) was discharged).**  Everything in the construction except
the *survivor* slot is now a theorem (`exists_kill_progression`): the slot-killing conditions
(K1) hold on a full residue class `n ≡ n₀ (mod M)`, `M = killModulus b (ℓ+K)`, whose survivor
entry `n + ℓ` is coprime to the odd modulus `M`, and whose size satisfies `M ≤ 2^{b^{K/4}}`
(`killModulus_le`, `exists_pad_budget`).  What is left is to find a member of that class at
which BOTH

* **(K2)** `τ(n+ℓ) ≡ t (mod b^ℓ)` — one application of Dirichlet: take `n+ℓ = 2^a·p` with
  `p ≡ (n₀+ℓ)·2^{−a} (mod M)` prime (legitimate since `M` is odd and `n₀+ℓ` is coprime to it);
  then `τ(n+ℓ) = 2(a+1)`, which runs over every residue mod `b^ℓ` for odd `b` and over every
  EVEN residue for even `b` — whence the parity hypothesis `2 ∣ b → 2 ∣ t`.  Qualitative
  Dirichlet suffices for this half alone.
* **(K3)** `carry b τ (n+ℓ+K) < b^K` — an almost-all divisor bound.  `carry ≤ Σ_k τ(n+L+k)/b^k`,
  whose AVERAGE over a full progression is `≍ log M ≤ b^{K/4} ≪ b^K`.  A first moment therefore
  suffices *if* one may average over the whole progression.

hold at the **same** `n`.  That is the difficulty: (K2) confines `n` to the prime-indexed
subfamily `{2^a p − ℓ}`, of density `≍ 1/(φ(M) log)` inside the class, so the first moment for
(K3) has to be run over that subfamily — a Brun–Titchmarsh (upper bound) plus Linnik-type (lower
bound) input, not a bare divisor average.  The budget is deliberately `b^{K/4}`, leaving the
whole range `[M², 2^{b^K}]` free for the prime.

**Why an almost-all bound is unavoidable** (structural finding, 2026-09-24): any mechanism
producing `b^{j+1} ∣ τ(n+1+j)` for all `j < L` needs `≳ L²/2` prime-power constraints — a prime
`q` can serve slots `j ≡ j₀ (mod q^b)` only, so primes below `L^{1/b}` contribute `O(L)`
incidences in total — hence `log n ≳ L² log L`.  The worst-case divisor bound at that size is
`exp(Θ(L²))`, which exceeds the budget `b^K ≤ b^L = exp(Θ(L))` for every admissible `K`.  So no
POINTWISE bound on `τ` can close (K3); only a statement about typical values can. -/
def SurvivorLeaf (b : ℕ) : Prop :=
  ∀ ℓ K M n₀ t : ℕ, 1 ≤ ℓ → 10 * ℓ + 100 ≤ K → 0 < M → Nat.Coprime 2 M →
    Nat.Coprime (n₀ + ℓ) M → t < b ^ ℓ → (2 ∣ b → 2 ∣ t) → M ≤ 2 ^ (b ^ (K / 4)) →
    ∃ n : ℕ, n ≡ n₀ [MOD M] ∧ ((tau (n + ℓ) : ℤ) ≡ (t : ℤ) [ZMOD (b : ℤ) ^ ℓ]) ∧
      carry b tau (n + (ℓ + K)) < (b : ℤ) ^ K

/-- **(K1) + the survivor leaf give the construction for the targets `ConjC2` needs.**  This is
the reduction the lap-17 CRT work buys: `SubLeafA`, `WindowShape`, `WindowPrescribable` and
`ConjC2` now rest on `SurvivorLeaf` alone. -/
theorem constructionInputsB_of_survivorLeaf (b : ℕ) (hb : 3 ≤ b) (h : SurvivorLeaf b) :
    ConstructionInputsB b := by
  intro ℓ hℓ t ht hbt
  obtain ⟨K, hK1, hKbud⟩ := exists_pad_budget b ℓ hb
  obtain ⟨n₀, hcop, hkill⟩ :=
    exists_kill_progression b (ℓ + K) (ℓ - 1) (by omega) (by omega) (by omega)
  have hrw : n₀ + 1 + (ℓ - 1) = n₀ + ℓ := by omega
  rw [hrw] at hcop
  obtain ⟨n, hn, hsurv, hcarry⟩ :=
    h ℓ K (killModulus b (ℓ + K)) n₀ t hℓ hK1 (killModulus_pos _ _)
      (coprime_two_killModulus _ _) hcop ht (fun hd => hd.trans hbt) hKbud
  exact ⟨n, K, hkill n hn, hsurv, hcarry⟩

/-- The same reduction for an ODD base, where no parity constraint is needed and the full
`ConstructionInputs` follows. -/
theorem constructionInputs_of_survivorLeaf (b : ℕ) (hb : 3 ≤ b) (hodd : ¬ 2 ∣ b)
    (h : SurvivorLeaf b) : ConstructionInputs b := by
  intro ℓ hℓ t ht
  obtain ⟨K, hK1, hKbud⟩ := exists_pad_budget b ℓ hb
  obtain ⟨n₀, hcop, hkill⟩ :=
    exists_kill_progression b (ℓ + K) (ℓ - 1) (by omega) (by omega) (by omega)
  have hrw : n₀ + 1 + (ℓ - 1) = n₀ + ℓ := by omega
  rw [hrw] at hcop
  obtain ⟨n, hn, hsurv, hcarry⟩ :=
    h ℓ K (killModulus b (ℓ + K)) n₀ t hℓ hK1 (killModulus_pos _ _)
      (coprime_two_killModulus _ _) hcop ht (fun hd => absurd hd hodd) hKbud
  exact ⟨n, K, hkill n hn, hsurv, hcarry⟩

/-- **The residual analytic leaf, in its sharpest form.**  After (K1) (`exists_kill_progression`)
and (K2) (`exists_survivor_data`), the ONLY thing still missing is this: among the primes of a
single arithmetic progression `p ≡ r (mod M)` one must find one — of moderate size, `p` is not
required to be large — at which the divisor function stays small just past `2^a·p`, in the
precise sense `Σ_{k≥1} τ(2^a p + K + k)/b^k < b^K`.

The hypotheses are exactly what the construction supplies: `M ≤ 2^{b^{K/4}}` and `a ≤ b^{K/4}`,
so `log(2^a·p) ≈ a + log p` is `O(b^{K/4})` as soon as `p` is polynomial in `M` — i.e. `≪ b^K`,
the budget.  Heuristically the first moment already closes it: the average of `τ(m)` for
`m ≍ 2^a p` is `≍ log(2^a p) ≪ b^K`, so the exceptional set has density `≪ log/b^K`.  Making
that rigorous ALONG THE PRIMES of the progression is a Brun–Titchmarsh (upper-bound sieve, for
`Σ_{p ≤ Y, p ≡ r} τ(2^a p + c)`) plus a Linnik-type lower bound (to have enough primes below
`Y = M^{O(1)}`).  Both are `🟡` project-scale, neither is in mathlib.

**`1 ≤ K` is necessary, not cosmetic.**  At `K = 0` the budget is `b^0 = 1`, i.e. the carry must
be `0`; `probes/swingc2_carryleaf_K0.py` shows that for `b = 3` the carry is `≥ 1` for EVERY
admissible datum (`a ≤ 1`, `M ≤ 2`, `N ≤ 1`) and every prime `p < 4000`, so the `K = 0` instance
is false.  The only consumer (`SurvivorLeaf`) supplies `K ≥ 110`.

The `N` parameter is capped by `b^{K/4}`: the prime only has to avoid the finitely many small
values (`p ≠ 2`, `p > ℓ`), NOT to be arbitrarily large — and indeed it must not be, since the
carry grows with `log p`. -/
def CarryLeaf (b : ℕ) : Prop :=
  ∀ K M r a N : ℕ, 2 ≤ K → 0 < M → Nat.Coprime r M → a ≤ b ^ (K / 4) →
    M ≤ 2 ^ (b ^ (K / 4)) → N ≤ b ^ (K / 4) →
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p ≡ r [MOD M] ∧ carry b tau (2 ^ a * p + K) < (b : ℤ) ^ K

/-- **(K2) + the carry leaf give the survivor leaf.**  The whole of `SurvivorLeaf` except the
size of the divisor function along one progression of primes is now a theorem. -/
theorem survivorLeaf_of_carryLeaf (b : ℕ) (hb : 3 ≤ b) (h : CarryLeaf b) : SurvivorLeaf b := by
  intro ℓ K M n₀ t hℓ hK hM h2M hcop ht hpar hbud
  obtain ⟨a, r, ha, hrcop, hall⟩ := exists_survivor_data b ℓ M n₀ t hb hℓ hM h2M hcop ht hpar
  have hK2 : ℓ ≤ K / 4 := by omega
  have hK21 : 1 ≤ K / 4 := by omega
  have hpowmono : ∀ i j : ℕ, i ≤ j → b ^ i ≤ b ^ j := fun i j hij =>
    Nat.pow_le_pow_right (by omega) hij
  have haK : a ≤ b ^ (K / 4) := le_of_lt (lt_of_lt_of_le ha (hpowmono ℓ (K / 4) hK2))
  have hNK : max 2 ℓ ≤ b ^ (K / 4) := by
    refine max_le ?_ ?_
    · calc (2 : ℕ) ≤ b := by omega
        _ = b ^ 1 := (pow_one b).symm
        _ ≤ b ^ (K / 4) := hpowmono 1 (K / 4) hK21
    · exact le_trans hK2 (le_of_lt (Nat.lt_pow_self (by omega)))
  obtain ⟨p, hpN, hpp, hpr, hpc⟩ := h K M r a (max 2 ℓ) (by omega) hM hrcop haK hbud hNK
  have hp2 : p ≠ 2 := by
    have : 2 < p := lt_of_le_of_lt (le_max_left 2 ℓ) hpN
    omega
  have hpℓ : ℓ < p := lt_of_le_of_lt (le_max_right 2 ℓ) hpN
  obtain ⟨hmod, htau⟩ := hall p hpp hp2 hpr
  have hge : ℓ ≤ 2 ^ a * p := by
    calc ℓ ≤ p := hpℓ.le
      _ = 1 * p := (one_mul p).symm
      _ ≤ 2 ^ a * p := Nat.mul_le_mul_right _ (Nat.one_le_two_pow)
  refine ⟨2 ^ a * p - ℓ, ?_, ?_, ?_⟩
  · refine Nat.ModEq.add_right_cancel' ℓ ?_
    rw [Nat.sub_add_cancel hge]
    exact hmod
  · rw [Nat.sub_add_cancel hge]
    exact htau
  · have he : 2 ^ a * p - ℓ + (ℓ + K) = 2 ^ a * p + K := by omega
    rw [he]
    exact hpc

/-! ### The elementary half of `CarryLeaf`: the first moment of `τ` along a progression

`SwingC2Moment.tau_sum_AP_le_log` is a full theorem: over the FULL progression `n ≡ r (mod M)`,
`n ≤ X`, with `gcd(r,M) = 1`,

    Σ τ(n) ≤ 2·( (X/M)·(log₂ √X + 2) + √X ).

Restated here for `tau`, together with the exceptional-set (Markov) form that `CarryLeaf` wants.
The gap that remains is exactly the transfer of this first moment from the integers of the
progression to its PRIMES (`TauMomentPrimes` below). -/

/-- First moment of `tau` over `{n ≤ X : n ≡ r (mod M)}`, `gcd(r,M) = 1`. -/
theorem tau_sum_AP (M r X : ℕ) (hM : 0 < M) (hr : Nat.Coprime r M) :
    ∑ n ∈ SwingC2Moment.apSet M r X, tau n
      ≤ 2 * ((X / M) * (Nat.log 2 (Nat.sqrt X) + 2) + Nat.sqrt X) :=
  SwingC2Moment.tau_sum_AP_le_log M r X hM hr

/-- **Exceptional set.**  At most `2((X/M)(log₂√X+2)+√X)/T` of the `n ≤ X` in the class have
`τ(n) ≥ T`.  For `T ≍ b^K` and `X` polynomial in `M ≤ 2^{b^{K/4}}` the right side is `≪ X/M`, so
almost every element of the progression is good — this is the statement `CarryLeaf` needs, except
that `CarryLeaf` must land on a PRIME. -/
theorem card_large_tau_le (M r X T : ℕ) (hM : 0 < M) (hr : Nat.Coprime r M) :
    T * ((SwingC2Moment.apSet M r X).filter (fun n => T ≤ tau n)).card
      ≤ 2 * ((X / M) * (Nat.log 2 (Nat.sqrt X) + 2) + Nat.sqrt X) := by
  classical
  refine le_trans ?_ (tau_sum_AP M r X hM hr)
  have h1 : ∑ n ∈ (SwingC2Moment.apSet M r X).filter (fun n => T ≤ tau n), T
      ≤ ∑ n ∈ (SwingC2Moment.apSet M r X).filter (fun n => T ≤ tau n), tau n :=
    Finset.sum_le_sum (fun n hn => (Finset.mem_filter.1 hn).2)
  have h2 : ∑ n ∈ (SwingC2Moment.apSet M r X).filter (fun n => T ≤ tau n), tau n
      ≤ ∑ n ∈ SwingC2Moment.apSet M r X, tau n :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h3 : ∑ _n ∈ (SwingC2Moment.apSet M r X).filter (fun n => T ≤ tau n), T
      = T * ((SwingC2Moment.apSet M r X).filter (fun n => T ≤ tau n)).card := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  omega

/-! ### The crux, decomposed with a GEOMETRIC threshold

Lap 18b–18e used the linear threshold `A·(k+1)`.  That is sound but useless: the trivial bound
`τ(m) ≤ 2√m` only overtakes a linear threshold at `k ≈ √N`, so a union bound over shifts costs a
factor `√N ≈ 2^{a/2}√Y` and swamps the budget `b^K`.  With the geometric threshold
`A·(k+1)·2^k` (`carry_le_of_tau_geom`) two things improve at once: the trivial bound takes over
at `k ≈ log₂√N`, and — decisively — the *per-shift exceptional densities may decay like `2^{-k}`*,
so the union bound over shifts converges and costs NOTHING.  The budget then has the full factor
`b^K` against `log(2^a Y)` of slack. -/

/-- `k ≤ 2^(k-1)` for `k ≥ 1`. -/
theorem le_two_pow_pred {k : ℕ} (hk : 1 ≤ k) : k ≤ 2 ^ (k - 1) := by
  have := Nat.lt_two_pow_self (n := k - 1)
  omega

/-- **The geometric union bound.**  If `4·2^k·B k ≤ C` for every `k`, then every partial sum of
`B` is at most `C/2`.  This is what makes the union over shifts free. -/
theorem sum_le_of_geom_bound (B : ℕ → ℕ) (C : ℕ) (h : ∀ k, 4 * 2 ^ k * B k ≤ C) (n : ℕ) :
    2 * ∑ k ∈ Finset.range n, B k ≤ C := by
  have key : ∀ m : ℕ, 4 * 2 ^ m * (∑ k ∈ Finset.range m, B k) + 2 * C ≤ 2 * C * 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hb := h m
      have hexp : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
      rw [Finset.sum_range_succ]
      calc 4 * 2 ^ (m + 1) * ((∑ k ∈ Finset.range m, B k) + B m) + 2 * C
          = 2 * (4 * 2 ^ m * (∑ k ∈ Finset.range m, B k) + 2 * C)
              + 2 * (4 * 2 ^ m * B m) - 2 * C := by
            rw [hexp]; ring_nf; omega
        _ ≤ 2 * (2 * C * 2 ^ m) + 2 * C - 2 * C := by omega
        _ = 2 * C * 2 ^ (m + 1) := by rw [hexp]; ring_nf; omega
  have hn := key n
  have hpos : 0 < (2 : ℕ) ^ n := Nat.pow_pos (by norm_num : 0 < 2)
  have h2 : 2 ^ n * (4 * ∑ k ∈ Finset.range n, B k) ≤ 2 ^ n * (2 * C) := by
    have : 4 * 2 ^ n * (∑ k ∈ Finset.range n, B k) ≤ 2 * C * 2 ^ n := by omega
    calc 2 ^ n * (4 * ∑ k ∈ Finset.range n, B k)
        = 4 * 2 ^ n * (∑ k ∈ Finset.range n, B k) := by ring
      _ ≤ 2 * C * 2 ^ n := this
      _ = 2 ^ n * (2 * C) := by ring
  have := Nat.le_of_mul_le_mul_left h2 hpos
  omega

/-- **The remaining, genuinely analytic, half of `CarryLeaf`.**  One prime `p` of the progression
at which the divisor function obeys the *geometric* threshold `(b^K/4)·(k+1)·2^k` at EVERY shift
`2^a p + K + 1 + k` simultaneously.  `carry_le_of_tau_geom` then gives
`carry ≤ 3·(b^K/4) < b^K`. -/
def TauMomentPrimes (b : ℕ) : Prop :=
  ∀ K M r a N : ℕ, 2 ≤ K → 0 < M → Nat.Coprime r M → a ≤ b ^ (K / 4) →
    M ≤ 2 ^ (b ^ (K / 4)) → N ≤ b ^ (K / 4) →
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p ≡ r [MOD M] ∧
      ∀ k : ℕ, tau (2 ^ a * p + K + 1 + k) ≤ b ^ K / 4 * (k + 1) * 2 ^ k

/-- **Per-shift density form.**  The `k`-th exceptional set is allowed to occupy a `2^{-k}/4`
fraction of `P`; `sum_le_of_geom_bound` then sums these to `≤ |P|/2 < |P|`. -/
def TauMomentPrimesShift (b : ℕ) : Prop :=
  ∀ K M r a N : ℕ, 2 ≤ K → 0 < M → Nat.Coprime r M → a ≤ b ^ (K / 4) →
    M ≤ 2 ^ (b ^ (K / 4)) → N ≤ b ^ (K / 4) →
    ∃ Y : ℕ, ∃ P : Finset ℕ,
      (∀ p ∈ P, N < p ∧ p.Prime ∧ p ≡ r [MOD M] ∧ p ≤ Y) ∧ 0 < P.card ∧
      ∀ k : ℕ, 4 * 2 ^ k *
          (P.filter (fun p => b ^ K / 4 * (k + 1) * 2 ^ k < tau (2 ^ a * p + K + 1 + k))).card
        ≤ P.card

/-- **The gcd structure of the incidence sum.**  A prime `q` dividing the modulus `M` can divide
the shifted value `2^a p + e` only if it divides the single fixed integer `n + e`, where `n` is
the survivor residue (`2^a r ≡ n [MOD M]`).  In particular the divisibility does not depend on
`p` at all: within the progression it either always holds or never does.

This is what rescues the incidence sum from the `τ(M)` loss.  In the `SwingC2` construction
`n = n₀ + ℓ` and, modulo a kill prime `q` assigned to slot `j`, `n ≡ ℓ−1−j`; so for the shift
`e = K+1+k` the condition reads `q ∣ (ℓ−1−j) + K+1+k` — `q` must divide one of only `ℓ`
integers, each of size `≤ ℓ+K+1+k`.  Since every kill prime exceeds `ℓ+K+2`, only the shifts
with `k ≥ q − ℓ − K` are affected at all, and `gcd(2^a p + e, M)` is a product of at most
`ℓ·log(ℓ+K+1+k)/log(ℓ+K)` kill primes rather than a divisor of all of `M`. -/
theorem dvd_of_dvd_shift {q M a e p r n : ℕ} (hq : q ∣ M) (hp : p ≡ r [MOD M])
    (hr : 2 ^ a * r ≡ n [MOD M]) (h : q ∣ 2 ^ a * p + e) : q ∣ n + e := by
  have hpq : p ≡ r [MOD q] := Nat.ModEq.of_dvd hq hp
  have hrq : 2 ^ a * r ≡ n [MOD q] := Nat.ModEq.of_dvd hq hr
  have h1 : 2 ^ a * p ≡ 2 ^ a * r [MOD q] := Nat.ModEq.mul_left _ hpq
  have h2 : 2 ^ a * p + e ≡ n + e [MOD q] := (h1.trans hrq).add_right e
  have h3 : (2 ^ a * p + e) % q = 0 := Nat.mod_eq_zero_of_dvd h
  have h4 : (n + e) % q = 0 := by
    have := h2
    unfold Nat.ModEq at this
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 h4

/-! ### The 2-adic reduction of a shift

`sum_card_shift_dvd_le'` still needs `Coprime (2^a) d`, i.e. `d` odd, and the shifts
`e = K+1+k` are even half the time.  The fix is to factor the 2-part out of the shifted value
ONCE, before the hyperbola reduction: with `e = 2^v u`, `u` odd and `v < a`,

    `2^a n + e = 2^v (2^{a−v} n + u)`,  the second factor ODD,

so `τ(2^a n + e) = (v+1)·τ(2^{a−v} n + u)` and every divisor of the odd part is odd.  The loss
is `v + 1 ≤ log₂ e + 1`, negligible against the budget `b^K`. -/

/-- `τ(2^v m) = (v+1) τ(m)` for odd `m`. -/
theorem tau_two_pow_mul_odd {v m : ℕ} (hm : ¬ 2 ∣ m) : tau (2 ^ v * m) = (v + 1) * tau m := by
  have hcop : Nat.Coprime (2 ^ v) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm)
  rw [tau_mul_coprime hcop, tau_two_pow]

/-- **The 2-adic reduction, packaged.**  Any shift `e` with `0 < e < 2^a` splits as `2^v u` with
`u` odd and `v < a`, and the shifted value factors accordingly. -/
theorem tau_shift_two_adic (a n e : ℕ) (he : 0 < e) (hea : e < 2 ^ a) :
    ∃ v u : ℕ, e = 2 ^ v * u ∧ ¬ 2 ∣ u ∧ v < a ∧ 2 ^ v ≤ e ∧ 0 < u ∧
      tau (2 ^ a * n + e) = (v + 1) * tau (2 ^ (a - v) * n + u) := by
  classical
  set v : ℕ := e.factorization 2 with hv
  set u : ℕ := e / 2 ^ v with hu
  have hne : e ≠ 0 := by omega
  have hsplit : 2 ^ v * u = e := Nat.ordProj_mul_ordCompl_eq_self e 2
  have hodd : ¬ 2 ∣ u := Nat.not_dvd_ordCompl Nat.prime_two hne
  have hupos : 0 < u := Nat.ordCompl_pos 2 hne
  have hdvd : (2 : ℕ) ^ v ∣ e := Nat.ordProj_dvd e 2
  have hle : (2 : ℕ) ^ v ≤ e := Nat.le_of_dvd he hdvd
  have hva : v < a := by
    by_contra hcon
    have : (2 : ℕ) ^ a ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hfac : 2 ^ a * n + e = 2 ^ v * (2 ^ (a - v) * n + u) := by
    have h1 : (2 : ℕ) ^ v * (2 ^ (a - v) * n) = 2 ^ a * n := by
      rw [← Nat.mul_assoc, ← pow_add]
      congr 2
      omega
    rw [Nat.mul_add, h1, hsplit]
  have hoddm : ¬ 2 ∣ 2 ^ (a - v) * n + u := by
    intro hcon
    have h2 : (2 : ℕ) ∣ 2 ^ (a - v) * n :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (by omega : a - v ≠ 0)) n
    exact hodd (by omega)
  exact ⟨v, u, hsplit.symm, hodd, hva, hle, hupos, by rw [hfac, tau_two_pow_mul_odd hoddm]⟩

/-- **The non-coprime divisors contribute nothing.**  If the modulus `M` is coprime to the
single fixed integer `c·r + e`, then no `d` sharing a factor with `M` can divide `c·n + e` for
any `n` of the progression: `dvd_of_dvd_shift` transports the divisibility from `n` to `r`.

Combined with `coprime_killModulus_shift`, this is what removes the `2^{ω(M)}` loss from the
incidence sum (lap-18j finding 6): for the near shifts the *whole* range of divisors `d` is
effectively coprime to `M`, without any hypothesis on `d`. -/
theorem filter_shift_eq_empty {c e M r Y d : ℕ}
    (hcop : Nat.Coprime M (c * r + e)) (hdM : ¬ Nat.Coprime d M) :
    (Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e) = ∅ := by
  classical
  rw [Finset.filter_eq_empty_iff]
  intro n _ hn
  obtain ⟨hnm, hdvd⟩ := hn
  obtain ⟨q, hqp, hqd, hqM⟩ := Nat.Prime.not_coprime_iff_dvd.1 hdM
  have hq1 : q ∣ c * n + e := hqd.trans hdvd
  have hnr : n ≡ r [MOD M] := hnm
  have hq2 : q ∣ c * r + e := by
    have h1 : c * n ≡ c * r [MOD q] := (Nat.ModEq.of_dvd hqM hnr).mul_left c
    have h2 : c * n + e ≡ c * r + e [MOD q] := h1.add_right e
    have h3 : (c * n + e) % q = 0 := Nat.mod_eq_zero_of_dvd hq1
    have h4 : (c * r + e) % q = 0 := by
      have := h2
      unfold Nat.ModEq at this
      omega
    exact Nat.dvd_iff_mod_eq_zero.2 h4
  have hone : q = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqM hcop) hq2
  exact hqp.one_lt.ne' hone

/-- **The crude incidence bound, with the `gcd(d,M)` hypothesis removed.**  Only coprimality of
`d` with `c` is still required (for `c = 2^a` that is just "`d` odd"); the interaction with `M`
is now handled by `filter_shift_eq_empty` from the single hypothesis `gcd(M, c·r+e) = 1`. -/
theorem sum_card_shift_dvd_le' (c e M r Y D : ℕ) (hM : 0 < M)
    (hcM : Nat.Coprime M (c * r + e)) (hcd : ∀ d ∈ Finset.Icc 1 D, Nat.Coprime c d) :
    ∑ d ∈ Finset.Icc 1 D,
        ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).card
      ≤ (Y / M) * (Nat.log 2 D + 2) + D := by
  classical
  have hstep : ∀ d ∈ Finset.Icc 1 D,
      ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).card
        ≤ Y / M / d + 1 := by
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Icc.1 hd).1
    by_cases hdM : Nat.Coprime d M
    · have := SwingC2Moment.card_shift_dvd_le c e M r Y d hd0 hM (hcd d hd) hdM
      have hdiv : Y / M / d = Y / (d * M) := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm M d]
      omega
    · rw [filter_shift_eq_empty hcM hdM]
      simp
  calc ∑ d ∈ Finset.Icc 1 D,
        ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).card
      ≤ ∑ d ∈ Finset.Icc 1 D, (Y / M / d + 1) := Finset.sum_le_sum hstep
    _ = (∑ d ∈ Finset.Icc 1 D, Y / M / d) + D := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
        omega
    _ ≤ (Y / M) * (Nat.log 2 D + 2) + D := by
        have := SwingC2Moment.sum_div_le_log (Y / M) D
        omega

/-! ### The shifted first moment over a progression, with no side conditions

The three ingredients now combine.  Along the progression `n ≡ r (mod M)` with `u` ODD and
`gcd(M, 2^a r + u) = 1`:

* the even `d` contribute nothing, because `2^a n + u` is odd (`filter_shift_eq_empty_even`);
* the `d` sharing a factor with `M` contribute nothing (`filter_shift_eq_empty`);
* every surviving `d` is counted by `SwingC2Moment.card_shift_dvd_le`.

So the shifted first moment obeys the SAME bound as the unshifted one — no `τ(M)` and no
`2^{ω(M)}` loss anywhere. -/

/-- Even divisors of an odd shifted value contribute nothing. -/
theorem filter_shift_eq_empty_even {a u M r Y d : ℕ} (ha : 1 ≤ a) (hu : ¬ 2 ∣ u)
    (hd : 2 ∣ d) :
    (Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ 2 ^ a * n + u) = ∅ := by
  classical
  rw [Finset.filter_eq_empty_iff]
  intro n _ hn
  obtain ⟨-, hdvd⟩ := hn
  have h2 : (2 : ℕ) ∣ 2 ^ a * n + u := hd.trans hdvd
  have h3 : (2 : ℕ) ∣ 2 ^ a * n :=
    Dvd.dvd.mul_right (dvd_pow_self 2 (by omega : a ≠ 0)) n
  exact hu (by omega)

/-- **The crude incidence bound with NO side condition on the divisors.** -/
theorem sum_card_shift_dvd_le_odd (a u M r Y D : ℕ) (ha : 1 ≤ a) (hM : 0 < M)
    (hu : ¬ 2 ∣ u) (hcM : Nat.Coprime M (2 ^ a * r + u)) :
    ∑ d ∈ Finset.Icc 1 D,
        ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ 2 ^ a * n + u)).card
      ≤ (Y / M) * (Nat.log 2 D + 2) + D := by
  classical
  have hstep : ∀ d ∈ Finset.Icc 1 D,
      ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ 2 ^ a * n + u)).card
        ≤ Y / M / d + 1 := by
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Icc.1 hd).1
    by_cases hdodd : 2 ∣ d
    · rw [filter_shift_eq_empty_even ha hu hdodd]; simp
    · by_cases hdM : Nat.Coprime d M
      · have hcd : Nat.Coprime (2 ^ a) d :=
          Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hdodd)
        have := SwingC2Moment.card_shift_dvd_le (2 ^ a) u M r Y d hd0 hM hcd hdM
        have hdiv : Y / M / d = Y / (d * M) := by
          rw [Nat.div_div_eq_div_mul, Nat.mul_comm M d]
        omega
      · rw [filter_shift_eq_empty hcM hdM]; simp
  calc ∑ d ∈ Finset.Icc 1 D,
        ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ 2 ^ a * n + u)).card
      ≤ ∑ d ∈ Finset.Icc 1 D, (Y / M / d + 1) := Finset.sum_le_sum hstep
    _ = (∑ d ∈ Finset.Icc 1 D, Y / M / d) + D := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
        omega
    _ ≤ (Y / M) * (Nat.log 2 D + 2) + D := by
        have := SwingC2Moment.sum_div_le_log (Y / M) D
        omega

/-- **The shifted first moment along the progression, unconditional on the divisor range.**
This is the full-progression analogue of `tau_sum_AP` for the shifted values `2^a n + u`,
`u` odd and coprime-compatible with `M`.  It is the elementary engine the crux needs: the only
thing still missing afterwards is the transfer from the integers of the progression to its
PRIMES. -/
theorem tau_shift_sum_AP_odd (a u M r Y : ℕ) (ha : 1 ≤ a) (hM : 0 < M) (hu : ¬ 2 ∣ u)
    (hcM : Nat.Coprime M (2 ^ a * r + u)) :
    ∑ n ∈ SwingC2Moment.apSet M r Y, tau (2 ^ a * n + u)
      ≤ 2 * ((Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ a * Y + u)) + 2)
              + Nat.sqrt (2 ^ a * Y + u)) := by
  classical
  set D : ℕ := Nat.sqrt (2 ^ a * Y + u) with hD
  have hmem : ∀ n ∈ SwingC2Moment.apSet M r Y, n ≤ Y := by
    intro n hn
    rw [SwingC2Moment.apSet, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1.2
  have h1 := SwingC2Moment.tau_shift_sum_le (2 ^ a) u Y (SwingC2Moment.apSet M r Y) hmem
  have hfil : ∀ d : ℕ, (SwingC2Moment.apSet M r Y).filter (fun n => d ∣ 2 ^ a * n + u)
      = (Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ 2 ^ a * n + u) := by
    intro d
    rw [SwingC2Moment.apSet, Finset.filter_filter]
  have h2 : ∑ d ∈ Finset.Icc 1 D,
      ((SwingC2Moment.apSet M r Y).filter (fun n => d ∣ 2 ^ a * n + u)).card
        ≤ (Y / M) * (Nat.log 2 D + 2) + D := by
    simp only [hfil]
    exact sum_card_shift_dvd_le_odd a u M r Y D ha hM hu hcM
  have h3 : ∑ n ∈ SwingC2Moment.apSet M r Y, tau (2 ^ a * n + u)
      = ∑ n ∈ SwingC2Moment.apSet M r Y, (2 ^ a * n + u).divisors.card := rfl
  rw [h3]
  exact le_trans h1 (Nat.mul_le_mul_left 2 h2)

/-! ### The incidence count with NO coprimality to the modulus: the `lcm` form

`SwingC2Moment.card_shift_dvd_le` needs `gcd(d,M) = 1` only to turn "congruent mod `d` and mod
`M`" into "congruent mod `dM`".  The honest statement needs no hypothesis at all: two solutions
are congruent modulo `lcm(d,M)`, so the count is `Y/lcm(d,M) + 1 = Y·gcd(d,M)/(dM) + 1`.

This is the form in which the gcd loss becomes *visible and payable*: summing over `d ≤ D`,
the loss over the coprime case is exactly `Σ_d gcd(d,M)/d`, and `filter_shift_eq_empty`
restricts the gcds that occur to divisors of the `M`-part of `2^a r + e` — which, for the kill
modulus, `exists_kill_progression'` caps by the shift. -/
theorem card_shift_dvd_le_lcm (c e M r Y d : ℕ) (hd : 0 < d) (hM : 0 < M)
    (hcd : Nat.Coprime c d) :
    ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).card
      ≤ Y / (Nat.lcm d M) + 1 := by
  classical
  have hlcm : 0 < Nat.lcm d M := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  refine SwingC2Moment.card_le_of_mod_eq (m := Nat.lcm d M) (X := Y) hlcm _ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    exact hx.1.2
  · -- two solutions are congruent modulo `d` and modulo `M`, hence modulo `lcm`
    have hkey : ∀ x y : ℕ, x ≤ y →
        (x ∈ (Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)) →
        (y ∈ (Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)) →
        x % Nat.lcm d M = y % Nat.lcm d M := by
      intro x y hxy hx hy
      rw [Finset.mem_filter, Finset.mem_Icc] at hx hy
      obtain ⟨-, hxm, hxd⟩ := hx
      obtain ⟨-, hym, hyd⟩ := hy
      have hdd : d ∣ y - x := by
        have hsub : d ∣ (c * y + e) - (c * x + e) := Nat.dvd_sub hyd hxd
        have hmul : c * (y - x) = c * y - c * x := Nat.mul_sub c y x
        have hcxy : c * x ≤ c * y := Nat.mul_le_mul_left c hxy
        have he : (c * y + e) - (c * x + e) = (y - x) * c := by
          rw [Nat.mul_comm (y - x) c, hmul]; omega
        rw [he] at hsub
        exact Nat.Coprime.dvd_of_dvd_mul_right hcd.symm hsub
      have hMd : M ∣ y - x := by
        refine (Nat.modEq_iff_dvd' hxy).1 ?_
        show x % M = y % M
        rw [hxm, hym]
      exact (Nat.modEq_iff_dvd' hxy).2 (Nat.lcm_dvd hdd hMd)
    intro x hx y hy
    rcases Nat.le_total x y with h | h
    · exact hkey x y h hx hy
    · exact (hkey y x h hy hx).symm

/-- **The incidence sum with the gcd loss made explicit.**  Summing `card_shift_dvd_le_lcm`
over `d ≤ D`, fibred by `g = gcd(d,M)`: on the fibre `gcd(d,M) = g` the count is
`Y/((d/g)·M) + 1`, and `d ↦ d/g` is injective into `[1,D]`, so each fibre contributes at most
the coprime bound.  The total loss is therefore exactly the NUMBER of gcds that occur, and by
`filter_shift_eq_empty` those are confined to the divisors of any `G` that the `M`-part of
`c·r + e` divides. -/
theorem sum_card_shift_dvd_le_gcd (c e M r Y D G : ℕ) (hM : 0 < M) (hG : G ≠ 0)
    (hcd : ∀ d ∈ Finset.Icc 1 D, Nat.Coprime c d ∨
      (Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e) = ∅)
    (hvan : ∀ d ∈ Finset.Icc 1 D, ¬ (Nat.gcd d M ∣ G) →
      (Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e) = ∅) :
    ∑ d ∈ Finset.Icc 1 D,
        ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).card
      ≤ G.divisors.card * ((Y / M) * (Nat.log 2 D + 2) + D) := by
  classical
  set F : ℕ → ℕ := fun d =>
    ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).card with hF
  set A : Finset ℕ := (Finset.Icc 1 D).filter (fun d => Nat.gcd d M ∣ G) with hA
  -- outside `A` every term vanishes
  have hsplit : ∑ d ∈ Finset.Icc 1 D, F d = ∑ d ∈ A, F d := by
    rw [hA, eq_comm, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 D)
      (fun d => Nat.gcd d M ∣ G) F]
    have : ∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ (Nat.gcd d M ∣ G)), F d = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      rw [Finset.mem_filter] at hd
      rw [hF]
      simp only
      rw [hvan d hd.1 hd.2]
      simp
    omega
  -- the fibres of `d ↦ gcd d M`
  have hmaps : ∀ d ∈ A, Nat.gcd d M ∈ G.divisors := by
    intro d hd
    rw [hA, Finset.mem_filter] at hd
    exact Nat.mem_divisors.2 ⟨hd.2, hG⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps F
  -- each fibre is at most the coprime bound
  have hinner : ∀ g ∈ G.divisors, ∑ d ∈ A.filter (fun d => Nat.gcd d M = g), F d
      ≤ (Y / M) * (Nat.log 2 D + 2) + D := by
    intro g _
    set B : Finset ℕ := A.filter (fun d => Nat.gcd d M = g) with hB
    have hgpos : ∀ d ∈ B, 0 < g := by
      intro d hd
      rw [hB, Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_Icc] at hd
      have := hd.1.1.1
      rw [← hd.2]
      exact Nat.gcd_pos_of_pos_left M (by omega)
    have hstep : ∀ d ∈ B, F d ≤ Y / M / (d / g) + 1 := by
      intro d hd
      have hgp := hgpos d hd
      rw [hB, Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨⟨hd1, hdD⟩, -⟩, hgd⟩ := hd
      have hgdvd : g ∣ d := by rw [← hgd]; exact Nat.gcd_dvd_left d M
      have hlcm : Nat.lcm d M = (d / g) * M := by
        have h1 : Nat.gcd d M * Nat.lcm d M = d * M := Nat.gcd_mul_lcm d M
        have h2 : g * (d / g) = d := Nat.mul_div_cancel' hgdvd
        have h3 : g * Nat.lcm d M = g * ((d / g) * M) := by
          rw [← Nat.mul_assoc, h2, ← hgd]; exact h1
        exact Nat.eq_of_mul_eq_mul_left hgp h3
      rcases hcd d (Finset.mem_Icc.2 ⟨hd1, hdD⟩) with hco | hem
      · have := card_shift_dvd_le_lcm c e M r Y d (by omega) hM hco
        rw [hlcm] at this
        have hdiv : Y / ((d / g) * M) = Y / M / (d / g) := by
          rw [Nat.div_div_eq_div_mul, Nat.mul_comm M (d / g)]
        rw [hdiv] at this
        exact this
      · rw [hF]
        simp only
        rw [hem]
        simp
    have hinj : Set.InjOn (fun d => d / g) ↑B := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, hB, hA, Set.mem_ofPred_eq, Finset.mem_filter] at hx hy
      have hgx : g ∣ x := by rw [← hx.2]; exact Nat.gcd_dvd_left x M
      have hgy : g ∣ y := by rw [← hy.2]; exact Nat.gcd_dvd_left y M
      have hgp : 0 < g := by
        have hx1 : 1 ≤ x := (Finset.mem_Icc.1 hx.1.1).1
        rw [← hx.2]; exact Nat.gcd_pos_of_pos_left M (by omega)
      simp only at hxy
      have h1 : g * (x / g) = x := Nat.mul_div_cancel' hgx
      have h2 : g * (y / g) = y := Nat.mul_div_cancel' hgy
      rw [← h1, ← h2, hxy]
    have hsub : B.image (fun d => d / g) ⊆ Finset.Icc 1 D := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx
      have hgp := hgpos d hd
      rw [hB, Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨⟨hd1, hdD⟩, -⟩, hgd⟩ := hd
      have hgdvd : g ∣ d := by rw [← hgd]; exact Nat.gcd_dvd_left d M
      refine Finset.mem_Icc.2 ⟨?_, ?_⟩
      · exact Nat.one_le_div_iff hgp |>.2 (Nat.le_of_dvd (by omega) hgdvd)
      · exact le_trans (Nat.div_le_self d g) hdD
    calc ∑ d ∈ B, F d ≤ ∑ d ∈ B, (Y / M / (d / g) + 1) := Finset.sum_le_sum hstep
      _ = ∑ x ∈ B.image (fun d => d / g), (Y / M / x + 1) :=
          (Finset.sum_image (f := fun x => Y / M / x + 1)
            (fun x hx y hy hxy => hinj hx hy hxy)).symm
      _ ≤ ∑ x ∈ Finset.Icc 1 D, (Y / M / x + 1) :=
          Finset.sum_le_sum_of_subset hsub
      _ = (∑ x ∈ Finset.Icc 1 D, Y / M / x) + D := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
          omega
      _ ≤ (Y / M) * (Nat.log 2 D + 2) + D := by
          have := SwingC2Moment.sum_div_le_log (Y / M) D
          omega
  calc ∑ d ∈ Finset.Icc 1 D, F d = ∑ d ∈ A, F d := hsplit
    _ = ∑ g ∈ G.divisors, ∑ d ∈ A.filter (fun d => Nat.gcd d M = g), F d := hfib.symm
    _ ≤ ∑ _g ∈ G.divisors, ((Y / M) * (Nat.log 2 D + 2) + D) := Finset.sum_le_sum hinner
    _ = G.divisors.card * ((Y / M) * (Nat.log 2 D + 2) + D) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **The gcd that occurs always divides `gcd(M, c·r+e)`.**  Sharper than
`filter_shift_eq_empty`, which only handled the prime level: if `g = gcd(d,M)` then `g ∣ M`
and, from `g ∣ d ∣ c·n+e` together with `n ≡ r (mod g)`, also `g ∣ c·r+e`. -/
theorem gcd_dvd_gcd_shift {c e M r Y d : ℕ}
    (hne : ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).Nonempty) :
    Nat.gcd d M ∣ Nat.gcd M (c * r + e) := by
  classical
  obtain ⟨n, hn⟩ := hne
  rw [Finset.mem_filter] at hn
  obtain ⟨-, hnm, hdvd⟩ := hn
  set g : ℕ := Nat.gcd d M with hg
  have hgM : g ∣ M := Nat.gcd_dvd_right d M
  have hgd : g ∣ d := Nat.gcd_dvd_left d M
  have hg1 : g ∣ c * n + e := hgd.trans hdvd
  have hnr : n ≡ r [MOD M] := hnm
  have hg2 : g ∣ c * r + e := by
    have h1 : c * n ≡ c * r [MOD g] := (Nat.ModEq.of_dvd hgM hnr).mul_left c
    have h2 : c * n + e ≡ c * r + e [MOD g] := h1.add_right e
    have h3 : (c * n + e) % g = 0 := Nat.mod_eq_zero_of_dvd hg1
    have h4 : (c * r + e) % g = 0 := by
      have := h2
      unfold Nat.ModEq at this
      omega
    exact Nat.dvd_iff_mod_eq_zero.2 h4
  exact Nat.dvd_gcd hgM hg2

/-- **The crude incidence bound, fully general.**  No hypothesis on `M` at all: the loss over
the coprime case is `τ(gcd(M, c·r+e))`, and nothing else. -/
theorem sum_card_shift_dvd_le_gcd' (c e M r Y D : ℕ) (hM : 0 < M)
    (hcd : ∀ d ∈ Finset.Icc 1 D, Nat.Coprime c d ∨
      (Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e) = ∅) :
    ∑ d ∈ Finset.Icc 1 D,
        ((Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ c * n + e)).card
      ≤ (Nat.gcd M (c * r + e)).divisors.card * ((Y / M) * (Nat.log 2 D + 2) + D) := by
  classical
  refine sum_card_shift_dvd_le_gcd c e M r Y D _ hM ?_ hcd ?_
  · have : 0 < Nat.gcd M (c * r + e) := Nat.gcd_pos_of_pos_left _ hM
    omega
  · intro d _ hnd
    by_contra hcon
    exact hnd (gcd_dvd_gcd_shift (Finset.nonempty_iff_ne_empty.2 hcon))

/-! ### The shifted first moment for a GENERAL shift, and its exceptional set

Combining the 2-adic reduction with `tau_shift_sum_AP_odd`: for any shift `e` with
`0 < e < 2^a` and `gcd(M, 2^a r + e) = 1`, the first moment of `τ(2^a n + e)` along the
progression is the unshifted bound times `log₂ e + 1`.  Nothing here is analytic and nothing
is lost to the modulus. -/

/-- The 2-adic split of a shift, uniform in `n`. -/
theorem tau_shift_two_adic' (a e : ℕ) (he : 0 < e) (hea : e < 2 ^ a) :
    ∃ v u : ℕ, e = 2 ^ v * u ∧ ¬ 2 ∣ u ∧ v < a ∧ 2 ^ v ≤ e ∧ 0 < u ∧ u ≤ e ∧
      ∀ n : ℕ, tau (2 ^ a * n + e) = (v + 1) * tau (2 ^ (a - v) * n + u) := by
  classical
  set v : ℕ := e.factorization 2 with hv
  set u : ℕ := e / 2 ^ v with hu
  have hne : e ≠ 0 := by omega
  have hsplit : 2 ^ v * u = e := Nat.ordProj_mul_ordCompl_eq_self e 2
  have hodd : ¬ 2 ∣ u := Nat.not_dvd_ordCompl Nat.prime_two hne
  have hupos : 0 < u := Nat.ordCompl_pos 2 hne
  have hle : (2 : ℕ) ^ v ≤ e := Nat.le_of_dvd he (Nat.ordProj_dvd e 2)
  have hva : v < a := by
    by_contra hcon
    have : (2 : ℕ) ^ a ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hue : u ≤ e := by
    have h1 : 1 * u ≤ 2 ^ v * u := Nat.mul_le_mul_right u Nat.one_le_two_pow
    omega
  refine ⟨v, u, hsplit.symm, hodd, hva, hle, hupos, hue, fun n => ?_⟩
  have hfac : 2 ^ a * n + e = 2 ^ v * (2 ^ (a - v) * n + u) := by
    have h1 : (2 : ℕ) ^ v * (2 ^ (a - v) * n) = 2 ^ a * n := by
      rw [← Nat.mul_assoc, ← pow_add]
      congr 2
      omega
    rw [Nat.mul_add, h1, hsplit]
  have hoddm : ¬ 2 ∣ 2 ^ (a - v) * n + u := by
    intro hcon
    have h2 : (2 : ℕ) ∣ 2 ^ (a - v) * n :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (by omega : a - v ≠ 0)) n
    exact hodd (by omega)
  rw [hfac, tau_two_pow_mul_odd hoddm]

/-- **The shifted first moment along the progression, for a general shift.** -/
theorem tau_shift_sum_AP (a e M r Y : ℕ) (he : 0 < e) (hea : e < 2 ^ a) (hM : 0 < M)
    (hcM : Nat.Coprime M (2 ^ a * r + e)) :
    ∑ n ∈ SwingC2Moment.apSet M r Y, tau (2 ^ a * n + e)
      ≤ (Nat.log 2 e + 1) *
          (2 * ((Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ a * Y + e)) + 2)
                  + Nat.sqrt (2 ^ a * Y + e))) := by
  classical
  obtain ⟨v, u, hsplit, hodd, hva, hle, hupos, hue, hfac⟩ := tau_shift_two_adic' a e he hea
  set c : ℕ := a - v with hc
  have hc1 : 1 ≤ c := by omega
  have hcv : 2 ^ v * (2 ^ c * r) = 2 ^ a * r := by
    rw [← Nat.mul_assoc, ← pow_add]
    congr 2
    omega
  have hdvd : 2 ^ c * r + u ∣ 2 ^ a * r + e := by
    refine ⟨2 ^ v, ?_⟩
    rw [Nat.mul_comm (2 ^ c * r + u) (2 ^ v), Nat.mul_add, hcv, hsplit]
  have hcM' : Nat.Coprime M (2 ^ c * r + u) := Nat.Coprime.coprime_dvd_right hdvd hcM
  have hmain := tau_shift_sum_AP_odd c u M r Y hc1 hM hodd hcM'
  have hmono : Nat.sqrt (2 ^ c * Y + u) ≤ Nat.sqrt (2 ^ a * Y + e) := by
    refine Nat.sqrt_le_sqrt ?_
    have h1 : (2 : ℕ) ^ c ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ c * Y ≤ 2 ^ a * Y := Nat.mul_le_mul_right Y h1
    omega
  have hlogmono : Nat.log 2 (Nat.sqrt (2 ^ c * Y + u)) ≤ Nat.log 2 (Nat.sqrt (2 ^ a * Y + e)) :=
    Nat.log_mono_right hmono
  have hvlog : v ≤ Nat.log 2 e := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 hle
  have hsum : ∑ n ∈ SwingC2Moment.apSet M r Y, tau (2 ^ a * n + e)
      = (v + 1) * ∑ n ∈ SwingC2Moment.apSet M r Y, tau (2 ^ c * n + u) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => hfac n
  rw [hsum]
  refine Nat.mul_le_mul (by omega) (le_trans hmain ?_)
  have h1 : (Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ c * Y + u)) + 2)
      ≤ (Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ a * Y + e)) + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The exceptional set of a general shift, over the integers of the progression.**  This is
the integer-level statement that `TauMomentPrimesShift` needs; the ONLY thing still missing on
the headline path is the transfer from these integers to the PRIMES of the progression. -/
theorem card_large_tau_shift_le (a e M r Y T : ℕ) (he : 0 < e) (hea : e < 2 ^ a) (hM : 0 < M)
    (hcM : Nat.Coprime M (2 ^ a * r + e)) :
    T * ((SwingC2Moment.apSet M r Y).filter
          (fun n => T ≤ tau (2 ^ a * n + e))).card
      ≤ (Nat.log 2 e + 1) *
          (2 * ((Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ a * Y + e)) + 2)
                  + Nat.sqrt (2 ^ a * Y + e))) := by
  classical
  refine le_trans ?_ (tau_shift_sum_AP a e M r Y he hea hM hcM)
  set S : Finset ℕ := (SwingC2Moment.apSet M r Y).filter
    (fun n => T ≤ tau (2 ^ a * n + e)) with hS
  have h1 : ∑ _n ∈ S, T ≤ ∑ n ∈ S, tau (2 ^ a * n + e) := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    simp only [hS, Finset.mem_filter] at hn
    exact hn.2
  have h2 : ∑ n ∈ S, tau (2 ^ a * n + e)
      ≤ ∑ n ∈ SwingC2Moment.apSet M r Y, tau (2 ^ a * n + e) :=
    Finset.sum_le_sum_of_subset (by rw [hS]; exact Finset.filter_subset _ _)
  have h3 : ∑ _n ∈ S, T = T * S.card := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  omega

/-- **The shifted first moment along a progression, with NO hypothesis on the modulus.**  The
odd case; the loss over the coprime case is exactly `τ(gcd(M, 2^a r + u))`. -/
theorem tau_shift_sum_AP_odd_gcd (a u M r Y : ℕ) (ha : 1 ≤ a) (hM : 0 < M) (hu : ¬ 2 ∣ u) :
    ∑ n ∈ SwingC2Moment.apSet M r Y, tau (2 ^ a * n + u)
      ≤ 2 * ((Nat.gcd M (2 ^ a * r + u)).divisors.card *
          ((Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ a * Y + u)) + 2)
            + Nat.sqrt (2 ^ a * Y + u))) := by
  classical
  set D : ℕ := Nat.sqrt (2 ^ a * Y + u) with hD
  have hmem : ∀ n ∈ SwingC2Moment.apSet M r Y, n ≤ Y := by
    intro n hn
    rw [SwingC2Moment.apSet, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1.2
  have h1 := SwingC2Moment.tau_shift_sum_le (2 ^ a) u Y (SwingC2Moment.apSet M r Y) hmem
  have hfil : ∀ d : ℕ, (SwingC2Moment.apSet M r Y).filter (fun n => d ∣ 2 ^ a * n + u)
      = (Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ 2 ^ a * n + u) := by
    intro d
    rw [SwingC2Moment.apSet, Finset.filter_filter]
  have hcd : ∀ d ∈ Finset.Icc 1 D, Nat.Coprime (2 ^ a) d ∨
      (Finset.Icc 1 Y).filter (fun n => n % M = r % M ∧ d ∣ 2 ^ a * n + u) = ∅ := by
    intro d _
    by_cases hdodd : 2 ∣ d
    · exact Or.inr (filter_shift_eq_empty_even ha hu hdodd)
    · exact Or.inl (Nat.Coprime.pow_left _
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hdodd))
  have h2 : ∑ d ∈ Finset.Icc 1 D,
      ((SwingC2Moment.apSet M r Y).filter (fun n => d ∣ 2 ^ a * n + u)).card
        ≤ (Nat.gcd M (2 ^ a * r + u)).divisors.card * ((Y / M) * (Nat.log 2 D + 2) + D) := by
    simp only [hfil]
    exact sum_card_shift_dvd_le_gcd' (2 ^ a) u M r Y D hM hcd
  have h3 : ∑ n ∈ SwingC2Moment.apSet M r Y, tau (2 ^ a * n + u)
      = ∑ n ∈ SwingC2Moment.apSet M r Y, (2 ^ a * n + u).divisors.card := rfl
  rw [h3]
  exact le_trans h1 (Nat.mul_le_mul_left 2 h2)

/-- **The shifted first moment, general shift, general modulus — no hypotheses left.**  For any
`0 < e < 2^a` and any `M > 0`,

    `Σ_{n ≤ Y, n ≡ r (M)} τ(2^a n + e) ≤ (log₂ e + 1)·τ(gcd(M, 2^a r + e))·2((Y/M)(log₂D+2)+D)`.

Both loss factors are explicit functions of the SHIFT and of one fixed integer; neither
involves `ω(M)` or `τ(M)`.  This is the final elementary form of the first moment: the whole
of the crux except the passage from the integers of the progression to its primes. -/
theorem tau_shift_sum_AP_gen (a e M r Y : ℕ) (he : 0 < e) (hea : e < 2 ^ a) (hM : 0 < M) :
    ∑ n ∈ SwingC2Moment.apSet M r Y, tau (2 ^ a * n + e)
      ≤ (Nat.log 2 e + 1) * ((Nat.gcd M (2 ^ a * r + e)).divisors.card *
          (2 * ((Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ a * Y + e)) + 2)
                  + Nat.sqrt (2 ^ a * Y + e)))) := by
  classical
  obtain ⟨v, u, hsplit, hodd, hva, hle, hupos, hue, hfac⟩ := tau_shift_two_adic' a e he hea
  set c : ℕ := a - v with hc
  have hc1 : 1 ≤ c := by omega
  have hcv : 2 ^ v * (2 ^ c * r) = 2 ^ a * r := by
    rw [← Nat.mul_assoc, ← pow_add]
    congr 2
    omega
  have hdvd : 2 ^ c * r + u ∣ 2 ^ a * r + e := by
    refine ⟨2 ^ v, ?_⟩
    rw [Nat.mul_comm (2 ^ c * r + u) (2 ^ v), Nat.mul_add, hcv, hsplit]
  -- the gcd of the odd part divides the gcd of the whole
  have hgdvd : Nat.gcd M (2 ^ c * r + u) ∣ Nat.gcd M (2 ^ a * r + e) :=
    Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans hdvd)
  have hgne : Nat.gcd M (2 ^ a * r + e) ≠ 0 := by
    have : 0 < Nat.gcd M (2 ^ a * r + e) := Nat.gcd_pos_of_pos_left _ hM
    omega
  have hgcard : (Nat.gcd M (2 ^ c * r + u)).divisors.card
      ≤ (Nat.gcd M (2 ^ a * r + e)).divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd hgne hgdvd)
  have hmain := tau_shift_sum_AP_odd_gcd c u M r Y hc1 hM hodd
  have hmono : Nat.sqrt (2 ^ c * Y + u) ≤ Nat.sqrt (2 ^ a * Y + e) := by
    refine Nat.sqrt_le_sqrt ?_
    have h1 : (2 : ℕ) ^ c ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ c * Y ≤ 2 ^ a * Y := Nat.mul_le_mul_right Y h1
    omega
  have hlogmono : Nat.log 2 (Nat.sqrt (2 ^ c * Y + u)) ≤ Nat.log 2 (Nat.sqrt (2 ^ a * Y + e)) :=
    Nat.log_mono_right hmono
  have hvlog : v ≤ Nat.log 2 e := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 hle
  have hsum : ∑ n ∈ SwingC2Moment.apSet M r Y, tau (2 ^ a * n + e)
      = (v + 1) * ∑ n ∈ SwingC2Moment.apSet M r Y, tau (2 ^ c * n + u) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => hfac n
  rw [hsum]
  refine Nat.mul_le_mul (by omega) (le_trans hmain ?_)
  have hbody : (Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ c * Y + u)) + 2) + Nat.sqrt (2 ^ c * Y + u)
      ≤ (Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ a * Y + e)) + 2) + Nat.sqrt (2 ^ a * Y + e) := by
    have h1 : (Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ c * Y + u)) + 2)
        ≤ (Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ a * Y + e)) + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  calc 2 * ((Nat.gcd M (2 ^ c * r + u)).divisors.card *
        ((Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ c * Y + u)) + 2) + Nat.sqrt (2 ^ c * Y + u)))
      ≤ 2 * ((Nat.gcd M (2 ^ a * r + e)).divisors.card *
        ((Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ a * Y + e)) + 2) + Nat.sqrt (2 ^ a * Y + e))) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul hgcard hbody)
    _ = (Nat.gcd M (2 ^ a * r + e)).divisors.card *
        (2 * ((Y / M) * (Nat.log 2 (Nat.sqrt (2 ^ a * Y + e)) + 2)
              + Nat.sqrt (2 ^ a * Y + e))) := by ring

/-- **The sieve input, in its final single-inequality form.**  For one family `P` of primes of
the progression and one shift `e = K+1+k`, the number of *divisor incidences*

    Inc_k = Σ_{d ≤ √(2^a Y + e)} #{p ∈ P : d ∣ 2^a p + e}

satisfies `8·Inc_k ≤ (b^K/4)·(k+1)·|P|`.  Note the `2^k` has cancelled: the requirement is the
same at every shift, and it is exactly "the average of `τ(2^a p + e)` over the primes `p` of the
progression is `≪ b^K`", with `b^K` exponentially larger than the truth `≍ log(2^a Y)`.

Each inner count is `#(P ∩ one class mod lcm(d,M))`, i.e. `π(Y;q,·)`, so this is
Brun–Titchmarsh summed over `d ≤ Y^{0.6}`.  (An *integer* count of the incidences does NOT
suffice — it overshoots `|P|` by `log²`; the one logarithm the sieve gains is load-bearing.) -/
def ShiftedDivisorIncidence (b : ℕ) : Prop :=
  ∀ K M r a N : ℕ, 2 ≤ K → 0 < M → Nat.Coprime r M → a ≤ b ^ (K / 4) →
    M ≤ 2 ^ (b ^ (K / 4)) → N ≤ b ^ (K / 4) →
    ∃ Y : ℕ, ∃ P : Finset ℕ,
      (∀ p ∈ P, N < p ∧ p.Prime ∧ p ≡ r [MOD M] ∧ p ≤ Y) ∧ 0 < P.card ∧
      ∀ k : ℕ,
        8 * (∑ d ∈ Finset.Icc 1 (Nat.sqrt (2 ^ a * Y + (K + 1 + k))),
              (P.filter (fun p => d ∣ 2 ^ a * p + (K + 1 + k))).card)
          ≤ b ^ K / 4 * (k + 1) * P.card

/-- **Markov + the hyperbola reduction give the density bound.**  Nothing analytic is left. -/
theorem tauMomentPrimesShift_of_incidence (b : ℕ) (hb : 3 ≤ b)
    (h : ShiftedDivisorIncidence b) : TauMomentPrimesShift b := by
  classical
  intro K M r a N hK hM hr ha hMb hN
  obtain ⟨Y, P, hPmem, hPcard, hinc⟩ := h K M r a N hK hM hr ha hMb hN
  refine ⟨Y, P, hPmem, hPcard, fun k => ?_⟩
  set e : ℕ := K + 1 + k with he
  set T : ℕ := b ^ K / 4 * (k + 1) * 2 ^ k with hT
  have hbK4 : 4 ≤ b ^ K := by
    calc (4 : ℕ) ≤ 9 := by norm_num
      _ = 3 ^ 2 := by norm_num
      _ ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
      _ ≤ b ^ K := Nat.pow_le_pow_right (by omega) hK
  have hApos : 0 < b ^ K / 4 := Nat.div_pos hbK4 (by norm_num)
  have hTpos : 0 < T := by
    have h1 : 0 < (2 : ℕ) ^ k := Nat.pow_pos (by norm_num : 0 < 2)
    rw [hT]; positivity
  set Bad : Finset ℕ := P.filter (fun p => T < tau (2 ^ a * p + K + 1 + k)) with hBad
  have hmarkov : T * Bad.card ≤ ∑ p ∈ P, tau (2 ^ a * p + e) := by
    have h1 : ∑ _p ∈ Bad, T ≤ ∑ p ∈ Bad, tau (2 ^ a * p + e) := by
      refine Finset.sum_le_sum fun p hp => ?_
      rw [hBad, Finset.mem_filter] at hp
      have h2 := hp.2
      rw [show 2 ^ a * p + e = 2 ^ a * p + K + 1 + k by rw [he]; ring]
      omega
    have h2 : ∑ p ∈ Bad, tau (2 ^ a * p + e) ≤ ∑ p ∈ P, tau (2 ^ a * p + e) :=
      Finset.sum_le_sum_of_subset (by rw [hBad]; exact Finset.filter_subset _ _)
    have h3 : ∑ _p ∈ Bad, T = T * Bad.card := by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    omega
  have hhyp : ∑ p ∈ P, tau (2 ^ a * p + e)
      ≤ 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (2 ^ a * Y + e)),
          (P.filter (fun p => d ∣ 2 ^ a * p + e)).card :=
    SwingC2Moment.tau_shift_sum_le (2 ^ a) e Y P (fun p hp => (hPmem p hp).2.2.2)
  have hinck := hinc k
  have hkey : T * (4 * 2 ^ k * Bad.card) ≤ T * P.card := by
    calc T * (4 * 2 ^ k * Bad.card)
        = 4 * 2 ^ k * (T * Bad.card) := by ring
      _ ≤ 4 * 2 ^ k * (2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (2 ^ a * Y + e)),
            (P.filter (fun p => d ∣ 2 ^ a * p + e)).card) :=
          Nat.mul_le_mul_left _ (le_trans hmarkov hhyp)
      _ = 2 ^ k * (8 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt (2 ^ a * Y + e)),
            (P.filter (fun p => d ∣ 2 ^ a * p + e)).card) := by ring
      _ ≤ 2 ^ k * (b ^ K / 4 * (k + 1) * P.card) := Nat.mul_le_mul_left _ hinck
      _ = T * P.card := by rw [hT]; ring
  exact Nat.le_of_mul_le_mul_left hkey hTpos

/-- **The pigeonhole at the heart of the shift route, extracted.**  Given a family `P` of
primes of the progression whose per-shift exceptional sets occupy at most a `2^{-k}/4`
fraction, some member of `P` obeys the geometric threshold at EVERY shift simultaneously. -/
theorem exists_good_prime_of_density (b K M r a N Y : ℕ) (P : Finset ℕ) (hb : 3 ≤ b)
    (hK : 2 ≤ K)
    (hPmem : ∀ p ∈ P, N < p ∧ p.Prime ∧ p ≡ r [MOD M] ∧ p ≤ Y) (hPcard : 0 < P.card)
    (hdens : ∀ k : ℕ, 4 * 2 ^ k *
        (P.filter (fun p => b ^ K / 4 * (k + 1) * 2 ^ k < tau (2 ^ a * p + K + 1 + k))).card
      ≤ P.card) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p ≡ r [MOD M] ∧
      ∀ k : ℕ, tau (2 ^ a * p + K + 1 + k) ≤ b ^ K / 4 * (k + 1) * 2 ^ k := by
  classical
  set X : ℕ := 2 ^ a * Y + K with hX
  set S : ℕ := Nat.sqrt X + 1 with hS
  set kb : ℕ := Nat.log 2 S + 2 with hkb
  have hbK4 : 4 ≤ b ^ K := by
    calc (4 : ℕ) ≤ 9 := by norm_num
      _ = 3 ^ 2 := by norm_num
      _ ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
      _ ≤ b ^ K := Nat.pow_le_pow_right (by omega) hK
  have hApos : 0 < b ^ K / 4 := Nat.div_pos hbK4 (by norm_num)
  -- beyond `kb` the trivial divisor bound already gives the threshold
  have htriv : ∀ p ∈ P, ∀ k : ℕ, kb ≤ k →
      tau (2 ^ a * p + K + 1 + k) ≤ b ^ K / 4 * (k + 1) * 2 ^ k := by
    intro p hp k hkbk
    obtain ⟨-, -, -, hpY⟩ := hPmem p hp
    have hle : 2 ^ a * p + K + 1 + k ≤ X + (1 + k) := by
      have : 2 ^ a * p ≤ 2 ^ a * Y := Nat.mul_le_mul_left _ hpY
      omega
    have h1 : tau (2 ^ a * p + K + 1 + k) ≤ 2 * Nat.sqrt (2 ^ a * p + K + 1 + k) :=
      tau_le_two_mul_sqrt (by omega)
    have h2 : Nat.sqrt (2 ^ a * p + K + 1 + k) ≤ Nat.sqrt (X + (1 + k)) :=
      Nat.sqrt_le_sqrt hle
    have h3 : Nat.sqrt (X + (1 + k)) ≤ Nat.sqrt X + (1 + k) := sqrt_add_le X (1 + k)
    -- `S + k ≤ 2^k` for `k ≥ kb`
    have hSlt : S ≤ 2 ^ (Nat.log 2 S + 1) := le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) S)
    have hk1 : 1 ≤ k := by omega
    have hmono : (2 : ℕ) ^ (Nat.log 2 S + 1) ≤ 2 ^ (k - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hkk : k ≤ 2 ^ (k - 1) := le_two_pow_pred hk1
    have hsplit : (2 : ℕ) ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
      have : k - 1 + 1 = k := by omega
      calc (2 : ℕ) ^ (k - 1) + 2 ^ (k - 1) = 2 ^ (k - 1 + 1) := by ring
        _ = 2 ^ k := by rw [this]
    have hgoal : 2 * Nat.sqrt X + 2 + 2 * k ≤ 2 * 2 ^ k := by omega
    have h4 : 1 * (2 * 2 ^ k) ≤ b ^ K / 4 * (k + 1) * 2 ^ k := by
      have : 2 * 2 ^ k ≤ (k + 1) * 2 ^ k := Nat.mul_le_mul_right _ (by omega)
      calc 1 * (2 * 2 ^ k) = 2 * 2 ^ k := by ring
        _ ≤ (k + 1) * 2 ^ k := this
        _ ≤ b ^ K / 4 * ((k + 1) * 2 ^ k) := Nat.le_mul_of_pos_left _ hApos
        _ = b ^ K / 4 * (k + 1) * 2 ^ k := by ring
    omega
  set Bad : ℕ → Finset ℕ := fun k =>
    P.filter (fun p => b ^ K / 4 * (k + 1) * 2 ^ k < tau (2 ^ a * p + K + 1 + k)) with hBad
  have hdens' : ∀ k : ℕ, 4 * 2 ^ k * (Bad k).card ≤ P.card := fun k => hdens k
  set U : Finset ℕ := (Finset.range kb).biUnion Bad with hU
  have hUcard : U.card < P.card := by
    have h1 : U.card ≤ ∑ k ∈ Finset.range kb, (Bad k).card := Finset.card_biUnion_le
    have h2 := sum_le_of_geom_bound (fun k => (Bad k).card) P.card hdens' kb
    omega
  obtain ⟨p, hpP, hpU⟩ : ∃ p ∈ P, p ∉ U := by
    by_contra hcon
    push_neg at hcon
    exact absurd (Finset.card_le_card (fun x hx => hcon x hx)) (by omega)
  obtain ⟨hpN, hpp, hpr, -⟩ := hPmem p hpP
  refine ⟨p, hpN, hpp, hpr, fun k => ?_⟩
  rcases Nat.lt_or_ge k kb with hk1 | hk1
  · have hnb : p ∉ Bad k := fun hmem => hpU (Finset.mem_biUnion.2
      ⟨k, Finset.mem_range.2 hk1, hmem⟩)
    simp only [hBad, Finset.mem_filter, not_and, not_lt] at hnb
    exact hnb hpP
  · exact htriv p hpP k hk1

/-- **The union bound over shifts is discharged, and it is free.**  Beyond
`kb = log₂(√X + 1) + 2` shifts the trivial bound `τ(m) ≤ 2√m` already beats the geometric
threshold; the remaining exceptional sets sum to `≤ |P|/2 < |P|` by `sum_le_of_geom_bound`. -/
theorem tauMomentPrimes_of_shift (b : ℕ) (hb : 3 ≤ b) (h : TauMomentPrimesShift b) :
    TauMomentPrimes b := by
  intro K M r a N hK hM hr ha hMb hN
  obtain ⟨Y, P, hPmem, hPcard, hdens⟩ := h K M r a N hK hM hr ha hMb hN
  exact exists_good_prime_of_density b K M r a N Y P hb hK hPmem hPcard hdens

/-- **`CarryLeaf` follows from `TauMomentPrimes` by pure analysis** (`carry_le_of_tau_geom`). -/
theorem carryLeaf_of_tauMomentPrimes (b : ℕ) (hb : 3 ≤ b) (h : TauMomentPrimes b) :
    CarryLeaf b := by
  intro K M r a N hK hM hr ha hMb hN
  obtain ⟨p, hpN, hpp, hpr, hk⟩ := h K M r a N hK hM hr ha hMb hN
  refine ⟨p, hpN, hpp, hpr, ?_⟩
  have hbK4 : 4 ≤ b ^ K := by
    calc (4 : ℕ) ≤ 9 := by norm_num
      _ = 3 ^ 2 := by norm_num
      _ ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
      _ ≤ b ^ K := Nat.pow_le_pow_right (by omega) hK
  have hle := carry_le_of_tau_geom b hb (2 ^ a * p + K) (b ^ K / 4) hk
  have hq : 4 * (b ^ K / 4) ≤ b ^ K := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have hqpos : 1 ≤ b ^ K / 4 := Nat.one_le_div_iff (by norm_num) |>.2 hbK4
  have hint : (3 : ℤ) * ((b ^ K / 4 : ℕ) : ℤ) < ((b ^ K : ℕ) : ℤ) := by
    have : 3 * (b ^ K / 4) < b ^ K := by omega
    exact_mod_cast this
  have hcast : ((b ^ K : ℕ) : ℤ) = (b : ℤ) ^ K := by push_cast; ring
  omega

/-! ### The decomposition of the crux into ONE arithmetic hypothesis

Everything elementary is now proved (`tau_shift_sum_AP_gen`): along the INTEGERS of the
progression the shifted divisor function obeys the first moment with the two explicit loss
factors `log₂ e + 1` and `τ(gcd(M, 2^a r + e))`.  What is missing is only that the survivor
must be PRIME.

The gap is therefore a single statement about the density of primes in an arithmetic
progression, in one specific and completely explicit range.  It is stated below as
`PrimeDensityAP`, and the crux splits into exactly two named leaves:

* `tauMomentPrimesShiftStruct_of_primeDensity` — Markov on `tau_shift_sum_AP_gen`, the union
  over shifts by `sum_le_of_geom_bound`, and the pigeonhole against `PrimeDensityAP`.  No new
  mathematics; the budget inequality is `b^K ≥ 32·(log₂e+1)·2^{k}·(log₂D+2)·B²` which, with
  `B = b^{K/4}` and `log₂ D ≤ b^{K/4}`, clears with a factor `b^{K/4}` to spare.
* `survivorLeaf_of_struct` — supplies the two structural hypotheses from the kill progression:
  the gcd bound from `exists_kill_progression'` (every prime of `gcd(M, 2^a r + K+1+k)` is
  `≤ j₀ + e`, hence at most `k−2` of them, each to the first power, so `τ ≤ 2^k`) and the
  2-adic room from `exists_survivor_data_large`.

**On the status of `PrimeDensityAP`.**  For a FIXED modulus it is the prime number theorem in
arithmetic progressions, and the `B²` of slack is two logarithms more than PNT gives.  The
content is the uniformity: here `log₂ M ≤ B` and `log₂ Y ≤ B`, i.e. `M` may be a genuine power
of `Y`.  The budget forces this — `b^K ≥ (log Y)²` caps `log₂ Y` at `b^{K/2}` while
`log₂ M ≈ b(ℓ+K+5)^4` is polynomial in `K`, so `M = exp((log Y)^θ)` with `θ` bounded away from
`0` and `M` is never polylogarithmic in `Y`.  That places the statement inside the classical
zero-free-region range but OUTSIDE the range in which a Landau–Siegel zero can be excluded, so
it is not a consequence of anything unconditional in the literature.  It is the honest single
hypothesis on which this route rests. -/

/-- **The one open arithmetic input: primes in an arithmetic progression, with `log₂ M ≤ B`
and `log₂ Y ≤ B`, at density `(Y/M)/B²`.**  See the section docstring for its status. -/
def PrimeDensityAP : Prop :=
  ∀ M r N B : ℕ, 0 < M → Nat.Coprime r M → Nat.log 2 M ≤ B → N ≤ B → 4 ≤ B →
    ∃ Y : ℕ, N < Y ∧ Nat.log 2 Y ≤ B ∧
      Y / M ≤ B ^ 2 *
        ((Finset.Icc 1 Y).filter (fun p => N < p ∧ p.Prime ∧ p % M = r % M)).card

/-- **The shift leaf with the structural hypotheses the construction actually supplies.**
Two extra hypotheses over `TauMomentPrimesShift`: `hgcd`, which `exists_kill_progression'`
gives, and the 2-adic room `log₂(b^{K/4}) ≤ a`, which `exists_survivor_data_large` gives. -/
def TauMomentPrimesShiftStruct (b : ℕ) : Prop :=
  ∀ K M r a N : ℕ, 2 ≤ K → 0 < M → Nat.Coprime r M →
    Nat.log 2 M ≤ b ^ (K / 4) → N ≤ b ^ (K / 4) →
    Nat.log 2 (b ^ (K / 4)) ≤ a → a ≤ b ^ (K / 4) →
    (∀ k : ℕ, (Nat.gcd M (2 ^ a * r + (K + 1 + k))).divisors.card ≤ 2 ^ k) →
    ∃ Y : ℕ, ∃ P : Finset ℕ,
      (∀ p ∈ P, N < p ∧ p.Prime ∧ p ≡ r [MOD M] ∧ p ≤ Y) ∧ 0 < P.card ∧
      ∀ k : ℕ, 4 * 2 ^ k *
          (P.filter (fun p => b ^ K / 4 * (k + 1) * 2 ^ k < tau (2 ^ a * p + K + 1 + k))).card
        ≤ P.card

/-- **Leaf 1 of the decomposition.**  Markov on `tau_shift_sum_AP_gen` plus the pigeonhole
against `PrimeDensityAP`.  Every ingredient is proved; what remains is the arithmetic of the
budget inequality.  Open. -/
theorem tauMomentPrimesShiftStruct_of_primeDensity (b : ℕ) (hb : 3 ≤ b) (H : PrimeDensityAP) :
    TauMomentPrimesShiftStruct b := by
  sorry

/-- **Leaf 2 of the decomposition.**  Supplies the two structural hypotheses of
`TauMomentPrimesShiftStruct` from the kill progression (`exists_kill_progression'`, this
session) and the large-exponent survivor data (`exists_survivor_data_large`), then runs the
already-proved chain `TauMomentPrimesShift ⟹ TauMomentPrimes ⟹ CarryLeaf ⟹ SurvivorLeaf`.
Open. -/
theorem survivorLeaf_of_struct (b : ℕ) (hb : 3 ≤ b) (h : TauMomentPrimesShiftStruct b) :
    SurvivorLeaf b := by
  sorry

/-- **The one open obligation on the headline path.**  A SINGLE shifted-divisor estimate along
the primes of one arithmetic progression: Brun–Titchmarsh applied to
`SwingC2Moment.tau_shift_sum_le`, plus a Linnik-type lower bound so that `P` is non-empty.
Everything else on the path — the series, the simultaneity over shifts, the union bound, the
full-progression first moment (`card_large_tau_le`) — is proved. -/
theorem shiftedDivisorIncidence_holds (b : ℕ) (hb : 3 ≤ b) : ShiftedDivisorIncidence b := by
  sorry

theorem tauMomentPrimesShift_holds (b : ℕ) (hb : 3 ≤ b) : TauMomentPrimesShift b :=
  tauMomentPrimesShift_of_incidence b hb (shiftedDivisorIncidence_holds b hb)

theorem tauMomentPrimes_holds (b : ℕ) (hb : 3 ≤ b) : TauMomentPrimes b :=
  tauMomentPrimes_of_shift b hb (tauMomentPrimesShift_holds b hb)

theorem carryLeaf_holds (b : ℕ) (hb : 3 ≤ b) : CarryLeaf b :=
  carryLeaf_of_tauMomentPrimes b hb (tauMomentPrimes_holds b hb)

theorem survivorLeaf_holds (b : ℕ) (hb : 3 ≤ b) : SurvivorLeaf b :=
  survivorLeaf_of_carryLeaf b hb (carryLeaf_holds b hb)

/-- **The even-base survivor, off the headline path.**  `ConstructionInputs` in its unrestricted
form asks for ODD targets too, which for an even base forces the survivor entry `n+ℓ` to be a
perfect square (`ConstructionInputsB`'s docstring).  That needs the kill progression to be built
from primes `q` at which `ℓ−1−j` is a quadratic residue — available by quadratic reciprocity plus
Dirichlet, but a second layer that `ConjC2` does not require.  Disclosed open; the headline chain
goes through `ConstructionInputsB`. -/
theorem constructionInputs_even (b : ℕ) (hb : 3 ≤ b) (heven : 2 ∣ b) : ConstructionInputs b := by
  sorry

theorem constructionInputs_hold (b : ℕ) (hb : 3 ≤ b) : ConstructionInputs b := by
  by_cases he : 2 ∣ b
  · exact constructionInputs_even b hb he
  · exact constructionInputs_of_survivorLeaf b hb he (survivorLeaf_holds b hb)

theorem subLeafA_holds (b : ℕ) (hb : 3 ≤ b) : SubLeafA b :=
  subLeafA_of_constructionInputsB b hb (constructionInputsB_of_survivorLeaf b hb
    (survivorLeaf_holds b hb))

/-- **THE CRUX.**  For `b ≥ 3`, the divisor-count windows realise every residue mod `b^ℓ`:
for every `ℓ ≥ 1` and every `t < b^ℓ` there is an `n` with

    Σ_{j<ℓ} τ(n+1+j)·b^{ℓ−1−j}  +  ⌊Σ_{k≥1} τ(n+ℓ+k)/b^k⌋  ≡  t   (mod b^ℓ).

By `conjC2_of_windowPrescribable` this is *equivalent* to `ConjC2` (the converse holds by
`floor_lambertVal_emod` read backwards), so it is the whole content of the swing, restated as a
statement about `τ` on intervals of length `ℓ` — no real analysis left.

Status 2026-09-24: **open.**  The `ω`-route (`G4SchedBAssembly.isDisjunctive_base`) proves the
corresponding statement for `ω` via the exact *additive* transport of `G4Transport`; `τ` has no
such identity (`tau_not_additive`, `tau_ne_weightN`).  Its replacement is the *multiplicative*
transport `tau_transport_frozen`, which is exact only on a progression freezing the valuations at
the primes of the dilation `D` — a congruence modulo `rad(D)^T`, not `rad D`.  The next attack is
to rebuild the G4 frame over that finer modulus and check whether the `Σ_p p^{−T}` exceptional
density is affordable in the §4D remainder budget. -/
theorem tau_windowPrescribable (b : ℕ) (hb : 3 ≤ b) : WindowPrescribable b tau :=
  windowPrescribable_of_subLeafA b hb (subLeafA_holds b hb)

/-- Helper for the base-3 anchors: the carry at `n+6` is below `3^5 = 243` whenever
`2√(n+6)+2 < 243`, i.e. for every `n ≤ 14634`. -/
theorem padOK (N : ℕ) (h : 2 * Nat.sqrt N + 2 < 243 := by native_decide) :
    carry 3 tau N < (3 : ℤ) ^ 5 := by
  refine lt_of_le_of_lt (carry_le_sqrt 3 (by norm_num) N) ?_
  have h' : ((2 * Nat.sqrt N + 2 : ℕ) : ℤ) < ((243 : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at h'
  norm_num
  linarith

/-! ### 5. Non-vacuity anchors for `SubLeafA` (base 3, `ℓ ≤ 2`) -/

/-- `SubLeafA 3` at `ℓ = 1`: every base-3 digit is realised by a padded divisor window
(`K = 5`; witnesses found by `probes/swingc2_window.py`). -/
theorem subLeafA_three_one (t : ℕ) (ht : t < 3) : ∃ n K : ℕ,
    carry 3 tau (n + (1 + K)) < (3 : ℤ) ^ K ∧
    paddedSum 3 tau n (1 + K) % (3 : ℤ) ^ (1 + K) = (t : ℤ) * (3 : ℤ) ^ K := by
  interval_cases t
  · exact ⟨1830, 5, padOK _, by native_decide⟩
  · exact ⟨1022, 5, padOK _, by native_decide⟩
  · exact ⟨1342, 5, padOK _, by native_decide⟩

/-- `SubLeafA 3` at `ℓ = 2`: all nine base-3 words of length two are realised (`K = 5`). -/
theorem subLeafA_three_two (t : ℕ) (ht : t < 9) : ∃ n K : ℕ,
    carry 3 tau (n + (2 + K)) < (3 : ℤ) ^ K ∧
    paddedSum 3 tau n (2 + K) % (3 : ℤ) ^ (2 + K) = (t : ℤ) * (3 : ℤ) ^ K := by
  interval_cases t
  · exact ⟨1829, 5, padOK _, by native_decide⟩
  · exact ⟨1021, 5, padOK _, by native_decide⟩
  · exact ⟨1341, 5, padOK _, by native_decide⟩
  · exact ⟨14405, 5, padOK _, by native_decide⟩
  · exact ⟨4322, 5, padOK _, by native_decide⟩
  · exact ⟨2709, 5, padOK _, by native_decide⟩
  · exact ⟨2501, 5, padOK _, by native_decide⟩
  · exact ⟨2637, 5, padOK _, by native_decide⟩
  · exact ⟨5236, 5, padOK _, by native_decide⟩

/-! ### 6. `SubLeafB` witnesses (base 3, `ℓ = 1`) -/

/-- `SubLeafB 3` witness at `ℓ = 1`, `t = 0` (`n = 2109`, `K = 5`): all six window entries are
`q^a·s` with `s` squarefree.  Found by `probes/swingc2_window.py`. -/
theorem subLeafB_three_one_0 : ∃ n K : ℕ, ∃ q a s : ℕ → ℕ,
    carry 3 tau (n + (1 + K)) < (3 : ℤ) ^ K ∧
    (∀ j < 1 + K, Structured (n + 1 + j) (q j) (a j) (s j)) ∧
    (∑ j ∈ range (1 + K),
        (((a j + 1) * 2 ^ ((s j).primeFactors.card) : ℕ) : ℤ) * (3 : ℤ) ^ (1 + K - 1 - j))
        % (3 : ℤ) ^ (1 + K) = (0 : ℤ) * (3 : ℤ) ^ K := by
  refine ⟨2109, 5, fun j => [3, 2, 2, 2, 3, 3].getD j 2, fun j => [0, 0, 6, 0, 0, 2].getD j 0,
    fun j => [2110, 2111, 33, 2113, 2114, 235].getD j 1, padOK _, ?_, by native_decide⟩
  intro j hj
  interval_cases j <;>
    exact ⟨by norm_num, by native_decide, by decide, by norm_num⟩

/-- `SubLeafB 3` witness at `ℓ = 1`, `t = 1` (`n = 1022`, `K = 5`): all six window entries are
`q^a·s` with `s` squarefree.  Found by `probes/swingc2_window.py`. -/
theorem subLeafB_three_one_1 : ∃ n K : ℕ, ∃ q a s : ℕ → ℕ,
    carry 3 tau (n + (1 + K)) < (3 : ℤ) ^ K ∧
    (∀ j < 1 + K, Structured (n + 1 + j) (q j) (a j) (s j)) ∧
    (∑ j ∈ range (1 + K),
        (((a j + 1) * 2 ^ ((s j).primeFactors.card) : ℕ) : ℤ) * (3 : ℤ) ^ (1 + K - 1 - j))
        % (3 : ℤ) ^ (1 + K) = (1 : ℤ) * (3 : ℤ) ^ K := by
  refine ⟨1022, 5, fun j => [2, 2, 5, 3, 2, 2].getD j 2, fun j => [0, 10, 2, 3, 0, 2].getD j 0,
    fun j => [1023, 1, 41, 38, 1027, 257].getD j 1, padOK _, ?_, by native_decide⟩
  intro j hj
  interval_cases j <;>
    exact ⟨by norm_num, by native_decide, by decide, by norm_num⟩

/-- `SubLeafB 3` witness at `ℓ = 1`, `t = 2` (`n = 1342`, `K = 5`): all six window entries are
`q^a·s` with `s` squarefree.  Found by `probes/swingc2_window.py`. -/
theorem subLeafB_three_one_2 : ∃ n K : ℕ, ∃ q a s : ℕ → ℕ,
    carry 3 tau (n + (1 + K)) < (3 : ℤ) ^ K ∧
    (∀ j < 1 + K, Structured (n + 1 + j) (q j) (a j) (s j)) ∧
    (∑ j ∈ range (1 + K),
        (((a j + 1) * 2 ^ ((s j).primeFactors.card) : ℕ) : ℤ) * (3 : ℤ) ^ (1 + K - 1 - j))
        % (3 : ℤ) ^ (1 + K) = (2 : ℤ) * (3 : ℤ) ^ K := by
  refine ⟨1342, 5, fun j => [2, 2, 2, 3, 2, 2].getD j 2, fun j => [0, 6, 0, 0, 0, 2].getD j 0,
    fun j => [1343, 21, 1345, 1346, 1347, 337].getD j 1, padOK _, ?_, by native_decide⟩
  intro j hj
  interval_cases j <;>
    exact ⟨by norm_num, by native_decide, by decide, by norm_num⟩

end NormalNumbers.SwingC2

namespace NormalNumbers.CastingOut

theorem conjC2 : ConjC2 :=
  NormalNumbers.SwingC2.conjC2_of_windowPrescribable
    NormalNumbers.SwingC2.tau_windowPrescribable

end NormalNumbers.CastingOut
