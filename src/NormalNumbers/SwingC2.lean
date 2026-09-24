/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CastingOut
import NormalNumbers.G4WeightInterface

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

/-- **The padding reduction.**  Sub-leaf A implies the crux. -/
theorem windowPrescribable_of_subLeafA (b : ℕ) (hb : 3 ≤ b) (h : SubLeafA b) :
    WindowPrescribable b tau := by
  have hb2 : 2 ≤ b := by omega
  have hbpos : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (show 0 < b by omega)
  intro ℓ hℓ t ht0 htlt
  lift t to ℕ using ht0 with t₀
  have ht₀ : t₀ < b ^ ℓ := by exact_mod_cast htlt
  obtain ⟨n, K, hK, hP⟩ := h ℓ hℓ t₀ ht₀
  set L := ℓ + K with hL
  set x : ℝ := lambertVal b tau with hx
  have hbK : (0 : ℤ) < (b : ℤ) ^ K := by positivity
  have hbL : (0 : ℤ) < (b : ℤ) ^ L := by positivity
  -- the carry at the right end of the padded window
  set C : ℤ := carry b tau (n + L) with hC
  have hC0 : 0 ≤ C := carry_nonneg b hb2 tau tau_le_self _
  have hCK : C < (b : ℤ) ^ K := hK
  -- the padded window value
  have hV : ⌊x * (b : ℝ) ^ (n + L)⌋ % (b : ℤ) ^ L = (t₀ : ℤ) * (b : ℤ) ^ K + C := by
    rw [floor_lambertVal_emod b hb2 tau tau_le_self n L, windowNum_eq]
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
        = ((paddedSum b tau n L % (b : ℤ) ^ L) + C) % (b : ℤ) ^ L := by
          exact (Int.emod_add_emod _ _ _).symm
      _ = ((t₀ : ℤ) * (b : ℤ) ^ K + C) % (b : ℤ) ^ L := by rw [hP]
      _ = (t₀ : ℤ) * (b : ℤ) ^ K + C := Int.emod_eq_of_lt hsmall.1 hsmall.2
  -- read off the top `ℓ` digits
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

/-! ### 4. The crux leaf -/

/-- **THE CRUX (2026-09-24, after the structured reduction).**  The single open obligation behind
`ConjC2`.  Every divisor count in the window has been replaced by `(a_j+1)·2^{ω(s_j)}`, so the
statement lives entirely in the ADDITIVE category: one must prescribe, modulo `b^{ℓ+K}`, a
weighted sum of `2^{ω(s_j)}` over `L = ℓ+K` consecutive integers whose non-squarefree parts are
single prime powers `q_j^{a_j}` fixed by CRT.

Status: **open**.  Empirically true and comfortably so (`probes/swingc2_window.py`; the anchors
`subLeafA_three_one`, `subLeafA_three_two` verify `SubLeafA 3` for `ℓ ≤ 2` in the kernel).
The `(a_j+1)` factors supply the residues outside `⟨2⟩ ≤ (ℤ/b^L)^×`; the `ω(s_j)` supply the rest,
and `e(ω(·)/q)` IS multiplicative, so Selberg–Delange / the G4 Fourier control applies to it. -/
theorem subLeafB_holds (b : ℕ) (hb : 3 ≤ b) : SubLeafB b := by
  sorry

/-- **THE CRUX, after the 2026-09-24 padding reduction.**  `SubLeafA b` is the only open
obligation behind `ConjC2`.  It is a pure statement about the divisor function on a short
interval in residue classes modulo powers of `b`; `windowPrescribable_of_subLeafA` shows it
suffices, and `floor_lambertVal_emod` read backwards shows it is essentially necessary.

Status 2026-09-24: **open**.  The attack is `tau_transport_frozen`: on a progression freezing the
valuations at the primes of a dilation `D`, `τ(D·m)` is a fixed rational multiple of `τ(m)`, so
the G4 frame's translation action is replaced by multiplication by `τ(D)` on `ℤ/b^{ℓ+K}`. -/
theorem subLeafA_holds (b : ℕ) (hb : 3 ≤ b) : SubLeafA b :=
  subLeafA_of_subLeafB b (subLeafB_holds b hb)

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
