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

/-! ### 4. The crux leaf -/

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
theorem tau_windowPrescribable (b : ℕ) (hb : 3 ≤ b) : WindowPrescribable b tau := by
  sorry

end NormalNumbers.SwingC2

namespace NormalNumbers.CastingOut

theorem conjC2 : ConjC2 :=
  NormalNumbers.SwingC2.conjC2_of_windowPrescribable
    NormalNumbers.SwingC2.tau_windowPrescribable

end NormalNumbers.CastingOut
