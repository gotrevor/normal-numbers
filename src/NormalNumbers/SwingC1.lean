import NormalNumbers.CastingOut

/-!
# Swing at C1 (natural density)

`ConjC1` (frozen in `CastingOut.lean`): for `b ≥ 3` and every `L`, the length-`L` window digit
sums of `G4_b` mod `b − 1` follow `normalCastLaw`.  Expected to be Elliott-hard.  The swing
succeeds if it isolates the EXACT arithmetic input as a named hypothesis `H` and proves
`conjC1_of_H : H → ConjC1`, or if it refutes a candidate `H`.

## This file: the exact digit-free reduction

`windowDigitSum_lambert_modEq` says the window digit sum of `G4_b = Σ ω(m) b^{-m}` is
`Σ_{m ∈ (n, n+L]} ω(m) + c_{n+L} − c_n` modulo `b − 1`, where `c_N = ⌊Σ_{k≥1} ω(N+k) b^{−k}⌋`.
We package that combination as `castState b L n : ZMod (b − 1)` and prove

* `castFreq_eq_stateFreq` — the two counting functions are **equal**, not merely asymptotic;
* `conjC1_iff_stateLaw` — `ConjC1 ↔ HState`.

So `ConjC1` contains no digit, no floor of `b^N x` and no real number any more: it is exactly a
density statement about `ω` and its own carry sequence.  Everything downstream attacks `HState`.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- `ω(m)`, the number of distinct prime factors, as a `ℕ`-valued weight. -/
def omegaNat (m : ℕ) : ℕ := m.primeFactors.card

lemma omegaNat_le (m : ℕ) : omegaNat m ≤ m := card_primeFactors_le_self m

lemma primeLambertAtBase_eq_lambertVal_omegaNat (b : ℕ) :
    primeLambertAtBase b = lambertVal b omegaNat :=
  primeLambertAtBase_eq_lambertVal b

/-- The `b`-adic tail of `G4_b` at `N`: `Σ_{k ≥ 1} ω(N+k) b^{−k}`. -/
noncomputable def omegaTail (b N : ℕ) : ℝ :=
  ∑' k : ℕ, (omegaNat (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)

/-- The carry sequence of `G4_b`: `c_N = ⌊Σ_{k ≥ 1} ω(N+k) b^{−k}⌋`. -/
noncomputable def omegaCarry (b N : ℕ) : ℤ := carry b omegaNat N

lemma omegaCarry_eq_floor (b N : ℕ) : omegaCarry b N = ⌊omegaTail b N⌋ := rfl

lemma omegaTail_term (b : ℕ) (hb : 2 ≤ b) (N k : ℕ) :
    (omegaNat (k + (N + 1)) : ℝ) / (b : ℝ) ^ (k + (N + 1)) * (b : ℝ) ^ N
      = (omegaNat (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1) := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hbn : ((b : ℝ) ^ N) ≠ 0 := pow_ne_zero _ (ne_of_gt hb0)
  rw [show k + (N + 1) = N + 1 + k by omega, show N + 1 + k = N + (k + 1) by omega, pow_add,
    div_mul_eq_mul_div, mul_comm ((omegaNat (N + (k + 1)) : ℝ)) ((b : ℝ) ^ N),
    mul_div_mul_left _ _ hbn]

set_option maxHeartbeats 1000000 in
lemma summable_omegaTail (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    Summable (fun k : ℕ => (omegaNat (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)) := by
  have hs := summable_lambert b hb omegaNat omegaNat_le
  have hshift : Summable (fun k : ℕ => (omegaNat (k + (N + 1)) : ℝ) / (b : ℝ) ^ (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr hs
  exact (hshift.mul_right ((b : ℝ) ^ N)).congr (omegaTail_term b hb N)

/-- `b · tail_N = ω(N+1) + tail_{N+1}`: the shift identity behind the carry recursion. -/
lemma omegaTail_rec (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    (b : ℝ) * omegaTail b N = (omegaNat (N + 1) : ℝ) + omegaTail b (N + 1) := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb0
  have hs := summable_omegaTail b hb N
  rw [omegaTail, ← hs.tsum_mul_left, (hs.mul_left (b : ℝ)).tsum_eq_zero_add]
  congr 1
  · rw [pow_one, Nat.add_zero, mul_div_cancel₀ _ hbne]
  · rw [omegaTail]
    refine tsum_congr fun k => ?_
    rw [show N + 1 + (k + 1) = N + 1 + 1 + k by omega, show k + 1 + 1 = (k + 1) + 1 by omega,
      pow_succ]
    field_simp

/-- **Exact carry recursion.**  `ω(N+1) + c_{N+1} = b·c_N + d_N`, where `d_N ∈ [0, b)` is the
`N`-th base-`b` digit of `G4_b`.  Equivalently `c_N = ⌊(ω(N+1) + c_{N+1}) / b⌋`: the digit
sequence of `G4_b` is produced from the `ω` sequence by ordinary right-to-left carrying.  This is
the structural fact that makes `castState` a function of the `ω` process alone. -/
theorem omegaCarry_rec (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    omegaCarry b N = ((omegaNat (N + 1) : ℤ) + omegaCarry b (N + 1)) / (b : ℤ) := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hbz : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (by omega : 0 < b)
  have hfl : ⌊(b : ℝ) * omegaTail b N⌋ = (omegaNat (N + 1) : ℤ) + omegaCarry b (N + 1) := by
    rw [omegaTail_rec b hb N, omegaCarry_eq_floor]
    rw [show ((omegaNat (N + 1) : ℝ)) = (((omegaNat (N + 1) : ℤ)) : ℝ) by push_cast; ring,
      Int.floor_intCast_add]
  rw [← hfl, omegaCarry_eq_floor]
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb0
  have := Int.floor_div_natCast ((b : ℝ) * omegaTail b N) b
  rw [mul_comm, mul_div_assoc, div_self hbne, mul_one] at this
  rw [this, mul_comm]

/-- The `ZMod (b−1)`-valued statistic that the length-`L` window digit sum of `G4_b` equals:
`Σ_{m ∈ (n, n+L]} ω(m) + c_{n+L} − c_n`. -/
noncomputable def castState (b L n : ℕ) : ZMod (b - 1) :=
  ((∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ)) + omegaCarry b (n + L) - omegaCarry b n : ℤ)

/-- Frequency of `n < N` with `castState b L n = r`. -/
noncomputable def stateFreq (b L : ℕ) (r : ZMod (b - 1)) (N : ℕ) : ℝ :=
  (((range N).filter (fun n => castState b L n = r)).card : ℝ) / N

lemma sum_Ioc_omegaNat (n L : ℕ) :
    ∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ)
      = ∑ i ∈ range L, (omegaNat (n + 1 + i) : ℤ) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [show n + (L + 1) = (n + L) + 1 by omega, Finset.sum_Ioc_succ_top (by omega), ih,
        Finset.sum_range_succ]
      ring_nf

/-- The `ω`-head of the length-`L` window at `n`: `Σ_{i<L} ω(n+1+i) b^{L-1-i}`. -/
def omegaHead (b L n : ℕ) : ℤ :=
  ∑ i ∈ range L, (omegaNat (n + 1 + i) : ℤ) * (b : ℤ) ^ (L - 1 - i)

lemma omegaHead_succ (b L n : ℕ) :
    omegaHead b (L + 1) n = (b : ℤ) * omegaHead b L n + (omegaNat (n + 1 + L) : ℤ) := by
  rw [omegaHead, omegaHead, Finset.sum_range_succ, Finset.mul_sum]
  have hcongr : ∀ i ∈ range L, (b : ℤ) * ((omegaNat (n + 1 + i) : ℤ) * (b : ℤ) ^ (L - 1 - i))
      = (omegaNat (n + 1 + i) : ℤ) * (b : ℤ) ^ (L + 1 - 1 - i) := by
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    rw [show L + 1 - 1 - i = (L - 1 - i) + 1 by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl hcongr]
  simp

/-- `Σ_{m ∈ (n, n+L]} ω(m)·b^{n+L−m} = omegaHead b L n`. -/
lemma sum_Ioc_omegaNat_pow (b n L : ℕ) :
    ∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ) * (b : ℤ) ^ (n + L - m) = omegaHead b L n := by
  induction L with
  | zero => simp [omegaHead]
  | succ L ih =>
      rw [show n + (L + 1) = (n + L) + 1 by omega, Finset.sum_Ioc_succ_top (by omega),
        omegaHead_succ]
      rw [← ih, Finset.mul_sum]
      rw [show n + L + 1 - (n + L + 1) = 0 by omega, pow_zero, mul_one]
      congr 1
      · refine Finset.sum_congr rfl fun m hm => ?_
        have hm' := Finset.mem_Ioc.mp hm
        rw [show n + L + 1 - m = (n + L - m) + 1 by omega, pow_succ]
        ring
      · rw [show n + L + 1 = n + 1 + L by omega]

/-- The integer the length-`L` window of `G4_b` at `n` reads off, before reduction mod `b^L`:
`Σ_{i<L} ω(n+1+i) b^{L-1-i} + c_{n+L}`.  By `omegaCarry_eq_windowVal_div` its quotient by `b^L`
is `c_n`, so its residue mod `b^L` is exactly the window word. -/
noncomputable def omegaWindowVal (b L n : ℕ) : ℤ := omegaHead b L n + omegaCarry b (n + L)

/-- `b^L · tail_n = head + tail_{n+L}`: the `L`-step form of `omegaTail_rec`. -/
lemma omegaTail_pow (b : ℕ) (hb : 2 ≤ b) (L n : ℕ) :
    (b : ℝ) ^ L * omegaTail b n = ((omegaHead b L n : ℤ) : ℝ) + omegaTail b (n + L) := by
  induction L with
  | zero => simp [omegaHead]
  | succ L ih =>
      have hstep := omegaTail_rec b hb (n + L)
      have : (b : ℝ) ^ (L + 1) * omegaTail b n = (b : ℝ) * ((b : ℝ) ^ L * omegaTail b n) := by
        rw [pow_succ]; ring
      rw [this, ih, mul_add, hstep]
      have hhead : ((omegaHead b (L + 1) n : ℤ) : ℝ)
          = (b : ℝ) * ((omegaHead b L n : ℤ) : ℝ) + (omegaNat (n + 1 + L) : ℝ) := by
        rw [omegaHead_succ]; push_cast; ring
      rw [hhead, show n + (L + 1) = n + L + 1 by omega]
      ring

lemma omegaWindowVal_eq_floor (b : ℕ) (hb : 2 ≤ b) (L n : ℕ) :
    omegaWindowVal b L n = ⌊(b : ℝ) ^ L * omegaTail b n⌋ := by
  rw [omegaWindowVal, omegaTail_pow b hb L n, Int.floor_intCast_add, omegaCarry_eq_floor]

/-- **The carry is the quotient.**  `c_n = ⌊(Σ_{i<L} ω(n+1+i) b^{L-1-i} + c_{n+L}) / b^L⌋`;
for `L = 1` this is `omegaCarry_rec`. -/
theorem omegaCarry_eq_windowVal_div (b : ℕ) (hb : 2 ≤ b) (L n : ℕ) :
    omegaCarry b n = omegaWindowVal b L n / (b : ℤ) ^ L := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hbne : ((b : ℝ) ^ L) ≠ 0 := by positivity
  have h := Int.floor_div_natCast ((b : ℝ) ^ L * omegaTail b n) (b ^ L)
  push_cast at h
  rw [mul_comm ((b : ℝ) ^ L) (omegaTail b n), mul_div_assoc, div_self hbne, mul_one] at h
  rw [omegaWindowVal_eq_floor b hb L n, mul_comm ((b : ℝ) ^ L) (omegaTail b n)]
  exact h

/-- **The window word is an `ω`-object.**  `castState b L n` is the residue mod `b − 1` of
`omegaWindowVal b L n mod b^L` — a bounded function of `ω(n+1), …, ω(n+L)` and `c_{n+L} mod b^L`.
(The unbounded part of the carry cancels: `b^L ≡ 1 mod b−1`.) -/
theorem castState_eq_windowVal_emod (b : ℕ) (hb : 2 ≤ b) (L n : ℕ) :
    castState b L n = ((omegaWindowVal b L n % (b : ℤ) ^ L : ℤ) : ZMod (b - 1)) := by
  have hcast : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
    have : 1 ≤ b := by omega
    push_cast [Nat.cast_sub this]; ring
  have hq : ∀ j : ℕ, ((b : ℤ) - 1) ∣ ((b : ℤ) ^ j - 1) := fun j => by
    simpa using sub_dvd_pow_sub_pow (b : ℤ) 1 j
  set S : ℤ := ∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ) with hS
  set c : ℤ := omegaCarry b n with hc
  -- the window residue, written out
  have hV : omegaWindowVal b L n % (b : ℤ) ^ L
      = omegaHead b L n + omegaCarry b (n + L) - (b : ℤ) ^ L * c := by
    rw [Int.emod_def, ← omegaCarry_eq_windowVal_div b hb L n, omegaWindowVal, hc]
  -- head ≡ plain ω-sum
  have hre : S = ∑ i ∈ range L, (omegaNat (n + 1 + i) : ℤ) := by
    rw [hS]; exact sum_Ioc_omegaNat n L
  obtain ⟨u, hu⟩ : ((b : ℤ) - 1) ∣ (S - omegaHead b L n) := by
    rw [hre, omegaHead, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    obtain ⟨w, hw⟩ := hq (L - 1 - i)
    exact ⟨-(omegaNat (n + 1 + i) : ℤ) * w, by
      rw [show (omegaNat (n + 1 + i) : ℤ) - (omegaNat (n + 1 + i) : ℤ) * (b : ℤ) ^ (L - 1 - i)
        = -((omegaNat (n + 1 + i) : ℤ) * ((b : ℤ) ^ (L - 1 - i) - 1)) by ring, hw]; ring⟩
  obtain ⟨w, hw⟩ := hq L
  have hmain : S + omegaCarry b (n + L) - c
      ≡ omegaWindowVal b L n % (b : ℤ) ^ L [ZMOD ((b : ℤ) - 1)] := by
    refine Int.modEq_iff_dvd.mpr ⟨-u - c * w, ?_⟩
    rw [hV, mul_sub, mul_neg, ← hu]
    have : (b : ℤ) ^ L = ((b : ℤ) - 1) * w + 1 := by linarith
    rw [this]; ring
  have hZ : ((S + omegaCarry b (n + L) - c : ℤ) : ZMod (b - 1))
      = ((omegaWindowVal b L n % (b : ℤ) ^ L : ℤ) : ZMod (b - 1)) :=
    (ZMod.intCast_eq_intCast_iff _ _ (b - 1)).mpr (by rw [hcast]; exact hmain)
  rw [hS, hc] at hZ
  simpa [castState, omegaCarry] using hZ

/-- The window digit sum of `G4_b`, pushed into `ZMod (b−1)`, **is** `castState`. -/
theorem windowDigitSum_cast_eq_castState (b : ℕ) (hb : 2 ≤ b) (L n : ℕ) :
    ((windowDigitSum b (primeLambertAtBase b) n L : ℕ) : ZMod (b - 1)) = castState b L n := by
  have hmod := windowDigitSum_lambert_modEq b hb omegaNat omegaNat_le n L
  rw [← primeLambertAtBase_eq_lambertVal_omegaNat b] at hmod
  have hcast : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
    have : 1 ≤ b := by omega
    push_cast [Nat.cast_sub this]; ring
  have key : (((windowDigitSum b (primeLambertAtBase b) n L : ℕ) : ℤ) : ZMod (b - 1))
      = (((∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ))
          + carry b omegaNat (n + L) - carry b omegaNat n : ℤ) : ZMod (b - 1)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (by rw [hcast]; exact hmod)
  simpa [castState, omegaCarry] using key

/-- **Exact rewrite of the counting function.**  No limits are taken: for every `N` the C1
frequency and the `ω`-side frequency coincide on the nose. -/
theorem castFreq_eq_stateFreq (b : ℕ) (hb : 2 ≤ b) (L r N : ℕ) (hr : r < b - 1) :
    castFreq b (primeLambertAtBase b) L r N = stateFreq b L ((r : ℕ) : ZMod (b - 1)) N := by
  classical
  have hp : ((range N).filter
        (fun n => windowDigitSum b (primeLambertAtBase b) n L % (b - 1) = r))
      = ((range N).filter (fun n => castState b L n = ((r : ℕ) : ZMod (b - 1)))) := by
    refine Finset.filter_congr fun n _ => ?_
    rw [← windowDigitSum_cast_eq_castState b hb L n,
      ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]
  unfold castFreq stateFreq
  rw [hp]

/-- The `ω`-side form of `CastLaw` at window length `L`. -/
def StateLaw (b L : ℕ) : Prop :=
  ∀ r < b - 1, Tendsto (stateFreq b L ((r : ℕ) : ZMod (b - 1))) atTop (𝓝 (normalCastLaw b L r))

/-- **H (digit-free form of C1).**  For every base `b ≥ 3` and every window length `L`, the
`ZMod (b−1)`-valued statistic `Σ_{m ∈ (n,n+L]} ω(m) + c_{n+L} − c_n` has, in natural density, the
law of a sum of `L` independent uniform base-`b` digits reduced mod `b − 1`. -/
def HState : Prop := ∀ b, 3 ≤ b → ∀ L, StateLaw b L

theorem castLaw_iff_stateLaw (b : ℕ) (hb : 2 ≤ b) (L : ℕ) :
    CastLaw b (primeLambertAtBase b) L ↔ StateLaw b L := by
  constructor
  · intro h r hr
    have := h r hr
    simpa only [funext fun N => castFreq_eq_stateFreq b hb L r N hr] using this
  · intro h r hr
    have := h r hr
    simpa only [funext fun N => castFreq_eq_stateFreq b hb L r N hr] using this

/-- **The exact reduction.**  `ConjC1` and `HState` are the same statement. -/
theorem conjC1_iff_hState : ConjC1 ↔ HState := by
  constructor
  · intro h b hb L
    exact (castLaw_iff_stateLaw b (by omega) L).mp (h b hb L)
  · intro h b hb L
    exact (castLaw_iff_stateLaw b (by omega) L).mpr (h b hb L)

theorem conjC1_of_hState : HState → ConjC1 := conjC1_iff_hState.mpr

/-! ### The finite count: `normalCastLaw` is the residue count in `[0, b^L)` -/

lemma filter_mod_range_mul (q m r : ℕ) (hq : 0 < q) (hr : r < q) :
    (range (q * m)).filter (fun v => v % q = r) = (range m).image (fun a => q * a + r) := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hv, hmod⟩
    refine ⟨v / q, ?_, ?_⟩
    · exact Nat.div_lt_of_lt_mul (by omega)
    · have hd := Nat.div_add_mod v q
      omega
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, by simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]⟩
    have : q * a + q ≤ q * m := by
      have : a + 1 ≤ m := ha
      calc q * a + q = q * (a + 1) := by ring
        _ ≤ q * m := Nat.mul_le_mul_left q this
    omega

lemma card_filter_mod_range_mul (q m r : ℕ) (hq : 0 < q) (hr : r < q) :
    ((range (q * m)).filter (fun v => v % q = r)).card = m := by
  rw [filter_mod_range_mul q m r hq hr, Finset.card_image_of_injective _ (by
    intro a₁ a₂ h; simp only at h
    exact Nat.eq_of_mul_eq_mul_left hq (by omega)), Finset.card_range]

/-- `#{v < q·m + 1 : v ≡ r mod q} = m + [r = 0]`. -/
lemma card_filter_mod_range_mul_succ (q m r : ℕ) (hq : 0 < q) (hr : r < q) :
    ((range (q * m + 1)).filter (fun v => v % q = r)).card = m + (if r = 0 then 1 else 0) := by
  classical
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : q * m % q = r
  · have hr0 : r = 0 := by
      rw [Nat.mul_mod_right] at h; omega
    rw [if_pos h, Finset.card_insert_of_notMem (by simp), card_filter_mod_range_mul q m r hq hr,
      if_pos hr0]
  · have hr0 : r ≠ 0 := by
      intro h0; exact h (by rw [Nat.mul_mod_right, h0])
    rw [if_neg h, card_filter_mod_range_mul q m r hq hr, if_neg hr0]
    omega

/-- **`normalCastLaw` is a residue count.**  The law of the digit sum of `L` iid uniform base-`b`
digits mod `b−1` is just the proportion of `v ∈ [0, b^L)` with `v ≡ r (mod b−1)` — casting out
nines turns the word count into an interval count. -/
theorem normalCastLaw_eq_residue_count (b L r : ℕ) (hb : 3 ≤ b) (hr : r < b - 1) :
    normalCastLaw b L r
      = ((((range (b ^ L)).filter (fun v => v % (b - 1) = r)).card : ℝ)) / (b : ℝ) ^ L := by
  classical
  obtain ⟨q, rfl⟩ : ∃ q, b = q + 1 := ⟨b - 1, by omega⟩
  have hq : 0 < q := by omega
  have hqr : q + 1 - 1 = q := by omega
  rw [hqr] at hr ⊢
  -- `q ∣ (q+1)^L − 1`
  obtain ⟨m, hm⟩ : ∃ m, (q + 1) ^ L = q * m + 1 := by
    induction L with
    | zero => exact ⟨0, by simp⟩
    | succ L ih =>
        obtain ⟨m, hm⟩ := ih
        exact ⟨q * m + m + 1, by rw [pow_succ, hm]; ring⟩
  rw [hm, card_filter_mod_range_mul_succ q m r hq hr]
  rw [normalCastLaw_closed (q + 1) L r hb hr]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow : ((q : ℝ) + 1) ^ L = q * m + 1 := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hm
    push_cast at this
    linarith
  have hpos : (0 : ℝ) < ((q : ℝ) + 1) ^ L := by positivity
  push_cast
  rw [hpow]
  by_cases h : r = 0 <;> simp [h] <;> field_simp <;> ring

/-! ### Numerical anchors for the model side

`normalCastLaw_eq_residue_count` says the length-`L` digit-sum law mod `b−1` equals the count of
residues in `[0, b^L)`.  These are the two sides evaluated independently by the kernel. -/

example : ((Finset.range (3 ^ 1)).filter (fun v => v % 2 = 0)).card
    = (Finset.univ.filter (fun v : Fin 1 → Fin 3 => (∑ i, (v i : ℕ)) % 2 = 0)).card := by decide

example : ((Finset.range (3 ^ 3)).filter (fun v => v % 2 = 1)).card
    = (Finset.univ.filter (fun v : Fin 3 → Fin 3 => (∑ i, (v i : ℕ)) % 2 = 1)).card := by decide

example : ((Finset.range (4 ^ 2)).filter (fun v => v % 3 = 2)).card
    = (Finset.univ.filter (fun v : Fin 2 → Fin 4 => (∑ i, (v i : ℕ)) % 3 = 2)).card := by decide

example : ((Finset.range (5 ^ 2)).filter (fun v => v % 4 = 0)).card
    = (Finset.univ.filter (fun v : Fin 2 → Fin 5 => (∑ i, (v i : ℕ)) % 4 = 0)).card := by decide

/-- The bias is real: at `b = 3, L = 3` the residue `0` is hit 14 times out of 27 and the residue
`1` only 13 — `normalCastLaw` is NOT uniform, which is why `CastUniform` was the wrong target. -/
example : ((Finset.range (3 ^ 3)).filter (fun v => v % 2 = 0)).card = 14 := by decide

example : ((Finset.range (3 ^ 3)).filter (fun v => v % 2 = 1)).card = 13 := by decide

/-! ### The window residue and the equidistribution hypothesis -/

/-- The window word of `G4_b` at `n`, as a natural number in `[0, b^L)`. -/
noncomputable def windowResidue (b L n : ℕ) : ℕ := (omegaWindowVal b L n % (b : ℤ) ^ L).toNat

lemma windowResidue_lt (b : ℕ) (hb : 2 ≤ b) (L n : ℕ) : windowResidue b L n < b ^ L := by
  have hp : (0 : ℤ) < (b : ℤ) ^ L := by positivity
  have h := Int.emod_lt_of_pos (omegaWindowVal b L n) hp
  have h0 := Int.emod_nonneg (omegaWindowVal b L n) (ne_of_gt hp)
  have : ((windowResidue b L n : ℕ) : ℤ) = omegaWindowVal b L n % (b : ℤ) ^ L :=
    Int.toNat_of_nonneg h0
  have hlt : ((windowResidue b L n : ℕ) : ℤ) < ((b ^ L : ℕ) : ℤ) := by push_cast; omega
  exact_mod_cast hlt

lemma castState_eq_windowResidue (b : ℕ) (hb : 2 ≤ b) (L n : ℕ) :
    castState b L n = ((windowResidue b L n : ℕ) : ZMod (b - 1)) := by
  have hp : (0 : ℤ) < (b : ℤ) ^ L := by positivity
  have h0 := Int.emod_nonneg (omegaWindowVal b L n) (ne_of_gt hp)
  have he : ((omegaWindowVal b L n % (b : ℤ) ^ L).toNat : ℤ)
      = omegaWindowVal b L n % (b : ℤ) ^ L := Int.toNat_of_nonneg h0
  rw [castState_eq_windowVal_emod b hb L n]
  conv_lhs => rw [← he]
  rw [windowResidue]
  norm_cast

/-- **H (equidistribution of the window word).**  The `ω`-side window value
`Σ_{i<L} ω(n+1+i) b^{L-1-i} + c_{n+L}` is equidistributed modulo `b^L`. -/
def HWindow (b L : ℕ) : Prop :=
  ∀ v < b ^ L, Tendsto
    (fun N => (((range N).filter (fun n => windowResidue b L n = v)).card : ℝ) / N)
    atTop (𝓝 (((b : ℝ) ^ L)⁻¹))

/-- **The model lemma.**  Equidistribution of the window word mod `b^L` gives C1 at length `L`,
with no error term: casting out `b−1` turns the residue count into `normalCastLaw`. -/
theorem stateLaw_of_hWindow (b : ℕ) (hb : 3 ≤ b) (L : ℕ) (h : HWindow b L) : StateLaw b L := by
  classical
  intro r hr
  set t : Finset ℕ := (range (b ^ L)).filter (fun v => v % (b - 1) = r) with ht
  have hfib : ∀ N : ℕ,
      ((range N).filter (fun n => castState b L n = ((r : ℕ) : ZMod (b - 1)))).card
        = ∑ v ∈ t, ((range N).filter (fun n => windowResidue b L n = v)).card := by
    intro N
    have hset : (range N).filter (fun n => castState b L n = ((r : ℕ) : ZMod (b - 1)))
        = (range N).filter (fun n => windowResidue b L n % (b - 1) = r) := by
      refine Finset.filter_congr fun n _ => ?_
      rw [castState_eq_windowResidue b (by omega) L n, ZMod.natCast_eq_natCast_iff',
        Nat.mod_eq_of_lt hr]
    rw [hset, Finset.card_eq_sum_card_fiberwise (f := fun n => windowResidue b L n) (t := t) ?_]
    · refine Finset.sum_congr rfl fun v hv => ?_
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      have hvt := (Finset.mem_filter.mp (ht ▸ hv)).2
      constructor
      · rintro ⟨⟨hn, _⟩, hw⟩; exact ⟨hn, hw⟩
      · rintro ⟨hn, hw⟩; exact ⟨⟨hn, by rw [hw]; exact hvt⟩, hw⟩
    · intro n hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (windowResidue_lt b (by omega) L n), ?_⟩
      exact (Finset.mem_filter.mp hn).2
  have hsum : ∀ N : ℕ, stateFreq b L ((r : ℕ) : ZMod (b - 1)) N
      = ∑ v ∈ t, (((range N).filter (fun n => windowResidue b L n = v)).card : ℝ) / N := by
    intro N
    rw [stateFreq, hfib N]
    push_cast
    rw [Finset.sum_div]
  have hlim : Tendsto (fun N => ∑ v ∈ t,
      (((range N).filter (fun n => windowResidue b L n = v)).card : ℝ) / N) atTop
      (𝓝 (∑ _v ∈ t, ((b : ℝ) ^ L)⁻¹)) :=
    tendsto_finsetSum _ fun v hv => h v (Finset.mem_range.mp (Finset.mem_filter.mp (ht ▸ hv)).1)
  have hfun : (stateFreq b L ((r : ℕ) : ZMod (b - 1)))
      = fun N => ∑ v ∈ t, (((range N).filter (fun n => windowResidue b L n = v)).card : ℝ) / N :=
    funext hsum
  have hval : normalCastLaw b L r = ∑ _v ∈ t, ((b : ℝ) ^ L)⁻¹ := by
    rw [normalCastLaw_eq_residue_count b L r hb hr, ← ht, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hfun, hval]
  exact hlim

theorem hState_of_hWindow (h : ∀ b, 3 ≤ b → ∀ L, HWindow b L) : HState :=
  fun b hb L => stateLaw_of_hWindow b hb L (h b hb L)

/-! ### Truncating the carry to finite depth -/

lemma omegaTail_nonneg (b : ℕ) (hb : 2 ≤ b) (N : ℕ) : 0 ≤ omegaTail b N :=
  tsum_nonneg fun k => by positivity

lemma omegaCarry_nonneg (b : ℕ) (hb : 2 ≤ b) (N : ℕ) : 0 ≤ omegaCarry b N :=
  Int.floor_nonneg.mpr (omegaTail_nonneg b hb N)

lemma omegaNat_le_log (m : ℕ) (hm : m ≠ 0) : omegaNat m ≤ Nat.log 2 m := by
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  calc 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

/-- `Σ_{k≥0} (1/2)^{k+1} = 1`. -/
private lemma tsum_half_succ : ∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 1) = 1 := by
  have hgeo := tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)
  calc ∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 1)
      = ∑' k : ℕ, (1/2 : ℝ) * ((1 : ℝ) / 2) ^ k := tsum_congr fun k => by ring
    _ = (1/2 : ℝ) * ∑' k : ℕ, ((1 : ℝ) / 2) ^ k := tsum_mul_left
    _ = 1 := by rw [hgeo]; norm_num

/-- `Σ_{k≥0} k·(1/2)^{k+1} = 1`. -/
private lemma tsum_half_succ_mul : ∑' k : ℕ, (k : ℝ) * ((1 : ℝ) / 2) ^ (k + 1) = 1 := by
  have h := tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := (1:ℝ)/2)
    (by rw [Real.norm_eq_abs]; norm_num)
  calc ∑' k : ℕ, (k : ℝ) * ((1 : ℝ) / 2) ^ (k + 1)
      = ∑' k : ℕ, (1/2 : ℝ) * ((k : ℝ) * ((1 : ℝ) / 2) ^ k) := tsum_congr fun k => by ring
    _ = (1/2 : ℝ) * ∑' k : ℕ, (k : ℝ) * ((1 : ℝ) / 2) ^ k := tsum_mul_left
    _ = 1 := by rw [h]; norm_num

/-- **The carry is `O(log N)`.**  `Σ_{k≥1} ω(N+k) b^{−k} ≤ log₂(N+1) + 1`, from
`ω(m) ≤ log₂ m` and `N+1+k ≤ (N+1)·2^k`.  This pins the depth a truncation of the carry needs:
`b^K` must beat `log₂ N`, i.e. `K ≳ log_b log N`. -/
theorem omegaTail_le_log (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    omegaTail b N ≤ (Nat.log 2 (N + 1) : ℝ) + 1 := by
  set A := Nat.log 2 (N + 1) with hA
  have hterm : ∀ k : ℕ, (omegaNat (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)
      ≤ ((A : ℝ) + k) * ((1 : ℝ) / 2) ^ (k + 1) := by
    intro k
    have hne : N + 1 + k ≠ 0 := by omega
    have hlog : omegaNat (N + 1 + k) ≤ Nat.log 2 (N + 1 + k) :=
      omegaNat_le_log (N + 1 + k) hne
    have hk : k < 2 ^ k := Nat.lt_two_pow_self
    have ht : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h4 : N ≤ N * 2 ^ k := Nat.le_mul_of_pos_right N (by positivity)
    have h3 : N + 1 + k ≤ (N + 1) * 2 ^ k := by
      calc N + 1 + k = N + (k + 1) := by omega
        _ ≤ N * 2 ^ k + 2 ^ k := by omega
        _ = (N + 1) * 2 ^ k := by ring
    have h2 : N + 1 < 2 ^ (A + 1) := Nat.lt_pow_succ_log_self (by norm_num) (N + 1)
    have hlt : N + 1 + k < 2 ^ (A + k + 1) := by
      calc N + 1 + k ≤ (N + 1) * 2 ^ k := h3
        _ < 2 ^ (A + 1) * 2 ^ k := by
            exact (Nat.mul_lt_mul_right (by positivity)).mpr h2
        _ = 2 ^ (A + k + 1) := by rw [← pow_add]; congr 1; omega
    have hloglt : Nat.log 2 (N + 1 + k) < A + k + 1 := Nat.log_lt_of_lt_pow hne hlt
    have h1 : omegaNat (N + 1 + k) ≤ A + k := by omega
    have hnum : (omegaNat (N + 1 + k) : ℝ) ≤ (A : ℝ) + k := by exact_mod_cast h1
    have hden : (2 : ℝ) ^ (k + 1) ≤ (b : ℝ) ^ (k + 1) := by
      refine pow_le_pow_left₀ (by norm_num) ?_ _
      exact_mod_cast hb
    have hrhs : ((A : ℝ) + k) * ((1 : ℝ) / 2) ^ (k + 1) = ((A : ℝ) + k) / (2 : ℝ) ^ (k + 1) := by
      rw [div_pow, one_pow]; ring
    rw [hrhs]
    gcongr
  have hsum1 : Summable (fun k : ℕ => (A : ℝ) * ((1 : ℝ) / 2) ^ (k + 1)) := by
    refine Summable.mul_left _ ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1) |>.congr fun k => rfl
  have hsum2 : Summable (fun k : ℕ => (k : ℝ) * ((1 : ℝ) / 2) ^ (k + 1)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rw [Real.norm_eq_abs]; norm_num : ‖(1:ℝ)/2‖ < 1)
    have h2 := h.mul_left ((1:ℝ)/2)
    refine h2.congr fun k => ?_
    rw [pow_one]
    ring
  have hsumg : Summable (fun k : ℕ => ((A : ℝ) + k) * ((1 : ℝ) / 2) ^ (k + 1)) := by
    refine (hsum1.add hsum2).congr fun k => ?_
    ring
  have hle := Summable.tsum_le_tsum hterm (summable_omegaTail b hb N) hsumg
  refine hle.trans (le_of_eq ?_)
  have : ∑' k : ℕ, ((A : ℝ) + k) * ((1 : ℝ) / 2) ^ (k + 1)
      = (∑' k : ℕ, (A : ℝ) * ((1 : ℝ) / 2) ^ (k + 1))
        + ∑' k : ℕ, (k : ℝ) * ((1 : ℝ) / 2) ^ (k + 1) := by
    rw [← Summable.tsum_add hsum1 hsum2]
    exact tsum_congr fun k => by ring
  rw [this, tsum_mul_left, tsum_half_succ, tsum_half_succ_mul, mul_one]

/-- `c_N ≤ log₂(N+1) + 1`. -/
theorem omegaCarry_le_log (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    omegaCarry b N ≤ (Nat.log 2 (N + 1) : ℤ) + 1 := by
  rw [omegaCarry_eq_floor]
  have h1 : (⌊omegaTail b N⌋ : ℤ) ≤ ⌊((Nat.log 2 (N + 1) : ℝ) + 1)⌋ :=
    Int.floor_le_floor (omegaTail_le_log b hb N)
  refine h1.trans (le_of_eq ?_)
  rw [show ((Nat.log 2 (N + 1) : ℝ) + 1) = (((Nat.log 2 (N + 1) : ℤ) + 1 : ℤ) : ℝ) by push_cast; ring,
    Int.floor_intCast]

/-- **Carry truncation, exactly.**  `c_N` is its own depth-`K` truncation `⌊Σ_{k≤K} ω(N+k)b^{-k}⌋
= H/b^K` plus `c_{N+K}/b^K` plus an explicit `0` or `1`.  So the error made by truncating the
carry at depth `K` is at most `c_{N+K}/b^K + 1`: once `b^K` exceeds `c_{N+K} ≈ log log N / (b−1)`
the truncation is exact up to a single unit.  This is the quantitative form of the depth needed by
the character-sum leaf `hWindowCharAll`. -/
theorem omegaCarry_eq_trunc_add (b : ℕ) (hb : 2 ≤ b) (K N : ℕ) :
    omegaCarry b N
      = omegaHead b K N / (b : ℤ) ^ K + omegaCarry b (N + K) / (b : ℤ) ^ K
        + (omegaHead b K N % (b : ℤ) ^ K + omegaCarry b (N + K) % (b : ℤ) ^ K) / (b : ℤ) ^ K := by
  set M : ℤ := (b : ℤ) ^ K with hMdef
  have hMpos : (0 : ℤ) < M := by
    have : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (by omega : 0 < b)
    rw [hMdef]; positivity
  have hMne : M ≠ 0 := ne_of_gt hMpos
  set H : ℤ := omegaHead b K N with hHdef
  set c : ℤ := omegaCarry b (N + K) with hcdef
  have hW : omegaCarry b N = (H + c) / M := by
    rw [omegaCarry_eq_windowVal_div b hb K N, omegaWindowVal, hHdef, hcdef, hMdef]
  have hsplit : H + c = M * (H / M + c / M) + (H % M + c % M) := by
    have h1 := Int.mul_ediv_add_emod H M
    have h2 := Int.mul_ediv_add_emod c M
    linarith [h1, h2, mul_add M (H / M) (c / M)]
  rw [hW, hsplit, add_comm (M * (H / M + c / M)) (H % M + c % M),
    Int.add_mul_ediv_left _ _ hMne]
  ring

/-- The truncation defect is between `0` and `1`. -/
theorem trunc_defect_mem (b : ℕ) (hb : 2 ≤ b) (K N : ℕ) :
    0 ≤ (omegaHead b K N % (b : ℤ) ^ K + omegaCarry b (N + K) % (b : ℤ) ^ K) / (b : ℤ) ^ K ∧
      (omegaHead b K N % (b : ℤ) ^ K + omegaCarry b (N + K) % (b : ℤ) ^ K) / (b : ℤ) ^ K ≤ 1 := by
  have hMpos : (0 : ℤ) < (b : ℤ) ^ K := by
    have : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (by omega : 0 < b)
    positivity
  have hMne : ((b : ℤ) ^ K) ≠ 0 := ne_of_gt hMpos
  have hr1 := Int.emod_nonneg (omegaHead b K N) hMne
  have hr2 := Int.emod_nonneg (omegaCarry b (N + K)) hMne
  have hr1' := Int.emod_lt_of_pos (omegaHead b K N) hMpos
  have hr2' := Int.emod_lt_of_pos (omegaCarry b (N + K)) hMpos
  refine ⟨Int.ediv_nonneg (by linarith) (le_of_lt hMpos), ?_⟩
  refine (Int.ediv_le_ediv hMpos (by linarith : _ ≤ 2 * (b : ℤ) ^ K - 2)).trans ?_
  rw [Int.ediv_le_iff_le_mul hMpos]
  linarith

/-- The depth-`K` truncation of the window value: a function of `ω(n+1), …, ω(n+L+K)` only. -/
noncomputable def windowValTrunc (b L K n : ℕ) : ℤ :=
  omegaHead b L n + omegaHead b K (n + L) / (b : ℤ) ^ K

/-- **Finite-window approximation of the window value.**  `omegaWindowVal` differs from its
depth-`K` truncation — which involves only `ω(n+1), …, ω(n+L+K)` — by `c_{n+L+K}/b^K` plus `0`
or `1`. -/
theorem omegaWindowVal_eq_trunc_add (b : ℕ) (hb : 2 ≤ b) (L K n : ℕ) :
    omegaWindowVal b L n
      = windowValTrunc b L K n + omegaCarry b (n + L + K) / (b : ℤ) ^ K
        + (omegaHead b K (n + L) % (b : ℤ) ^ K
            + omegaCarry b (n + L + K) % (b : ℤ) ^ K) / (b : ℤ) ^ K := by
  have he := omegaCarry_eq_trunc_add b hb K (n + L)
  rw [omegaWindowVal, he, windowValTrunc]
  ring

/-- **The bad event, explicitly.**  Once the depth `K` is large enough that `b^K` exceeds the
carry `c_{n+L+K}` — by `omegaCarry_le_log` it is enough that `b^K > log₂(n+L+K+1) + 1` — the
depth-`K` truncation of the window value is wrong at `n` **exactly** when the depth-`K` head
overflows:  `H_K(n+L) mod b^K + c_{n+L+K} ≥ b^K`.  This is the precise arithmetic event whose
density Leaf B must control. -/
theorem windowVal_ne_trunc_iff (b : ℕ) (hb : 2 ≤ b) (L K n : ℕ)
    (hsmall : omegaCarry b (n + L + K) < (b : ℤ) ^ K) :
    omegaWindowVal b L n ≠ windowValTrunc b L K n
      ↔ (b : ℤ) ^ K ≤ omegaHead b K (n + L) % (b : ℤ) ^ K + omegaCarry b (n + L + K) := by
  have hMpos : (0 : ℤ) < (b : ℤ) ^ K := by
    have : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (by omega : 0 < b)
    positivity
  have hc0 := omegaCarry_nonneg b hb (n + L + K)
  have hcz : omegaCarry b (n + L + K) / (b : ℤ) ^ K = 0 :=
    Int.ediv_eq_zero_of_lt hc0 hsmall
  have hcm : omegaCarry b (n + L + K) % (b : ℤ) ^ K = omegaCarry b (n + L + K) :=
    Int.emod_eq_of_lt hc0 hsmall
  have he := omegaWindowVal_eq_trunc_add b hb L K n
  rw [hcz, hcm, add_zero] at he
  set r : ℤ := omegaHead b K (n + L) % (b : ℤ) ^ K + omegaCarry b (n + L + K) with hr
  have hr0 : 0 ≤ r := by
    have := Int.emod_nonneg (omegaHead b K (n + L)) (ne_of_gt hMpos)
    omega
  constructor
  · intro hne
    by_contra hlt
    push_neg at hlt
    exact hne (by rw [he, Int.ediv_eq_zero_of_lt hr0 hlt, add_zero])
  · intro hge hEq
    have : r / (b : ℤ) ^ K = 0 := by omega
    have h1 : 1 ≤ r / (b : ℤ) ^ K := (Int.le_ediv_iff_mul_le hMpos).mpr (by linarith)
    omega

/-! ### Finite Fourier: the character-sum form of the hypothesis -/

/-- A primitive `M`-th root of unity. -/
noncomputable def zetaRoot (M : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / M)

lemma zetaRoot_ne_zero (M : ℕ) : zetaRoot M ≠ 0 := Complex.exp_ne_zero _

lemma zetaRoot_zpow (M : ℕ) (k : ℤ) :
    zetaRoot M ^ k = Complex.exp ((k : ℂ) * (2 * Real.pi * Complex.I / M)) := by
  rw [zetaRoot, ← Complex.exp_int_mul]

lemma zetaRoot_zpow_eq_one_iff (M : ℕ) (hM : 0 < M) (k : ℤ) :
    zetaRoot M ^ k = 1 ↔ (M : ℤ) ∣ k := by
  have hMC : ((M : ℂ)) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero]
  rw [zetaRoot_zpow, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    field_simp at hn
    exact_mod_cast hn
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    field_simp

/-- **Orthogonality.**  `Σ_{a<M} ζ^{ak} = M` if `M ∣ k`, else `0`. -/
lemma sum_zetaRoot_zpow (M : ℕ) (hM : 0 < M) (k : ℤ) :
    ∑ a ∈ range M, zetaRoot M ^ ((a : ℤ) * k) = if (M : ℤ) ∣ k then (M : ℂ) else 0 := by
  have hx : ∀ a : ℕ, zetaRoot M ^ ((a : ℤ) * k) = (zetaRoot M ^ k) ^ a := by
    intro a
    rw [mul_comm, zpow_mul, zpow_natCast]
  rw [Finset.sum_congr rfl fun a _ => hx a]
  by_cases hd : (M : ℤ) ∣ k
  · rw [if_pos hd, (zetaRoot_zpow_eq_one_iff M hM k).mpr hd]
    simp
  · rw [if_neg hd]
    have hne : zetaRoot M ^ k ≠ 1 := fun h => hd ((zetaRoot_zpow_eq_one_iff M hM k).mp h)
    rw [geom_sum_eq hne]
    have hMk : (zetaRoot M ^ k) ^ M = 1 := by
      rw [← zpow_natCast (zetaRoot M ^ k) M, ← zpow_mul]
      exact (zetaRoot_zpow_eq_one_iff M hM _).mpr ⟨k, by ring⟩
    rw [hMk, sub_self, zero_div]

/-- The normalised character sum of the window value at frequency `a / b^L`. -/
noncomputable def windowCharSum (b L a N : ℕ) : ℂ :=
  (∑ n ∈ range N, zetaRoot (b ^ L) ^ ((a : ℤ) * omegaWindowVal b L n)) / N

lemma norm_zetaRoot_zpow (M : ℕ) (k : ℤ) : ‖zetaRoot M ^ k‖ = 1 := by
  rw [zetaRoot_zpow, Complex.norm_exp]
  have : (((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ))).re) = 0 := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq]
  rw [this, Real.exp_zero]

/-- The truncated character sum at depth profile `κ`: at `n` it is a correlation of
`ω(n+1), …, ω(n+L+κ n)` only.  A CONSTANT `κ` is not enough — see `HCarryOverflow`. -/
noncomputable def windowCharSumTrunc (b L : ℕ) (κ : ℕ → ℕ) (a N : ℕ) : ℂ :=
  (∑ n ∈ range N, zetaRoot (b ^ L) ^ ((a : ℤ) * windowValTrunc b L (κ n) n)) / N

/-- How often the depth-`κ n` truncation of the window value is wrong at all. -/
noncomputable def carryBadCount (b L : ℕ) (κ : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((range N).filter (fun n => omegaWindowVal b L n ≠ windowValTrunc b L (κ n) n)).card

/-- **Truncation error bound.**  The exact and the depth-`K` character sums differ by at most
twice the frequency of `n` at which the truncation is wrong. -/
theorem norm_windowCharSum_sub_trunc (b L : ℕ) (κ : ℕ → ℕ) (a N : ℕ) :
    ‖windowCharSum b L a N - windowCharSumTrunc b L κ a N‖
      ≤ 2 * (carryBadCount b L κ N : ℝ) / N := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [windowCharSum, windowCharSumTrunc, carryBadCount]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNC : ((N : ℂ)) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hdiff : windowCharSum b L a N - windowCharSumTrunc b L κ a N
      = (∑ n ∈ range N, (zetaRoot (b ^ L) ^ ((a : ℤ) * omegaWindowVal b L n)
          - zetaRoot (b ^ L) ^ ((a : ℤ) * windowValTrunc b L (κ n) n))) / N := by
    rw [windowCharSum, windowCharSumTrunc, ← sub_div, Finset.sum_sub_distrib]
  rw [hdiff, norm_div, Complex.norm_natCast]
  rw [div_le_div_iff_of_pos_right hNR]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ range N,
      ‖zetaRoot (b ^ L) ^ ((a : ℤ) * omegaWindowVal b L n)
        - zetaRoot (b ^ L) ^ ((a : ℤ) * windowValTrunc b L (κ n) n)‖
      ≤ (if omegaWindowVal b L n ≠ windowValTrunc b L (κ n) n then (2 : ℝ) else 0) := by
    intro n _
    by_cases he : omegaWindowVal b L n = windowValTrunc b L (κ n) n
    · rw [if_neg (by simpa using he), he, sub_self, norm_zero]
    · rw [if_pos he]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_zetaRoot_zpow, norm_zetaRoot_zpow]
      norm_num
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [smul_eq_mul, mul_zero, add_zero, nsmul_eq_mul]
  rw [carryBadCount]
  rw [mul_comm]

/-- **H, Weyl form.**  All nontrivial `b^L`-th-root-of-unity character sums of the `ω`-side
window value have mean zero.  This is the shape in which the literature states Elliott/Kátai-type
inputs: `ζ^{a·(Σ ω(n+1+i) b^{L-1-i} + c_{n+L})}` is a correlation of additively-twisted
`ω`-values in a short window. -/
def HWindowChar (b L : ℕ) : Prop :=
  ∀ a, 0 < a → a < b ^ L → Tendsto (windowCharSum b L a) atTop (𝓝 0)

theorem hWindow_of_hWindowChar (b : ℕ) (hb : 2 ≤ b) (L : ℕ) (h : HWindowChar b L) :
    HWindow b L := by
  classical
  set M := b ^ L with hM
  have hMpos : 0 < M := by positivity
  have hMC : ((M : ℂ)) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hMR : ((M : ℕ) : ℝ) = (b : ℝ) ^ L := by rw [hM]; push_cast; ring
  have hMz : ((M : ℤ)) = (b : ℤ) ^ L := by rw [hM]; push_cast; ring
  have hMzpos : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hMpos
  -- the character sum only sees the residue
  have hres : ∀ a n : ℕ, zetaRoot M ^ ((a : ℤ) * omegaWindowVal b L n)
      = zetaRoot M ^ ((a : ℤ) * (windowResidue b L n : ℤ)) := by
    intro a n
    have h0 := Int.emod_nonneg (omegaWindowVal b L n) (by positivity : ((b : ℤ) ^ L) ≠ 0)
    have he : ((windowResidue b L n : ℕ) : ℤ) = omegaWindowVal b L n % (b : ℤ) ^ L :=
      Int.toNat_of_nonneg h0
    obtain ⟨d, hd⟩ : ((M : ℤ)) ∣ (omegaWindowVal b L n - (windowResidue b L n : ℤ)) := by
      rw [he, hMz]
      exact ⟨omegaWindowVal b L n / (b : ℤ) ^ L, by rw [Int.emod_def]; ring⟩
    have hsplit : (a : ℤ) * omegaWindowVal b L n
        = (a : ℤ) * (windowResidue b L n : ℤ) + (M : ℤ) * ((a : ℤ) * d) := by
      have hw : omegaWindowVal b L n = (windowResidue b L n : ℤ) + (M : ℤ) * d := by omega
      rw [hw]; ring
    rw [hsplit, zpow_add₀ (zetaRoot_ne_zero M), zpow_mul (zetaRoot M) (M : ℤ) ((a : ℤ) * d),
      (zetaRoot_zpow_eq_one_iff M hMpos (M : ℤ)).mpr dvd_rfl, one_zpow, mul_one]
  intro v hv
  have hvz : (v : ℤ) < (M : ℤ) := by exact_mod_cast hv
  -- indicator via orthogonality
  have hind : ∀ n : ℕ, ((if windowResidue b L n = v then (1 : ℂ) else 0))
      = (M : ℂ)⁻¹ * ∑ a ∈ range M, zetaRoot M ^ ((a : ℤ) * ((windowResidue b L n : ℤ) - v)) := by
    intro n
    rw [sum_zetaRoot_zpow M hMpos]
    have hlt : ((windowResidue b L n : ℕ) : ℤ) < (M : ℤ) := by
      exact_mod_cast windowResidue_lt b hb L n
    by_cases he : windowResidue b L n = v
    · rw [if_pos he, if_pos (by rw [he]; simp)]
      field_simp
    · have hnd : ¬ ((M : ℤ) ∣ ((windowResidue b L n : ℤ) - (v : ℤ))) := by
        intro hdvd
        have habs : |((windowResidue b L n : ℤ) - (v : ℤ))| < (M : ℤ) := by
          rw [abs_lt]
          constructor <;> [skip; skip] <;> omega
        exact he (by have := Int.eq_zero_of_abs_lt_dvd hdvd habs; omega)
      rw [if_neg he, if_neg hnd, mul_zero]
  -- the count, in ℂ
  have hcount : ∀ N : ℕ, ((((range N).filter (fun n => windowResidue b L n = v)).card : ℂ))
      = ∑ a ∈ range M, ((M : ℂ)⁻¹ * (zetaRoot M ^ (-((a : ℤ) * (v : ℤ)))) *
          ∑ n ∈ range N, zetaRoot M ^ ((a : ℤ) * omegaWindowVal b L n)) := by
    intro N
    have h1 : ((((range N).filter (fun n => windowResidue b L n = v)).card : ℂ))
        = ∑ n ∈ range N, (if windowResidue b L n = v then (1 : ℂ) else 0) := by
      rw [← Finset.sum_filter]
      simp
    rw [h1, Finset.sum_congr rfl fun n _ => hind n, ← Finset.mul_sum, Finset.sum_comm,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hexp : (a : ℤ) * ((windowResidue b L n : ℤ) - (v : ℤ))
        = -((a : ℤ) * (v : ℤ)) + (a : ℤ) * (windowResidue b L n : ℤ) := by ring
    rw [hres a n, hexp, zpow_add₀ (zetaRoot_ne_zero M), mul_assoc]
  -- per-frequency limits
  have hw0 : ∀ N : ℕ, 0 < N → windowCharSum b L 0 N = 1 := by
    intro N hN
    have hNC : ((N : ℂ)) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    simp only [windowCharSum, Nat.cast_zero, zero_mul, zpow_zero, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    exact div_self hNC
  have hterm : ∀ a ∈ range M, Tendsto (fun N : ℕ => (M : ℂ)⁻¹ *
      (zetaRoot M ^ (-((a : ℤ) * (v : ℤ)))) * windowCharSum b L a N) atTop
      (𝓝 (if a = 0 then ((M : ℂ)⁻¹) else 0)) := by
    intro a ha
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [if_pos rfl]
      refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := ((M : ℂ)⁻¹)))
      filter_upwards [Filter.eventually_gt_atTop 0] with N hN
      rw [hw0 N hN]
      simp
    · rw [if_neg ha0]
      have hlim0 := h a (Nat.pos_of_ne_zero ha0) (by rw [← hM]; exact Finset.mem_range.mp ha)
      simpa using hlim0.const_mul ((M : ℂ)⁻¹ * (zetaRoot M ^ (-((a : ℤ) * (v : ℤ)))))
  have hsum : Tendsto (fun N : ℕ => ∑ a ∈ range M, ((M : ℂ)⁻¹ *
      (zetaRoot M ^ (-((a : ℤ) * (v : ℤ)))) * windowCharSum b L a N)) atTop
      (𝓝 (∑ a ∈ range M, (if a = 0 then ((M : ℂ)⁻¹) else 0))) :=
    tendsto_finsetSum _ hterm
  have heq : (∑ a ∈ range M, (if a = 0 then ((M : ℂ)⁻¹) else 0)) = (M : ℂ)⁻¹ := by
    rw [Finset.sum_ite_eq' (range M) 0 (fun _ => ((M : ℂ)⁻¹))]
    simp [hMpos]
  rw [heq] at hsum
  -- assemble in ℂ, then descend to ℝ
  have hrw : ∀ N : ℕ,
      (((((range N).filter (fun n => windowResidue b L n = v)).card : ℝ) / N : ℝ) : ℂ)
        = ∑ a ∈ range M, ((M : ℂ)⁻¹ * (zetaRoot M ^ (-((a : ℤ) * (v : ℤ)))) *
            windowCharSum b L a N) := by
    intro N
    push_cast
    rw [hcount N, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [windowCharSum, ← hM]
    ring
  have hC : Tendsto (fun N : ℕ =>
      (((((range N).filter (fun n => windowResidue b L n = v)).card : ℝ) / N : ℝ) : ℂ))
      atTop (𝓝 (((((M : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ)) := by
    rw [show (fun N : ℕ =>
        (((((range N).filter (fun n => windowResidue b L n = v)).card : ℝ) / N : ℝ) : ℂ)) = _
      from funext hrw]
    simpa using hsum
  have hfin := (Complex.continuous_re.tendsto ((((M : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)).comp hC
  simp only [Function.comp_def, Complex.ofReal_re] at hfin
  rw [hMR] at hfin
  exact hfin

/-- **Leaf A at depth profile `κ`.**  Every nontrivial character sum of the truncation
`windowValTrunc b L (κ n) n` — which at `n` depends only on `ω(n+1), …, ω(n+L+κ n)` — has mean
zero.  This is the joint-equidistribution input: the one-coordinate case is Delange (1969), `ω` is
uniformly distributed mod every `q ≥ 2` because `ω(p) = 1` and `Σ_p 1/p = ∞`; the joint version
over the shifts is open. -/
def HTruncDecayAt (b L : ℕ) (κ : ℕ → ℕ) : Prop :=
  ∀ a, 0 < a → a < b ^ L → Tendsto (windowCharSumTrunc b L κ a) atTop (𝓝 0)

/-- **Leaf B at depth profile `κ`.**  The depth-`κ n` truncation is wrong on a density-zero set.
By `windowVal_ne_trunc_iff` the bad event at an admissible depth is exactly the overflow
`H_{κ n}(n+L) mod b^{κ n} + c_{n+L+κ n} ≥ b^{κ n}`; by `omegaCarry_le_log` the carry there is
`≤ log₂(·)+1`, so the depth must satisfy `b^{κ n} ≳ log n`, i.e. `κ n ≳ log_b log n`. -/
def HCarryOverflowAt (b L : ℕ) (κ : ℕ → ℕ) : Prop :=
  Tendsto (fun N => (carryBadCount b L κ N : ℝ) / N) atTop (𝓝 0)

/-- **The single leaf, in its weakest useful form.**  There EXISTS one depth profile `κ → ∞` that
serves both purposes at once.  This is strictly weaker than asking Leaf A for every `κ`. -/
def HDepth (b L : ℕ) : Prop :=
  ∃ κ : ℕ → ℕ, Tendsto κ atTop atTop ∧ HTruncDecayAt b L κ ∧ HCarryOverflowAt b L κ

/-- **The split.**  One good depth profile ⟹ the Weyl form of C1 at length `L`. -/
theorem hWindowChar_of_hDepth (b L : ℕ) (h : HDepth b L) : HWindowChar b L := by
  obtain ⟨κ, _, hA, hB⟩ := h
  intro a ha haL
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro ε hε
  have hbad' := (NormedAddCommGroup.tendsto_nhds_zero.mp hB) (ε / 4) (by linarith)
  have h1 := (NormedAddCommGroup.tendsto_nhds_zero.mp (hA a ha haL)) (ε / 4) (by linarith)
  filter_upwards [h1, hbad'] with N hN1 hN2
  have hbd := norm_windowCharSum_sub_trunc b L κ a N
  have hN2' : (carryBadCount b L κ N : ℝ) / N ≤ ε / 4 := le_of_lt (by simpa using hN2)
  have h2 : 2 * (carryBadCount b L κ N : ℝ) / N ≤ 2 * (ε / 4) := by
    rw [mul_div_assoc]; linarith
  have hsplit : windowCharSum b L a N
      = (windowCharSum b L a N - windowCharSumTrunc b L κ a N)
        + windowCharSumTrunc b L κ a N := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans_lt ?_
  linarith

/-- **THE LEAF.**  Open.  Asks for one slowly growing depth profile `κ n ≳ log_b log n` such that
(A) the finite-window correlations of `ω(n+1), …, ω(n+L+κ n)` at the rational frequencies `a/b^L`
have mean zero, and (B) the head `H_{κ n}(n+L)` overflows mod `b^{κ n}` only on a null set.

(A) is the joint/Elliott branch of the literature; (B) is the *varying-moduli* branch, since the
modulus `b^{κ n}` grows with `n`.  Delange (1969) settles the one-coordinate, fixed-modulus case.
A CONSTANT `κ` cannot work — see the warning on `omegaWindowVal_eq_trunc_add` and the handoff. -/
theorem hDepthAll : ∀ b, 3 ≤ b → ∀ L, HDepth b L := by
  sorry

theorem hWindowCharAll : ∀ b, 3 ≤ b → ∀ L, HWindowChar b L :=
  fun b hb L => hWindowChar_of_hDepth b L (hDepthAll b hb L)

/-! ### Bridge to the classical Weyl sums of `x` itself

The C1 character sums are the Weyl sums `(1/N) Σ e(a·bⁿ·x)` twisted by a factor that depends only
on the tail `fract(b^{n+L}x)`.  This is what connects the present chain to the repo's existing
`G4WiringCRT` machinery (`fullWindowMean`, `WindowDecay`, `isNormal_G4_of_windowDecay`). -/

/-- `⌊x·b^{n+L}⌋ = b^L·(head up to n) + omegaWindowVal`: the window value IS the low `L` digits. -/
theorem floor_mul_pow_eq_windowVal (b : ℕ) (hb : 2 ≤ b) (L n : ℕ) :
    ⌊primeLambertAtBase b * (b : ℝ) ^ (n + L)⌋
      = (b : ℤ) ^ L * ((∑ m ∈ range (n + 1), omegaNat m * b ^ (n - m) : ℕ) : ℤ)
        + omegaWindowVal b L n := by
  rw [primeLambertAtBase_eq_lambertVal_omegaNat b,
    floor_lambertVal_mul_pow b hb omegaNat omegaNat_le (n + L)]
  have hsplit : ((∑ m ∈ range (n + L + 1), omegaNat m * b ^ (n + L - m) : ℕ) : ℤ)
      = (b : ℤ) ^ L * ((∑ m ∈ range (n + 1), omegaNat m * b ^ (n - m) : ℕ) : ℤ)
        + omegaHead b L n := by
    rw [← sum_Ioc_omegaNat_pow b n L]
    have hIoc : Finset.Ioc n (n + L) = Finset.Ico (n + 1) (n + L + 1) := by
      ext m; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    push_cast
    rw [hIoc, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun m => (omegaNat m : ℤ) * (b : ℤ) ^ (n + L - m))
        (Nat.zero_le (n + 1)) (by omega : n + 1 ≤ n + L + 1), ← Finset.range_eq_Ico,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [show n + L - m = L + (n - m) by omega, pow_add]
    ring
  rw [hsplit, omegaWindowVal, omegaCarry, add_assoc]

/-- **The C1 characters are twisted Weyl sums of `x`.**

    ζ_{b^L}^{a·omegaWindowVal b L n}  =  e(a·bⁿ·x) · e(−a·fract(b^{n+L}x)/b^L),

`x = G4_b`.  The first factor is the classical Weyl exponential whose averages the repo's
`G4WiringCRT` layer studies (`fullWindowMean`, `WindowDecay`, `isNormal_G4_of_windowDecay`); the
second depends only on the tail beyond position `n+L` and is bounded by `1` in modulus.  For a
FIXED frequency `a` the twist is `1 + O(a/b^L)`, so C1 at large `L` and small `a` is a Weyl
statement; the difficulty is concentrated in the frequencies `a` comparable to `b^L`. -/
theorem zetaRoot_windowVal_eq (b : ℕ) (hb : 2 ≤ b) (L a n : ℕ) :
    zetaRoot (b ^ L) ^ ((a : ℤ) * omegaWindowVal b L n)
      = Complex.exp (2 * Real.pi * Complex.I *
            ((a : ℂ) * ((b : ℝ) ^ n * primeLambertAtBase b)))
        * Complex.exp (-(2 * Real.pi * Complex.I *
            ((a : ℂ) * (Int.fract (primeLambertAtBase b * (b : ℝ) ^ (n + L)) : ℝ)
              / ((b : ℝ) ^ L)))) := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hbL : ((b : ℂ)) ^ L ≠ 0 := by
    have : ((b : ℂ)) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
    positivity
  set y : ℝ := primeLambertAtBase b * (b : ℝ) ^ (n + L) with hy
  set S : ℕ := ∑ m ∈ range (n + 1), omegaNat m * b ^ (n - m) with hS
  have hfloor := floor_mul_pow_eq_windowVal b hb L n
  have hWR : ((omegaWindowVal b L n : ℤ) : ℝ) = (y - Int.fract y) - (b : ℝ) ^ L * (S : ℝ) := by
    have h1 : ((⌊y⌋ : ℤ) : ℝ) = y - Int.fract y := (Int.self_sub_fract y).symm
    have h2 : ((⌊y⌋ : ℤ) : ℝ)
        = (b : ℝ) ^ L * (S : ℝ) + ((omegaWindowVal b L n : ℤ) : ℝ) := by
      rw [hy] at h1 ⊢
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hfloor
    rw [← h1]
    linarith [h2]
  have hWC : ((omegaWindowVal b L n : ℤ) : ℂ)
      = ((y : ℝ) : ℂ) - ((Int.fract y : ℝ) : ℂ) - ((b : ℂ)) ^ L * (S : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hWR
    push_cast at this ⊢
    linear_combination this
  have hyC : ((y : ℝ) : ℂ) = ((b : ℂ)) ^ L * (((b : ℝ) ^ n * primeLambertAtBase b : ℝ) : ℂ) := by
    rw [hy]; push_cast; rw [pow_add]; ring
  rw [zetaRoot_zpow, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-((a : ℤ) * (S : ℤ)), ?_⟩
  push_cast
  rw [hWC, hyC]
  push_cast
  field_simp
  ring

/-! ### The minimal open case `L = 1`

Everything above is uniform in `L`.  At `L = 1` the window value is just `ω(n+1) + c_{n+1}` and
the modulus is `b`, so the open statement reads as compactly as it ever will. -/

@[simp] lemma omegaHead_one (b n : ℕ) : omegaHead b 1 n = (omegaNat (n + 1) : ℤ) := by
  simp [omegaHead]

lemma omegaWindowVal_one (b n : ℕ) :
    omegaWindowVal b 1 n = (omegaNat (n + 1) : ℤ) + omegaCarry b (n + 1) := by
  rw [omegaWindowVal, omegaHead_one]

/-- **The first open case of C1, fully explicit.**  If for every `0 < a < b`

    (1/N) Σ_{n<N} e^{2πi·a·(ω(n+1) + c_{n+1})/b}  →  0,      c_N = ⌊Σ_{k≥1} ω(N+k) b^{−k}⌋,

then `G4_b` has the normal casting-out law at window length `1`.  Here `ζ^{a·ω(n+1)}` is a
multiplicative function of modulus one with `ζ^{a·ω(p)} = ζ^a ≠ 1`, whose own mean value is `0`
by Delange; the whole difficulty is the SHIFT `n ↦ n+1` together with the carry factor. -/
theorem castLaw_one_of_charSum (b : ℕ) (hb : 3 ≤ b)
    (h : ∀ a, 0 < a → a < b →
      Tendsto (fun N => (∑ n ∈ range N,
        zetaRoot b ^ ((a : ℤ) * ((omegaNat (n + 1) : ℤ) + omegaCarry b (n + 1)))) / N)
        atTop (𝓝 0)) :
    CastLaw b (primeLambertAtBase b) 1 := by
  refine (castLaw_iff_stateLaw b (by omega) 1).mpr
    (stateLaw_of_hWindow b hb 1 (hWindow_of_hWindowChar b (by omega) 1 ?_))
  intro a ha haL
  rw [pow_one] at haL
  have hfun : windowCharSum b 1 a = fun N => (∑ n ∈ range N,
      zetaRoot b ^ ((a : ℤ) * ((omegaNat (n + 1) : ℤ) + omegaCarry b (n + 1)))) / N := by
    funext N
    rw [windowCharSum, pow_one]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [omegaWindowVal_one]
  rw [hfun]
  exact h a ha haL

theorem hWindowAll : ∀ b, 3 ≤ b → ∀ L, HWindow b L :=
  fun b hb L => hWindow_of_hWindowChar b (by omega) L (hWindowCharAll b hb L)

/-- The strictly-stronger (block-normality) route also reaches `HState`; it is kept for the
record but is NOT what `conjC1` below rests on — see `hAutoCorrAll`. -/
theorem hState_of_blockRoute : HState := hState_of_hWindow hWindowAll


/-! ### A strictly weaker leaf: the autocorrelation spectrum at the FIXED modulus `b − 1`

The chain `HWindow → HState` above asks for equidistribution of the length-`L` window WORD in
`ZMod (b^L)`, i.e. for block normality of `G4_b`; that is strictly stronger than `ConjC1`, which
only sees the window word's digit sum mod `b − 1`.  This section replaces it.

Write `T(n) := Σ_{m ≤ n} ω(m) + c_n : ℤ`.  Then

    castState b L n = T(n+L) − T(n)   in `ZMod (b−1)`,

so `StateLaw b L` for every `L` is a statement about the *increments of one sequence*.  Passing to
characters, `ψ(castState b L n) = u(n+L)·conj(u(n))` for the unit-modulus sequence
`u(n) = ζ_{b−1}^{j·T(n)}`: `ConjC1` is exactly the assertion that `u` has lag-`L` autocorrelation
`b^{−L}` for every nontrivial `j` and every `L`.  (`b^{−L}` is forced: a uniform base-`b` digit
reduced mod `b − 1` hits `0` twice, and `Σ_{d<b} ζ_{b−1}^{jd} = 1`, giving one factor `1/b` per
step.  Matching `normalCastLaw_closed` below is the proof that this is the right constant.)

The gain is that the modulus is now FIXED at `b − 1` — the unbounded carry enters only mod `b − 1`,
there is no `b^{κ n}` varying-moduli branch, and no block normality is demanded. -/

/-- `T(n) = Σ_{m ≤ n} ω(m) + c_n`: the potential whose `L`-step increment is `castState`. -/
noncomputable def castSum (b n : ℕ) : ℤ :=
  (∑ m ∈ range (n + 1), (omegaNat m : ℤ)) + omegaCarry b n

/-- **The increment identity.**  `castState b L n = T(n+L) − T(n)` in `ZMod (b−1)`. -/
theorem castState_eq_castSum_sub (b L n : ℕ) :
    castState b L n = ((castSum b (n + L) - castSum b n : ℤ) : ZMod (b - 1)) := by
  have hsum : (∑ m ∈ range (n + L + 1), (omegaNat m : ℤ))
      - (∑ m ∈ range (n + 1), (omegaNat m : ℤ))
      = ∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ) := by
    have hIoc : Finset.Ioc n (n + L) = Finset.Ico (n + 1) (n + L + 1) := by
      ext m; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun m => (omegaNat m : ℤ))
        (Nat.zero_le (n + 1)) (by omega : n + 1 ≤ n + L + 1)]
    ring
  rw [castState]
  congr 1
  rw [castSum, castSum, show n + L + 1 = n + L + 1 from rfl]
  linarith [hsum]

/-- The lag-`L` autocorrelation sum of the unit-modulus sequence `n ↦ ζ_{b−1}^{j·T(n)}`. -/
noncomputable def corrSum (b j L N : ℕ) : ℂ :=
  (∑ n ∈ range N, zetaRoot (b - 1) ^ ((j : ℤ) * (castSum b (n + L) - castSum b n))) / N

/-- **THE LEAF, fixed-modulus form.**  For every nontrivial character index `j` and every lag `L`,
the sequence `n ↦ ζ_{b−1}^{j·(Σ_{m≤n} ω(m) + c_n)}` has lag-`L` autocorrelation exactly `b^{−L}`.

This is equivalent to `ConjC1` (`conjC1_iff_hAutoCorr` below) and asks nothing about the digits of
`G4_b` in `ZMod (b^L)`: the modulus is the fixed `b − 1`.  The `L = 1` instance,
`mean_n ζ^{j·(ω(n+1) + c_{n+1} − c_n)} = 1/b`, is the one-coordinate case. -/
def HAutoCorr (b : ℕ) : Prop :=
  ∀ j, 0 < j → j < b - 1 → ∀ L, Tendsto (corrSum b j L) atTop (𝓝 (((b : ℂ))⁻¹ ^ L))

/-- **The reduction.**  The autocorrelation spectrum gives `StateLaw` at every `L`. -/
theorem stateLaw_of_hAutoCorr (b : ℕ) (hb : 3 ≤ b) (h : HAutoCorr b) (L : ℕ) :
    StateLaw b L := by
  classical
  set q := b - 1 with hq
  have hqpos : 0 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hqC : ((q : ℂ)) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqR : ((q : ℝ)) = (b : ℝ) - 1 := by
    have : ((q : ℕ) : ℝ) = ((b - 1 : ℕ) : ℝ) := by rw [hq]
    rw [this, Nat.cast_sub (by omega : 1 ≤ b)]; norm_num
  intro r hr
  have hrq : r < q := by omega
  set D : ℕ → ℤ := fun n => castSum b (n + L) - castSum b n with hD
  -- the fibre condition, as a divisibility
  have hfib : ∀ n : ℕ, (castState b L n = ((r : ℕ) : ZMod q)) ↔ ((q : ℤ) ∣ (D n - (r : ℤ))) := by
    intro n
    rw [castState_eq_castSum_sub b L n, show ((r : ℕ) : ZMod q) = ((r : ℤ) : ZMod q) by
      push_cast; ring, ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd, dvd_sub_comm]
  -- orthogonality on `ZMod q`
  have hind : ∀ n : ℕ, ((if castState b L n = ((r : ℕ) : ZMod q) then (1 : ℂ) else 0))
      = (q : ℂ)⁻¹ * ∑ j ∈ range q, zetaRoot q ^ ((j : ℤ) * (D n - (r : ℤ))) := by
    intro n
    rw [sum_zetaRoot_zpow q hqpos]
    by_cases he : castState b L n = ((r : ℕ) : ZMod q)
    · rw [if_pos he, if_pos ((hfib n).mp he)]
      field_simp
    · rw [if_neg he, if_neg (fun hd => he ((hfib n).mpr hd)), mul_zero]
  -- the count as a sum over frequencies
  have hcount : ∀ N : ℕ, ((stateFreq b L ((r : ℕ) : ZMod q) N : ℝ) : ℂ)
      = ∑ j ∈ range q, ((q : ℂ)⁻¹ * zetaRoot q ^ (-((j : ℤ) * (r : ℤ))) * corrSum b j L N) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [stateFreq, corrSum]
    have hNC : ((N : ℂ)) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have h1 : ((((range N).filter (fun n => castState b L n = ((r : ℕ) : ZMod q))).card : ℂ))
        = ∑ n ∈ range N, (if castState b L n = ((r : ℕ) : ZMod q) then (1 : ℂ) else 0) := by
      rw [← Finset.sum_filter]; simp
    have h2 : ((((range N).filter (fun n => castState b L n = ((r : ℕ) : ZMod q))).card : ℂ))
        = ∑ j ∈ range q, ((q : ℂ)⁻¹ * zetaRoot q ^ (-((j : ℤ) * (r : ℤ))) *
            ∑ n ∈ range N, zetaRoot q ^ ((j : ℤ) * D n)) := by
      rw [h1, Finset.sum_congr rfl fun n _ => hind n, ← Finset.mul_sum, Finset.sum_comm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show (j : ℤ) * (D n - (r : ℤ)) = -((j : ℤ) * (r : ℤ)) + (j : ℤ) * D n by ring,
        zpow_add₀ (zetaRoot_ne_zero q), mul_assoc]
    simp only [stateFreq]
    push_cast
    rw [h2, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [corrSum, hD, ← hq]
    ring
  -- per-frequency limits
  have hterm : ∀ j ∈ range q, Tendsto (fun N : ℕ =>
      ((q : ℂ)⁻¹ * zetaRoot q ^ (-((j : ℤ) * (r : ℤ))) * corrSum b j L N)) atTop
      (𝓝 ((q : ℂ)⁻¹ * zetaRoot q ^ (-((j : ℤ) * (r : ℤ))) *
        (if j = 0 then 1 else ((b : ℂ))⁻¹ ^ L))) := by
    intro j hj
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [if_pos rfl]
      refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds
        (x := (q : ℂ)⁻¹ * zetaRoot q ^ (-((0 : ℤ) * (r : ℤ))) * 1))
      filter_upwards [Filter.eventually_gt_atTop 0] with N hN
      have hNC : ((N : ℂ)) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      simp only [corrSum, Nat.cast_zero, zero_mul, zpow_zero, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one]
      rw [div_self hNC, mul_one]
    · rw [if_neg hj0]
      exact ((h j (Nat.pos_of_ne_zero hj0) (by rw [← hq]; exact Finset.mem_range.mp hj) L)).const_mul _
  have hsum := tendsto_finsetSum _ hterm
  -- evaluate the limit
  have hgeom : (∑ j ∈ range q, zetaRoot q ^ (-((j : ℤ) * (r : ℤ))))
      = (if r = 0 then (q : ℂ) else 0) := by
    have : (∑ j ∈ range q, zetaRoot q ^ ((j : ℤ) * (-(r : ℤ))))
        = if ((q : ℤ)) ∣ (-(r : ℤ)) then (q : ℂ) else 0 := sum_zetaRoot_zpow q hqpos _
    rw [show (fun j : ℕ => zetaRoot q ^ (-((j : ℤ) * (r : ℤ))))
      = (fun j : ℕ => zetaRoot q ^ ((j : ℤ) * (-(r : ℤ)))) from
      funext fun j => by rw [show -((j : ℤ) * (r : ℤ)) = (j : ℤ) * (-(r : ℤ)) by ring]]
    rw [this]
    by_cases hr0 : r = 0
    · simp [hr0]
    · rw [if_neg hr0, if_neg ?_]
      intro hdvd
      have : ((q : ℤ)) ∣ (r : ℤ) := (dvd_neg).mp hdvd
      have := Int.le_of_dvd (by exact_mod_cast (by omega : 0 < r)) this
      omega
  have hlim : (∑ j ∈ range q, ((q : ℂ)⁻¹ * zetaRoot q ^ (-((j : ℤ) * (r : ℤ))) *
      (if j = 0 then 1 else ((b : ℂ))⁻¹ ^ L)))
      = (q : ℂ)⁻¹ * (1 + ((b : ℂ))⁻¹ ^ L * ((if r = 0 then (q : ℂ) else 0) - 1)) := by
    have hsplit : ∀ j ∈ range q, ((q : ℂ)⁻¹ * zetaRoot q ^ (-((j : ℤ) * (r : ℤ))) *
        (if j = 0 then 1 else ((b : ℂ))⁻¹ ^ L))
        = (q : ℂ)⁻¹ * (((b : ℂ))⁻¹ ^ L * zetaRoot q ^ (-((j : ℤ) * (r : ℤ)))
            + (if j = 0 then 1 - ((b : ℂ))⁻¹ ^ L else 0)) := by
      intro j _
      rcases eq_or_ne j 0 with rfl | hj0
      · simp
      · rw [if_neg hj0, if_neg hj0]; ring
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
      hgeom, Finset.sum_ite_eq' (range q) 0 (fun _ => (1 : ℂ) - ((b : ℂ))⁻¹ ^ L)]
    rw [if_pos (Finset.mem_range.mpr hqpos)]
    ring
  rw [hlim] at hsum
  -- descend to ℝ
  have hreal : ((q : ℂ)⁻¹ * (1 + ((b : ℂ))⁻¹ ^ L * ((if r = 0 then (q : ℂ) else 0) - 1)))
      = ((normalCastLaw b L r : ℝ) : ℂ) := by
    rw [normalCastLaw_closed b L r hb (by omega)]
    have hbC : ((b : ℂ)) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
    have hqC' : ((b : ℂ)) - 1 = (q : ℂ) := by
      have : ((q : ℕ) : ℂ) = ((b - 1 : ℕ) : ℂ) := by rw [hq]
      rw [this, Nat.cast_sub (by omega : 1 ≤ b)]; norm_num
    push_cast
    rw [← hqC']
    have hpow : ((b : ℂ)) ^ L ≠ 0 := pow_ne_zero _ hbC
    rw [inv_pow]
    by_cases hr0 : r = 0 <;> simp [hr0] <;> field_simp <;> ring
  rw [hreal] at hsum
  have hfin := (Complex.continuous_re.tendsto (((normalCastLaw b L r : ℝ)) : ℂ)).comp
    (Filter.Tendsto.congr (fun N => (hcount N).symm) hsum)
  simpa [Function.comp_def] using hfin

/-- **`ConjC1` from the fixed-modulus autocorrelation leaf.** -/
theorem conjC1_of_hAutoCorr (h : ∀ b, 3 ≤ b → HAutoCorr b) : ConjC1 :=
  conjC1_of_hState fun b hb L => stateLaw_of_hAutoCorr b hb (h b hb) L

/-! #### The leaf is EXACT: `HAutoCorr` is equivalent to `ConjC1`

Expanding the autocorrelation over the fibres of `castState` turns `corrSum` into the finite
Fourier transform of `stateFreq`, so `StateLaw` gives the autocorrelation back.  Hence no strength
whatever is lost in passing to `HAutoCorr`: it is `ConjC1`, re-coordinatised. -/

/-- `corrSum` is the finite Fourier transform of `stateFreq`, for every `N`. -/
theorem corrSum_eq_sum_stateFreq (b : ℕ) (hb : 3 ≤ b) (j L N : ℕ) :
    corrSum b j L N
      = ∑ r ∈ range (b - 1), (stateFreq b L ((r : ℕ) : ZMod (b - 1)) N : ℂ) *
          zetaRoot (b - 1) ^ ((j : ℤ) * (r : ℤ)) := by
  classical
  let q : ℕ := b - 1
  have hq : q = b - 1 := rfl
  have hqpos : 0 < q := by omega
  haveI : NeZero q := ⟨by omega⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [corrSum, stateFreq]
  have hNC : ((N : ℂ)) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  set D : ℕ → ℤ := fun n => castSum b (n + L) - castSum b n with hD
  have hcs : corrSum b j L N
      = (∑ n ∈ range N, zetaRoot q ^ ((j : ℤ) * D n)) / N := by rw [corrSum, hD]
  -- the fibre map
  have hmaps : ∀ n ∈ range N, (castState b L n).val ∈ range q :=
    fun n _ => Finset.mem_range.mpr (ZMod.val_lt _)
  have hval : ∀ (r : ℕ), r < q → ∀ n : ℕ,
      ((castState b L n).val = r ↔ castState b L n = ((r : ℕ) : ZMod q)) := by
    intro r hr n
    constructor
    · intro h; rw [← h, ZMod.natCast_val, ZMod.cast_id]
    · intro h; rw [h, ZMod.val_natCast_of_lt hr]
  -- on a fibre the character is constant
  have hconst : ∀ (r : ℕ), r < q → ∀ n : ℕ, castState b L n = ((r : ℕ) : ZMod q) →
      zetaRoot q ^ ((j : ℤ) * D n) = zetaRoot q ^ ((j : ℤ) * (r : ℤ)) := by
    intro r hr n hn
    have hdvd : ((q : ℤ)) ∣ (D n - (r : ℤ)) := by
      have : ((D n : ℤ) : ZMod q) = ((r : ℤ) : ZMod q) := by
        rw [← castState_eq_castSum_sub b L n] at *
        rw [hn]; push_cast; ring
      rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd] at this
      exact (dvd_sub_comm).mp this
    obtain ⟨c, hc⟩ := hdvd
    rw [show (j : ℤ) * D n = (j : ℤ) * (r : ℤ) + (q : ℤ) * ((j : ℤ) * c) by
      have : D n = (r : ℤ) + (q : ℤ) * c := by omega
      rw [this]; ring, zpow_add₀ (zetaRoot_ne_zero q),
      zpow_mul (zetaRoot q) (q : ℤ) ((j : ℤ) * c),
      (zetaRoot_zpow_eq_one_iff q hqpos (q : ℤ)).mpr dvd_rfl, one_zpow, mul_one]
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => zetaRoot q ^ ((j : ℤ) * D n))
  rw [hcs, ← hfib, Finset.sum_div]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrq : r < q := Finset.mem_range.mp hr
  have hfilt : (range N).filter (fun n => (castState b L n).val = r)
      = (range N).filter (fun n => castState b L n = ((r : ℕ) : ZMod q)) :=
    Finset.filter_congr fun n _ => by simpa using (hval r hrq n)
  rw [hfilt, Finset.sum_congr rfl (fun n hn =>
    hconst r hrq n (Finset.mem_filter.mp hn).2), Finset.sum_const, stateFreq]
  push_cast
  rw [nsmul_eq_mul]
  ring

/-- **The model's Fourier transform.**  `normalCastLaw b L ·`, transformed at a nontrivial
character of `ZMod (b−1)`, is exactly `b^{−L}`.  This is the identity that FORCES the leaf's
constant, and it is proved from `normalCastLaw_closed` alone — a purely finite, combinatorial
statement about `L` independent uniform base-`b` digits.  `mean_zetaRoot_block` derives the same
constant a second, independent way, as the mean value of the test function over `[0,1)`. -/
theorem fourier_normalCastLaw (b : ℕ) (hb : 3 ≤ b) (L j : ℕ) (hj : 0 < j) (hjq : j < b - 1) :
    (∑ r ∈ range (b - 1),
        ((normalCastLaw b L r : ℝ) : ℂ) * zetaRoot (b - 1) ^ ((j : ℤ) * (r : ℤ)))
      = ((b : ℂ))⁻¹ ^ L := by
  classical
  set q := b - 1 with hq
  have hqpos : 0 < q := by omega
  have hqC : ((q : ℂ)) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hbC : ((b : ℂ)) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hqC' : ((b : ℂ)) - 1 = (q : ℂ) := by
    have : ((q : ℕ) : ℂ) = ((b - 1 : ℕ) : ℂ) := by rw [hq]
    rw [this, Nat.cast_sub (by omega : 1 ≤ b)]; norm_num
  have hgeom : (∑ r ∈ range q, zetaRoot q ^ ((j : ℤ) * (r : ℤ))) = 0 := by
    have hswap : (∑ r ∈ range q, zetaRoot q ^ ((j : ℤ) * (r : ℤ)))
        = ∑ r ∈ range q, zetaRoot q ^ ((r : ℤ) * (j : ℤ)) :=
      Finset.sum_congr rfl fun r _ => by rw [mul_comm]
    rw [hswap, sum_zetaRoot_zpow q hqpos, if_neg]
    intro hdvd
    have := Int.le_of_dvd (by exact_mod_cast hj) hdvd
    omega
  have hcl : ∀ r ∈ range q, ((normalCastLaw b L r : ℝ) : ℂ)
      = (q : ℂ)⁻¹ + ((b : ℂ) ^ L)⁻¹ * ((if r = 0 then (q : ℂ) else 0) - 1) * (q : ℂ)⁻¹ := by
    intro r hr
    have hrq : r < b - 1 := by rw [← hq]; exact Finset.mem_range.mp hr
    rw [normalCastLaw_closed b L r hb hrq]
    push_cast
    rw [← hqC']
    rcases eq_or_ne r 0 with rfl | hr0
    · norm_num
      ring
    · norm_num [hr0]
      ring
  rw [Finset.sum_congr rfl fun r hr => by rw [hcl r hr]]
  have hexp : ∀ r ∈ range q,
      ((q : ℂ)⁻¹ + ((b : ℂ) ^ L)⁻¹ * ((if r = 0 then (q : ℂ) else 0) - 1) * (q : ℂ)⁻¹)
        * zetaRoot q ^ ((j : ℤ) * (r : ℤ))
      = ((q : ℂ)⁻¹ - ((b : ℂ) ^ L)⁻¹ * (q : ℂ)⁻¹) * zetaRoot q ^ ((j : ℤ) * (r : ℤ))
        + (if r = 0 then ((b : ℂ) ^ L)⁻¹ else 0) := by
    intro r _
    rcases eq_or_ne r 0 with rfl | hr0
    · rw [if_pos rfl, if_pos rfl]
      simp only [Nat.cast_zero, mul_zero, zpow_zero]
      field_simp
      ring
    · rw [if_neg hr0, if_neg hr0]; ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hgeom, mul_zero,
    zero_add, Finset.sum_ite_eq' (range q) 0 (fun _ => ((b : ℂ) ^ L)⁻¹),
    if_pos (Finset.mem_range.mpr hqpos), inv_pow]

/-- **The converse.**  `StateLaw` at every `L` gives the autocorrelation spectrum. -/
theorem hAutoCorr_of_stateLaw (b : ℕ) (hb : 3 ≤ b) (h : ∀ L, StateLaw b L) : HAutoCorr b := by
  classical
  set q := b - 1 with hq
  have hqpos : 0 < q := by omega
  have hqC : ((q : ℂ)) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hbC : ((b : ℂ)) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hqC' : ((b : ℂ)) - 1 = (q : ℂ) := by
    have : ((q : ℕ) : ℂ) = ((b - 1 : ℕ) : ℂ) := by rw [hq]
    rw [this, Nat.cast_sub (by omega : 1 ≤ b)]; norm_num
  intro jj hjj hjjq L
  -- the nontrivial character sums to zero
  have hgeom : (∑ r ∈ range q, zetaRoot q ^ ((jj : ℤ) * (r : ℤ))) = 0 := by
    have hswap : (∑ r ∈ range q, zetaRoot q ^ ((jj : ℤ) * (r : ℤ)))
        = ∑ r ∈ range q, zetaRoot q ^ ((r : ℤ) * (jj : ℤ)) :=
      Finset.sum_congr rfl fun r _ => by rw [mul_comm]
    rw [hswap, sum_zetaRoot_zpow q hqpos, if_neg]
    intro hdvd
    have := Int.le_of_dvd (by exact_mod_cast hjj) hdvd
    omega
  -- termwise limits
  have hterm : ∀ r ∈ range q, Tendsto (fun N : ℕ =>
      ((stateFreq b L ((r : ℕ) : ZMod q) N : ℂ) * zetaRoot q ^ ((jj : ℤ) * (r : ℤ)))) atTop
      (𝓝 (((normalCastLaw b L r : ℝ) : ℂ) * zetaRoot q ^ ((jj : ℤ) * (r : ℤ)))) := by
    intro r hr
    have hlim := h L r (by rw [← hq]; exact Finset.mem_range.mp hr)
    exact (Complex.continuous_ofReal.tendsto _ |>.comp hlim).mul tendsto_const_nhds
  have hsum := tendsto_finsetSum _ hterm
  -- evaluate
  have hval : (∑ r ∈ range q, ((normalCastLaw b L r : ℝ) : ℂ) * zetaRoot q ^ ((jj : ℤ) * (r : ℤ)))
      = ((b : ℂ))⁻¹ ^ L := by
    rw [hq]
    exact fourier_normalCastLaw b hb L jj hjj hjjq
  rw [hval] at hsum
  exact Filter.Tendsto.congr (fun N => (corrSum_eq_sum_stateFreq b hb jj L N).symm) hsum

/-- **`ConjC1` ⟺ the fixed-modulus autocorrelation leaf.**  The reduction is EXACT. -/
theorem conjC1_iff_hAutoCorr : ConjC1 ↔ ∀ b, 3 ≤ b → HAutoCorr b := by
  refine ⟨fun h b hb => hAutoCorr_of_stateLaw b hb fun L => ?_, conjC1_of_hAutoCorr⟩
  exact (castLaw_iff_stateLaw b (by omega) L).mp (h b hb L)

/-! #### The leaf is weak equidistribution of the `×b`-orbit against `b^L`-step functions

`A_{n+L} = b^L A_n + W_n` with `W_n = ⌊b^L · fract(b^n x)⌋ ∈ [0, b^L)` the window word, and
`b^L − 1 ≡ 0 (mod b−1)`, so

    A_{n+L} − A_n  ≡  W_n  =  ⌊b^L · fract(b^n x)⌋   (mod b − 1).

Hence the leaf is exactly: the orbit `t_n = fract(b^n x)` equidistributes against the `b^L`-step
test functions `t ↦ ζ_{b−1}^{j·⌊b^L t⌋}`, whose mean value over `[0,1)` is

    (1/b^L) Σ_{v < b^L} ζ_{b−1}^{jv}  =  b^{−L},

because `Σ_{v < b^L} ζ_{b−1}^{jv} = 1`: the `b^L` terms are `(b^L − 1)/(b−1)` complete periods,
which cancel, plus one leftover term `ζ^{j(b^L−1)} = 1`.  So the constant `b^{−L}` is not an
artefact of the model — it is the integral of the test function, computed here independently of
`normalCastLaw_closed`.  This also pins the leaf's exact strength: full normality of `G4_b` would be
equidistribution against ALL Riemann-integrable test functions; the leaf needs only these. -/

/-- `⌊m·y⌋ = m⌊y⌋ + ⌊m·fract y⌋` for a natural multiplier. -/
lemma floor_nat_mul_eq (m : ℕ) (y : ℝ) :
    ⌊(m : ℝ) * y⌋ = (m : ℤ) * ⌊y⌋ + ⌊(m : ℝ) * Int.fract y⌋ := by
  have h : (m : ℝ) * y = (m : ℝ) * Int.fract y + (((m : ℤ) * ⌊y⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.floor_add_intCast, add_comm]

/-- **The window word is the orbit's truncation.**  `A_{n+L} − b^L·A_n = ⌊b^L·fract(b^n x)⌋`. -/
theorem floor_sub_eq_floor_fract (b : ℕ) (_hb : 2 ≤ b) (L n : ℕ) :
    ⌊primeLambertAtBase b * (b : ℝ) ^ (n + L)⌋
        - (b : ℤ) ^ L * ⌊primeLambertAtBase b * (b : ℝ) ^ n⌋
      = ⌊((b : ℝ)) ^ L * Int.fract (primeLambertAtBase b * (b : ℝ) ^ n)⌋ := by
  have hpow : primeLambertAtBase b * (b : ℝ) ^ (n + L)
      = ((b ^ L : ℕ) : ℝ) * (primeLambertAtBase b * (b : ℝ) ^ n) := by
    push_cast
    rw [pow_add]
    ring
  rw [hpow, floor_nat_mul_eq (b ^ L) (primeLambertAtBase b * (b : ℝ) ^ n)]
  push_cast
  ring

/-- `Σ_{v < b^L} ζ_{b−1}^{jv} = 1` for a nontrivial `j`: the complete periods cancel and one
leftover term survives.  This is casting out nines in Fourier form. -/
theorem sum_zetaRoot_range_pow (b : ℕ) (hb : 3 ≤ b) (L j : ℕ) (hj : 0 < j) (hjq : j < b - 1) :
    (∑ v ∈ range (b ^ L), zetaRoot (b - 1) ^ ((j : ℤ) * (v : ℤ))) = 1 := by
  classical
  set q := b - 1 with hq
  have hqpos : 0 < q := by omega
  set z : ℂ := zetaRoot q ^ ((j : ℤ)) with hz
  have hzpow : ∀ v : ℕ, zetaRoot q ^ ((j : ℤ) * (v : ℤ)) = z ^ v := by
    intro v
    rw [hz, ← zpow_natCast (zetaRoot q ^ ((j : ℤ))) v, ← zpow_mul]
  have hzne : z ≠ 1 := by
    rw [hz]
    intro hcon
    have := (zetaRoot_zpow_eq_one_iff q hqpos (j : ℤ)).mp hcon
    obtain ⟨c, hc⟩ := this
    have hjq' : (j : ℤ) < (q : ℤ) := by exact_mod_cast (by omega : j < q)
    have hj' : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
    have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hqpos
    rcases lt_trichotomy c 0 with h | h | h
    · nlinarith
    · simp [h] at hc; omega
    · nlinarith
  -- `z^q = 1`, so `z^(b^L - 1) = 1` since `q ∣ b^L - 1`
  have hzq : z ^ q = 1 := by
    rw [hz, ← zpow_natCast (zetaRoot q ^ ((j : ℤ))) q, ← zpow_mul]
    exact (zetaRoot_zpow_eq_one_iff q hqpos _).mpr ⟨(j : ℤ), by ring⟩
  have hdvd : q ∣ b ^ L - 1 := by
    rw [hq]
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow b 1 L
  obtain ⟨m, hm⟩ := hdvd
  have hbL : 1 ≤ b ^ L := Nat.one_le_pow _ _ (by omega)
  have hsplit : b ^ L = (b ^ L - 1) + 1 := by omega
  rw [Finset.sum_congr rfl fun v _ => hzpow v, hsplit, geom_sum_eq hzne, pow_succ,
    show z ^ (b ^ L - 1) = 1 by rw [hm, pow_mul, hzq, one_pow], one_mul,
    div_self (sub_ne_zero.mpr hzne)]

/-- **The constant `b^{−L}` is the mean value of the test function.**  Model-free derivation. -/
theorem mean_zetaRoot_block (b : ℕ) (hb : 3 ≤ b) (L j : ℕ) (hj : 0 < j) (hjq : j < b - 1) :
    (((b : ℂ)) ^ L)⁻¹ * (∑ v ∈ range (b ^ L), zetaRoot (b - 1) ^ ((j : ℤ) * (v : ℤ)))
      = ((b : ℂ))⁻¹ ^ L := by
  rw [sum_zetaRoot_range_pow b hb L j hj hjq, mul_one, inv_pow]

/-! #### `ω` disappears: the potential `T` is the integer part of the `×b` orbit

Casting out nines on the integer `⌊b^n x⌋ = Σ_{m ≤ n} d_m b^{n−m}` gives `⌊b^n x⌋ ≡ Σ_{m≤n} d_m`
mod `b − 1`, and the `d`'s telescope to `T`.  So

    T(n)  ≡  ⌊b^n · G4_b⌋   (mod b − 1),

and the leaf `HAutoCorr` can be stated with NO reference to `ω`, the carry, or the digits: it is a
property of the integer parts of the `×b`-orbit of the single real number `G4_b`.  This is the form
to hand to an auditor, and the form in which the hypothesis is comparable with the repo's Weyl-side
objects (`floor_mul_pow_eq_windowVal`, `zetaRoot_windowVal_eq`). -/

/-- `b ≡ 1` in `ZMod (b − 1)` — casting out nines, as a cast lemma. -/
lemma natCast_base_eq_one (b : ℕ) (hb : 1 ≤ b) : ((b : ℕ) : ZMod (b - 1)) = 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, b = q + 1 := ⟨b - 1, by omega⟩
  have : q + 1 - 1 = q := by omega
  rw [this]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- **`T(n) ≡ ⌊b^n · G4_b⌋ (mod b − 1)`.**  The potential of the leaf is the integer part of the
`×b`-orbit, cast out mod `b − 1`; every trace of `ω` and of the carry cancels. -/
theorem castSum_cast_eq_floor (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    ((castSum b n : ℤ) : ZMod (b - 1))
      = ((⌊primeLambertAtBase b * (b : ℝ) ^ n⌋ : ℤ) : ZMod (b - 1)) := by
  have hfloor := floor_mul_pow_eq_windowVal b hb 0 n
  simp only [Nat.add_zero, pow_zero, one_mul] at hfloor
  have hw : omegaWindowVal b 0 n = omegaCarry b n := by
    simp [omegaWindowVal, omegaHead]
  rw [hw] at hfloor
  rw [hfloor, castSum]
  push_cast
  -- `b^k ≡ 1`, so the positional sum collapses to the plain sum
  have hb1 : ((b : ℕ) : ZMod (b - 1)) = 1 := natCast_base_eq_one b (by omega)
  have hcollapse : ∀ m ∈ range (n + 1),
      ((omegaNat m : ZMod (b - 1))) * ((b : ZMod (b - 1))) ^ (n - m)
        = ((omegaNat m : ZMod (b - 1))) := by
    intro m _
    rw [show ((b : ℕ) : ZMod (b - 1)) = 1 from hb1, one_pow, mul_one]
  rw [Finset.sum_congr rfl hcollapse]

/-- The leaf, with `ω` eliminated: the correlation of `n ↦ ζ_{b−1}^{j·⌊b^n·G4_b⌋}`. -/
noncomputable def floorCorrSum (b j L N : ℕ) : ℂ :=
  (∑ n ∈ range N, zetaRoot (b - 1) ^
    ((j : ℤ) * (⌊primeLambertAtBase b * (b : ℝ) ^ (n + L)⌋
      - ⌊primeLambertAtBase b * (b : ℝ) ^ n⌋))) / N

/-- **The two forms of the leaf agree, for every `N`.** -/
theorem floorCorrSum_eq_corrSum (b : ℕ) (hb : 2 ≤ b) (j L N : ℕ) :
    floorCorrSum b j L N = corrSum b j L N := by
  have hqpos : 0 < b - 1 := by omega
  rw [floorCorrSum, corrSum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  -- the exponents agree mod `b − 1`
  have hA := castSum_cast_eq_floor b hb (n + L)
  have hB := castSum_cast_eq_floor b hb n
  have hdvd : ((b - 1 : ℕ) : ℤ) ∣
      ((⌊primeLambertAtBase b * (b : ℝ) ^ (n + L)⌋ - ⌊primeLambertAtBase b * (b : ℝ) ^ n⌋)
        - (castSum b (n + L) - castSum b n)) := by
    have : (((⌊primeLambertAtBase b * (b : ℝ) ^ (n + L)⌋
        - ⌊primeLambertAtBase b * (b : ℝ) ^ n⌋)
        - (castSum b (n + L) - castSum b n) : ℤ) : ZMod (b - 1)) = 0 := by
      push_cast
      rw [← hA, ← hB]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  obtain ⟨c, hc⟩ := hdvd
  have hsplit : (j : ℤ) * (⌊primeLambertAtBase b * (b : ℝ) ^ (n + L)⌋
      - ⌊primeLambertAtBase b * (b : ℝ) ^ n⌋)
      = (j : ℤ) * (castSum b (n + L) - castSum b n)
        + ((b - 1 : ℕ) : ℤ) * ((j : ℤ) * c) := by
    linear_combination (j : ℤ) * hc
  rw [hsplit, zpow_add₀ (zetaRoot_ne_zero (b - 1)),
    zpow_mul (zetaRoot (b - 1)) (((b - 1 : ℕ)) : ℤ) ((j : ℤ) * c),
    (zetaRoot_zpow_eq_one_iff (b - 1) hqpos (((b - 1 : ℕ)) : ℤ)).mpr dvd_rfl, one_zpow, mul_one]

/-- **The leaf in `x`-only form.**  `ConjC1` says exactly this about the `×b`-orbit of `G4_b`. -/
def HFloorCorr (b : ℕ) : Prop :=
  ∀ j, 0 < j → j < b - 1 → ∀ L, Tendsto (floorCorrSum b j L) atTop (𝓝 (((b : ℂ))⁻¹ ^ L))

theorem hFloorCorr_iff_hAutoCorr (b : ℕ) (hb : 2 ≤ b) : HFloorCorr b ↔ HAutoCorr b := by
  constructor <;> intro h j hj hjq L
  · exact Filter.Tendsto.congr (fun N => floorCorrSum_eq_corrSum b hb j L N) (h j hj hjq L)
  · exact Filter.Tendsto.congr (fun N => (floorCorrSum_eq_corrSum b hb j L N).symm) (h j hj hjq L)

/-- **`ConjC1` ⟺ an `ω`-free statement about the `×b`-orbit of `G4_b`.** -/
theorem conjC1_iff_hFloorCorr : ConjC1 ↔ ∀ b, 3 ≤ b → HFloorCorr b := by
  rw [conjC1_iff_hAutoCorr]
  exact ⟨fun h b hb => (hFloorCorr_iff_hAutoCorr b (by omega)).mpr (h b hb),
    fun h b hb => (hFloorCorr_iff_hAutoCorr b (by omega)).mp (h b hb)⟩

/-- The orbit form of the leaf: the average of the `b^L`-step test function
`t ↦ ζ_{b−1}^{j·⌊b^L t⌋}` along the orbit `t_n = fract(b^n·G4_b)`. -/
noncomputable def orbitCorrSum (b j L N : ℕ) : ℂ :=
  (∑ n ∈ range N, zetaRoot (b - 1) ^
    ((j : ℤ) * ⌊((b : ℝ)) ^ L * Int.fract (primeLambertAtBase b * (b : ℝ) ^ n)⌋)) / N

/-- **The orbit form equals the leaf, for every `N`.**  `A_{n+L} − A_n = (b^L−1)A_n + W_n` and
`b − 1 ∣ b^L − 1`, so the long-range part of the orbit is annihilated by the modulus. -/
theorem orbitCorrSum_eq_floorCorrSum (b : ℕ) (hb : 2 ≤ b) (j L N : ℕ) :
    orbitCorrSum b j L N = floorCorrSum b j L N := by
  have hqpos : 0 < b - 1 := by omega
  rw [orbitCorrSum, floorCorrSum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  set A : ℤ := ⌊primeLambertAtBase b * (b : ℝ) ^ n⌋ with hA
  have hW := floor_sub_eq_floor_fract b hb L n
  -- `b − 1 ∣ b^L − 1`
  obtain ⟨m, hm⟩ : ((b : ℤ) - 1) ∣ ((b : ℤ) ^ L - 1) := by
    simpa using sub_dvd_pow_sub_pow (b : ℤ) 1 L
  have hqz : (((b - 1 : ℕ)) : ℤ) = (b : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ b)]; norm_num
  have hsplit : (j : ℤ) * (⌊primeLambertAtBase b * (b : ℝ) ^ (n + L)⌋ - A)
      = (j : ℤ) * ⌊((b : ℝ)) ^ L * Int.fract (primeLambertAtBase b * (b : ℝ) ^ n)⌋
        + (((b - 1 : ℕ)) : ℤ) * ((j : ℤ) * (m * A)) := by
    rw [hqz]
    linear_combination (j : ℤ) * hW + (j : ℤ) * A * hm
  rw [hsplit, zpow_add₀ (zetaRoot_ne_zero (b - 1)),
    zpow_mul (zetaRoot (b - 1)) (((b - 1 : ℕ)) : ℤ) ((j : ℤ) * (m * A)),
    (zetaRoot_zpow_eq_one_iff (b - 1) hqpos (((b - 1 : ℕ)) : ℤ)).mpr dvd_rfl, one_zpow, mul_one]

/-- **The leaf as weak equidistribution.**  The `×b`-orbit of `G4_b` averages the `b^L`-step test
functions `t ↦ ζ_{b−1}^{j·⌊b^L t⌋}` to their mean values `b^{−L}` (`mean_zetaRoot_block`).  Full
normality of `G4_b` would be this for ALL Riemann-integrable test functions; `ConjC1` needs only
these finitely many per `L`. -/
def HOrbit (b : ℕ) : Prop :=
  ∀ j, 0 < j → j < b - 1 → ∀ L, Tendsto (orbitCorrSum b j L) atTop (𝓝 (((b : ℂ))⁻¹ ^ L))

theorem hOrbit_iff_hAutoCorr (b : ℕ) (hb : 2 ≤ b) : HOrbit b ↔ HAutoCorr b := by
  have hcongr : ∀ j L N, orbitCorrSum b j L N = corrSum b j L N := fun j L N => by
    rw [orbitCorrSum_eq_floorCorrSum b hb j L N, floorCorrSum_eq_corrSum b hb j L N]
  constructor <;> intro h j hj hjq L
  · exact Filter.Tendsto.congr (fun N => hcongr j L N) (h j hj hjq L)
  · exact Filter.Tendsto.congr (fun N => (hcongr j L N).symm) (h j hj hjq L)

/-- **`ConjC1` ⟺ weak equidistribution of the `×b`-orbit against `b^L`-step functions.** -/
theorem conjC1_iff_hOrbit : ConjC1 ↔ ∀ b, 3 ≤ b → HOrbit b := by
  rw [conjC1_iff_hAutoCorr]
  exact ⟨fun h b hb => (hOrbit_iff_hAutoCorr b (by omega)).mpr (h b hb),
    fun h b hb => (hOrbit_iff_hAutoCorr b (by omega)).mp (h b hb)⟩


/-! #### The Weyl bridge at INTEGER frequency

`ζ_{b−1}^{j·A_n} = e(j·b^n x/(b−1)) · e(−j·t_n/(b−1))` exactly, since `A_n = b^n x − t_n`.  Taking the
lag-`L` difference, the two denominators `b − 1` combine with `b^L − 1`, and

    (b^L − 1)/(b − 1) = 1 + b + ⋯ + b^{L−1} =: σ_L  ∈ ℕ,

so the denominator disappears completely:

    ζ_{b−1}^{j(A_{n+L} − A_n)}  =  e(j·σ_L·b^n·x) · e(−j(t_{n+L} − t_n)/(b−1)).

The first factor is a classical Weyl exponential at the INTEGER frequency `j·σ_L`, exactly the shape
the repo's `G4WiringCRT` layer controls (`fullWindowMean`, `WindowDecay`, `isNormal_G4_of_windowDecay`);
the second is a unimodular twist depending only on the fractional parts.  This supersedes the old
bridge `zetaRoot_windowVal_eq`, whose frequencies were the non-integral `a/b^L`. -/

/-- `σ_L = 1 + b + ⋯ + b^{L−1}`, the integer `(b^L − 1)/(b − 1)`. -/
def geomNat (b L : ℕ) : ℕ := ∑ i ∈ range L, b ^ i

lemma sub_one_mul_geomNat (b : ℕ) (L : ℕ) :
    ((b : ℤ) - 1) * (geomNat b L : ℤ) = (b : ℤ) ^ L - 1 := by
  induction L with
  | zero => simp [geomNat]
  | succ L ih =>
      rw [geomNat, Finset.sum_range_succ, ← geomNat]
      push_cast
      rw [mul_add, ih]
      ring

/-- **`ζ_{b−1}^{j·⌊b^n x⌋` splits into a Weyl exponential and a tail twist.** -/
theorem zetaRoot_floor_eq (b : ℕ) (hb : 2 ≤ b) (j n : ℕ) :
    zetaRoot (b - 1) ^ ((j : ℤ) * ⌊primeLambertAtBase b * (b : ℝ) ^ n⌋)
      = Complex.exp (2 * Real.pi * Complex.I *
            ((j : ℂ) * (((b : ℝ) ^ n * primeLambertAtBase b : ℝ) : ℂ)) / ((b : ℂ) - 1))
        * Complex.exp (-(2 * Real.pi * Complex.I *
            ((j : ℂ) * ((Int.fract (primeLambertAtBase b * (b : ℝ) ^ n) : ℝ) : ℂ))
              / ((b : ℂ) - 1))) := by
  have hqz : (((b - 1 : ℕ)) : ℂ) = (b : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ b)]; norm_num
  have hqne : ((b : ℂ)) - 1 ≠ 0 := by
    rw [← hqz]
    have : ((b - 1 : ℕ)) ≠ 0 := by omega
    exact_mod_cast this
  set y : ℝ := primeLambertAtBase b * (b : ℝ) ^ n with hy
  have hfl : ((⌊y⌋ : ℤ) : ℂ) = ((y : ℝ) : ℂ) - ((Int.fract y : ℝ) : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) (Int.self_sub_fract y)
    push_cast at this ⊢
    linear_combination -this
  rw [zetaRoot_zpow, ← Complex.exp_add, hqz]
  congr 1
  have hyC : ((y : ℝ) : ℂ) = (((b : ℝ) ^ n * primeLambertAtBase b : ℝ) : ℂ) := by
    rw [hy]; push_cast; ring
  push_cast
  rw [hfl, hyC]
  field_simp
  push_cast
  ring

/-- **The leaf's character sum is a Weyl sum at the integer frequency `j·σ_L`, twisted.** -/
theorem zetaRoot_floor_diff_eq (b : ℕ) (hb : 2 ≤ b) (j L n : ℕ) :
    zetaRoot (b - 1) ^ ((j : ℤ) * (⌊primeLambertAtBase b * (b : ℝ) ^ (n + L)⌋
        - ⌊primeLambertAtBase b * (b : ℝ) ^ n⌋))
      = Complex.exp (2 * Real.pi * Complex.I *
            ((j * geomNat b L : ℕ) : ℂ) * (((b : ℝ) ^ n * primeLambertAtBase b : ℝ) : ℂ))
        * Complex.exp (-(2 * Real.pi * Complex.I * (j : ℂ) *
            ((((Int.fract (primeLambertAtBase b * (b : ℝ) ^ (n + L))
              - Int.fract (primeLambertAtBase b * (b : ℝ) ^ n) : ℝ)) : ℂ)) / ((b : ℂ) - 1))) := by
  have hqz : (((b - 1 : ℕ)) : ℂ) = (b : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ b)]; norm_num
  have hqne : ((b : ℂ)) - 1 ≠ 0 := by
    rw [← hqz]
    have : ((b - 1 : ℕ)) ≠ 0 := by omega
    exact_mod_cast this
  have hgeo : ((b : ℂ)) ^ L - 1 = ((b : ℂ) - 1) * ((geomNat b L : ℕ) : ℂ) := by
    have := congrArg (fun z : ℤ => (z : ℂ)) (sub_one_mul_geomNat b L)
    push_cast at this ⊢
    linear_combination -this
  rw [mul_sub, zpow_sub₀ (zetaRoot_ne_zero (b - 1)), zetaRoot_floor_eq b hb j (n + L),
    zetaRoot_floor_eq b hb j n]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub, ← Complex.exp_add]
  congr 1
  have hpow : (((b : ℝ) ^ (n + L) * primeLambertAtBase b : ℝ) : ℂ)
      = ((b : ℂ)) ^ L * (((b : ℝ) ^ n * primeLambertAtBase b : ℝ) : ℂ) := by
    push_cast; rw [pow_add]; ring
  rw [hpow]
  push_cast
  field_simp
  ring_nf
  linear_combination (j : ℂ) * ((b : ℂ)) ^ n * ((primeLambertAtBase b : ℝ) : ℂ) * hgeo

/-! #### The crux, named: the digit character has factorizing multiple correlations

Put `D_j(n) := ζ_{b−1}^{j·d_{n+1}} = ζ_{b−1}^{j(T(n+1) − T(n))}`, a unimodular sequence (`d_{n+1}` is
the `(n+1)`-st base-`b` digit of `G4_b`).  Telescoping `T` turns the lag-`L` correlation into an
`L`-fold shifted PRODUCT:

    ζ_{b−1}^{j(T(n+L) − T(n))}  =  ∏_{i < L} D_j(n + i),

so the leaf says exactly that the `L`-fold multiple correlation of `D_j` equals the `L`-th power of
its own mean `1/b`:

    lim_N (1/N) Σ_{n<N} ∏_{i<L} D_j(n+i)  =  (1/b)^L  =  (lim_N (1/N) Σ_{n<N} D_j(n))^L.

That is precisely the shape of the Chowla/Elliott-type hypotheses: a unimodular arithmetic sequence
whose multiple correlations factorize as products of one-point means.  The `L = 1` case fixes the
mean at `1/b`; every `L ≥ 2` is an independence-across-shifts assertion.  Recording this is the
kickoff's step 4: the leaf IS an Elliott-type statement, not a weaker classical one — the
one-coordinate mean is Delange's theorem, but the factorization over shifts is open. -/

/-- `D_j(n) = ζ_{b−1}^{j·d_{n+1}}`, the character of the `(n+1)`-st base-`b` digit of `G4_b`. -/
noncomputable def digitChar (b j n : ℕ) : ℂ :=
  zetaRoot (b - 1) ^ ((j : ℤ) * (castSum b (n + 1) - castSum b n))

lemma norm_digitChar (b j n : ℕ) : ‖digitChar b j n‖ = 1 := norm_zetaRoot_zpow _ _

/-- **Telescoping.**  The lag-`L` correland is the `L`-fold shifted product of `D_j`. -/
theorem prod_digitChar (b j L n : ℕ) :
    (∏ i ∈ range L, digitChar b j (n + i))
      = zetaRoot (b - 1) ^ ((j : ℤ) * (castSum b (n + L) - castSum b n)) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.prod_range_succ, ih, digitChar,
        ← zpow_add₀ (zetaRoot_ne_zero (b - 1))]
      congr 1
      rw [show n + L + 1 = n + (L + 1) by omega]
      ring

/-- **The leaf is a multiple-correlation statement.**  `corrSum` is the mean of the `L`-fold
shifted product of the unimodular sequence `D_j`. -/
theorem corrSum_eq_mean_prod (b j L N : ℕ) :
    corrSum b j L N = (∑ n ∈ range N, ∏ i ∈ range L, digitChar b j (n + i)) / N := by
  rw [corrSum]
  congr 1
  exact (Finset.sum_congr rfl fun n _ => prod_digitChar b j L n).symm

/-- The Chowla/Elliott-shaped form of the leaf: all multiple correlations of `D_j` factorize. -/
def HFactorizes (b : ℕ) : Prop :=
  ∀ j, 0 < j → j < b - 1 → ∀ L,
    Tendsto (fun N => (∑ n ∈ range N, ∏ i ∈ range L, digitChar b j (n + i)) / N)
      atTop (𝓝 (((b : ℂ))⁻¹ ^ L))

theorem hFactorizes_iff_hAutoCorr (b : ℕ) : HFactorizes b ↔ HAutoCorr b := by
  constructor <;> intro h j hj hjq L
  · exact Filter.Tendsto.congr (fun N => (corrSum_eq_mean_prod b j L N).symm) (h j hj hjq L)
  · exact Filter.Tendsto.congr (fun N => corrSum_eq_mean_prod b j L N) (h j hj hjq L)

/-- **`ConjC1` ⟺ the digit character's multiple correlations factorize.** -/
theorem conjC1_iff_hFactorizes : ConjC1 ↔ ∀ b, 3 ≤ b → HFactorizes b := by
  rw [conjC1_iff_hAutoCorr]
  exact ⟨fun h b hb => (hFactorizes_iff_hAutoCorr b).mpr (h b hb),
    fun h b hb => (hFactorizes_iff_hAutoCorr b).mp (h b hb)⟩

/-- The `L = 1` instance: the digit character's own mean is `1/b`.  (One-coordinate case.) -/
theorem mean_digitChar_of_hAutoCorr (b : ℕ) (h : HAutoCorr b) (j : ℕ)
    (hj : 0 < j) (hjq : j < b - 1) :
    Tendsto (fun N => (∑ n ∈ range N, digitChar b j n) / N) atTop (𝓝 (((b : ℂ))⁻¹)) := by
  have h1 := (hFactorizes_iff_hAutoCorr b).mpr h j hj hjq 1
  simpa using h1

/-! #### The exact split: a MULTIPLICATIVE function times a telescoping carry boundary term

Mod `b − 1` the digit recursion `d_{n+1} = ω(n+1) + c_{n+1} − b·c_n` reads
`d_{n+1} ≡ ω(n+1) + c_{n+1} − c_n`, so with

    f_j(m) := ζ_{b−1}^{j·ω(m)}      (unimodular, MULTIPLICATIVE: `omegaChar_mul_of_coprime`)
    g_j(m) := ζ_{b−1}^{j·c_m}       (the carry character, |g| = 1)

we get `D_j(n) = f_j(n+1)·g_j(n+1)·g_j(n)⁻¹`, and in the `L`-fold product the carry factors
TELESCOPE, leaving only a boundary term:

    ∏_{i<L} D_j(n+i)  =  (∏_{i<L} f_j(n+1+i)) · g_j(n+L) · g_j(n)⁻¹.

This is the sharpest localisation of the leaf against the literature.  `f_j` is exactly the kind of
object Elliott's conjecture is about: a modulus-one multiplicative function with `f_j(p) = ζ_{b−1}^j`
constant and `≠ 1`, i.e. the `ω`-analogue of `λ(n) = (−1)^{Ω(n)}`.  Its ONE-point mean vanishes by
Delange/Halász, and its shifted correlations `Σ_n ∏_{i<L} f_j(n+1+i)` are precisely the Elliott
correlations — known to vanish in logarithmic density for `L = 2` (Tao, 2015) and for odd `L`
(Tao–Teräväinen), but NOT in natural density, which is what `ConjC1` needs.

So the leaf is `Elliott correlations of an explicit multiplicative function` × `a carry boundary
term`.  Note the two cannot be separated: by `not_hAutoCorr_of_carryNegligible` the `f`-part alone
would give `0`, while the leaf needs `b^{−L}`, so the boundary term `g_j(n+L)g_j(n)⁻¹` is not a
harmless factor — it is where the whole answer comes from, and `g` is not independent of `f`
(`c_n` is a function of `ω(n+1), ω(n+2), …`). -/

/-- `f_j(m) = ζ_{b−1}^{j·ω(m)}`, a unimodular multiplicative function. -/
noncomputable def omegaChar (b j m : ℕ) : ℂ :=
  zetaRoot (b - 1) ^ ((j : ℤ) * (omegaNat m : ℤ))

/-- `g_j(m) = ζ_{b−1}^{j·c_m}`, the carry character. -/
noncomputable def carryChar (b j m : ℕ) : ℂ :=
  zetaRoot (b - 1) ^ ((j : ℤ) * omegaCarry b m)

lemma norm_omegaChar (b j m : ℕ) : ‖omegaChar b j m‖ = 1 := norm_zetaRoot_zpow _ _

lemma norm_carryChar (b j m : ℕ) : ‖carryChar b j m‖ = 1 := norm_zetaRoot_zpow _ _

lemma omegaChar_ne_zero (b j m : ℕ) : omegaChar b j m ≠ 0 := by
  rw [omegaChar]; exact zpow_ne_zero _ (zetaRoot_ne_zero _)

lemma carryChar_ne_zero (b j m : ℕ) : carryChar b j m ≠ 0 := by
  rw [carryChar]; exact zpow_ne_zero _ (zetaRoot_ne_zero _)

/-- **`f_j` is multiplicative**, because `ω` is additive on coprime arguments.  This is what makes
the leaf an Elliott-type statement rather than a generic correlation statement. -/
theorem omegaChar_mul_of_coprime (b j m m' : ℕ) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (h : Nat.Coprime m m') :
    omegaChar b j (m * m') = omegaChar b j m * omegaChar b j m' := by
  have hadd : omegaNat (m * m') = omegaNat m + omegaNat m' := by
    rw [omegaNat, omegaNat, omegaNat, h.primeFactors_mul,
      Finset.card_union_of_disjoint h.disjoint_primeFactors]
  rw [omegaChar, omegaChar, omegaChar, hadd]
  push_cast
  rw [mul_add, zpow_add₀ (zetaRoot_ne_zero (b - 1))]

/-- **The split.**  `D_j(n) = f_j(n+1)·g_j(n+1)·g_j(n)⁻¹`. -/
theorem digitChar_eq (b j n : ℕ) :
    digitChar b j n = omegaChar b j (n + 1) * carryChar b j (n + 1) * (carryChar b j n)⁻¹ := by
  have hcs : castSum b (n + 1) - castSum b n
      = (omegaNat (n + 1) : ℤ) + omegaCarry b (n + 1) - omegaCarry b n := by
    rw [castSum, castSum, Finset.sum_range_succ]
    ring
  rw [digitChar, hcs, omegaChar, carryChar, carryChar, ← zpow_neg,
    ← zpow_add₀ (zetaRoot_ne_zero (b - 1)), ← zpow_add₀ (zetaRoot_ne_zero (b - 1))]
  congr 1
  ring

lemma prod_omegaChar (b j L n : ℕ) :
    (∏ i ∈ range L, omegaChar b j (n + 1 + i))
      = zetaRoot (b - 1) ^ ((j : ℤ) * ∑ i ∈ range L, (omegaNat (n + 1 + i) : ℤ)) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.prod_range_succ, ih, omegaChar, ← zpow_add₀ (zetaRoot_ne_zero (b - 1)),
        Finset.sum_range_succ]
      congr 1
      ring

/-- **The carry telescopes.**  The `L`-fold correland is an Elliott correlation of the
multiplicative `f_j`, times a single carry boundary term. -/
theorem prod_digitChar_eq_omega_mul_boundary (b j L n : ℕ) :
    (∏ i ∈ range L, digitChar b j (n + i))
      = (∏ i ∈ range L, omegaChar b j (n + 1 + i))
          * carryChar b j (n + L) * (carryChar b j n)⁻¹ := by
  have hsum : (∑ m ∈ range (n + L + 1), (omegaNat m : ℤ))
      - (∑ m ∈ range (n + 1), (omegaNat m : ℤ))
      = ∑ i ∈ range L, (omegaNat (n + 1 + i) : ℤ) := by
    have hsum0 : (∑ m ∈ range (n + L + 1), (omegaNat m : ℤ))
        - (∑ m ∈ range (n + 1), (omegaNat m : ℤ))
        = ∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ) := by
      have hIoc : Finset.Ioc n (n + L) = Finset.Ico (n + 1) (n + L + 1) := by
        ext m; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
      rw [hIoc, Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun m => (omegaNat m : ℤ))
          (Nat.zero_le (n + 1)) (by omega : n + 1 ≤ n + L + 1)]
      ring
    rw [hsum0, sum_Ioc_omegaNat]
  rw [prod_digitChar, prod_omegaChar, carryChar, carryChar, ← zpow_neg,
    ← zpow_add₀ (zetaRoot_ne_zero (b - 1)), ← zpow_add₀ (zetaRoot_ne_zero (b - 1))]
  congr 1
  rw [castSum, castSum]
  linear_combination (j : ℤ) * hsum

/-- The leaf, as an Elliott correlation with a carry boundary term. -/
theorem corrSum_eq_elliott (b j L N : ℕ) :
    corrSum b j L N
      = (∑ n ∈ range N, (∏ i ∈ range L, omegaChar b j (n + 1 + i))
            * carryChar b j (n + L) * (carryChar b j n)⁻¹) / N := by
  rw [corrSum_eq_mean_prod]
  congr 1
  exact Finset.sum_congr rfl fun n _ => prod_digitChar_eq_omega_mul_boundary b j L n

/-! #### The block spectrum of the mod-`(b−1)` statistic is FULL — no sparse-frequency route

`stateLaw_of_hAutoCorr` expands the `ZMod (b−1)`-statistic in characters of `ZMod (b−1)`.  One might
hope instead to expand the test function `v ↦ ζ_{b−1}^{jv}` on the block alphabet `ZMod (b^L)` and
find that only a few block frequencies `a` matter — that would let the integer-frequency Weyl bridge
`zetaRoot_floor_diff_eq` close using finitely many Weyl sums.  It cannot: EVERY one of the `b^L`
coefficients is nonzero.  Concretely, with `w = ζ_{b−1}^{j}·ζ_{b^L}^{−a}`,

    Σ_{v < b^L} ζ_{b−1}^{jv} ζ_{b^L}^{−av}  =  (ζ_{b−1}^{j} − 1)/(w − 1)  ≠  0,

for every `a`, because `gcd(b−1, b^L) = 1` keeps `w ≠ 1` while `w^{b^L} = ζ_{b−1}^{j}` (using
`b^L ≡ 1 mod b−1`).  So no finite or sparse set of block frequencies carries the statistic, and any
route that needs only finitely many Weyl frequencies is dead. -/

/-- `ζ_{b−1}^{j}·ζ_{b^L}^{−a} = ζ_{(b−1)b^L}^{j b^L − a(b−1)}`: a common denominator for the two
coprime moduli. -/
lemma zetaRoot_mul_eq (b : ℕ) (hb : 2 ≤ b) (L a j v : ℕ) :
    zetaRoot (b - 1) ^ ((j : ℤ) * (v : ℤ)) * zetaRoot (b ^ L) ^ (-((a : ℤ) * (v : ℤ)))
      = zetaRoot ((b - 1) * b ^ L) ^
          (((j : ℤ) * ((b : ℤ) ^ L) - (a : ℤ) * ((b : ℤ) - 1)) * (v : ℤ)) := by
  have hq : ((b - 1 : ℕ) : ℂ) = (b : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ b)]; norm_num
  have hqne : ((b : ℂ)) - 1 ≠ 0 := by
    rw [← hq]
    have : ((b - 1 : ℕ)) ≠ 0 := by omega
    exact_mod_cast this
  have hbne : ((b : ℂ)) ^ L ≠ 0 := by
    have : ((b : ℂ)) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
    positivity
  rw [zetaRoot_zpow, zetaRoot_zpow, zetaRoot_zpow, ← Complex.exp_add]
  congr 1
  push_cast
  rw [hq]
  field_simp
  ring

/-- **The block spectrum is full.**  For every block frequency `a`, the mod-`(b−1)` test function's
coefficient on the `ZMod (b^L)` character `a` is nonzero. -/
theorem sum_zetaRoot_mixed_ne_zero (b : ℕ) (hb : 3 ≤ b) (L j a : ℕ)
    (hj : 0 < j) (hjq : j < b - 1) :
    (∑ v ∈ range (b ^ L),
      zetaRoot (b - 1) ^ ((j : ℤ) * (v : ℤ)) * zetaRoot (b ^ L) ^ (-((a : ℤ) * (v : ℤ)))) ≠ 0 := by
  classical
  set q := b - 1 with hqd
  have hqpos : 0 < q := by omega
  set Q := q * b ^ L with hQd
  have hQpos : 0 < Q := by
    have : 0 < b ^ L := Nat.pow_pos (by omega)
    exact Nat.mul_pos hqpos this
  set e : ℤ := (j : ℤ) * ((b : ℤ) ^ L) - (a : ℤ) * ((b : ℤ) - 1) with hed
  set w : ℂ := zetaRoot Q ^ e with hwd
  have hQz : ((Q : ℕ) : ℤ) = ((b : ℤ) - 1) * (b : ℤ) ^ L := by
    rw [hQd, hqd]
    push_cast [Nat.cast_sub (by omega : 1 ≤ b)]
    ring
  -- `w ≠ 1`
  have hw1 : w ≠ 1 := by
    rw [hwd]
    intro hcon
    obtain ⟨c, hc⟩ := (zetaRoot_zpow_eq_one_iff Q hQpos e).mp hcon
    -- reduce mod `b − 1`
    have hdvd : ((b : ℤ) - 1) ∣ e := by
      refine ⟨(b : ℤ) ^ L * c, ?_⟩
      rw [hc, hQz]; ring
    have hgeo := sub_one_mul_geomNat b L
    have hdj : ((b : ℤ) - 1) ∣ (j : ℤ) := by
      obtain ⟨d, hd⟩ := hdvd
      refine ⟨d + (a : ℤ) - (j : ℤ) * (geomNat b L : ℤ), ?_⟩
      have : (j : ℤ) * ((b : ℤ) ^ L) - (a : ℤ) * ((b : ℤ) - 1) = ((b : ℤ) - 1) * d := by
        rw [← hed]; exact hd
      linear_combination this + (j : ℤ) * hgeo
    have hjz : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
    have hjq' : (j : ℤ) < ((b : ℤ) - 1) := by
      have : (j : ℤ) < ((q : ℕ) : ℤ) := by exact_mod_cast (by omega : j < q)
      rw [hqd] at this
      push_cast [Nat.cast_sub (by omega : 1 ≤ b)] at this
      linarith
    have := Int.le_of_dvd hjz hdj
    linarith
  -- `w^{b^L} = ζ_{b−1}^j`
  have hqC : ((q : ℕ) : ℂ) = (b : ℂ) - 1 := by
    rw [hqd, Nat.cast_sub (by omega : 1 ≤ b)]; norm_num
  have hQC : ((Q : ℕ) : ℂ) = ((b : ℂ) - 1) * (b : ℂ) ^ L := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hQz
    push_cast at this ⊢
    linear_combination this
  have hqne : ((b : ℂ)) - 1 ≠ 0 := by
    rw [← hqC]
    have : ((q : ℕ)) ≠ 0 := by omega
    exact_mod_cast this
  have hbne : ((b : ℂ)) ^ L ≠ 0 := by
    have : ((b : ℂ)) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
    positivity
  -- the two moduli share the exponent `j·b^L` over the common denominator `Q`
  have hqQ : zetaRoot q ^ ((j : ℤ)) = zetaRoot Q ^ ((j : ℤ) * ((b : ℤ) ^ L)) := by
    rw [zetaRoot_zpow, zetaRoot_zpow]
    congr 1
    rw [hqC, hQC]
    push_cast
    field_simp
  have hwpow : w ^ (b ^ L) = zetaRoot q ^ ((j : ℤ)) := by
    have h1 : w ^ (b ^ L) = zetaRoot Q ^ (e * ((b : ℤ) ^ L)) := by
      rw [hwd, ← zpow_natCast (zetaRoot Q ^ e) (b ^ L), ← zpow_mul]
      congr 1
    obtain ⟨c, hc⟩ : ((Q : ℕ) : ℤ) ∣ (e * ((b : ℤ) ^ L) - (j : ℤ) * ((b : ℤ) ^ L)) := by
      refine ⟨(j : ℤ) * (geomNat b L : ℤ) - (a : ℤ), ?_⟩
      rw [hQz, hed]
      linear_combination (-(j : ℤ) * ((b : ℤ) ^ L)) * (sub_one_mul_geomNat b L)
    have hsplit : e * ((b : ℤ) ^ L)
        = (j : ℤ) * ((b : ℤ) ^ L) + ((Q : ℕ) : ℤ) * c := by linear_combination hc
    rw [h1, hqQ, hsplit, zpow_add₀ (zetaRoot_ne_zero Q),
      zpow_mul (zetaRoot Q) (((Q : ℕ)) : ℤ) c,
      (zetaRoot_zpow_eq_one_iff Q hQpos (((Q : ℕ)) : ℤ)).mpr dvd_rfl, one_zpow, mul_one]
  -- `ζ_{b−1}^j ≠ 1`
  have hzj : zetaRoot q ^ ((j : ℤ)) ≠ 1 := by
    intro hcon
    obtain ⟨c, hc⟩ := (zetaRoot_zpow_eq_one_iff q hqpos (j : ℤ)).mp hcon
    have hjz : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
    have hjq' : (j : ℤ) < ((q : ℕ) : ℤ) := by exact_mod_cast (by omega : j < q)
    have := Int.le_of_dvd hjz ⟨c, hc⟩
    omega
  -- geometric sum
  have hsum : (∑ v ∈ range (b ^ L),
      zetaRoot (b - 1) ^ ((j : ℤ) * (v : ℤ)) * zetaRoot (b ^ L) ^ (-((a : ℤ) * (v : ℤ))))
      = (w ^ (b ^ L) - 1) / (w - 1) := by
    rw [← geom_sum_eq hw1]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [zetaRoot_mul_eq b (by omega) L a j v, hwd,
      ← zpow_natCast (zetaRoot Q ^ e) v, ← zpow_mul]
  rw [hsum, hwpow]
  exact div_ne_zero (sub_ne_zero.mpr hzj) (sub_ne_zero.mpr hw1)

/-! #### Carry inertness: the leaf's whole content sits where `ω` reaches `b − 1`

`c_N = ⌊Σ_{k≥1} ω(N+k) b^{−k}⌋` is IDENTICALLY ZERO as long as `ω` stays `≤ b − 2` on the tail,
because then the tail is at most `(b−2)/(b−1) < 1`.  Since `ω(m) ≥ t` first happens at the `t`-th
primorial, base-`b` carrying is inert below roughly the `b`-th primorial — `6.5 · 10⁹` already at
`b = 10`.  Combined with `not_hAutoCorr_of_carryNegligible` (the carry is what produces the leaf's
`b^{−L}`), this says the leaf's entire content lives in the range where `ω` exceeds `b − 2`, and it
is why `probes/swingc1_autocorr.py` cannot test `HAutoCorr` numerically at any feasible `N`. -/

/-- If `ω ≤ B` on the tail beyond `N` then `Σ_{k≥1} ω(N+k) b^{−k} ≤ B/(b−1)`. -/
theorem omegaTail_le_of_bound (b : ℕ) (hb : 2 ≤ b) (N B : ℕ)
    (h : ∀ k : ℕ, omegaNat (N + 1 + k) ≤ B) :
    omegaTail b N ≤ (B : ℝ) / ((b : ℝ) - 1) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hinv : (1 : ℝ) / b < 1 := by
    rw [div_lt_one hb0]; linarith
  have hinv0 : (0 : ℝ) ≤ 1 / b := by positivity
  have hg : Summable (fun k : ℕ => (B : ℝ) * ((1 : ℝ) / b) ^ (k + 1)) := by
    refine Summable.mul_left _ ?_
    exact ((summable_geometric_of_lt_one hinv0 hinv).mul_left ((1 : ℝ) / b)).congr
      fun k => by rw [pow_succ]; ring
  have hterm : ∀ k : ℕ, (omegaNat (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)
      ≤ (B : ℝ) * ((1 : ℝ) / b) ^ (k + 1) := by
    intro k
    have hnum : (omegaNat (N + 1 + k) : ℝ) ≤ (B : ℝ) := by exact_mod_cast h k
    rw [div_pow, one_pow, mul_one_div, div_le_div_iff_of_pos_right (by positivity)]
    exact hnum
  refine (Summable.tsum_le_tsum hterm (summable_omegaTail b hb N) hg).trans (le_of_eq ?_)
  rw [tsum_mul_left]
  have hgeo : (∑' k : ℕ, ((1 : ℝ) / b) ^ (k + 1)) = (1 : ℝ) / ((b : ℝ) - 1) := by
    have h1 : (∑' k : ℕ, ((1 : ℝ) / b) ^ (k + 1))
        = ((1 : ℝ) / b) * ∑' k : ℕ, ((1 : ℝ) / b) ^ k := by
      rw [← tsum_mul_left]
      exact tsum_congr fun k => by rw [pow_succ]; ring
    rw [h1, tsum_geometric_of_lt_one hinv0 hinv]
    have : (1 : ℝ) - 1 / b = ((b : ℝ) - 1) / b := by field_simp
    rw [this]
    field_simp
  rw [hgeo]
  ring

/-- **Carry inertness.**  If `ω ≤ b − 2` on the whole tail beyond `N`, the carry at `N` is `0`. -/
theorem omegaCarry_eq_zero_of_omega_le (b : ℕ) (hb : 2 ≤ b) (N : ℕ)
    (h : ∀ k : ℕ, omegaNat (N + 1 + k) + 2 ≤ b) : omegaCarry b N = 0 := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  have hle := omegaTail_le_of_bound b hb N (b - 2) (fun k => by have := h k; omega)
  have hcast : ((b - 2 : ℕ) : ℝ) = (b : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ b)]; norm_num
  rw [hcast] at hle
  have hlt1 : omegaTail b N < 1 := by
    refine hle.trans_lt ?_
    rw [div_lt_one hb1]
    linarith
  have hge0 : (0 : ℝ) ≤ omegaTail b N := omegaTail_nonneg b hb N
  rw [omegaCarry_eq_floor]
  exact Int.floor_eq_zero_iff.mpr ⟨hge0, by simpa using hlt1⟩

/-! #### The carry is ESSENTIAL: a refutation of the naive independence heuristic

The natural first guess for the leaf is "`ω` is uniformly distributed mod `b − 1` (Delange 1969),
and is asymptotically independent of its own carry sequence, so the carry can be dropped".  That
guess is WRONG, and provably so: dropping the carry leaves the `ω`-only correlation

    (1/N) Σ_{n<N} ζ_{b−1}^{j·Σ_{m ∈ (n,n+L]} ω(m)},

whose limit is `0` for every nontrivial `j` — for `L = 1` that IS Delange's theorem.  But the leaf
demands `b^{−L} ≠ 0`.  So at least one of the two naive clauses fails, and since the `ω`-only clause
at `L = 1` is a theorem of Delange, it is the independence clause that must fail:
`c_{n+1} − c_n` is NOT divisible by `b − 1` on a density-one set.

Mechanistically this is forced: `c_n = ⌊(ω(n+1) + c_{n+1})/b⌋` is itself a function of `ω(n+1)`, so
`ω(n+1)` and `c_n` can never be independent.  The entire gap between the naive `0` and the true
`b^{−L}` is that coupling, which is why `ConjC1` is not a corollary of Delange. -/

/-- The `ω`-only correlation: `castState` with the carry difference deleted. -/
noncomputable def corrSumOmega (b j L N : ℕ) : ℂ :=
  (∑ n ∈ range N,
    zetaRoot (b - 1) ^ ((j : ℤ) * ∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ))) / N

/-- How often the carry difference is not annihilated by the modulus `b − 1`. -/
noncomputable def carryDiffBadCount (b L N : ℕ) : ℕ :=
  ((range N).filter
    (fun n => ¬ (((b : ℤ) - 1) ∣ (omegaCarry b (n + L) - omegaCarry b n)))).card

/-- The naive independence clause: the carry difference vanishes mod `b − 1` on a density-one set. -/
def CarryNegligible (b L : ℕ) : Prop :=
  Tendsto (fun N => (carryDiffBadCount b L N : ℝ) / N) atTop (𝓝 0)

/-- Deleting the carry changes the correlation by at most twice the bad-set frequency. -/
theorem norm_corrSum_sub_omega (b : ℕ) (hb : 3 ≤ b) (j L N : ℕ) :
    ‖corrSum b j L N - corrSumOmega b j L N‖
      ≤ 2 * (carryDiffBadCount b L N : ℝ) / N := by
  classical
  set q := b - 1 with hq
  have hqz : ((q : ℤ)) = (b : ℤ) - 1 := by
    rw [hq]; push_cast [Nat.cast_sub (by omega : 1 ≤ b)]; ring
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [corrSum, corrSumOmega, carryDiffBadCount]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqpos : 0 < q := by omega
  -- off the bad set the two characters agree
  have hoff : ∀ n : ℕ, (((b : ℤ) - 1) ∣ (omegaCarry b (n + L) - omegaCarry b n)) →
      zetaRoot q ^ ((j : ℤ) * (castSum b (n + L) - castSum b n))
        = zetaRoot q ^ ((j : ℤ) * ∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ)) := by
    intro n hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hsum : (∑ m ∈ range (n + L + 1), (omegaNat m : ℤ))
        - (∑ m ∈ range (n + 1), (omegaNat m : ℤ))
        = ∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ) := by
      have hIoc : Finset.Ioc n (n + L) = Finset.Ico (n + 1) (n + L + 1) := by
        ext m; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
      rw [hIoc, Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun m => (omegaNat m : ℤ))
          (Nat.zero_le (n + 1)) (by omega : n + 1 ≤ n + L + 1)]
      ring
    have hsplit : (j : ℤ) * (castSum b (n + L) - castSum b n)
        = (j : ℤ) * (∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ)) + (q : ℤ) * ((j : ℤ) * c) := by
      rw [castSum, castSum, hqz]
      linear_combination (j : ℤ) * hsum + (j : ℤ) * hc
    rw [hsplit, zpow_add₀ (zetaRoot_ne_zero q), zpow_mul (zetaRoot q) (q : ℤ) ((j : ℤ) * c),
      (zetaRoot_zpow_eq_one_iff q hqpos (q : ℤ)).mpr dvd_rfl, one_zpow, mul_one]
  have hdiff : corrSum b j L N - corrSumOmega b j L N
      = (∑ n ∈ range N, (zetaRoot q ^ ((j : ℤ) * (castSum b (n + L) - castSum b n))
          - zetaRoot q ^ ((j : ℤ) * ∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ)))) / N := by
    rw [corrSum, corrSumOmega, ← sub_div, Finset.sum_sub_distrib]
  rw [hdiff, norm_div, Complex.norm_natCast, div_le_div_iff_of_pos_right hNR]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ range N,
      ‖zetaRoot q ^ ((j : ℤ) * (castSum b (n + L) - castSum b n))
        - zetaRoot q ^ ((j : ℤ) * ∑ m ∈ Finset.Ioc n (n + L), (omegaNat m : ℤ))‖
      ≤ (if ¬ (((b : ℤ) - 1) ∣ (omegaCarry b (n + L) - omegaCarry b n)) then (2 : ℝ) else 0) := by
    intro n _
    by_cases hd : ((b : ℤ) - 1) ∣ (omegaCarry b (n + L) - omegaCarry b n)
    · rw [if_neg (by simpa using hd), hoff n hd, sub_self, norm_zero]
    · rw [if_pos hd]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_zetaRoot_zpow, norm_zetaRoot_zpow]
      norm_num
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [mul_zero, add_zero, nsmul_eq_mul]
  rw [carryDiffBadCount, mul_comm]

/-- **The naive route is refuted.**  If the carry difference were negligible mod `b − 1` AND the
`ω`-only correlations vanished, the leaf would be FALSE.  Since the `ω`-only clause at `L = 1` is
Delange's theorem, it is the negligibility of the carry that fails. -/
theorem not_hAutoCorr_of_carryNegligible (b : ℕ) (hb : 3 ≤ b) (L : ℕ)
    (hneg : CarryNegligible b L)
    (homega : ∀ j, 0 < j → j < b - 1 → Tendsto (corrSumOmega b j L) atTop (𝓝 0)) :
    ¬ HAutoCorr b := by
  intro h
  have hj1 : (0 : ℕ) < 1 := one_pos
  have hj1' : (1 : ℕ) < b - 1 := by omega
  -- corrSum → 0
  have hzero : Tendsto (corrSum b 1 L) atTop (𝓝 0) := by
    have hsq : Tendsto (fun N => corrSum b 1 L N - corrSumOmega b 1 L N) atTop (𝓝 0) := by
      rw [NormedAddGroup.tendsto_nhds_zero]
      intro ε hε
      have hb2 := (NormedAddGroup.tendsto_nhds_zero.mp hneg) (ε / 4) (by linarith)
      filter_upwards [hb2] with N hN
      have hbd := norm_corrSum_sub_omega b hb 1 L N
      have hN' : (carryDiffBadCount b L N : ℝ) / N ≤ ε / 4 := le_of_lt (by simpa using hN)
      have : 2 * (carryDiffBadCount b L N : ℝ) / N ≤ 2 * (ε / 4) := by
        rw [mul_div_assoc]; linarith
      linarith
    have := hsq.add (homega 1 hj1 hj1')
    simpa using this
  -- but HAutoCorr says it tends to b^{-L} ≠ 0
  have hlim := h 1 hj1 hj1' L
  have heq : (0 : ℂ) = ((b : ℂ))⁻¹ ^ L := tendsto_nhds_unique hzero hlim
  have hbC : ((b : ℂ)) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  exact (pow_ne_zero L (inv_ne_zero hbC)) heq.symm

/-- **THE LEAF.**  Open.  For each base `b ≥ 3` and each nontrivial character `j` of
`ZMod (b−1)`, the unit-modulus sequence `u(n) = ζ_{b−1}^{j·(Σ_{m≤n} ω(m) + c_n)}` has lag-`L`
autocorrelation exactly `b^{−L}`.

This supersedes `hDepthAll`: it is at the FIXED modulus `b − 1`, needs no growing truncation depth,
and does not demand block equidistribution of `G4_b` in `ZMod (b^L)` (which would be normality, a
strictly stronger statement than `ConjC1`).  The `L = 1` instance is the one-coordinate statement
`mean_n ζ_{b−1}^{j·d_{n+1}} = 1/b`; the general `L` is its multiplicativity across shifts. -/
theorem hAutoCorrAll : ∀ b, 3 ≤ b → HAutoCorr b := by
  sorry

theorem hState : HState := fun b hb L => stateLaw_of_hAutoCorr b hb (hAutoCorrAll b hb) L

theorem conjC1 : ConjC1 := conjC1_of_hAutoCorr hAutoCorrAll


end NormalNumbers.CastingOut