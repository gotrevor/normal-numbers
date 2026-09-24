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
        have : omegaHead b (L + 1) n
            = (b : ℤ) * omegaHead b L n + (omegaNat (n + 1 + L) : ℤ) := by
          rw [omegaHead, omegaHead, Finset.sum_range_succ, Finset.mul_sum]
          have : ∀ i ∈ range L, (b : ℤ) * ((omegaNat (n + 1 + i) : ℤ) * (b : ℤ) ^ (L - 1 - i))
              = (omegaNat (n + 1 + i) : ℤ) * (b : ℤ) ^ (L + 1 - 1 - i) := by
            intro i hi
            have hiL : i < L := Finset.mem_range.mp hi
            rw [show L + 1 - 1 - i = (L - 1 - i) + 1 by omega, pow_succ]
            ring
          rw [Finset.sum_congr rfl this]
          simp
        rw [this]; push_cast; ring
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

/-- **THE OPEN LEAF.**  All of C1, with every digit, floor and real number eliminated:

  `Σ_{i<L} ω(n+1+i)·b^{L-1-i} + c_{n+L}`  is equidistributed mod `b^L`,

where `c_N = ⌊Σ_{k≥1} ω(N+k) b^{−k}⌋`.  The conditioning is BOUNDED (`omegaCarry_eq_windowVal_div`
shows the unbounded part of the carry is the quotient `b^L·c_n`, which dies mod `b−1`), so this
needs no growing truncation depth.

Since `ω(n+L)` enters with coefficient `b^0 = 1` and `c_{n+L}` depends only on
`ω(n+L+1), ω(n+L+2), …`, it suffices that `ω(N) mod b^L` be equidistributed and asymptotically
independent of the `ω` values at other arguments — a Delange/Elliott-type input.  Open. -/
theorem hWindowAll : ∀ b, 3 ≤ b → ∀ L, HWindow b L := by
  sorry

theorem hState : HState := hState_of_hWindow hWindowAll

theorem conjC1 : ConjC1 := conjC1_of_hState hState

end NormalNumbers.CastingOut
