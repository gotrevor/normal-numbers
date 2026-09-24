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

/-- **THE OPEN LEAF.**  After `conjC1_iff_hState` this is all of C1: no digits, no floors of
`bᴺ·x`, no real numbers except the carry sequence `c_N = ⌊Σ_{k≥1} ω(N+k) b^{−k}⌋`, which
`omegaCarry_rec` shows is generated from `ω` by ordinary carrying.

Open.  Known to be false-in-general for arbitrary weights (see `not_castUniform_of_isNormal`
for the shape of the target law), and expected to need joint equidistribution of the `ω` values
in short windows — an Elliott-type input. -/
theorem hState : HState := by
  sorry

theorem conjC1 : ConjC1 := conjC1_of_hState hState

end NormalNumbers.CastingOut
