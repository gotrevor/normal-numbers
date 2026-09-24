/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Rotation

/-!
# B5 refuted: Leaf B cannot be proved from the dynamics alone

`SwingC3Rotation.tailLargeDecouple_iff_orbit` re-sites Leaf B as a statement about the `×b`
orbit of the single real number `L_P = largeLambert P b`: the empirical law along the residue
class `n ≡ r (mod Q)` agrees with `1/Q` of the global one.  Writing `y_n = orbit b x n`, the
only *dynamical* input the route has is the relation `y_{n+1} = fract (b · y_n)`
(`SwingC3Lambert.orbit_succ_eq`), which forces the class-`r` empirical measures to satisfy
`ν^{(r+1)} = T_* ν^{(r)}`, `T = ×b mod 1`.  Passing to a weak-`*` limit, `λ_r = T_*^r λ_0` and
`λ_0` is `T^Q`-invariant, while Leaf B is exactly the assertion that `λ_0` is `T`-invariant.

**Attack B5 of `PENDING_WORK.md` proposed deriving that invariance from the orbit relation plus a
quantitative recurrence.  This file shows that is impossible.**  A `T^Q`-invariant measure need
not be `T`-invariant, and the obstruction is realised by an honest `×b` orbit: for
`x = 1/(b^Q − 1)` the orbit is periodic of period `Q`, so `λ_0 = δ_x`, which is `T^Q`-invariant
and manifestly not `T`-invariant.  Hence `OrbitDecouple b Q x` is *false* for that `x`, and any
proof of Leaf B must use arithmetic of `ω_{>P}` — the orbit relation contributes nothing beyond
`λ_r = T_*^r λ_0`.

This is a refutation of a route, not of the route: `ConjC3`'s Leaf B stays open and is
untouched.  What it fixes is the *pricing*: B5 is dead, and the live attacks are the arithmetic
ones (B2, B3, B4).
-/

open Finset Filter Topology

namespace NormalNumbers

open PrimeLambert

/-- Leaf B, abstracted away from `ω`: the empirical law of the `×b` orbit of `x` along the
class `n ≡ r (mod Q)` is `1/Q` of the global one, for every arc and every rotation.
`SwingC3Rotation.tailLargeDecouple_iff_orbit` says `TailLargeDecouple b P Q` is exactly
`OrbitDecouple b Q (largeLambert P b)`. -/
def OrbitDecouple (b Q : ℕ) (x : ℝ) : Prop :=
  ∀ (r : ℕ) (θ α len : ℝ),
    Tendsto (fun N : ℕ =>
      ((((range N).filter (fun n => n ≡ r [MOD Q] ∧
            Int.fract (θ + orbit b x n) ∈ Set.Ico α (α + len))).card : ℝ)
        - (((range N).filter (fun n =>
            Int.fract (θ + orbit b x n) ∈ Set.Ico α (α + len))).card : ℝ) / (Q : ℝ)) / N)
      atTop (𝓝 0)

/-- The anchor: Leaf B of the rotation route **is** `OrbitDecouple` for the large-prime
Lambert number.  So any refutation of `OrbitDecouple` for a general orbit is a refutation of a
*dynamics-only* proof of Leaf B. -/
theorem tailLargeDecouple_iff_orbitDecouple {b : ℕ} (hb : 2 ≤ b) (P Q : ℕ) :
    CastingOut.TailLargeDecouple b P Q ↔ OrbitDecouple b Q (largeLambert P b) :=
  CastingOut.tailLargeDecouple_iff_orbit hb P Q

/-! ### Counting the class `0 (mod Q)` -/

lemma card_filter_mod_eq_zero {Q : ℕ} (hQ : 0 < Q) (m : ℕ) :
    ((range (Q * m)).filter (fun n => n % Q = 0)).card = m := by
  classical
  have hset : (range (Q * m)).filter (fun n => n % Q = 0)
      = (range m).image (fun i => Q * i) := by
    ext n
    simp only [Finset.mem_filter, mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hlt, hmod⟩
      refine ⟨n / Q, ?_, ?_⟩
      · have h' : n < m * Q := by rw [mul_comm]; exact hlt
        exact (Nat.div_lt_iff_lt_mul hQ).2 h'
      · exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hi hQ, by simp [Nat.mul_mod_right]⟩
  rw [hset, Finset.card_image_of_injective _ (fun i j h => by
    exact Nat.eq_of_mul_eq_mul_left hQ h), card_range]

/-! ### The periodic witness -/

section Witness

variable {b Q : ℕ}

/-- The witness: `x = 1/(b^Q − 1)`, whose base-`b` expansion is `0.0…01 0…01 …`. -/
noncomputable def periodicWitness (b Q : ℕ) : ℝ := 1 / ((b : ℝ) ^ Q - 1)

lemma one_lt_pow_sub (hb : 2 ≤ b) (hQ : 2 ≤ Q) : (1 : ℝ) < (b : ℝ) ^ Q - 1 := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have h : (4 : ℝ) ≤ (b : ℝ) ^ Q := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (b : ℝ) ^ 2 := by gcongr
      _ ≤ (b : ℝ) ^ Q := by
          refine pow_le_pow_right₀ (by linarith) hQ
  linarith

lemma periodicWitness_pos (hb : 2 ≤ b) (hQ : 2 ≤ Q) : 0 < periodicWitness b Q := by
  have := one_lt_pow_sub hb hQ
  rw [periodicWitness]; positivity

/-- For `s < Q` the orbit point `x·b^s` is still below `1`. -/
lemma periodicWitness_mul_lt_one (hb : 2 ≤ b) (hQ : 2 ≤ Q) {s : ℕ} (hs : s < Q) :
    periodicWitness b Q * (b : ℝ) ^ s < 1 := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hd := one_lt_pow_sub hb hQ
  have hstep : (b : ℝ) ^ s * (b : ℝ) ≤ (b : ℝ) ^ Q := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hpos : (0 : ℝ) < (b : ℝ) ^ s := by positivity
  rw [periodicWitness, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
  nlinarith [hpos, hstep, hbR]

/-- **The orbit is periodic of period `Q`.** -/
lemma orbit_periodicWitness (hb : 2 ≤ b) (hQ : 2 ≤ Q) (n : ℕ) :
    orbit b (periodicWitness b Q) n = periodicWitness b Q * (b : ℝ) ^ (n % Q) := by
  classical
  set x : ℝ := periodicWitness b Q with hx
  set B : ℕ := b ^ Q with hB
  have hd : (1 : ℝ) < (B : ℝ) - 1 := by
    have := one_lt_pow_sub hb hQ
    rw [hB]; push_cast; linarith
  have hBne : ((B : ℝ) - 1) ≠ 0 := by linarith
  set m : ℕ := n / Q with hm
  set s : ℕ := n % Q with hs
  set I : ℕ := ∑ i ∈ range m, B ^ i with hI
  have hIR : ((I : ℕ) : ℝ) = ∑ i ∈ range m, (B : ℝ) ^ i := by rw [hI]; push_cast; ring
  have hgeom : (∑ i ∈ range m, (B : ℝ) ^ i) * ((B : ℝ) - 1) = (B : ℝ) ^ m - 1 := geom_sum_mul _ _
  have hkey : x * (B : ℝ) ^ m = x + (I : ℝ) := by
    have hne : ((b : ℝ) ^ Q - 1) ≠ 0 := by
      have := one_lt_pow_sub hb hQ; linarith
    have hxd : x * ((B : ℝ) - 1) = 1 := by
      rw [hx, periodicWitness, hB]
      push_cast
      field_simp
    have : (x * (B : ℝ) ^ m) * ((B : ℝ) - 1) = (x + (I : ℝ)) * ((B : ℝ) - 1) := by
      rw [hIR]
      calc (x * (B : ℝ) ^ m) * ((B : ℝ) - 1) = (x * ((B : ℝ) - 1)) * (B : ℝ) ^ m := by ring
        _ = (B : ℝ) ^ m := by rw [hxd]; ring
        _ = (x * ((B : ℝ) - 1)) + ((∑ i ∈ range m, (B : ℝ) ^ i) * ((B : ℝ) - 1)) := by
            rw [hxd, hgeom]; ring
        _ = (x + ∑ i ∈ range m, (B : ℝ) ^ i) * ((B : ℝ) - 1) := by ring
    exact mul_right_cancel₀ hBne this
  have hsplit : (b : ℝ) ^ n = (B : ℝ) ^ m * (b : ℝ) ^ s := by
    rw [hB]
    push_cast
    rw [← pow_mul, ← pow_add]
    congr 1
    exact (Nat.div_add_mod n Q).symm
  have hval : x * (b : ℝ) ^ n = x * (b : ℝ) ^ s + ((I * b ^ s : ℕ) : ℝ) := by
    rw [hsplit, ← mul_assoc, hkey]
    push_cast
    ring
  have hQ0 : 0 < Q := by omega
  have hs0 : (0 : ℝ) ≤ x * (b : ℝ) ^ s :=
    mul_nonneg (le_of_lt (periodicWitness_pos hb hQ)) (by positivity)
  have hs1 : x * (b : ℝ) ^ s < 1 :=
    periodicWitness_mul_lt_one hb hQ (Nat.mod_lt n hQ0)
  rw [orbit, hval, Int.fract_add_natCast, Int.fract_eq_self.2 ⟨hs0, hs1⟩]

/-- **B5 refuted.**  The orbit relation `y_{n+1} = fract (b · y_n)` does not imply
`OrbitDecouple`: the periodic witness `1/(b^Q − 1)` is a genuine `×b` orbit for which the
class-`0` empirical measure is `δ_x`, hence `×b^Q`-invariant but not `×b`-invariant. -/
theorem not_orbitDecouple_periodicWitness (hb : 2 ≤ b) (hQ : 2 ≤ Q) :
    ¬ OrbitDecouple b Q (periodicWitness b Q) := by
  classical
  intro h
  set x : ℝ := periodicWitness b Q with hx
  have hx0 : 0 < x := periodicWitness_pos hb hQ
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hQ0 : 0 < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  -- the arc `[x, x·b)`
  have harc : ∀ n : ℕ, (Int.fract ((0 : ℝ) + orbit b x n)
      ∈ Set.Ico x (x + x * ((b : ℝ) - 1))) ↔ n % Q = 0 := by
    intro n
    have hs0 : (0 : ℝ) ≤ x * (b : ℝ) ^ (n % Q) :=
      mul_nonneg (le_of_lt hx0) (by positivity)
    have hs1 : x * (b : ℝ) ^ (n % Q) < 1 :=
      periodicWitness_mul_lt_one hb hQ (Nat.mod_lt n hQ0)
    have hfr : Int.fract ((0 : ℝ) + orbit b x n) = x * (b : ℝ) ^ (n % Q) := by
      rw [zero_add, orbit_periodicWitness hb hQ n, Int.fract_eq_self.2 ⟨hs0, hs1⟩]
    rw [hfr]
    have hrw : x + x * ((b : ℝ) - 1) = x * (b : ℝ) := by ring
    rw [hrw]
    constructor
    · rintro ⟨-, hlt⟩
      by_contra hne
      have hs1 : 1 ≤ n % Q := by omega
      have : x * (b : ℝ) ≤ x * (b : ℝ) ^ (n % Q) := by
        have : (b : ℝ) ^ 1 ≤ (b : ℝ) ^ (n % Q) := pow_le_pow_right₀ (by linarith) hs1
        rw [pow_one] at this
        nlinarith [hx0]
      linarith
    · intro hz
      rw [hz, pow_zero, mul_one]
      exact ⟨le_refl x, by nlinarith [hx0]⟩
  have hmodr : ∀ n : ℕ, (n ≡ 0 [MOD Q]) ↔ n % Q = 0 := by
    intro n; unfold Nat.ModEq; simp
  -- both filters are the class `0 (mod Q)`
  have hfilt : ∀ N : ℕ, ((range N).filter (fun n => n ≡ 0 [MOD Q] ∧
        Int.fract ((0 : ℝ) + orbit b x n) ∈ Set.Ico x (x + x * ((b : ℝ) - 1))))
      = (range N).filter (fun n => n % Q = 0) := by
    intro N
    apply Finset.filter_congr
    intro n _
    rw [hmodr n, harc n]
    tauto
  have hfilt2 : ∀ N : ℕ, ((range N).filter (fun n =>
        Int.fract ((0 : ℝ) + orbit b x n) ∈ Set.Ico x (x + x * ((b : ℝ) - 1))))
      = (range N).filter (fun n => n % Q = 0) := by
    intro N
    apply Finset.filter_congr
    intro n _
    exact harc n
  have hspec := h 0 0 x (x * ((b : ℝ) - 1))
  simp only [hfilt, hfilt2] at hspec
  -- restrict to `N = Q·m`
  have hcomp : Tendsto (fun m : ℕ => Q * m) atTop atTop :=
    tendsto_atTop_atTop.2 fun c => ⟨c, fun m hm => le_trans hm (Nat.le_mul_of_pos_left m hQ0)⟩
  have h2 := hspec.comp hcomp
  set c : ℝ := (1 - 1 / (Q : ℝ)) / (Q : ℝ) with hc
  have hconst : ∀ᶠ m : ℕ in atTop,
      ((fun N : ℕ => ((((range N).filter (fun n => n % Q = 0)).card : ℝ)
        - (((range N).filter (fun n => n % Q = 0)).card : ℝ) / (Q : ℝ)) / N) ∘
        (fun m : ℕ => Q * m)) m = c := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    simp only [Function.comp_apply, card_filter_mod_eq_zero hQ0 m]
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have : ((Q * m : ℕ) : ℝ) = (Q : ℝ) * m := by push_cast; ring
    rw [this, hc]
    field_simp
  have hlim : Tendsto ((fun N : ℕ => ((((range N).filter (fun n => n % Q = 0)).card : ℝ)
      - (((range N).filter (fun n => n % Q = 0)).card : ℝ) / (Q : ℝ)) / N) ∘
      (fun m : ℕ => Q * m)) atTop (𝓝 c) :=
    Tendsto.congr' (by filter_upwards [hconst] with m hm; exact hm.symm) tendsto_const_nhds
  have hzero : c = 0 := tendsto_nhds_unique hlim h2
  have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  rw [hc] at hzero
  have h1Q : 1 / (Q : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hQR (by norm_num)]; linarith
  have : (0 : ℝ) < (1 - 1 / (Q : ℝ)) / (Q : ℝ) := by
    apply div_pos (by linarith) hQR
  linarith

end Witness

end NormalNumbers
