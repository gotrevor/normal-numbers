/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.DiskResidue

/-!
# Route 3 costume audit: the disk premise is a π-orbit statement

`diskPhase_shadow` makes `diskResidue n / 8^n` track `orbit 2 π n` to within `5 / 2^n`.
So a quantitative window-cover of π's own binary orbit, with a slightly smaller target
(the middle quarter of each cylinder), already implies `DiskResidueCover`.  The lattice
arithmetic enters only through an error term that vanishes; it gives no lever by itself.
Probe evidence: `scripts/pi_route3_residue.py` (scaled error ≈ 0.002 at n = 11).
-/

namespace NormalNumbers.PiDisjunctiveRoutes

/-- Quantitative window-cover of π's binary orbit, middle-quarter targets.
Costume audit: a pure statement about the digits of π, implies the sink
(`IsDisjunctive 2 π`), and implies the route-3 premise (`diskResidueCover_of_piOrbitWindowCover`).
Odds of truth: as `DiskResidueCover` (~85%, heuristic); no known mechanism. -/
def PiOrbitWindowCover : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, 0 < k → ∀ N : ℕ, C * 4 ^ k ≤ N →
    ∀ j : ℕ, j < 2 ^ k → ∃ n : ℕ, N ≤ n ∧ n ≤ 2 * N ∧
      ((8 * j + 3 : ℝ) / (8 * 2 ^ k) < orbit 2 Real.pi n) ∧
      (orbit 2 Real.pi n < (8 * j + 5 : ℝ) / (8 * 2 ^ k))

/-- The route-3 premise is implied by the plain π-orbit cover: the disk is a costume. -/
theorem diskResidueCover_of_piOrbitWindowCover (h : PiOrbitWindowCover) :
    DiskResidueCover := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨64 * C, by positivity, fun k hk N hN j hj => ?_⟩
  have h4k : k + 6 ≤ 64 * 4 ^ k := by
    have := Nat.lt_pow_self (n := k) (by norm_num : 1 < 4); omega
  have hCN : C * 4 ^ k ≤ N := le_trans (by nlinarith) hN
  have hkn : k + 6 ≤ N := le_trans h4k (le_trans (by nlinarith) hN)
  obtain ⟨n, hNn, hn2, hlo, hhi⟩ := hC k hk N hCN j hj
  refine ⟨n, hNn, hn2, ?_⟩
  have h8 : (0 : ℝ) < 8 ^ n := by positivity
  set t : ℝ := 2 ^ k with ht
  have h2k : (0 : ℝ) < t := by positivity
  set u : ℝ := (diskResidue n : ℝ) / 8 ^ n with hu
  set q : ℕ := diskCount (4 ^ n) / 8 ^ n
  have hdec : diskPhase n = q + u := by
    have := Nat.div_add_mod (diskCount (4 ^ n)) (8 ^ n)
    have hcast : (diskCount (4 ^ n) : ℝ) = (8 : ℝ) ^ n * q + (diskResidue n : ℕ) := by
      rw [diskResidue]; exact_mod_cast this.symm
    rw [diskPhase, hu, hcast]; field_simp
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 := by
    rw [hu, div_lt_one h8]
    exact_mod_cast Nat.mod_lt _ (by positivity)
  -- shadow error below 1/(8t)
  have hδ : (5 : ℝ) / 2 ^ n < 1 / (8 * t) := by
    have h64 : (2 : ℝ) ^ (k + 6) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_add] at h64
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hs := diskPhase_sub_le n
  rw [hdec, abs_le] at hs
  set m : ℤ := ⌊Real.pi * (2 : ℝ) ^ n⌋
  have horb : orbit 2 Real.pi n = Real.pi * (2 : ℝ) ^ n - m := by
    simp only [orbit, Nat.cast_ofNat]; rfl
  rw [horb] at hlo hhi
  have hj' : ((j : ℝ) + 1) ≤ t := by
    have : (j + 1 : ℝ) ≤ (2 ^ k : ℕ) := by exact_mod_cast hj
    simpa [ht] using this
  have e1 : (8 * (j : ℝ) + 3) / (8 * t) - 1 / (8 * t) ≥ 0 := by
    rw [← sub_div]; exact div_nonneg (by have := j.cast_nonneg (α := ℝ); linarith) (by positivity)
  have e2 : (8 * (j : ℝ) + 5) / (8 * t) + 1 / (8 * t) ≤ 1 := by
    rw [← add_div, div_le_one (by positivity)]; linarith
  have hqm : (q : ℤ) = m := by
    have a1 : ((q : ℤ) - m : ℝ) < 1 := by push_cast; linarith
    have a2 : (-1 : ℝ) < ((q : ℤ) - m : ℝ) := by push_cast; linarith
    have b1 : (q : ℤ) - m < 1 := by exact_mod_cast a1
    have b2 : -1 < (q : ℤ) - m := by exact_mod_cast a2
    omega
  have hqm' : (q : ℝ) = m := by exact_mod_cast hqm
  have f1 : (4 * (j : ℝ) + 1) / (4 * t) = (8 * j + 3) / (8 * t) - 1 / (8 * t) := by
    field_simp; ring
  have f2 : (4 * (j : ℝ) + 3) / (4 * t) = (8 * j + 5) / (8 * t) + 1 / (8 * t) := by
    field_simp; ring
  have ulo : (4 * (j : ℝ) + 1) / (4 * t) < u := by rw [f1]; linarith
  have uhi : u < (4 * (j : ℝ) + 3) / (4 * t) := by rw [f2]; linarith
  rw [div_lt_div_iff₀ (by positivity) h8] at ulo
  rw [div_lt_div_iff₀ h8 (by positivity)] at uhi
  constructor
  · have : ((4 * j + 1) * 8 ^ n : ℝ) < 4 * 2 ^ k * diskResidue n := by
      rw [← ht]; linarith
    exact_mod_cast this
  · have : (4 * 2 ^ k * diskResidue n : ℝ) < (4 * j + 3) * 8 ^ n := by
      rw [← ht]; linarith
    exact_mod_cast this

/-- Small-`d` part of the χ₄ divisor identity at radius `4^n`. -/
def diskSmallPart (n D : ℕ) : ℤ :=
  ∑ d ∈ Finset.Icc 1 D, chiFour d * ((16 ^ n / d : ℕ) : ℤ)

/-- d-range finding: the small-`d` part, scaled by `8^n`, is the binary orbit point
`2^n · 4 L_D` of the Leibniz partial sum `L_D = Σ_{d ≤ D} χ₄(d)/d` (a rational), up to `4D/8^n`.
So the small-`d` range carries a periodic (rational) orbit; all π-content of the residue sits
in the tail `d > D`, where it is again `2^n · 4(π/4 − L_D)`: the digits of π, no new lever. -/
theorem diskSmallPart_orbit (n D : ℕ) :
    |4 * (diskSmallPart n D : ℝ) / 8 ^ n -
        (2 : ℝ) ^ n * (4 * ∑ d ∈ Finset.Icc 1 D, (chiFour d : ℝ) / d)| ≤ 4 * D / 8 ^ n := by
  have h8 : (0 : ℝ) < 8 ^ n := by positivity
  have e : (4 * (diskSmallPart n D : ℝ) / 8 ^ n -
        (2 : ℝ) ^ n * (4 * ∑ d ∈ Finset.Icc 1 D, (chiFour d : ℝ) / d)) =
      4 * (∑ d ∈ Finset.Icc 1 D, (chiFour d : ℝ) *
        (((16 ^ n / d : ℕ) : ℝ) - (16 : ℝ) ^ n / d)) / 8 ^ n := by
    have h16 : (16 : ℝ) ^ n = 2 ^ n * 8 ^ n := by rw [← mul_pow]; norm_num
    have hc : (diskSmallPart n D : ℝ) = ∑ d ∈ Finset.Icc 1 D,
        (chiFour d : ℝ) * ((16 ^ n / d : ℕ) : ℝ) := by
      rw [diskSmallPart, Int.cast_sum]; simp only [Int.cast_mul, Int.cast_natCast]
    rw [hc, h16]
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : (d : ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.1 hd).1; positivity
    field_simp
  rw [e, abs_div, abs_of_pos h8, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  gcongr
  calc |∑ d ∈ Finset.Icc 1 D, (chiFour d : ℝ) * (((16 ^ n / d : ℕ) : ℝ) - (16 : ℝ) ^ n / d)|
      ≤ ∑ d ∈ Finset.Icc 1 D, (1 : ℝ) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
        have hd1 : (0 : ℝ) < d := by
          have := (Finset.mem_Icc.1 hd).1; exact_mod_cast this
        have hχ : |(chiFour d : ℝ)| ≤ 1 := by
          unfold chiFour; split_ifs <;> norm_num
        have hfl : |(((16 ^ n / d : ℕ) : ℝ) - (16 : ℝ) ^ n / d)| ≤ 1 := by
          have a := Nat.cast_div_le (α := ℝ) (m := 16 ^ n) (n := d)
          have b : (16 : ℝ) ^ n / d - 1 < ((16 ^ n / d : ℕ) : ℝ) := by
            rw [sub_lt_iff_lt_add, div_lt_iff₀ hd1]
            have := Nat.lt_div_mul_add (a := 16 ^ n) (b := d) (by exact_mod_cast hd1)
            have : ((16 ^ n : ℕ) : ℝ) < ((16 ^ n / d * d + d : ℕ) : ℝ) := by exact_mod_cast this
            push_cast at this a ⊢; nlinarith
          push_cast at a; rw [abs_le]; constructor <;> linarith
        rw [abs_mul]; nlinarith [abs_nonneg (chiFour d : ℝ)]
    _ = D := by simp

end NormalNumbers.PiDisjunctiveRoutes
