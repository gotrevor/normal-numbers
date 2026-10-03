/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ComputableNormalB
import NormalNumbers.ExplicitSquareNonNormal

/-!
# `√(cantorReal e)` normal in every base, for a computable `e` (given polynomial decay)

The instance of `ComputableNormalB.exists_computable_absNormal` for `G ω = √(cantorReal ω)`.
Lower approximation from a prefix `p` of length `M`: `A p = √(Y/4^M)`, `Y = ⌊y·4^M⌋` read
from `p` (`SqrtFloor.cdL`); its base-`b` floors are `Nat.sqrt (Y·b^{2m} / 4^M)`.  Error:
`√y − √(Y/4^M) ≤ √(y − Y/4^M) ≤ 2^{-M}`.
-/

open MeasureTheory

namespace NormalNumbers.SqrtCantorAbs

open ExplicitSquare Derandomize SqrtFloor

/-- `⌊y·4^M⌋` read from a prefix of length `M`. -/
def Yp (p : List Bool) : ℕ :=
  ((List.range (2 * p.length)).map fun k => cdL k p * 2 ^ (2 * p.length - 1 - k)).sum

/-- The lower approximation `√(Y/4^M)`. -/
noncomputable def Ap (p : List Bool) : ℝ := Real.sqrt ((Yp p : ℝ) / 4 ^ p.length)

/-- Its base-`b` floors. -/
def Psi (b m : ℕ) (p : List Bool) : ℕ := Nat.sqrt (Yp p * b ^ (2 * m) / 4 ^ p.length)

theorem Psi_eq (b m : ℕ) (p : List Bool) : Psi b m p = ⌊Ap p * (b : ℝ) ^ m⌋₊ := by
  have h4 : (0 : ℝ) < 4 ^ p.length := by positivity
  have e : Ap p * (b : ℝ) ^ m = Real.sqrt (((Yp p * b ^ (2 * m) : ℕ) : ℝ) / ((4 ^ p.length : ℕ) : ℝ)) := by
    rw [Ap, show ((Yp p * b ^ (2 * m) : ℕ) : ℝ) / ((4 ^ p.length : ℕ) : ℝ) =
      (Yp p : ℝ) / 4 ^ p.length * ((b : ℝ) ^ m) ^ 2 by push_cast; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [e, floor_sqrt _ (by positivity), Nat.floor_div_eq_div, Psi]

theorem primrec_Yp : Primrec Yp := by
  have hf : Primrec fun p : List Bool => List.range (2 * p.length) :=
    Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.list_length)
  have hg : Primrec fun y : List Bool × ℕ => cdL y.2 y.1 * 2 ^ (2 * y.1.length - 1 - y.2) :=
    Primrec.nat_mul.comp (primrec_cdL.comp Primrec.snd Primrec.fst)
      (ComputableNormal.primrec_pow.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.list_length.comp Primrec.fst)) (Primrec.const 1)) Primrec.snd))
  exact (primrec_sum_map hf hg.to₂).of_eq fun p => rfl

theorem primrec_Psi : Primrec fun x : ℕ × ℕ × List Bool => Psi x.1 x.2.1 x.2.2 := by
  have hY := primrec_Yp.comp (Primrec.snd.comp (Primrec.snd (α := ℕ) (β := ℕ × List Bool)))
  have hB := ComputableNormal.primrec_pow.comp (Primrec.fst (α := ℕ) (β := ℕ × List Bool))
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd))
  have hD := ComputableNormal.primrec_pow.comp (Primrec.const 4)
    (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd (α := ℕ) (β := ℕ × List Bool))))
  exact (primrec_sqrt.comp (Primrec.nat_div.comp (Primrec.nat_mul.comp hY hB) hD)).of_eq
    fun x => rfl

theorem Yp_pre (ω : ℕ → Bool) (D : ℕ) :
    (Yp (pre ω D) : ℝ) = ⌊cantorReal ω * 2 ^ (2 * D)⌋₊ := by
  rw [cantorReal, floor_mul_two_pow _ (cantorDigits_lt ω) (cantorDigits_proper ω), Yp, length_pre]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
  have hk' := List.mem_range.1 hk
  congr 1
  unfold SqrtFloor.cdL cantorDigits Derandomize.pre
  split_ifs with h0 h2 h3 h3 <;> try rfl
  all_goals
    rw [List.getD_eq_getElem _ _ (by simp; omega)] at *
    simp_all

theorem sqrt_sub_le {a y : ℝ} (ha : 0 ≤ a) (hay : a ≤ y) :
    Real.sqrt y ≤ Real.sqrt a + Real.sqrt (y - a) := by
  have h1 : 0 ≤ y - a := by linarith
  rw [Real.sqrt_le_left]
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt h1, Real.sqrt_nonneg a, Real.sqrt_nonneg (y - a),
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg (y - a))]
  · positivity

theorem Ap_bounds (ω : ℕ → Bool) (D : ℕ) :
    Ap (pre ω D) ≤ Real.sqrt (cantorReal ω) ∧
      Real.sqrt (cantorReal ω) ≤ Ap (pre ω D) + (1 / 2 : ℝ) ^ D := by
  have hy := (cantorReal_mem_Ico ω).1
  have hY := Yp_pre ω D
  set y := cantorReal ω
  have h4 : (0 : ℝ) < 4 ^ D := by positivity
  have hfl := Nat.floor_le (show 0 ≤ y * 2 ^ (2 * D) by positivity)
  have hlt := Nat.lt_floor_add_one (y * 2 ^ (2 * D))
  have e4 : (2 : ℝ) ^ (2 * D) = 4 ^ D := by rw [pow_mul]; norm_num
  rw [e4] at hfl hlt hY
  rw [← hY] at hfl hlt
  have hA : (Yp (pre ω D) : ℝ) / 4 ^ (pre ω D).length = (Yp (pre ω D) : ℝ) / 4 ^ D := by
    rw [length_pre]
  have hlo : (Yp (pre ω D) : ℝ) / 4 ^ D ≤ y := by rw [div_le_iff₀ h4]; linarith
  have hhi : y - (Yp (pre ω D) : ℝ) / 4 ^ D ≤ 1 / 4 ^ D := by
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ h4]; linarith
  constructor
  · rw [Ap, hA]; exact Real.sqrt_le_sqrt hlo
  · rw [Ap, hA]
    refine (sqrt_sub_le (by positivity) hlo).trans (add_le_add_right ?_ _)
    have : Real.sqrt (1 / 4 ^ D) = (1 / 2 : ℝ) ^ D := by
      rw [show (1 : ℝ) / 4 ^ D = ((1 / 2 : ℝ) ^ D) ^ 2 by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num; rw [one_div, inv_pow], Real.sqrt_sq (by positivity)]
    rw [← this]; exact Real.sqrt_le_sqrt hhi

theorem measurable_sqrt_cantorReal : Measurable fun ω => Real.sqrt (cantorReal ω) := by
  have hc : Measurable cantorReal := by
    unfold cantorReal realOfDigits
    refine Measurable.tsum fun i => Measurable.div_const ?_ _
    refine Measurable.comp (measurable_of_countable (fun n : ℕ => (n : ℝ))) ?_
    exact (measurable_of_countable (fun b : Bool =>
      if i = 0 then 1 else if i % 2 = 0 then (if b then 1 else 0) else 0)).comp
      (measurable_pi_apply (i / 2 - 1))
  exact Real.continuous_sqrt.measurable.comp hc

/-- **All-bases derandomization of the `√` map.** -/
theorem exists_computable_absNormal_sqrt (hd : PolyDecay Real.sqrt) :
    ∃ e : ℕ → Bool, Computable e ∧ ∀ b, 2 ≤ b → IsNormal b (Real.sqrt (cantorReal e)) := by
  obtain ⟨C, δ, hC, hδ, hdec⟩ := hd
  exact ComputableNormalB.exists_computable_absNormal Psi primrec_Psi Ap Psi_eq
    (fun p => Real.sqrt_nonneg _) (fun ω => Real.sqrt (cantorReal ω))
    measurable_sqrt_cantorReal Ap_bounds hC hδ (fun ξ hξ => hdec ξ hξ)

end NormalNumbers.SqrtCantorAbs
