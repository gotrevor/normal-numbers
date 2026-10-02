/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Bridge
import NormalNumbers.ComputableNormal

/-!
# Binary floors of `√y` from the binary digits of `y`

`⌊√y · 2^m⌋₊ = Nat.sqrt ⌊y · 4^m⌋₊`, and `⌊y · 2^n⌋₊` is the integer with binary digits
`s 0 … s (n-1)`.  With `Nat.sqrt` primitive recursive this makes the binary floors of `√y`
a primitive-recursive function of finitely many digits of `y`.
-/

namespace NormalNumbers.SqrtFloor

theorem floor_sqrt (z : ℝ) (hz : 0 ≤ z) : ⌊Real.sqrt z⌋₊ = Nat.sqrt ⌊z⌋₊ := by
  set s := Nat.sqrt ⌊z⌋₊
  rw [Nat.floor_eq_iff (Real.sqrt_nonneg z)]
  have h1 : s * s ≤ ⌊z⌋₊ := Nat.sqrt_le _
  have h2 : ⌊z⌋₊ < (s + 1) * (s + 1) := Nat.lt_succ_sqrt _
  have hf1 : ((s * s : ℕ) : ℝ) ≤ z := (Nat.cast_le.2 h1).trans (Nat.floor_le hz)
  have hf2 : z < ((s + 1) * (s + 1) : ℕ) := by
    have := Nat.lt_floor_add_one z
    have h2' : ((⌊z⌋₊ + 1 : ℕ) : ℝ) ≤ ((s + 1) * (s + 1) : ℕ) := Nat.cast_le.2 h2
    push_cast at this h2' ⊢; linarith
  push_cast at hf1 hf2
  constructor
  · exact Real.le_sqrt_of_sq_le (by nlinarith)
  · rw [Real.sqrt_lt' (by positivity)]; nlinarith

theorem sqrt_eq_sum (n : ℕ) :
    Nat.sqrt n = ((List.range n).map fun k => if (k + 1) * (k + 1) ≤ n then 1 else 0).sum := by
  classical
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, ← Finset.card_filter]
  have : (Finset.range n).filter (fun k => (k + 1) * (k + 1) ≤ n) = Finset.range (Nat.sqrt n) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [← Nat.le_sqrt]
    constructor
    · rintro ⟨-, h⟩; omega
    · intro h; exact ⟨lt_of_lt_of_le h (Nat.sqrt_le_self n), h⟩
  rw [this, Finset.card_range]

theorem primrec_sqrt : Primrec Nat.sqrt := by
  have hg : Primrec fun y : ℕ × ℕ => if (y.2 + 1) * (y.2 + 1) ≤ y.1 then 1 else 0 :=
    Primrec.ite (Primrec.nat_le.comp (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.snd)
      (Primrec.succ.comp Primrec.snd)) Primrec.fst) (Primrec.const 1) (Primrec.const 0)
  exact (Derandomize.primrec_sum_map Primrec.list_range hg.to₂).of_eq fun n => (sqrt_eq_sum n).symm

/-- Binary floors of a digit expansion. -/
theorem floor_mul_two_pow (s : ℕ → ℕ) (hs : ∀ i, s i < 2) (hp : ProperDigits 2 s) (n : ℕ) :
    ⌊realOfDigits 2 s * 2 ^ n⌋₊ =
      ((List.range n).map fun k => s k * 2 ^ (n - 1 - k)).sum := by
  rcases n with _ | i
  · simp only [pow_zero, mul_one, List.range_zero, List.map_nil, List.sum_nil]
    rw [Nat.floor_eq_zero]
    exact (realOfDigits_mem_Ico 2 le_rfl s hs hp).2
  · have h := floor_realOfDigits_mul_pow 2 le_rfl s hs hp i
    have h0 : (0 : ℝ) ≤ realOfDigits 2 s * 2 ^ (i + 1) :=
      mul_nonneg (realOfDigits_mem_Ico 2 le_rfl s hs hp).1 (by positivity)
    rw [← Int.floor_toNat, show ((2 : ℕ) : ℝ) = 2 by norm_num] at *
    rw [h, Int.toNat_natCast, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    · rfl

/-- The quarter-Cantor digit `k` read from a finite prefix `p` of the coins (digit `0` is `1`,
even digits `k ≥ 2` are `p[k/2 - 1]`, odd digits are `0`). -/
def cdL (k : ℕ) (p : List Bool) : ℕ :=
  if k = 0 then 1 else if k % 2 = 0 then (if p.getD (k / 2 - 1) false = true then 1 else 0) else 0

/-- `⌊√y · 2^m⌋₊` computed from the first `2m` digits. -/
def sqrtPhi (m : ℕ) (p : List Bool) : ℕ :=
  Nat.sqrt (((List.range (2 * m)).map fun k => cdL k p * 2 ^ (2 * m - 1 - k)).sum)

theorem primrec_cdL : Primrec₂ cdL := by
  have hk : Primrec fun x : ℕ × List Bool => x.1 := Primrec.fst
  have hp : Primrec fun x : ℕ × List Bool => x.2 := Primrec.snd
  have hidx : Primrec fun x : ℕ × List Bool => x.1 / 2 - 1 :=
    Primrec.nat_sub.comp (Primrec.nat_div.comp hk (Primrec.const 2)) (Primrec.const 1)
  have hget : Primrec fun x : ℕ × List Bool => x.2.getD (x.1 / 2 - 1) false :=
    (Primrec.list_getD false).comp hp hidx
  have hb : Primrec fun x : ℕ × List Bool =>
      if x.2.getD (x.1 / 2 - 1) false = true then 1 else 0 :=
    Primrec.ite (Primrec.eq.comp hget (Primrec.const true)) (Primrec.const 1) (Primrec.const 0)
  have hev : Primrec fun x : ℕ × List Bool =>
      if x.1 % 2 = 0 then (if x.2.getD (x.1 / 2 - 1) false = true then 1 else 0) else 0 :=
    Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hk (Primrec.const 2)) (Primrec.const 0))
      hb (Primrec.const 0)
  exact (Primrec.ite (Primrec.eq.comp hk (Primrec.const 0)) (Primrec.const 1) hev).to₂.of_eq
    fun k p => rfl

theorem primrec_sqrtPhi : Primrec₂ sqrtPhi := by
  have hf : Primrec fun x : ℕ × List Bool => List.range (2 * x.1) :=
    Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
  have hg : Primrec fun y : (ℕ × List Bool) × ℕ => cdL y.2 y.1.2 * 2 ^ (2 * y.1.1 - 1 - y.2) :=
    Primrec.nat_mul.comp (primrec_cdL.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (ComputableNormal.primrec_pow.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.fst.comp (Primrec.fst))) (Primrec.const 1)) Primrec.snd))
  exact (SqrtFloor.primrec_sqrt.comp (Derandomize.primrec_sum_map hf hg.to₂)).to₂.of_eq
    fun m p => rfl

theorem floor_sqrt_digits (s : ℕ → ℕ) (hs : ∀ i, s i < 2) (hp : ProperDigits 2 s) (m : ℕ)
    (p : List Bool) (hsp : ∀ k < 2 * m, cdL k p = s k) :
    ⌊Real.sqrt (realOfDigits 2 s) * 2 ^ m⌋₊ = sqrtPhi m p := by
  have hy := (realOfDigits_mem_Ico 2 le_rfl s hs hp).1
  have e : Real.sqrt (realOfDigits 2 s) * 2 ^ m = Real.sqrt (realOfDigits 2 s * 2 ^ (2 * m)) := by
    rw [Real.sqrt_mul hy, show (2 : ℝ) ^ (2 * m) = (2 ^ m) ^ 2 by rw [← pow_mul, mul_comm],
      Real.sqrt_sq (by positivity)]
  rw [e, floor_sqrt _ (by positivity), floor_mul_two_pow _ hs hp, sqrtPhi]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
  rw [hsp k (List.mem_range.1 hk)]

end NormalNumbers.SqrtFloor
