/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyPinsker
import NormalNumbers.G4EntropyDiagonal

/-!
# The `ℓ`-block coordinates of a sampled window

`ZSample_eq_blockVal` says the sampled value `Z^x_{K,α}(n)` is the `m`-bit binary window of `x`
at position `2·kIdx`.  The frequency theorem needs that window broken into its `ℓ`-bit *blocks*,
because the entropy of the whole window bounds the sum of the block entropies
(`FinLaw.H₂_le_sum_H₂_map`) and each block entropy bounds that block's word frequencies
(`sq_prob_sub_le_logb_card_sub_H₂`).

This module supplies the combinatorial layer, with no analysis in it at all.

* `blockVal_lt`, `blockVal_add` — the window value is an `m`-bit number, and a window splits as
  `blockVal y p (a+b) = blockVal y p a · 2^b + blockVal y (p+a) b`.  Everything else follows
  from these two.
* `blkAt m ℓ j : Fin (2^m) → Fin (2^ℓ)` — the `j`-th aligned `ℓ`-block of an `m`-bit value,
  namely `z / 2^(m − (j+1)ℓ) % 2^ℓ`.  The *last* index `j = m/ℓ` is the low-order `ℓ` bits
  (`m − (j+1)ℓ` truncates to `0`), which overlaps block `m/ℓ − 1` but sweeps up the `m % ℓ`
  leftover bits — that redundancy is exactly what makes the family jointly injective without
  assuming `ℓ ∣ m`.
* `blkAt_injective` — the `m/ℓ + 1` coordinates determine the window.  This is the hypothesis
  of `FinLaw.H₂_le_sum_H₂_map`, so it is the load-bearing statement of the module.
* `blkAt_blockVal` — the dictionary: for `(j+1)ℓ ≤ m` the `j`-th coordinate of a window of `x`
  is the `ℓ`-bit window of `x` at position `p + jℓ`.  This is what turns an entropy statement
  about the sample into a statement about the *digits* of `x`.
-/

open Finset

namespace NormalNumbers.G4Entropy

/-! ### Window arithmetic -/

/-- A length-`m` binary window is an `m`-bit number. -/
lemma blockVal_lt (y : ℝ) (p : ℕ) : ∀ m : ℕ, blockVal y p m < 2 ^ m := by
  intro m
  induction m with
  | zero => simp [blockVal]
  | succ m ih =>
    rw [blockVal_succ]
    have hd : digitOf 2 y (p + m) < 2 := digitOf_lt 2 le_rfl y _
    have : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
    omega

/-- **Splitting a window.**  The first `a` digits contribute the high part, the next `b` the
low part. -/
lemma blockVal_add (y : ℝ) (p a : ℕ) : ∀ b : ℕ,
    blockVal y p (a + b) = blockVal y p a * 2 ^ b + blockVal y (p + a) b := by
  intro b
  induction b with
  | zero => simp [blockVal]
  | succ b ih =>
    have hassoc : p + (a + b) = (p + a) + b := by omega
    rw [show a + (b + 1) = (a + b) + 1 by omega, blockVal_succ, ih, blockVal_succ, hassoc]
    ring

/-! ### The block coordinates -/

/-- The `j`-th aligned `ℓ`-block of an `m`-bit value, read from the high end. -/
def blkAt (m ℓ j : ℕ) (z : Fin (2 ^ m)) : Fin (2 ^ ℓ) :=
  ⟨(z : ℕ) / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ, Nat.mod_lt _ (by positivity)⟩

@[simp] lemma blkAt_val (m ℓ j : ℕ) (z : Fin (2 ^ m)) :
    ((blkAt m ℓ j z : Fin (2 ^ ℓ)) : ℕ) = (z : ℕ) / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ := rfl

/-- The prefix recursion behind joint injectivity: agreeing on the first `j` blocks forces the
top `jℓ` bits to agree. -/
private lemma prefix_congr {m ℓ : ℕ} (hℓ : 0 < ℓ) {z z' : ℕ} (hz : z < 2 ^ m) (hz' : z' < 2 ^ m)
    (h : ∀ j < m / ℓ, z / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ
      = z' / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ) :
    ∀ j ≤ m / ℓ, z / 2 ^ (m - j * ℓ) = z' / 2 ^ (m - j * ℓ) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.zero_mul, Nat.sub_zero]
    rw [Nat.div_eq_of_lt hz, Nat.div_eq_of_lt hz']
  | succ j ih =>
    intro hj
    have hjr : j ≤ m / ℓ := by omega
    have hle : (j + 1) * ℓ ≤ m :=
      le_trans (Nat.mul_le_mul_right ℓ hj) (Nat.div_mul_le_self m ℓ)
    have hsplit : m - j * ℓ = (m - (j + 1) * ℓ) + ℓ := by
      have : (j + 1) * ℓ = j * ℓ + ℓ := by ring
      omega
    have key : ∀ w : ℕ, w / 2 ^ (m - (j + 1) * ℓ)
        = 2 ^ ℓ * (w / 2 ^ (m - j * ℓ)) + (w / 2 ^ (m - (j + 1) * ℓ)) % 2 ^ ℓ := by
      intro w
      have hdd : w / 2 ^ (m - (j + 1) * ℓ) / 2 ^ ℓ = w / 2 ^ (m - j * ℓ) := by
        rw [Nat.div_div_eq_div_mul, ← pow_add, ← hsplit]
      have hdm := Nat.div_add_mod (w / 2 ^ (m - (j + 1) * ℓ)) (2 ^ ℓ)
      rw [hdd] at hdm
      exact hdm.symm
    calc z / 2 ^ (m - (j + 1) * ℓ)
        = 2 ^ ℓ * (z / 2 ^ (m - j * ℓ)) + (z / 2 ^ (m - (j + 1) * ℓ)) % 2 ^ ℓ := key z
      _ = 2 ^ ℓ * (z' / 2 ^ (m - j * ℓ)) + (z' / 2 ^ (m - (j + 1) * ℓ)) % 2 ^ ℓ := by
          rw [ih hjr, h j (by omega)]
      _ = z' / 2 ^ (m - (j + 1) * ℓ) := (key z').symm

/-- **The `m/ℓ + 1` block coordinates determine the window.**  This is the joint-injectivity
hypothesis of `FinLaw.H₂_le_sum_H₂_map`.

No divisibility assumption: the last coordinate is the low `ℓ` bits, which overlaps the
previous block but covers the `m % ℓ` digits that the aligned blocks miss. -/
theorem blkAt_injective {m ℓ : ℕ} (hℓ : 0 < ℓ) :
    Function.Injective (fun z : Fin (2 ^ m) => fun j : Fin (m / ℓ + 1) => blkAt m ℓ j z) := by
  intro z z' hzz
  set r := m / ℓ with hr
  have hcoord : ∀ j : ℕ, j < r + 1 →
      (z : ℕ) / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ
        = (z' : ℕ) / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ := by
    intro j hj
    have := congrFun hzz ⟨j, hj⟩
    exact congrArg Fin.val this
  have hpre := prefix_congr hℓ z.isLt z'.isLt (fun j hj => hcoord j (by omega))
  -- the leftover `m % ℓ` bits
  have hmod : m % ℓ < ℓ := Nat.mod_lt _ hℓ
  have hdm : ℓ * r + m % ℓ = m := Nat.div_add_mod m ℓ
  have hrl : (r + 1) * ℓ = ℓ * r + ℓ := by ring
  have hlt : m < (r + 1) * ℓ := by omega
  have ht : m - r * ℓ = m % ℓ := by
    have : r * ℓ = ℓ * r := by ring
    omega
  have htop : (z : ℕ) / 2 ^ (m % ℓ) = (z' : ℕ) / 2 ^ (m % ℓ) := by
    have := hpre r le_rfl
    rwa [ht] at this
  have hlow : (z : ℕ) % 2 ^ (m % ℓ) = (z' : ℕ) % 2 ^ (m % ℓ) := by
    have hzero : m - (r + 1) * ℓ = 0 := by omega
    have hr1 := hcoord r (by omega)
    simp only [hzero, pow_zero, Nat.div_one] at hr1
    have hdvd : (2 : ℕ) ^ (m % ℓ) ∣ 2 ^ ℓ := pow_dvd_pow 2 hmod.le
    calc (z : ℕ) % 2 ^ (m % ℓ) = (z : ℕ) % 2 ^ ℓ % 2 ^ (m % ℓ) :=
          (Nat.mod_mod_of_dvd _ hdvd).symm
      _ = (z' : ℕ) % 2 ^ ℓ % 2 ^ (m % ℓ) := by rw [hr1]
      _ = (z' : ℕ) % 2 ^ (m % ℓ) := Nat.mod_mod_of_dvd _ hdvd
  refine Fin.ext ?_
  have hz := Nat.div_add_mod (z : ℕ) (2 ^ (m % ℓ))
  have hz' := Nat.div_add_mod (z' : ℕ) (2 ^ (m % ℓ))
  rw [htop, hlow] at hz
  omega

/-! ### The dictionary to digits -/

/-- **The `j`-th block coordinate of a window of `y` is the `ℓ`-bit window of `y` at
`p + jℓ`.** -/
theorem blkAt_blockVal (y : ℝ) (p m ℓ j : ℕ) (h : (j + 1) * ℓ ≤ m) :
    blkAt m ℓ j ⟨blockVal y p m, blockVal_lt y p m⟩
      = ⟨blockVal y (p + j * ℓ) ℓ, blockVal_lt y (p + j * ℓ) ℓ⟩ := by
  refine Fin.ext ?_
  rw [blkAt_val]
  set s := j * ℓ with hs
  set t := m - (j + 1) * ℓ with ht
  have hm : m = s + (ℓ + t) := by
    have : (j + 1) * ℓ = j * ℓ + ℓ := by ring
    omega
  have hsplit : blockVal y p m
      = blockVal y (p + s + ℓ) t
        + (blockVal y (p + s) ℓ + blockVal y p s * 2 ^ ℓ) * 2 ^ t := by
    rw [hm, blockVal_add y p s (ℓ + t), blockVal_add y (p + s) ℓ t, pow_add]
    ring
  have hlowlt : blockVal y (p + s + ℓ) t < 2 ^ t := blockVal_lt _ _ _
  have hdiv : blockVal y p m / 2 ^ t
      = blockVal y (p + s) ℓ + blockVal y p s * 2 ^ ℓ := by
    rw [hsplit, Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ t),
      Nat.div_eq_of_lt hlowlt]
    omega
  rw [hdiv, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (blockVal_lt _ _ _)]

end NormalNumbers.G4Entropy
