/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Progression
import NormalNumbers.G4EntropyInfo
import NormalNumbers.Disjunctive

/-!
# Entropy expedition §2: freezing the arithmetic sample

For a `GridParams` `G`, a scale `X`, an atom `α` and a sample point `n ∈ P = apSample X G.P₀ G.b₀`,
`G.exists_mult_mul` gives `n = t_α + d_α k` with `d_α ∣ k`.  The **orbit index** is

  `kIdx G n α = (n - t_α) / d_α`,

and `kIdx_spec` proves the exact identity `n = t_α + d_α · kIdx G n α` on `P` (so natural
subtraction and division never leak junk: they are only used inside their proved domain).

For `x ∈ ℝ` we then sample the base-four orbit and quantize it to `m` binary bits:

  `uSample G x n α = Int.fract (4 ^ kIdx G n α * x)`,
  `ZSample G m x n α = ⌊2 ^ m * uSample G x n α⌋₊`.

**The dictionary** (`ZSample_eq_blockVal`): `ZSample` is exactly the `m`-bit binary block of `x`
beginning at zero-based digit position `2 · kIdx G n α` — the factor two is the base-four ↔
base-two shift, and losing it changes the sampling law.  It is proved from scratch here through
two elementary floor identities that hold for every `0 ≤ y`:

* `floor_two_pow_succ` : `⌊y·2^{i+1}⌋ = 2⌊y·2^i⌋ + digitOf 2 y i`;
* `floor_two_pow_add`  : `⌊y·2^{j+m}⌋ = 2^m⌊y·2^j⌋ + blockVal y j m`.

`blockVal y j m = ∑_{i<m} digitOf 2 y (j+i) · 2^{m-1-i}` is the value of the length-`m` digit
window at `j`, so `OccursAt 2 x w j` pins `blockVal` (`blockVal_eq_of_occursAt`), which is the
link from the entropy sample back to the word-occurrence language of `IsDisjunctive`/`IsNormal`.

The **joint law** of the whole vector `α ↦ ZSample … α` is the pushforward of *one* uniform
choice of `n ∈ P` (`jointLaw`), never independent choices per atom.
-/

open Finset

namespace NormalNumbers.G4Entropy

/-! ### Binary windows: elementary floor identities -/

/-- The value of the length-`m` binary window of `y` starting at zero-based position `j`. -/
noncomputable def blockVal (y : ℝ) (j m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, digitOf 2 y (j + i) * 2 ^ (m - 1 - i)

@[simp] lemma blockVal_zero (y : ℝ) (j : ℕ) : blockVal y j 0 = 0 := by simp [blockVal]

/-- One step of the binary expansion: the floor doubles and picks up the next digit. -/
lemma floor_two_pow_succ {y : ℝ} (hy : 0 ≤ y) (i : ℕ) :
    ⌊y * 2 ^ (i + 1)⌋ = 2 * ⌊y * 2 ^ i⌋ + (digitOf 2 y i : ℤ) := by
  have ht : y * (2 : ℝ) ^ (i + 1) = 2 * (y * 2 ^ i) := by ring
  set t : ℝ := y * (2 : ℝ) ^ i with htdef
  have htnn : 0 ≤ t := by positivity
  have hB : ((⌊t⌋ : ℤ) : ℝ) ≤ t := Int.floor_le t
  have hB2 : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
  have hA1 : 2 * ⌊t⌋ ≤ ⌊2 * t⌋ := by
    refine Int.le_floor.2 ?_
    push_cast
    linarith
  have hA2 : ⌊2 * t⌋ < 2 * ⌊t⌋ + 2 := by
    refine Int.floor_lt.2 ?_
    push_cast
    linarith
  have hnn : 0 ≤ ⌊2 * t⌋ := Int.floor_nonneg.2 (by linarith)
  have hd : (digitOf 2 y i : ℤ) = ⌊2 * t⌋ % 2 := by
    unfold digitOf
    have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [h2, ht]
    push_cast [Int.toNat_of_nonneg hnn]
    rfl
  rw [ht, hd]
  omega

/-- The window identity: shifting the floor by `m` binary places adds the length-`m` window. -/
lemma floor_two_pow_add {y : ℝ} (hy : 0 ≤ y) (j m : ℕ) :
    ⌊y * 2 ^ (j + m)⌋ = 2 ^ m * ⌊y * 2 ^ j⌋ + (blockVal y j m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := floor_two_pow_succ hy (j + m)
      have hjm : j + (m + 1) = (j + m) + 1 := by omega
      rw [hjm, hstep, ih]
      have hblk : (blockVal y j (m + 1) : ℤ)
          = 2 * (blockVal y j m : ℤ) + (digitOf 2 y (j + m) : ℤ) := by
        unfold blockVal
        simp only [Nat.add_sub_cancel, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
        push_cast
        rw [Finset.mul_sum]
        have hkey : ∀ i ∈ Finset.range m,
            (digitOf 2 y (j + i) : ℤ) * 2 ^ (m - i)
              = 2 * ((digitOf 2 y (j + i) : ℤ) * 2 ^ (m - 1 - i)) := by
          intro i hi
          have hi' : i < m := Finset.mem_range.1 hi
          have he : m - i = (m - 1 - i) + 1 := by omega
          rw [he, pow_succ]
          ring
        rw [Finset.sum_congr rfl hkey]
      rw [hblk]
      ring

/-- A word occurring at position `j` pins the window value. -/
lemma blockVal_eq_of_occursAt {x : ℝ} {w : List ℕ} {j : ℕ} (h : OccursAt 2 x w j) :
    blockVal (Int.fract x) j w.length
      = ∑ i ∈ Finset.range w.length, w.getD i 0 * 2 ^ (w.length - 1 - i) := by
  unfold blockVal
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < w.length := Finset.mem_range.1 hi
  rw [h i hi', List.getD_eq_getElem w 0 hi']

/-! ### The sampled orbit index -/

open NormalNumbers.G4

variable (G : NormalNumbers.G4.GridParams)

/-- The base-four orbit index of the sample point `n` at the atom `α`. -/
def kIdx (n : ℕ) (α : G.Atom) : ℕ := (n - G.t α) / G.d α

/-- **The exact identity on the sample**: `n = t_α + d_α · kIdx n α`, with `d_α ∣ kIdx n α`
(the frozen multiplier residue).  Natural subtraction and division are used only here, inside
their proved domain. -/
theorem kIdx_spec {X n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀) (α : G.Atom) :
    n = G.t α + G.d α * kIdx G n α ∧ G.d α ∣ kIdx G n α := by
  obtain ⟨k, hk1, hk2⟩ := G.exists_mult_mul hn α
  have hd : 0 < G.d α := G.d_pos α
  have hk : kIdx G n α = k := by
    unfold kIdx
    rw [hk1]
    simp [Nat.mul_div_cancel_left _ hd]
  rw [hk]
  exact ⟨hk1, hk2⟩

/-! ### The quantized sample -/

/-- The sampled base-four orbit point `u = {4^k x}`. -/
noncomputable def uSample (x : ℝ) (n : ℕ) (α : G.Atom) : ℝ :=
  Int.fract ((4 : ℝ) ^ kIdx G n α * x)

/-- The `m`-bit quantization `Z = ⌊2^m u⌋` of the sampled orbit point. -/
noncomputable def ZSample (m : ℕ) (x : ℝ) (n : ℕ) (α : G.Atom) : ℕ :=
  ⌊(2 : ℝ) ^ m * uSample G x n α⌋₊

lemma uSample_mem_Ico (x : ℝ) (n : ℕ) (α : G.Atom) :
    uSample G x n α ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Coordinate range: `Z` is an `m`-bit value. -/
lemma ZSample_lt (m : ℕ) (x : ℝ) (n : ℕ) (α : G.Atom) : ZSample G m x n α < 2 ^ m := by
  have h1 : uSample G x n α < 1 := Int.fract_lt_one _
  have h2 : (0 : ℝ) ≤ uSample G x n α := Int.fract_nonneg _
  have hlt : (2 : ℝ) ^ m * uSample G x n α < 2 ^ m := by
    have : (0 : ℝ) < 2 ^ m := by positivity
    nlinarith
  rw [ZSample, Nat.floor_lt (by positivity)]
  push_cast
  exact hlt

/-! ### The dictionary: `Z` is the binary window at position `2k` -/

/-- `⌊2^m {2^j y}⌋` is the length-`m` binary window of `y` at `j`, for `0 ≤ y`. -/
lemma floor_fract_eq_blockVal {y : ℝ} (hy : 0 ≤ y) (j m : ℕ) :
    ⌊(2 : ℝ) ^ m * Int.fract ((2 : ℝ) ^ j * y)⌋₊ = blockVal y j m := by
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ m * Int.fract ((2 : ℝ) ^ j * y) := by
    have := Int.fract_nonneg ((2 : ℝ) ^ j * y)
    positivity
  have hfr : (2 : ℝ) ^ m * Int.fract ((2 : ℝ) ^ j * y)
      = y * 2 ^ (j + m) - ((2 ^ m * ⌊y * 2 ^ j⌋ : ℤ) : ℝ) := by
    simp only [Int.fract]
    have hcomm : (2 : ℝ) ^ j * y = y * 2 ^ j := by ring
    rw [hcomm]
    push_cast
    rw [pow_add]
    ring
  have hfloor : ⌊(2 : ℝ) ^ m * Int.fract ((2 : ℝ) ^ j * y)⌋ = (blockVal y j m : ℤ) := by
    rw [hfr, Int.floor_sub_intCast, floor_two_pow_add hy j m]
    ring
  have := Int.floor_toNat (α := ℝ) ((2 : ℝ) ^ m * Int.fract ((2 : ℝ) ^ j * y))
  rw [hfloor] at this
  simpa using this.symm

/-- **The dictionary** (brief §2): the quantized sample `Z` is exactly the `m`-bit binary
window of `x` beginning at zero-based digit position `2·k`, where `k` is the base-four orbit
index.  The factor two is the base-four ↔ base-two shift. -/
theorem ZSample_eq_blockVal (m : ℕ) (x : ℝ) (n : ℕ) (α : G.Atom) :
    ZSample G m x n α = blockVal (Int.fract x) (2 * kIdx G n α) m := by
  have hy : (0 : ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have hfour : (4 : ℝ) ^ kIdx G n α = (2 : ℝ) ^ (2 * kIdx G n α) := by
    rw [pow_mul]; norm_num
  have hfract : Int.fract ((4 : ℝ) ^ kIdx G n α * x)
      = Int.fract ((2 : ℝ) ^ (2 * kIdx G n α) * Int.fract x) := by
    rw [hfour]
    have hx : (2 : ℝ) ^ (2 * kIdx G n α) * x
        = (2 : ℝ) ^ (2 * kIdx G n α) * Int.fract x
          + ((2 ^ (2 * kIdx G n α) * ⌊x⌋ : ℤ) : ℝ) := by
      simp only [Int.fract]
      push_cast
      ring
    rw [hx, Int.fract_add_intCast]
  unfold ZSample uSample
  rw [hfract, floor_fract_eq_blockVal hy]

/-! ### The joint law -/

/-- The joint quantized sample vector at scale `m`, as a function of one sample point `n`.
Its coordinates are genuine `m`-bit values (`ZSample_lt`). -/
noncomputable def ZVec (m : ℕ) (x : ℝ) (n : ℕ) : G.Atom → Fin (2 ^ m) :=
  fun α => ⟨ZSample G m x n α, ZSample_lt G m x n α⟩

/-- `P_K` is nonempty as soon as the scale exceeds the residue. -/
lemma apSample_nonempty {X : ℕ} (hX : G.b₀ < X) :
    (apSample X G.P₀ G.b₀).Nonempty := by
  refine ⟨G.b₀, ?_⟩
  rw [apSample, Finset.mem_filter, Finset.mem_range]
  exact ⟨hX, Nat.mod_eq_of_lt G.b₀_lt_P₀⟩

/-- **The joint law** of `Z^x_K`: the pushforward of *one* uniform choice of `n ∈ P_K`.
Never independent choices per atom. -/
noncomputable def jointLaw {X : ℕ} (hX : G.b₀ < X) (m : ℕ) (x : ℝ) :
    FinLaw (G.Atom → Fin (2 ^ m)) :=
  empirical (apSample X G.P₀ G.b₀) (apSample_nonempty G hX) (ZVec G m x)

/-- Sanity bound, half one: `H₂(Z) ≤ log₂ |P_K|`. -/
theorem H₂_jointLaw_le_card {X : ℕ} (hX : G.b₀ < X) (m : ℕ) (x : ℝ) :
    (jointLaw G hX m x).H₂ ≤ Real.logb 2 (apSample X G.P₀ G.b₀).card :=
  H₂_empirical_le _ _

/-- Sanity bound, half two: `H₂(Z) ≤ m · H_K`, the full joint alphabet size.  Here
`H_K = |Atom| = (s+1)^K` and each coordinate carries `m` bits. -/
theorem H₂_jointLaw_le_mul {X : ℕ} (hX : G.b₀ < X) (m : ℕ) (x : ℝ) :
    (jointLaw G hX m x).H₂ ≤ m * (Fintype.card G.Atom : ℝ) := by
  classical
  have hcard : Fintype.card (G.Atom → Fin (2 ^ m)) = (2 ^ m) ^ Fintype.card G.Atom := by
    simp
  have hpos : 0 < Fintype.card (G.Atom → Fin (2 ^ m)) := by
    rw [hcard]
    positivity
  refine ((jointLaw G hX m x).H₂_le_logb_card hpos).trans_eq ?_
  rw [hcard]
  push_cast
  rw [← Real.rpow_natCast ((2 : ℝ) ^ m) (Fintype.card G.Atom), ← Real.rpow_natCast (2 : ℝ) m,
    ← Real.rpow_mul (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]

end NormalNumbers.G4Entropy
