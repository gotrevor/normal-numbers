/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs

/-!
# The digit ↔ interval dictionary

Toolkit connecting the digit map `digitOf` with b-adic intervals, the raw
material for Wall's theorem:

* `floor_mul_pow_succ`: the floor recursion
  `⌊y·b^(k+1)⌋ = b·⌊y·b^k⌋ + digitOf b y k` (for `y ≥ 0`);
* `digitOf_lt`: every digit is `< b`;
* `floor_eq_digitVal`: for `y ∈ [0,1)`, `⌊y·b^k⌋` is the base-`b` value of
  the first `k` digits of `y`;
* `blockNatVal`: big-endian base-`b` value of a digit block, with its
  arithmetic (`blockNatVal_cons`, `blockNatVal_lt`, `blockNatVal_eq_sum`,
  `blockNatVal_inj`);
* `padWord`: the length-`k` base-`b` block naming any value below `b^k`;
* `mem_Ico_div_pow_iff_floor_eq`: `y ∈ [n/b^k, (n+1)/b^k) ↔ ⌊y·b^k⌋ = n`;
* `digits_prefix_iff`: for `y ∈ [0,1)`, the first `w.length` digits of `y`
  spell exactly `w` iff `y` lies in the b-adic interval of `w`;
* `digitOf_orbit`: digit `j` of `orbit b x i` is digit `i + j` of `x`.
-/

namespace NormalNumbers

/-! ## The floor recursion -/

/-- **Floor recursion**: for `y ≥ 0`, going one digit deeper multiplies the
integer part by `b` and adds the next digit:
`⌊y·b^(k+1)⌋ = b·⌊y·b^k⌋ + digitOf b y k`. -/
theorem floor_mul_pow_succ (b : ℕ) (hb : 2 ≤ b) (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    ⌊y * (b : ℝ) ^ (k + 1)⌋ = b * ⌊y * (b : ℝ) ^ k⌋ + (digitOf b y k : ℤ) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have h1 : (b : ℤ) * ⌊y * (b : ℝ) ^ k⌋ ≤ ⌊y * (b : ℝ) ^ (k + 1)⌋ := by
    refine Int.le_floor.mpr ?_
    push_cast
    calc (b : ℝ) * (⌊y * (b : ℝ) ^ k⌋ : ℝ)
        ≤ (b : ℝ) * (y * (b : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (Int.floor_le _) hb0.le
      _ = y * (b : ℝ) ^ (k + 1) := by ring
  have h2 : ⌊y * (b : ℝ) ^ (k + 1)⌋ < (b : ℤ) * ⌊y * (b : ℝ) ^ k⌋ + b := by
    have h2' : ⌊y * (b : ℝ) ^ (k + 1)⌋ < (b : ℤ) * (⌊y * (b : ℝ) ^ k⌋ + 1) := by
      refine Int.floor_lt.mpr ?_
      push_cast
      calc y * (b : ℝ) ^ (k + 1) = (b : ℝ) * (y * (b : ℝ) ^ k) := by ring
        _ < (b : ℝ) * ((⌊y * (b : ℝ) ^ k⌋ : ℝ) + 1) :=
          mul_lt_mul_of_pos_left (Int.lt_floor_add_one _) hb0
    calc ⌊y * (b : ℝ) ^ (k + 1)⌋ < (b : ℤ) * (⌊y * (b : ℝ) ^ k⌋ + 1) := h2'
      _ = (b : ℤ) * ⌊y * (b : ℝ) ^ k⌋ + b := by ring
  have hA0 : 0 ≤ ⌊y * (b : ℝ) ^ (k + 1)⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg hy (by positivity))
  have hd : (digitOf b y k : ℤ) = ⌊y * (b : ℝ) ^ (k + 1)⌋ % b := by
    unfold digitOf
    push_cast
    rw [Int.toNat_of_nonneg hA0]
  have hmod : ⌊y * (b : ℝ) ^ (k + 1)⌋ % (b : ℤ)
      = ⌊y * (b : ℝ) ^ (k + 1)⌋ - (b : ℤ) * ⌊y * (b : ℝ) ^ k⌋ := by
    have h3 : (⌊y * (b : ℝ) ^ (k + 1)⌋ - (b : ℤ) * ⌊y * (b : ℝ) ^ k⌋) % (b : ℤ)
        = ⌊y * (b : ℝ) ^ (k + 1)⌋ - (b : ℤ) * ⌊y * (b : ℝ) ^ k⌋ :=
      Int.emod_eq_of_lt (by linarith) (by linarith)
    have h4 : (⌊y * (b : ℝ) ^ (k + 1)⌋ - (b : ℤ) * ⌊y * (b : ℝ) ^ k⌋
          + (b : ℤ) * ⌊y * (b : ℝ) ^ k⌋) % (b : ℤ)
        = (⌊y * (b : ℝ) ^ (k + 1)⌋ - (b : ℤ) * ⌊y * (b : ℝ) ^ k⌋) % (b : ℤ) :=
      Int.add_mul_emod_self_left _ _ _
    rw [show ⌊y * (b : ℝ) ^ (k + 1)⌋ - (b : ℤ) * ⌊y * (b : ℝ) ^ k⌋
        + (b : ℤ) * ⌊y * (b : ℝ) ^ k⌋ = ⌊y * (b : ℝ) ^ (k + 1)⌋ by ring] at h4
    exact h4.trans h3
  rw [hd, hmod]
  ring

/-- Every digit of the base-`b` expansion is `< b`. -/
theorem digitOf_lt (b : ℕ) (hb : 2 ≤ b) (y : ℝ) (k : ℕ) : digitOf b y k < b :=
  Nat.mod_lt _ (by omega)

/-! ## Digit reconstruction of the floor -/

/-- **Digit reconstruction**: for `y ∈ [0,1)`, the integer part of `y·b^k`
is the base-`b` value of the first `k` digits of `y` (an identity in `ℤ`). -/
theorem floor_eq_digitVal (b : ℕ) (hb : 2 ≤ b) (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (k : ℕ) :
    ⌊y * (b : ℝ) ^ k⌋
      = ∑ j ∈ Finset.range k, (digitOf b y j : ℤ) * (b : ℤ) ^ (k - 1 - j) := by
  induction k with
  | zero => simpa using Int.floor_eq_zero_iff.mpr hy
  | succ k ih =>
      rw [floor_mul_pow_succ b hb y hy.1 k, ih, Finset.sum_range_succ]
      have h0 : k + 1 - 1 - k = 0 := by omega
      simp only [h0, pow_zero, mul_one]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j < k := Finset.mem_range.mp hj
      have hexp : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
      rw [hexp, pow_succ]
      ring

/-! ## Digit blocks and their b-adic value -/

/-- Big-endian base-`b` value of a digit block `w`:
`blockNatVal b [d₀, d₁, …] = d₀·b^(len−1) + d₁·b^(len−2) + ⋯`. -/
def blockNatVal (b : ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun acc d => acc * b + d) 0

private theorem foldl_mul_add (b : ℕ) (w : List ℕ) (a : ℕ) :
    w.foldl (fun acc d => acc * b + d) a
      = a * b ^ w.length + w.foldl (fun acc d => acc * b + d) 0 := by
  induction w generalizing a with
  | nil => simp
  | cons d w ih =>
      simp only [List.foldl_cons, List.length_cons, zero_mul, zero_add]
      rw [ih (a * b + d), ih d]
      ring

/-- Peeling the leading digit off a block. -/
theorem blockNatVal_cons (b d : ℕ) (w : List ℕ) :
    blockNatVal b (d :: w) = d * b ^ w.length + blockNatVal b w := by
  show (d :: w).foldl (fun acc e => acc * b + e) 0 = d * b ^ w.length + blockNatVal b w
  simp only [List.foldl_cons, zero_mul, zero_add]
  exact foldl_mul_add b w d

/-- A block of digits `< b` has value `< b^length`. -/
theorem blockNatVal_lt (b : ℕ) (w : List ℕ) (hw : ∀ d ∈ w, d < b) :
    blockNatVal b w < b ^ w.length := by
  induction w with
  | nil =>
      show (0 : ℕ) < b ^ 0
      rw [pow_zero]
      exact Nat.zero_lt_one
  | cons d w ih =>
      have hd : d < b := hw d (by simp)
      have hw' : ∀ e ∈ w, e < b := fun e he => hw e (by simp [he])
      rw [blockNatVal_cons, List.length_cons]
      calc d * b ^ w.length + blockNatVal b w
          < d * b ^ w.length + b ^ w.length := Nat.add_lt_add_left (ih hw') _
        _ = (d + 1) * b ^ w.length := by ring
        _ ≤ b * b ^ w.length := Nat.mul_le_mul (by omega) (Nat.le_refl _)
        _ = b ^ (w.length + 1) := by ring

/-- `blockNatVal` as an explicit sum: the digit at position `j` carries
weight `b^(len−1−j)`. -/
theorem blockNatVal_eq_sum (b : ℕ) (w : List ℕ) :
    blockNatVal b w
      = ∑ j ∈ Finset.range w.length, w.getD j 0 * b ^ (w.length - 1 - j) := by
  induction w with
  | nil =>
      simp only [List.length_nil, Finset.range_zero, Finset.sum_empty]
      rfl
  | cons d w ih =>
      have hstep : ∑ j ∈ Finset.range (w.length + 1),
            (d :: w).getD j 0 * b ^ (w.length + 1 - 1 - j)
          = (∑ j ∈ Finset.range w.length, w.getD j 0 * b ^ (w.length - 1 - j))
            + d * b ^ w.length := by
        rw [Finset.sum_range_succ']
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [List.getD_cons_succ]
        congr 1
        congr 1
        omega
      calc blockNatVal b (d :: w)
          = d * b ^ w.length + blockNatVal b w := blockNatVal_cons b d w
        _ = d * b ^ w.length
            + ∑ j ∈ Finset.range w.length, w.getD j 0 * b ^ (w.length - 1 - j) := by
            rw [ih]
        _ = (∑ j ∈ Finset.range w.length, w.getD j 0 * b ^ (w.length - 1 - j))
            + d * b ^ w.length := Nat.add_comm _ _
        _ = ∑ j ∈ Finset.range (w.length + 1),
              (d :: w).getD j 0 * b ^ (w.length + 1 - 1 - j) := hstep.symm
        _ = ∑ j ∈ Finset.range (d :: w).length,
              (d :: w).getD j 0 * b ^ ((d :: w).length - 1 - j) := by
            rw [List.length_cons]

/-- Base-`b` uniqueness: two blocks of digits `< b` with the same length and
the same value are equal. -/
theorem blockNatVal_inj (b : ℕ) (hb : 1 ≤ b) (w₁ : List ℕ) :
    ∀ w₂ : List ℕ, w₁.length = w₂.length →
      (∀ d ∈ w₁, d < b) → (∀ d ∈ w₂, d < b) →
      blockNatVal b w₁ = blockNatVal b w₂ → w₁ = w₂ := by
  induction w₁ with
  | nil =>
      intro w₂ hlen _ _ _
      cases w₂ with
      | nil => rfl
      | cons d₂ w₂ => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons d₁ w₁ ih =>
      intro w₂ hlen h₁ h₂ hval
      cases w₂ with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons d₂ w₂ =>
          have hlen' : w₁.length = w₂.length := by
            simp only [List.length_cons] at hlen; omega
          have hB : (0 : ℕ) < b ^ w₂.length := pow_pos (by omega) _
          have hw₁ : ∀ e ∈ w₁, e < b := fun e he => h₁ e (by simp [he])
          have hw₂ : ∀ e ∈ w₂, e < b := fun e he => h₂ e (by simp [he])
          have hv₁ : blockNatVal b w₁ < b ^ w₂.length := by
            rw [← hlen']
            exact blockNatVal_lt b w₁ hw₁
          have hv₂ : blockNatVal b w₂ < b ^ w₂.length := blockNatVal_lt b w₂ hw₂
          rw [blockNatVal_cons, blockNatVal_cons, hlen'] at hval
          have extract : ∀ d v : ℕ, v < b ^ w₂.length →
              (d * b ^ w₂.length + v) / b ^ w₂.length = d
              ∧ (d * b ^ w₂.length + v) % b ^ w₂.length = v := by
            intro d v hv
            refine ⟨?_, ?_⟩
            · rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hv, Nat.add_zero]
            · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
          obtain ⟨hd₁, hm₁⟩ := extract d₁ _ hv₁
          obtain ⟨hd₂, hm₂⟩ := extract d₂ _ hv₂
          have hdd : d₁ = d₂ := by rw [← hd₁, ← hd₂, hval]
          have hvv : blockNatVal b w₁ = blockNatVal b w₂ := by rw [← hm₁, ← hm₂, hval]
          rw [hdd, ih w₂ hlen' hw₁ hw₂ hvv]

/-! ### Naming a cell by a block: `padWord` -/

/-- The length-`k` digit block whose value is `m`: big-endian digits of
`m`, zero-padded on the left. -/
def padWord (b k m : ℕ) : List ℕ :=
  List.replicate (k - (Nat.digits b m).length) 0 ++ (Nat.digits b m).reverse

theorem length_padWord {b : ℕ} (hb : 2 ≤ b) {k m : ℕ} (hm : m < b ^ k) :
    (padWord b k m).length = k := by
  have hlen : (Nat.digits b m).length ≤ k :=
    (Nat.digits_length_le_iff (by omega) m).mpr hm
  simp only [padWord, List.length_append, List.length_replicate,
    List.length_reverse]
  omega

theorem padWord_digits_lt {b : ℕ} (_hb : 2 ≤ b) (k m : ℕ) :
    ∀ d ∈ padWord b k m, d < b := by
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · rw [List.eq_of_mem_replicate h]
    omega
  · exact Nat.digits_lt_base (by omega) (List.mem_reverse.mp h)

private theorem blockNatVal_replicate_zero_append (b j : ℕ) (v : List ℕ) :
    blockNatVal b (List.replicate j 0 ++ v) = blockNatVal b v := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [List.replicate_succ, List.cons_append]
      show List.foldl (fun acc d => acc * b + d) 0 _ = _
      simp only [List.foldl_cons, Nat.zero_mul, Nat.add_zero]
      exact ih

private theorem foldl_reverse_digits (b : ℕ) (l : List ℕ) :
    l.reverse.foldl (fun acc d => acc * b + d) 0 = Nat.ofDigits b l := by
  rw [List.foldl_reverse]
  induction l with
  | nil => simp [Nat.ofDigits]
  | cons d l ih =>
      rw [List.foldr_cons, Nat.ofDigits_cons, ih]
      ring

theorem blockNatVal_padWord {b : ℕ} (_hb : 2 ≤ b) (k m : ℕ) :
    blockNatVal b (padWord b k m) = m := by
  rw [padWord, blockNatVal_replicate_zero_append]
  show (Nat.digits b m).reverse.foldl (fun acc d => acc * b + d) 0 = m
  rw [foldl_reverse_digits, Nat.ofDigits_digits]

/-! ## Prefix ↔ b-adic interval -/

/-- Membership in a b-adic interval is a statement about the floor:
`y ∈ [n/b^k, (n+1)/b^k) ↔ ⌊y·b^k⌋ = n`. -/
theorem mem_Ico_div_pow_iff_floor_eq (b : ℕ) (hb : 2 ≤ b) (y : ℝ) (k : ℕ) (n : ℤ) :
    y ∈ Set.Ico ((n : ℝ) / (b : ℝ) ^ k) (((n : ℝ) + 1) / (b : ℝ) ^ k)
      ↔ ⌊y * (b : ℝ) ^ k⌋ = n := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hb0 k
  rw [Set.mem_Ico, Int.floor_eq_iff, div_le_iff₀ hbk, lt_div_iff₀ hbk]

/-- **Prefix ↔ b-adic interval**: for `y ∈ [0,1)` and a block `w` of digits
`< b`, the first `w.length` digits of `y` spell exactly `w` iff `y` lies in
the b-adic interval `[v/b^len, (v+1)/b^len)` with `v = blockNatVal b w`. -/
theorem digits_prefix_iff (b : ℕ) (hb : 2 ≤ b) (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b) :
    (∀ j (h : j < w.length), digitOf b y j = w[j])
      ↔ y ∈ Set.Ico ((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length)
          (((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length) := by
  have key : (∀ j (h : j < w.length), digitOf b y j = w[j])
      ↔ ⌊y * (b : ℝ) ^ w.length⌋ = (blockNatVal b w : ℤ) := by
    constructor
    · intro hpre
      rw [floor_eq_digitVal b hb y hy w.length, blockNatVal_eq_sum]
      push_cast
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmw : m < w.length := Finset.mem_range.mp hm
      rw [hpre m hmw, List.getD_eq_getElem w 0 hmw]
    · intro hfloor j hj
      have hlen : (List.ofFn fun i : Fin w.length => digitOf b y i.val).length
          = w.length := List.length_ofFn
      have hval : blockNatVal b (List.ofFn fun i : Fin w.length => digitOf b y i.val)
          = blockNatVal b w := by
        have h1 : ⌊y * (b : ℝ) ^ w.length⌋
            = (blockNatVal b (List.ofFn fun i : Fin w.length => digitOf b y i.val) : ℤ) := by
          rw [floor_eq_digitVal b hb y hy w.length, blockNatVal_eq_sum, hlen]
          push_cast
          refine Finset.sum_congr rfl fun m hm => ?_
          have hmw : m < w.length := Finset.mem_range.mp hm
          have hm2 : m < (List.ofFn fun i : Fin w.length => digitOf b y i.val).length := by
            rw [hlen]; exact hmw
          rw [List.getD_eq_getElem _ _ hm2, List.getElem_ofFn]
        have h2 : (blockNatVal b (List.ofFn fun i : Fin w.length => digitOf b y i.val) : ℤ)
            = (blockNatVal b w : ℤ) := by rw [← h1, hfloor]
        exact_mod_cast h2
      have hveq : (List.ofFn fun i : Fin w.length => digitOf b y i.val) = w :=
        blockNatVal_inj b (by omega) _ w hlen
          (fun e he => by
            obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
            exact digitOf_lt b hb y i)
          hw hval
      have hj2 : j < (List.ofFn fun i : Fin w.length => digitOf b y i.val).length := by
        rw [hlen]; exact hj
      have hgd : digitOf b y j = w.getD j 0 := by
        conv_rhs => rw [← hveq]
        rw [List.getD_eq_getElem _ _ hj2, List.getElem_ofFn]
      rw [hgd, List.getD_eq_getElem w 0 hj]
  rw [key, ← mem_Ico_div_pow_iff_floor_eq b hb y w.length (blockNatVal b w),
    Int.cast_natCast]

/-! ## The shift lemma -/

private theorem sub_mul_emod_self (a c b : ℤ) : (a - c * b) % b = a % b := by
  conv_rhs => rw [show a = a - c * b + b * c by ring]
  rw [Int.add_mul_emod_self_left]

/-- **Shift lemma**: for `x ≥ 0`, digit `j` of the orbit point `b^i·x mod 1`
is digit `i + j` of `x` — shifting the orbit shifts the digit string. -/
theorem digitOf_orbit (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : 0 ≤ x) (i j : ℕ) :
    digitOf b (orbit b x i) j = digitOf b x (i + j) := by
  have hfract : orbit b x i = x * (b : ℝ) ^ i - (⌊x * (b : ℝ) ^ i⌋ : ℝ) :=
    (Int.self_sub_floor (x * (b : ℝ) ^ i)).symm
  have hkey : ⌊orbit b x i * (b : ℝ) ^ (j + 1)⌋
      = ⌊x * (b : ℝ) ^ (i + j + 1)⌋ - ⌊x * (b : ℝ) ^ i⌋ * (b : ℤ) ^ (j + 1) := by
    have h1 : orbit b x i * (b : ℝ) ^ (j + 1)
        = x * (b : ℝ) ^ (i + j + 1)
          - ((⌊x * (b : ℝ) ^ i⌋ * (b : ℤ) ^ (j + 1) : ℤ) : ℝ) := by
      rw [hfract]
      push_cast
      ring
    rw [h1, Int.floor_sub_intCast]
  have hO0 : 0 ≤ ⌊orbit b x i * (b : ℝ) ^ (j + 1)⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (Int.fract_nonneg _) (by positivity))
  have hA0 : 0 ≤ ⌊x * (b : ℝ) ^ (i + j + 1)⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg hx (by positivity))
  have hmod : ⌊orbit b x i * (b : ℝ) ^ (j + 1)⌋ % (b : ℤ)
      = ⌊x * (b : ℝ) ^ (i + j + 1)⌋ % (b : ℤ) := by
    rw [hkey, show ⌊x * (b : ℝ) ^ i⌋ * (b : ℤ) ^ (j + 1)
      = (⌊x * (b : ℝ) ^ i⌋ * (b : ℤ) ^ j) * (b : ℤ) by ring]
    exact sub_mul_emod_self _ _ _
  have hfin : (digitOf b (orbit b x i) j : ℤ) = (digitOf b x (i + j) : ℤ) := by
    unfold digitOf
    push_cast
    rw [Int.toNat_of_nonneg hO0, Int.toNat_of_nonneg hA0]
    exact hmod
  exact_mod_cast hfin

end NormalNumbers
