/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderEngineCore
import NormalNumbers.AdderEndgame

/-!
# Signed channels and the engine meta-theorem (module 6 of the adder wing)

Brief: `BRIEF-adder-signed-engine.md` §Objectives 1–2.

A **signed channel** is a linear form `z = a·X + b·Y` with `a b : ℤ`
(at least one positive coefficient) and an avoided binary word.  The true
carry/borrow of the column addition,

  `carryTZ a b X Y n = ⌊(a·X + b·Y)·2^n⌋ − a·⌊X·2^n⌋ − b·⌊Y·2^n⌋`,

equals `⌊a·fract(X·2^n) + b·fract(Y·2^n)⌋` (`carryTZ_eq_floor_fract`), so it
lies in the window `[−(a⁻+b⁻), a⁺+b⁺−1]` (`carryTZ_nonneg'`, `carryTZ_le'`).
States Nat-encode the carry with offset `+(a⁻+b⁻)`; the automaton step
recovers the digit and outgoing carry with `Int.emod`/`Int.ediv` at modulus 2
(floor-consistent: `v = 2·(v/2) + v%2`, `v%2 ∈ {0,1}` — NOT `Int.div`,
which is T-division).

Shadowing (`zhstep_zfamState`) mirrors the unsigned module; descent and the
certificate checker come from the parametric engine (`AdderEngineCore`).
The payoff is the **engine meta-theorem** `signed_engine`: any signed family
with a passing certificate forces, for every `X Y` not both rational, some
channel word to occur infinitely often in its channel's constant.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-! ## Signed channels -/

/-- A signed channel: linear form `a·X + b·Y` (`a b : ℤ`) and the avoided
binary word. -/
structure ZChannel where
  a : ℤ
  b : ℤ
  word : List ℕ
  deriving Repr, DecidableEq

namespace ZChannel

/-- Word length `ℓ`. -/
def ell (ch : ZChannel) : ℕ := ch.word.length

/-- The carry offset `a⁻ + b⁻` (negative parts). -/
def off (ch : ZChannel) : ℕ := (-ch.a).toNat + (-ch.b).toNat

/-- The positive-part sum `a⁺ + b⁺`. -/
def posSum (ch : ZChannel) : ℕ := ch.a.toNat + ch.b.toNat

/-- Number of encoded carry values: the window `[−off, posSum−1]` has
`posSum + off` points (`= |a| + |b|`). -/
def carrySize (ch : ZChannel) : ℕ := max (ch.posSum + ch.off) 1

/-- Number of window values: `2^(ℓ-1)`. -/
def winSize (ch : ZChannel) : ℕ := 2 ^ (ch.ell - 1)

/-- Channel state count. -/
def size (ch : ZChannel) : ℕ := ch.carrySize * ch.winSize

/-- The word as a `Nat`, bit `j` = `word[j]` (LSB-first). -/
def wordVal (ch : ZChannel) : ℕ := ch.word.foldr (fun d acc => d + 2 * acc) 0

/-- Channel-level predecessor with offset carry encoding: the deeper encoded
state `code'` holds encoded carry `code'/winSize` (true carry minus `−off`)
and window `code' % winSize`.  The column value
`v = a·x + b·y + (encoded carry − off)` splits floor-consistently as
`v = 2·(v/2) + v%2` (`Int.ediv`/`Int.emod`); `none` when the freshly formed
`ℓ`-digit window equals the avoided word. -/
def pred (ch : ZChannel) (x y code' : ℕ) : Option ℕ :=
  if ((ch.a * x + ch.b * y + (code' / ch.winSize : ℕ) - (ch.off : ℤ)) % 2).toNat
      + 2 * (code' % ch.winSize) = ch.wordVal then none
  else some (((ch.a * x + ch.b * y + (code' / ch.winSize : ℕ) - (ch.off : ℤ)) / 2
        + ch.off).toNat * ch.winSize
    + (((ch.a * x + ch.b * y + (code' / ch.winSize : ℕ) - (ch.off : ℤ)) % 2).toNat
        + 2 * (code' % ch.winSize)) % ch.winSize)

theorem winSize_pos (ch : ZChannel) : 0 < ch.winSize := Nat.two_pow_pos _

theorem carrySize_pos (ch : ZChannel) : 0 < ch.carrySize :=
  lt_of_lt_of_le Nat.one_pos (le_max_right _ _)

theorem size_pos (ch : ZChannel) : 0 < ch.size :=
  Nat.mul_pos ch.carrySize_pos ch.winSize_pos

theorem carrySize_eq (ch : ZChannel) (hpos : 1 ≤ ch.posSum) :
    ch.carrySize = ch.posSum + ch.off := by
  unfold carrySize; omega

/-- Coefficient-times-bit bounds: for a bit `x`, `−a⁻ ≤ a·x ≤ a⁺`. -/
theorem coeff_mul_bit_bounds (a : ℤ) (x : ℕ) (hx : x ≤ 1) :
    -(((-a).toNat : ℤ)) ≤ a * x ∧ a * (x : ℤ) ≤ a.toNat := by
  interval_cases x <;>
    simp only [Nat.cast_zero, mul_zero, Nat.cast_one, mul_one] <;>
    constructor <;> omega

theorem pred_lt (ch : ZChannel) (x y code' : ℕ) (hx : x ≤ 1) (hy : y ≤ 1)
    (hpos : 1 ≤ ch.posSum) (hcode : code' < ch.size) {c : ℕ}
    (h : ch.pred x y code' = some c) : c < ch.size := by
  unfold pred at h
  have hw : (0:ℕ) < ch.winSize := ch.winSize_pos
  have hc'lt : code' / ch.winSize < ch.carrySize :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcode)
  have hcs := ch.carrySize_eq hpos
  -- abstract the div/mod of the deeper code (omega cannot divide by a
  -- variable modulus)
  generalize hqe : code' / ch.winSize = q at h hc'lt
  generalize hre : code' % ch.winSize = r at h
  have hr : r < ch.winSize := hre ▸ Nat.mod_lt _ hw
  clear hqe hre
  split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h
    subst h
    set v : ℤ := ch.a * x + ch.b * y + (q : ℤ) - (ch.off : ℤ) with hv
    have ha := coeff_mul_bit_bounds ch.a x hx
    have hb := coeff_mul_bit_bounds ch.b y hy
    have hoff : (ch.off : ℤ) = (-ch.a).toNat + (-ch.b).toNat := by
      unfold ZChannel.off; push_cast; ring
    have hps : (ch.posSum : ℤ) = ch.a.toNat + ch.b.toNat := by
      unfold ZChannel.posSum; push_cast; ring
    have hvlo : -(2 * (ch.off : ℤ)) ≤ v := by omega
    have hvhi : v ≤ 2 * (ch.posSum : ℤ) - 1 := by omega
    have hcarry : (v / 2 + ch.off).toNat < ch.carrySize := by omega
    calc (v / 2 + ch.off).toNat * ch.winSize
          + ((v % 2).toNat + 2 * r) % ch.winSize
        < (v / 2 + ch.off).toNat * ch.winSize + ch.winSize :=
          Nat.add_lt_add_left (Nat.mod_lt _ hw) _
      _ = ((v / 2 + ch.off).toNat + 1) * ch.winSize := by ring
      _ ≤ ch.carrySize * ch.winSize := Nat.mul_le_mul_right _ (by omega)

end ZChannel

/-! ## The true signed carry -/

/-- The true carry/borrow of the column addition for `z = a·X + b·Y`
(`a b : ℤ`) at floor position `n`. -/
noncomputable def carryTZ (a b : ℤ) (X Y : ℝ) (n : ℕ) : ℤ :=
  ⌊(a * X + b * Y) * 2 ^ n⌋ - a * ⌊X * 2 ^ n⌋ - b * ⌊Y * 2 ^ n⌋

/-- The signed carry is the floor of the fractional-parts combination. -/
theorem carryTZ_eq_floor_fract (a b : ℤ) (X Y : ℝ) (n : ℕ) :
    carryTZ a b X Y n
      = ⌊a * Int.fract (X * 2 ^ n) + b * Int.fract (Y * 2 ^ n)⌋ := by
  unfold carryTZ
  have h : a * Int.fract (X * 2 ^ n) + b * Int.fract (Y * 2 ^ n)
      = (a * X + b * Y) * 2 ^ n - ((a * ⌊X * 2 ^ n⌋ + b * ⌊Y * 2 ^ n⌋ : ℤ) : ℝ) := by
    unfold Int.fract
    push_cast
    ring
  rw [h, Int.floor_sub_intCast]
  ring

/-- Coefficient-times-fract bounds: `−a⁻ ≤ a·fract u` and, when `a > 0`,
`a·fract u < a⁺` strictly (weakly `≤ a⁺` always). -/
theorem coeff_mul_fract_lb (a : ℤ) (u : ℝ) :
    -(((-a).toNat : ℤ) : ℝ) ≤ a * Int.fract u := by
  rcases le_or_gt 0 a with ha | ha
  · have h₁ : (0:ℝ) ≤ (a:ℝ) * Int.fract u :=
      mul_nonneg (by exact_mod_cast ha) (Int.fract_nonneg u)
    have h₂ : ((-a).toNat : ℤ) = 0 := by omega
    rw [show (-(((-a).toNat : ℤ) : ℝ)) = ((-((-a).toNat : ℤ) : ℤ) : ℝ) from by
      push_cast; ring]
    have : (-((-a).toNat : ℤ) : ℤ) = 0 := by omega
    rw [this]
    exact_mod_cast h₁
  · have haR : (a:ℝ) < 0 := by exact_mod_cast ha
    have h₁ : (a:ℝ) * Int.fract u ≥ a * 1 :=
      mul_le_mul_of_nonpos_left (Int.fract_lt_one u).le haR.le
    have h₂ : ((-a).toNat : ℤ) = -a := by omega
    have : (-(((-a).toNat : ℤ) : ℝ)) = (a:ℝ) := by
      rw [show (((-a).toNat : ℤ) : ℝ) = ((-a : ℤ) : ℝ) from by exact_mod_cast h₂]
      push_cast; ring
    rw [this]
    linarith

theorem coeff_mul_fract_ub (a : ℤ) (u : ℝ) :
    a * Int.fract u ≤ ((a.toNat : ℤ) : ℝ) := by
  rcases le_or_gt a 0 with ha | ha
  · have h₁ : (a:ℝ) * Int.fract u ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast ha) (Int.fract_nonneg u)
    have h₂ : (a.toNat : ℤ) = 0 := by omega
    rw [show ((a.toNat : ℤ) : ℝ) = ((0:ℤ):ℝ) from by exact_mod_cast h₂]
    simpa using h₁
  · have haR : (0:ℝ) < a := by exact_mod_cast ha
    have h₁ : (a:ℝ) * Int.fract u < a * 1 :=
      mul_lt_mul_of_pos_left (Int.fract_lt_one u) haR
    have h₂ : (a.toNat : ℤ) = a := by omega
    rw [show ((a.toNat : ℤ) : ℝ) = ((a : ℤ) : ℝ) from by exact_mod_cast h₂]
    linarith

theorem coeff_mul_fract_ub_strict (a : ℤ) (u : ℝ) (ha : 0 < a) :
    a * Int.fract u < ((a.toNat : ℤ) : ℝ) := by
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have h₁ : (a:ℝ) * Int.fract u < a * 1 :=
    mul_lt_mul_of_pos_left (Int.fract_lt_one u) haR
  have h₂ : (a.toNat : ℤ) = a := by omega
  rw [show ((a.toNat : ℤ) : ℝ) = ((a : ℤ) : ℝ) from by exact_mod_cast h₂]
  linarith

/-- Lower carry bound: `−(a⁻+b⁻) ≤ T(n)`. -/
theorem carryTZ_nonneg' (a b : ℤ) (X Y : ℝ) (n : ℕ) :
    -(((-a).toNat + (-b).toNat : ℕ) : ℤ) ≤ carryTZ a b X Y n := by
  rw [carryTZ_eq_floor_fract]
  apply Int.le_floor.2
  have h₁ := coeff_mul_fract_lb a (X * 2 ^ n)
  have h₂ := coeff_mul_fract_lb b (Y * 2 ^ n)
  push_cast at h₁ h₂ ⊢
  linarith

/-- Upper carry bound: `T(n) ≤ a⁺+b⁺−1` (needs a positive coefficient). -/
theorem carryTZ_le' (a b : ℤ) (X Y : ℝ) (n : ℕ)
    (hpos : 1 ≤ a.toNat + b.toNat) :
    carryTZ a b X Y n ≤ (a.toNat + b.toNat : ℕ) - 1 := by
  rw [carryTZ_eq_floor_fract]
  have hlt : a * Int.fract (X * 2 ^ n) + b * Int.fract (Y * 2 ^ n)
      < ((a.toNat + b.toNat : ℕ) : ℝ) := by
    rcases Nat.lt_or_ge 0 a.toNat with ha | ha
    · have h₁ := coeff_mul_fract_ub_strict a (X * 2 ^ n) (by omega)
      have h₂ := coeff_mul_fract_ub b (Y * 2 ^ n)
      push_cast at h₁ h₂ ⊢
      linarith
    · have hb : 0 < b := by omega
      have h₁ := coeff_mul_fract_ub a (X * 2 ^ n)
      have h₂ := coeff_mul_fract_ub_strict b (Y * 2 ^ n) hb
      push_cast at h₁ h₂ ⊢
      linarith
  have := Int.floor_lt.2 (by
    rw [show (((a.toNat + b.toNat : ℕ) : ℤ) : ℝ) = ((a.toNat + b.toNat : ℕ) : ℝ) from by
      push_cast; ring]
    exact hlt)
  omega

/-- **The signed column identity**: `a·xᵢ + b·yᵢ + T(i+1) = dᵢ(z) + 2·T(i)`
— a `ring` identity, valid over ℤ unchanged. -/
theorem carryZ_column (a b : ℤ) (X Y : ℝ) (i : ℕ) :
    a * rdigit X i + b * rdigit Y i + carryTZ a b X Y (i + 1)
      = rdigit (a * X + b * Y) i + 2 * carryTZ a b X Y i := by
  unfold rdigit carryTZ
  ring

/-! ## The signed true state and shadowing -/

/-- The signed channel's true state at position `m`: offset-encoded carry
(high part) and the `ℓ-1` deeper digits of `z` (low part). -/
noncomputable def zchanCode (ch : ZChannel) (X Y : ℝ) (m : ℕ) : ℕ :=
  (carryTZ ch.a ch.b X Y m + ch.off).toNat * ch.winSize
    + winCode (ch.a * X + ch.b * Y) m (ch.ell - 1)

theorem zchanCode_lt (ch : ZChannel) (X Y : ℝ) (m : ℕ) (hpos : 1 ≤ ch.posSum) :
    zchanCode ch X Y m < ch.size := by
  have hT0 := carryTZ_nonneg' ch.a ch.b X Y m
  have hT1 := carryTZ_le' ch.a ch.b X Y m hpos
  have hoff : (ch.off : ℤ) = ((-ch.a).toNat + (-ch.b).toNat : ℕ) := by
    unfold ZChannel.off; push_cast; ring
  have hcarry : (carryTZ ch.a ch.b X Y m + ch.off).toNat < ch.carrySize := by
    have hcs := ch.carrySize_eq hpos
    have hps : (ch.posSum : ℤ) = (ch.a.toNat + ch.b.toNat : ℕ) := by
      unfold ZChannel.posSum; push_cast; ring
    omega
  have hwin : winCode (ch.a * X + ch.b * Y) m (ch.ell - 1) < ch.winSize :=
    winCode_lt _ _ _
  calc zchanCode ch X Y m
      < (carryTZ ch.a ch.b X Y m + ch.off).toNat * ch.winSize + ch.winSize :=
        Nat.add_lt_add_left hwin _
    _ = ((carryTZ ch.a ch.b X Y m + ch.off).toNat + 1) * ch.winSize := by ring
    _ ≤ ch.carrySize * ch.winSize := Nat.mul_le_mul_right _ (by omega)

/-- **Per-channel signed shadowing**: if `ch`'s word does not occur at
position `m` in `z = a·X + b·Y`, then `ZChannel.pred` maps the true deeper
state at `m+1` to the true state at `m` under the input digits
`(x_m, y_m)`. -/
theorem zchan_shadow (ch : ZChannel) (X Y : ℝ) (m : ℕ)
    (_hpos : 1 ≤ ch.posSum) (hell : 1 ≤ ch.ell)
    (hword : ∀ d ∈ ch.word, d ≤ 1)
    (hnocc : ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word m) :
    ch.pred (rdigit X m).toNat (rdigit Y m).toNat (zchanCode ch X Y (m + 1))
      = some (zchanCode ch X Y m) := by
  set z : ℝ := ch.a * X + ch.b * Y with hz
  have hwpos := ch.winSize_pos
  -- decompose the deeper code
  have hwlt : winCode z (m + 1) (ch.ell - 1) < ch.winSize := winCode_lt _ _ _
  have hdiv : zchanCode ch X Y (m + 1) / ch.winSize
      = (carryTZ ch.a ch.b X Y (m + 1) + ch.off).toNat := by
    unfold zchanCode
    rw [← hz, Nat.add_comm, Nat.add_mul_div_right _ _ hwpos, Nat.div_eq_of_lt hwlt,
      Nat.zero_add]
  have hmod : zchanCode ch X Y (m + 1) % ch.winSize
      = winCode z (m + 1) (ch.ell - 1) := by
    unfold zchanCode
    rw [← hz, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hwlt]
  -- the column value
  set v : ℤ := ch.a * (rdigit X m).toNat + ch.b * (rdigit Y m).toNat
      + (zchanCode ch X Y (m + 1) / ch.winSize : ℕ) - (ch.off : ℤ) with hv
  have hT1lo := carryTZ_nonneg' ch.a ch.b X Y (m + 1)
  have hoff : (ch.off : ℤ) = ((-ch.a).toNat + (-ch.b).toNat : ℕ) := by
    unfold ZChannel.off; push_cast; ring
  have hveq : v = rdigit z m + 2 * carryTZ ch.a ch.b X Y m := by
    have hx : ((rdigit X m).toNat : ℤ) = rdigit X m :=
      Int.toNat_of_nonneg (rdigit_nonneg X m)
    have hy : ((rdigit Y m).toNat : ℤ) = rdigit Y m :=
      Int.toNat_of_nonneg (rdigit_nonneg Y m)
    have hcast : ((carryTZ ch.a ch.b X Y (m + 1) + ch.off).toNat : ℤ)
        = carryTZ ch.a ch.b X Y (m + 1) + ch.off := by omega
    have hcol := carryZ_column ch.a ch.b X Y m
    rw [← hz] at hcol
    rw [hv, hdiv, hcast, hx, hy]
    linarith
  have hzd0 := rdigit_nonneg z m
  have hzd1 := rdigit_le_one z m
  have hvmod : (v % 2).toNat = (rdigit z m).toNat := by omega
  have hvdiv : v / 2 = carryTZ ch.a ch.b X Y m := by omega
  -- the formed ℓ-bit window is the full window at m
  have hformed : (v % 2).toNat + 2 * (zchanCode ch X Y (m + 1) % ch.winSize)
      = winCode z m ch.ell := by
    rw [hvmod, hmod]
    unfold winCode
    rw [show ch.ell = (ch.ell - 1) + 1 from by omega, Finset.sum_range_succ']
    rw [Finset.mul_sum]
    have : ∀ j ∈ Finset.range (ch.ell - 1),
        2 * ((rdigit z (m + 1 + j)).toNat * 2 ^ j)
          = (rdigit z (m + (j + 1))).toNat * 2 ^ (j + 1) := by
      intro j _
      rw [show m + (j + 1) = m + 1 + j from by omega, pow_succ]
      ring
    simp only [Nat.add_sub_cancel, Nat.add_zero, pow_zero, mul_one] at *
    rw [Finset.sum_congr rfl this]
    omega
  -- the formed window differs from the word (else the word occurs at m)
  have hne : (v % 2).toNat + 2 * (zchanCode ch X Y (m + 1) % ch.winSize)
      ≠ ch.wordVal := by
    rw [hformed]
    intro heq
    apply hnocc
    rw [occursAt_iff_winList]
    refine bitsVal_inj _ ch.word ?_ hword (by simp) ?_
    · intro d hd
      simp only [List.mem_map, List.mem_range] at hd
      obtain ⟨j, _, rfl⟩ := hd
      exact rdigit_toNat_le_one z (m + j)
    · rw [bitsVal_map_range]
      have hwv : ch.wordVal = bitsVal ch.word := rfl
      rw [hwv] at heq
      simpa [winCode, ZChannel.ell] using heq
  -- reduce the emitted window mod winSize
  have hmodwin : winCode z m ch.ell % ch.winSize = winCode z m (ch.ell - 1) := by
    have hsplit : winCode z m ch.ell
        = winCode z m (ch.ell - 1)
          + 2 ^ (ch.ell - 1) * (rdigit z (m + (ch.ell - 1))).toNat := by
      conv_lhs => rw [show ch.ell = (ch.ell - 1) + 1 from by omega]
      unfold winCode
      rw [Finset.sum_range_succ]
      ring
    rw [hsplit]
    unfold ZChannel.winSize
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (winCode_lt z m (ch.ell - 1))]
  -- assemble
  unfold ZChannel.pred
  rw [← hv, if_neg hne]
  congr 1
  rw [hvdiv, hformed, hmodwin]
  unfold zchanCode
  rw [← hz]

/-! ## The signed family -/

/-- The signed family state count (mixed radix, channel 0 least
significant). -/
def zfamSize : List ZChannel → ℕ
  | [] => 1
  | ch :: rest => ch.size * zfamSize rest

/-- Signed family-level predecessor: componentwise `ZChannel.pred`. -/
def zfamPred (chs : List ZChannel) (x y : ℕ) (s' : ℕ) : Option ℕ :=
  match chs with
  | [] => some 0
  | ch :: rest =>
    match ch.pred x y (s' % ch.size), zfamPred rest x y (s' / ch.size) with
    | some c, some r => some (c + ch.size * r)
    | _, _ => none

theorem zfamPred_lt (chs : List ZChannel) (x y : ℕ) (hx : x ≤ 1) (hy : y ≤ 1)
    (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) (s' : ℕ) {s : ℕ}
    (h : zfamPred chs x y s' = some s) : s < zfamSize chs := by
  induction chs generalizing s' s with
  | nil =>
    simp only [zfamPred, Option.some.injEq] at h
    simp [zfamSize, ← h]
  | cons ch rest ih =>
    simp only [zfamPred] at h
    have hchsz : 0 < ch.size := ch.size_pos
    rcases hp : ch.pred x y (s' % ch.size) with _ | c <;> rw [hp] at h
    · exact absurd h (by simp)
    rcases hr : zfamPred rest x y (s' / ch.size) with _ | r <;> rw [hr] at h
    · exact absurd h (by simp)
    simp only [Option.some.injEq] at h
    subst h
    have hc : c < ch.size :=
      ch.pred_lt x y _ hx hy (hpos ch (by simp)) (Nat.mod_lt _ hchsz) hp
    have hrlt : r < zfamSize rest := ih (fun c hc => hpos c (by simp [hc])) _ hr
    calc c + ch.size * r < ch.size + ch.size * r := by omega
      _ = ch.size * (r + 1) := by ring
      _ ≤ ch.size * zfamSize rest := Nat.mul_le_mul_left _ (by omega)
      _ = zfamSize (ch :: rest) := rfl

/-- The signed family's true state. -/
noncomputable def zfamState : List ZChannel → ℝ → ℝ → ℕ → ℕ
  | [], _, _, _ => 0
  | ch :: rest, X, Y, m => zchanCode ch X Y m + ch.size * zfamState rest X Y m

theorem zfamState_lt (chs : List ZChannel) (X Y : ℝ) (m : ℕ)
    (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) :
    zfamState chs X Y m < zfamSize chs := by
  induction chs with
  | nil => simp [zfamState, zfamSize]
  | cons ch rest ih =>
    have h₀ : zchanCode ch X Y m < ch.size := zchanCode_lt ch X Y m (hpos ch (by simp))
    have h₁ : zfamState rest X Y m < zfamSize rest :=
      ih (fun c hc => hpos c (by simp [hc]))
    show zchanCode ch X Y m + ch.size * zfamState rest X Y m
        < ch.size * zfamSize rest
    calc zchanCode ch X Y m + ch.size * zfamState rest X Y m
        < ch.size + ch.size * zfamState rest X Y m := by omega
      _ = ch.size * (zfamState rest X Y m + 1) := by ring
      _ ≤ ch.size * zfamSize rest := Nat.mul_le_mul_left _ (by omega)

/-- **Signed shadowing** (family level). -/
theorem zfamState_shadow (chs : List ZChannel) (X Y : ℝ) (m : ℕ)
    (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d ≤ 1)
    (hnocc : ∀ ch ∈ chs, ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word m) :
    zfamPred chs (rdigit X m).toNat (rdigit Y m).toNat (zfamState chs X Y (m + 1))
      = some (zfamState chs X Y m) := by
  induction chs with
  | nil => rfl
  | cons ch rest ih =>
    have hpos₀ : 1 ≤ ch.posSum := hpos ch (by simp)
    have hclt : zchanCode ch X Y (m + 1) < ch.size := zchanCode_lt ch X Y (m + 1) hpos₀
    show zfamPred (ch :: rest) _ _ _ = _
    simp only [zfamPred, zfamState]
    have hmod : (zchanCode ch X Y (m + 1) + ch.size * zfamState rest X Y (m + 1)) % ch.size
        = zchanCode ch X Y (m + 1) := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hclt]
    have hdiv : (zchanCode ch X Y (m + 1) + ch.size * zfamState rest X Y (m + 1)) / ch.size
        = zfamState rest X Y (m + 1) := by
      rw [Nat.add_mul_div_left _ _ ch.size_pos, Nat.div_eq_of_lt hclt, Nat.zero_add]
    rw [hmod, hdiv,
      zchan_shadow ch X Y m hpos₀ (hell ch (by simp)) (hword ch (by simp))
        (hnocc ch (by simp)),
      ih (fun c hc => hpos c (by simp [hc])) (fun c hc => hell c (by simp [hc]))
        (fun c hc => hword c (by simp [hc])) (fun c hc => hnocc c (by simp [hc]))]

/-- Signed shadowing in `HStepP` form, with the packed input `σ = x + 2y`. -/
theorem zhstep_zfamState (chs : List ZChannel) (X Y : ℝ) (m : ℕ)
    (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d ≤ 1)
    (hnocc : ∀ ch ∈ chs, ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word m) :
    HStepP (zfamPred chs) (zfamState chs X Y m)
      ((rdigit X m).toNat + 2 * (rdigit Y m).toNat) (zfamState chs X Y (m + 1)) := by
  unfold HStepP
  have hx : (rdigit X m).toNat ≤ 1 := rdigit_toNat_le_one X m
  have hy : (rdigit Y m).toNat ≤ 1 := rdigit_toNat_le_one Y m
  have h₁ : ((rdigit X m).toNat + 2 * (rdigit Y m).toNat) % 2 = (rdigit X m).toNat := by
    omega
  have h₂ : ((rdigit X m).toNat + 2 * (rdigit Y m).toNat) / 2 = (rdigit Y m).toNat := by
    omega
  rw [h₁, h₂]
  exact zfamState_shadow chs X Y m hpos hell hword hnocc

/-! ## The engine meta-theorem -/

/-- Uniformize per-channel "eventually never occurs" bounds over the list. -/
theorem zexists_uniform_no_occurrence (chs : List ZChannel) (X Y : ℝ)
    (h : ∀ ch ∈ chs, ∃ N, ∀ n, N ≤ n → ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word n) :
    ∃ N₀, ∀ ch ∈ chs, ∀ n, N₀ ≤ n → ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word n := by
  induction chs with
  | nil => exact ⟨0, by simp⟩
  | cons ch rest ih =>
    obtain ⟨N₁, h₁⟩ := h ch (by simp)
    obtain ⟨N₂, h₂⟩ := ih (fun c hc => h c (by simp [hc]))
    refine ⟨max N₁ N₂, ?_⟩
    intro c hc n hn
    rcases List.mem_cons.1 hc with rfl | hc'
    · exact h₁ n (le_trans (le_max_left _ _) hn)
    · exact h₂ c hc' n (le_trans (le_max_right _ _) hn)

/-- **The engine meta-theorem**: for any finite signed family with a passing
certificate and any reals `X, Y` not both rational, some channel word occurs
infinitely often in the binary expansion of its channel's linear form. -/
theorem signed_engine (chs : List ZChannel) {S : ℕ}
    {live : ℕ → Bool} {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (hS : S = zfamSize chs)
    (hcert : checkCertP (zfamPred chs) S live rho omega forced = true)
    (X Y : ℝ) (hXY : Irrational X ∨ Irrational Y)
    (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d ≤ 1) :
    ∃ ch ∈ chs, ∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (ch.a * X + ch.b * Y) ch.word n := by
  by_contra hcon
  push Not at hcon
  have h : ∀ ch ∈ chs, ∃ N, ∀ n, N ≤ n → ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word n := by
    intro ch hch
    obtain ⟨N, hN⟩ := hcon ch hch
    exact ⟨N, fun n hn hocc => hN n hn hocc⟩
  obtain ⟨N₀, hN₀⟩ := zexists_uniform_no_occurrence chs X Y h
  have hσ : ∀ m, (rdigit X (N₀ + m)).toNat + 2 * (rdigit Y (N₀ + m)).toNat < 4 := by
    intro m
    have h₁ := rdigit_toNat_le_one X (N₀ + m)
    have h₂ := rdigit_toNat_le_one Y (N₀ + m)
    omega
  have hst : ∀ m, zfamState chs X Y (N₀ + m) < S :=
    fun m => hS ▸ zfamState_lt chs X Y (N₀ + m) hpos
  have hstep : ∀ m, HStepP (zfamPred chs) (zfamState chs X Y (N₀ + m))
      ((rdigit X (N₀ + m)).toNat + 2 * (rdigit Y (N₀ + m)).toNat)
      (zfamState chs X Y (N₀ + (m + 1))) := by
    intro m
    exact zhstep_zfamState chs X Y (N₀ + m) hpos hell hword
      (fun ch hch => hN₀ ch hch (N₀ + m) (by omega))
  obtain ⟨N, p, hp, hper⟩ := inputP_eventually_periodic
    (st := fun k => zfamState chs X Y (N₀ + k))
    (σi := fun k => (rdigit X (N₀ + k)).toNat + 2 * (rdigit Y (N₀ + k)).toNat)
    hcert hσ hst hstep
  have hsplit : ∀ m, N₀ + N ≤ m →
      (rdigit X (m + p)).toNat = (rdigit X m).toNat ∧
      (rdigit Y (m + p)).toNat = (rdigit Y m).toNat := by
    intro m hm
    have hk := hper (m - N₀) (by omega)
    rw [show N₀ + (m - N₀ + p) = m + p from by omega,
      show N₀ + (m - N₀) = m from by omega] at hk
    have b₁ := rdigit_toNat_le_one X (m + p)
    have b₂ := rdigit_toNat_le_one Y (m + p)
    have b₃ := rdigit_toNat_le_one X m
    have b₄ := rdigit_toNat_le_one Y m
    omega
  rcases hXY with hX | hY
  · refine not_irrational_of_periodic_digits X (N₀ + N) p hp ?_ hX
    intro m hm
    rw [digitOf_two_fract, digitOf_two_fract]
    exact (hsplit m hm).1
  · refine not_irrational_of_periodic_digits Y (N₀ + N) p hp ?_ hY
    intro m hm
    rw [digitOf_two_fract, digitOf_two_fract]
    exact (hsplit m hm).2

end NormalNumbers.Adder
