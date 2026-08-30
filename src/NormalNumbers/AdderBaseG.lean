/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderSigned
import NormalNumbers.AdderEngineCoreG

/-!
# The base-g signed stack (tower phase B)

Brief: `BRIEF-adder-tower.md` phase B; dossier
`EVIDENCE-2026-08-29-tower-formalization.md` §1.2.

Everything in `AdderCarry`/`AdderShadow`/`AdderSigned`/`AdderEndgame` with the
radix `2` replaced by a parameter `g ≥ 2`:

* `gdigit g w i = ⌊w·g^(i+1)⌋ − g·⌊w·g^i⌋` is the `i`-th base-`g` digit of `w`
  read off with floors of `w` itself; it agrees with the repo's
  `digitOf g (Int.fract w) i` (`gdigit_eq_digitOf`).
* `carryTG g a b X Y n = ⌊(a·X + b·Y)·g^n⌋ − a·⌊X·g^n⌋ − b·⌊Y·g^n⌋` is the true
  signed carry; its window `[−(a⁻+b⁻), a⁺+b⁺−1]` is EXACTLY the base-2 window
  (the bounds come from `fract < 1`, not from the radix), so `ZChannel` and its
  `off`/`posSum`/`carrySize` are reused unchanged.  The base-`g` column
  identity is `a·xᵢ + b·yᵢ + T(i+1) = dᵢ(z) + g·T(i)` (`carryG_column`).
* The base-`g` channel automaton (`ZChannel.gpred`) splits the column value
  floor-consistently with `Int.emod`/`Int.ediv` at modulus `g`; window states
  hold `ℓ−1` deeper digits base-`g` (`gwinSize = g^(ℓ−1)`); the avoided word's
  value is the base-`g` fold `gwordVal`.
* Shadowing (`gchan_shadow`, `gfamState_shadow`), the endgame in base `b`
  (`not_irrational_of_periodic_digits_g`), and the meta-theorem
  `signed_engine_g` over the packed alphabet `σ = x + g·y < g²` via the
  alphabet-generalized engine (`AdderEngineCoreG`).

Orientation (dossier §1.4): as in the base-2 pipeline, `gpred` is the
deep→shallow backward-deterministic predecessor form, so the certified graph
and the shadowed walk coincide by construction.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-! ## Base-g true digits -/

/-- The `i`-th base-`g` digit of `w`, computed from floors of `w` itself. -/
noncomputable def gdigit (g : ℕ) (w : ℝ) (i : ℕ) : ℤ :=
  ⌊w * (g : ℝ) ^ (i + 1)⌋ - g * ⌊w * (g : ℝ) ^ i⌋

/-- Generic digit extraction: `g·⌊u⌋ ≤ ⌊g·u⌋ < g·⌊u⌋ + g`. -/
theorem floor_g_mul_bounds (g : ℕ) (hg : 1 ≤ g) (u : ℝ) :
    (g : ℤ) * ⌊u⌋ ≤ ⌊(g : ℝ) * u⌋ ∧ ⌊(g : ℝ) * u⌋ < (g : ℤ) * ⌊u⌋ + g := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  constructor
  · apply Int.le_floor.2
    push_cast
    exact mul_le_mul_of_nonneg_left (Int.floor_le u) hg0.le
  · have h : ⌊(g : ℝ) * u⌋ < (g : ℤ) * (⌊u⌋ + 1) := by
      apply Int.floor_lt.2
      push_cast
      exact mul_lt_mul_of_pos_left (Int.lt_floor_add_one u) hg0
    have he : (g : ℤ) * (⌊u⌋ + 1) = (g : ℤ) * ⌊u⌋ + g := by ring
    omega

theorem gdigit_nonneg (g : ℕ) (hg : 1 ≤ g) (w : ℝ) (i : ℕ) : 0 ≤ gdigit g w i := by
  have h := floor_g_mul_bounds g hg (w * (g : ℝ) ^ i)
  unfold gdigit
  rw [show w * (g : ℝ) ^ (i + 1) = (g : ℝ) * (w * (g : ℝ) ^ i) by ring]
  omega

theorem gdigit_lt (g : ℕ) (hg : 1 ≤ g) (w : ℝ) (i : ℕ) : gdigit g w i < g := by
  have h := floor_g_mul_bounds g hg (w * (g : ℝ) ^ i)
  unfold gdigit
  rw [show w * (g : ℝ) ^ (i + 1) = (g : ℝ) * (w * (g : ℝ) ^ i) by ring]
  omega

theorem gdigit_toNat_lt (g : ℕ) (hg : 1 ≤ g) (w : ℝ) (i : ℕ) :
    (gdigit g w i).toNat < g := by
  have h0 := gdigit_nonneg g hg w i
  have h1 := gdigit_lt g hg w i
  omega

/-- The floor of a fractional part after scaling by `g^k`. -/
theorem floor_fract_mul_pow_g (g : ℕ) (w : ℝ) (k : ℕ) :
    ⌊Int.fract w * (g : ℝ) ^ k⌋ = ⌊w * (g : ℝ) ^ k⌋ - ⌊w⌋ * (g : ℤ) ^ k := by
  rw [Int.fract, sub_mul]
  rw [show (⌊w⌋ : ℝ) * (g : ℝ) ^ k = ((⌊w⌋ * (g : ℤ) ^ k : ℤ) : ℝ) by push_cast; ring]
  rw [Int.floor_sub_intCast]

/-- The repo's digit map agrees with `gdigit`: integer parts drop out. -/
theorem gdigit_eq_digitOf (g : ℕ) (hg : 2 ≤ g) (w : ℝ) (i : ℕ) :
    (digitOf g (Int.fract w) i : ℤ) = gdigit g w i := by
  have hg1 : 1 ≤ g := by omega
  have hnn : 0 ≤ ⌊Int.fract w * (g : ℝ) ^ (i + 1)⌋ :=
    Int.floor_nonneg.2 (mul_nonneg (Int.fract_nonneg w) (by positivity))
  have hfl := floor_fract_mul_pow_g g w (i + 1)
  have hd0 := gdigit_nonneg g hg1 w i
  have hd1 := gdigit_lt g hg1 w i
  have hsplit : ⌊w * (g : ℝ) ^ (i + 1)⌋ - ⌊w⌋ * (g : ℤ) ^ (i + 1)
      = gdigit g w i + (g : ℤ) * (⌊w * (g : ℝ) ^ i⌋ - ⌊w⌋ * (g : ℤ) ^ i) := by
    unfold gdigit
    rw [pow_succ]
    ring
  unfold digitOf
  push_cast
  rw [Int.toNat_of_nonneg hnn, hfl, hsplit, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt hd0 hd1]

/-- The repo digit map in `toNat` form, base `g`. -/
theorem digitOf_g_fract (g : ℕ) (hg : 2 ≤ g) (w : ℝ) (i : ℕ) :
    digitOf g (Int.fract w) i = (gdigit g w i).toNat := by
  have := gdigit_eq_digitOf g hg w i
  omega

/-! ## The base-g true signed carry -/

/-- The true carry/borrow of the base-`g` column addition for `z = a·X + b·Y`
at floor position `n`. -/
noncomputable def carryTG (g : ℕ) (a b : ℤ) (X Y : ℝ) (n : ℕ) : ℤ :=
  ⌊(a * X + b * Y) * (g : ℝ) ^ n⌋ - a * ⌊X * (g : ℝ) ^ n⌋ - b * ⌊Y * (g : ℝ) ^ n⌋

/-- The base-`g` signed carry is the floor of the fractional-parts
combination — the base plays no role in the window. -/
theorem carryTG_eq_floor_fract (g : ℕ) (a b : ℤ) (X Y : ℝ) (n : ℕ) :
    carryTG g a b X Y n
      = ⌊a * Int.fract (X * (g : ℝ) ^ n) + b * Int.fract (Y * (g : ℝ) ^ n)⌋ := by
  unfold carryTG
  have h : a * Int.fract (X * (g : ℝ) ^ n) + b * Int.fract (Y * (g : ℝ) ^ n)
      = (a * X + b * Y) * (g : ℝ) ^ n
        - ((a * ⌊X * (g : ℝ) ^ n⌋ + b * ⌊Y * (g : ℝ) ^ n⌋ : ℤ) : ℝ) := by
    unfold Int.fract
    push_cast
    ring
  rw [h, Int.floor_sub_intCast]
  ring

/-- Lower carry bound: `−(a⁻+b⁻) ≤ T(n)` — same window as base 2. -/
theorem carryTG_nonneg' (g : ℕ) (a b : ℤ) (X Y : ℝ) (n : ℕ) :
    -(((-a).toNat + (-b).toNat : ℕ) : ℤ) ≤ carryTG g a b X Y n := by
  rw [carryTG_eq_floor_fract]
  apply Int.le_floor.2
  have h₁ := coeff_mul_fract_lb a (X * (g : ℝ) ^ n)
  have h₂ := coeff_mul_fract_lb b (Y * (g : ℝ) ^ n)
  push_cast at h₁ h₂ ⊢
  linarith

/-- Upper carry bound: `T(n) ≤ a⁺+b⁺−1` (needs a positive coefficient). -/
theorem carryTG_le' (g : ℕ) (a b : ℤ) (X Y : ℝ) (n : ℕ)
    (hpos : 1 ≤ a.toNat + b.toNat) :
    carryTG g a b X Y n ≤ (a.toNat + b.toNat : ℕ) - 1 := by
  rw [carryTG_eq_floor_fract]
  have hlt : a * Int.fract (X * (g : ℝ) ^ n) + b * Int.fract (Y * (g : ℝ) ^ n)
      < ((a.toNat + b.toNat : ℕ) : ℝ) := by
    rcases Nat.lt_or_ge 0 a.toNat with ha | ha
    · have h₁ := coeff_mul_fract_ub_strict a (X * (g : ℝ) ^ n) (by omega)
      have h₂ := coeff_mul_fract_ub b (Y * (g : ℝ) ^ n)
      push_cast at h₁ h₂ ⊢
      linarith
    · have hb : 0 < b := by omega
      have h₁ := coeff_mul_fract_ub a (X * (g : ℝ) ^ n)
      have h₂ := coeff_mul_fract_ub_strict b (Y * (g : ℝ) ^ n) hb
      push_cast at h₁ h₂ ⊢
      linarith
  have := Int.floor_lt.2 (by
    rw [show (((a.toNat + b.toNat : ℕ) : ℤ) : ℝ) = ((a.toNat + b.toNat : ℕ) : ℝ) from by
      push_cast; ring]
    exact hlt)
  omega

/-- **The base-`g` signed column identity**:
`a·xᵢ + b·yᵢ + T(i+1) = dᵢ(z) + g·T(i)`. -/
theorem carryG_column (g : ℕ) (a b : ℤ) (X Y : ℝ) (i : ℕ) :
    a * gdigit g X i + b * gdigit g Y i + carryTG g a b X Y (i + 1)
      = gdigit g (a * X + b * Y) i + g * carryTG g a b X Y i := by
  unfold gdigit carryTG
  ring

/-! ## Base-g windows and word values -/

/-- The `k` base-`g` digits of `z` at positions `m, …, m+k−1`, packed
least-significant first. -/
noncomputable def winCodeG (g : ℕ) (z : ℝ) (m k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, (gdigit g z (m + j)).toNat * g ^ j

theorem winCodeG_lt (g : ℕ) (hg : 1 ≤ g) (z : ℝ) (m : ℕ) :
    ∀ k, winCodeG g z m k < g ^ k := by
  intro k
  induction k with
  | zero => simp [winCodeG]
  | succ n ih =>
    have hd : (gdigit g z (m + n)).toNat * g ^ n ≤ (g - 1) * g ^ n := by
      have := gdigit_toNat_lt g hg z (m + n)
      exact Nat.mul_le_mul_right _ (by omega)
    have hsum : winCodeG g z m (n + 1)
        = winCodeG g z m n + (gdigit g z (m + n)).toNat * g ^ n := by
      unfold winCodeG
      rw [Finset.sum_range_succ]
    have key : g ^ n + (g - 1) * g ^ n = g ^ (n + 1) := by
      have h1 : g ^ n + (g - 1) * g ^ n = (1 + (g - 1)) * g ^ n := by ring
      rw [h1, show 1 + (g - 1) = g from by omega, pow_succ, Nat.mul_comm]
    calc winCodeG g z m (n + 1)
        < g ^ n + (g - 1) * g ^ n := by omega
      _ = g ^ (n + 1) := key

/-- The base-`g` value of a digit list, least-significant digit first. -/
def digitsValG (g : ℕ) (l : List ℕ) : ℕ := l.foldr (fun d acc => d + g * acc) 0

@[simp] theorem digitsValG_nil (g : ℕ) : digitsValG g [] = 0 := rfl

@[simp] theorem digitsValG_cons (g d : ℕ) (l : List ℕ) :
    digitsValG g (d :: l) = d + g * digitsValG g l := rfl

theorem digitsValG_inj (g : ℕ) (hg : 0 < g) :
    ∀ (l₁ l₂ : List ℕ), (∀ d ∈ l₁, d < g) → (∀ d ∈ l₂, d < g) →
      l₁.length = l₂.length → digitsValG g l₁ = digitsValG g l₂ → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | d₁ :: t₁, d₂ :: t₂, h₁, h₂, hlen, hval => by
    simp only [digitsValG_cons] at hval
    have hd₁ : d₁ < g := h₁ d₁ (by simp)
    have hd₂ : d₂ < g := h₂ d₂ (by simp)
    have hd : d₁ = d₂ := by
      have hmod := congrArg (· % g) hval
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd₁, Nat.mod_eq_of_lt hd₂]
        using hmod
    subst hd
    have hmul : g * digitsValG g t₁ = g * digitsValG g t₂ := Nat.add_left_cancel hval
    have ht : digitsValG g t₁ = digitsValG g t₂ := Nat.eq_of_mul_eq_mul_left hg hmul
    have := digitsValG_inj g hg t₁ t₂ (fun d hd => h₁ d (by simp [hd]))
      (fun d hd => h₂ d (by simp [hd])) (by simpa using hlen) ht
    rw [this]

/-- `digitsValG` of a mapped range is the weighted digit sum. -/
theorem digitsValG_map_range (g : ℕ) : ∀ (k : ℕ) (f : ℕ → ℕ),
    digitsValG g ((List.range k).map f) = ∑ j ∈ Finset.range k, f j * g ^ j := by
  intro k
  induction k with
  | zero => intro f; simp [digitsValG]
  | succ n ih =>
    intro f
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, digitsValG_cons,
      Finset.sum_range_succ']
    rw [ih (f ∘ Nat.succ), Finset.mul_sum]
    have : ∀ j ∈ Finset.range n, g * ((f ∘ Nat.succ) j * g ^ j) = f (j + 1) * g ^ (j + 1) := by
      intro j _
      simp only [Function.comp_apply, Nat.succ_eq_add_one, pow_succ]
      ring
    rw [Finset.sum_congr rfl this, pow_zero, mul_one]
    ring

/-- The formed `ℓ`-digit window equals the word list iff the word occurs at
`m` in base `g`. -/
theorem occursAt_iff_winListG (g : ℕ) (hg : 2 ≤ g) (z : ℝ) (w : List ℕ) (m : ℕ) :
    OccursAt g z w m
      ↔ (List.range w.length).map (fun j => (gdigit g z (m + j)).toNat) = w := by
  have hdig : ∀ i, digitOf g (Int.fract z) i = (gdigit g z i).toNat :=
    fun i => digitOf_g_fract g hg z i
  constructor
  · intro h
    apply List.ext_getElem (by simp)
    intro j hj₁ hj₂
    simp only [List.getElem_map, List.getElem_range]
    rw [← hdig (m + j)]
    exact h j (by simpa using hj₁)
  · intro h j hj
    rw [hdig (m + j)]
    have hj' : j < ((List.range w.length).map fun i => (gdigit g z (m + i)).toNat).length := by
      simpa using hj
    calc (gdigit g z (m + j)).toNat
        = ((List.range w.length).map fun i => (gdigit g z (m + i)).toNat)[j]'hj' := by simp
      _ = w[j] := by simp only [h]

/-! ## The base-g channel automaton

`ZChannel` (coefficients + word) is reused unchanged: `off`, `posSum` and
`carrySize` are radix-independent.  Only the window arithmetic and the column
split change. -/

namespace ZChannel

/-- Base-`g` window state count: `g^(ℓ−1)`. -/
def gwinSize (g : ℕ) (ch : ZChannel) : ℕ := g ^ (ch.ell - 1)

/-- Base-`g` channel state count. -/
def gsize (g : ℕ) (ch : ZChannel) : ℕ := ch.carrySize * ch.gwinSize g

/-- The word's base-`g` value, LSD-first. -/
def gwordVal (g : ℕ) (ch : ZChannel) : ℕ := digitsValG g ch.word

theorem gwinSize_pos (g : ℕ) (hg : 1 ≤ g) (ch : ZChannel) : 0 < ch.gwinSize g :=
  Nat.pow_pos (by omega)

theorem gsize_pos (g : ℕ) (hg : 1 ≤ g) (ch : ZChannel) : 0 < ch.gsize g :=
  Nat.mul_pos ch.carrySize_pos (ch.gwinSize_pos g hg)

/-- Base-`g` channel-level predecessor with offset carry encoding.  The
column value `v = a·x + b·y + (encoded carry − off)` splits floor-consistently
as `v = g·(v/g) + v%g` (`Int.ediv`/`Int.emod`); `none` when the freshly formed
`ℓ`-digit window equals the avoided word. -/
def gpred (g : ℕ) (ch : ZChannel) (x y code' : ℕ) : Option ℕ :=
  if ((ch.a * x + ch.b * y + (code' / ch.gwinSize g : ℕ) - (ch.off : ℤ)) % g).toNat
      + g * (code' % ch.gwinSize g) = ch.gwordVal g then none
  else some (((ch.a * x + ch.b * y + (code' / ch.gwinSize g : ℕ) - (ch.off : ℤ)) / g
        + ch.off).toNat * ch.gwinSize g
    + (((ch.a * x + ch.b * y + (code' / ch.gwinSize g : ℕ) - (ch.off : ℤ)) % g).toNat
        + g * (code' % ch.gwinSize g)) % ch.gwinSize g)

/-- Coefficient-times-digit bounds: for a digit `x < g`,
`−(g−1)·a⁻ ≤ a·x ≤ (g−1)·a⁺`. -/
theorem coeff_mul_digit_bounds (a : ℤ) (g x : ℕ) (hg : 1 ≤ g) (hx : x < g) :
    -(((g : ℤ) - 1) * (-a).toNat) ≤ a * x ∧ a * (x : ℤ) ≤ ((g : ℤ) - 1) * a.toNat := by
  have hxle : (x : ℤ) ≤ (g : ℤ) - 1 := by
    have : (x : ℤ) < (g : ℤ) := by exact_mod_cast hx
    omega
  have hx0 : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg x
  have hg1 : (1 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg
  rcases le_or_gt 0 a with ha | ha
  · constructor
    · have h₁ : (0 : ℤ) ≤ a * x := mul_nonneg ha hx0
      have h₂ : (0 : ℤ) ≤ ((g : ℤ) - 1) * (-a).toNat :=
        mul_nonneg (by omega) (Int.natCast_nonneg _)
      linarith
    · calc a * (x : ℤ) ≤ a * ((g : ℤ) - 1) := mul_le_mul_of_nonneg_left hxle ha
        _ = ((g : ℤ) - 1) * a := by ring
        _ = ((g : ℤ) - 1) * a.toNat := by rw [Int.toNat_of_nonneg ha]
  · constructor
    · have h₁ : a * ((g : ℤ) - 1) ≤ a * (x : ℤ) := mul_le_mul_of_nonpos_left hxle ha.le
      have h₂ : ((-a).toNat : ℤ) = -a := by omega
      have h₃ : -(((g : ℤ) - 1) * (-a).toNat) = a * ((g : ℤ) - 1) := by
        rw [h₂]; ring
      linarith
    · have h₁ : a * (x : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha.le hx0
      have h₂ : (a.toNat : ℤ) = 0 := by omega
      rw [h₂, mul_zero]
      exact h₁

theorem gpred_lt (g : ℕ) (ch : ZChannel) (x y code' : ℕ) (hg : 2 ≤ g)
    (hx : x < g) (hy : y < g) (hpos : 1 ≤ ch.posSum) (hcode : code' < ch.gsize g)
    {c : ℕ} (h : ch.gpred g x y code' = some c) : c < ch.gsize g := by
  unfold gpred at h
  have hg1 : 1 ≤ g := by omega
  have hw : (0 : ℕ) < ch.gwinSize g := ch.gwinSize_pos g hg1
  have hc'lt : code' / ch.gwinSize g < ch.carrySize :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcode)
  have hcs := ch.carrySize_eq hpos
  generalize hqe : code' / ch.gwinSize g = q at h hc'lt
  generalize hre : code' % ch.gwinSize g = r at h
  have hr : r < ch.gwinSize g := hre ▸ Nat.mod_lt _ hw
  clear hqe hre
  split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h
    subst h
    set v : ℤ := ch.a * x + ch.b * y + (q : ℤ) - (ch.off : ℤ) with hv
    have ha := coeff_mul_digit_bounds ch.a g x hg1 hx
    have hb := coeff_mul_digit_bounds ch.b g y hg1 hy
    have hoff : (ch.off : ℤ) = (-ch.a).toNat + (-ch.b).toNat := by
      unfold ZChannel.off; push_cast; ring
    have hps : (ch.posSum : ℤ) = ch.a.toNat + ch.b.toNat := by
      unfold ZChannel.posSum; push_cast; ring
    have hq0 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
    have hqhi : (q : ℤ) ≤ (ch.posSum : ℤ) + (ch.off : ℤ) - 1 := by
      have h₁ : (q : ℤ) < (ch.carrySize : ℤ) := by exact_mod_cast hc'lt
      have h₂ : (ch.carrySize : ℤ) = (ch.posSum : ℤ) + (ch.off : ℤ) := by
        rw [hcs]; push_cast; ring
      omega
    have hvlo : -((g : ℤ) * ch.off) ≤ v := by
      have hkey : -((g : ℤ) * ch.off)
          = -(((g : ℤ) - 1) * (-ch.a).toNat) + -(((g : ℤ) - 1) * (-ch.b).toNat)
            + -(ch.off : ℤ) := by
        rw [hoff]; ring
      have := ha.1
      have := hb.1
      omega
    have hvhi : v ≤ (g : ℤ) * ch.posSum - 1 := by
      have hkey : (g : ℤ) * ch.posSum - 1
          = ((g : ℤ) - 1) * ch.a.toNat + ((g : ℤ) - 1) * ch.b.toNat
            + (ch.posSum : ℤ) - 1 := by
        rw [hps]; ring
      have := ha.2
      have := hb.2
      omega
    have hgZ : (0 : ℤ) < g := by exact_mod_cast (show 0 < g by omega)
    have hdivlo : -(ch.off : ℤ) ≤ v / g := by
      rw [Int.le_ediv_iff_mul_le hgZ]
      have : -(ch.off : ℤ) * g = -((g : ℤ) * ch.off) := by ring
      omega
    have hdivhi : v / g < (ch.posSum : ℤ) := by
      rw [Int.ediv_lt_iff_lt_mul hgZ]
      have : (ch.posSum : ℤ) * g = (g : ℤ) * ch.posSum := by ring
      omega
    have hcarry : (v / g + ch.off).toNat < ch.carrySize := by omega
    calc (v / g + ch.off).toNat * ch.gwinSize g
          + (((v % g).toNat + g * r) % ch.gwinSize g)
        < (v / g + ch.off).toNat * ch.gwinSize g + ch.gwinSize g :=
          Nat.add_lt_add_left (Nat.mod_lt _ hw) _
      _ = ((v / g + ch.off).toNat + 1) * ch.gwinSize g := by ring
      _ ≤ ch.carrySize * ch.gwinSize g := Nat.mul_le_mul_right _ (by omega)

end ZChannel

/-! ## The base-g true state and shadowing -/

/-- The base-`g` signed channel's true state at position `m`: offset-encoded
carry (high part) and the `ℓ−1` deeper base-`g` digits of `z` (low part). -/
noncomputable def gchanCode (g : ℕ) (ch : ZChannel) (X Y : ℝ) (m : ℕ) : ℕ :=
  (carryTG g ch.a ch.b X Y m + ch.off).toNat * ch.gwinSize g
    + winCodeG g (ch.a * X + ch.b * Y) m (ch.ell - 1)

theorem gchanCode_lt (g : ℕ) (hg : 1 ≤ g) (ch : ZChannel) (X Y : ℝ) (m : ℕ)
    (hpos : 1 ≤ ch.posSum) : gchanCode g ch X Y m < ch.gsize g := by
  have hT0 := carryTG_nonneg' g ch.a ch.b X Y m
  have hT1 := carryTG_le' g ch.a ch.b X Y m hpos
  have hoff : (ch.off : ℤ) = ((-ch.a).toNat + (-ch.b).toNat : ℕ) := by
    unfold ZChannel.off; push_cast; ring
  have hcarry : (carryTG g ch.a ch.b X Y m + ch.off).toNat < ch.carrySize := by
    have hcs := ch.carrySize_eq hpos
    have hps : (ch.posSum : ℤ) = (ch.a.toNat + ch.b.toNat : ℕ) := by
      unfold ZChannel.posSum; push_cast; ring
    omega
  have hwin : winCodeG g (ch.a * X + ch.b * Y) m (ch.ell - 1) < ch.gwinSize g :=
    winCodeG_lt g hg _ m _
  calc gchanCode g ch X Y m
      < (carryTG g ch.a ch.b X Y m + ch.off).toNat * ch.gwinSize g + ch.gwinSize g :=
        Nat.add_lt_add_left hwin _
    _ = ((carryTG g ch.a ch.b X Y m + ch.off).toNat + 1) * ch.gwinSize g := by ring
    _ ≤ ch.carrySize * ch.gwinSize g := Nat.mul_le_mul_right _ (by omega)

/-- **Per-channel base-`g` signed shadowing**: if `ch`'s word does not occur
at position `m` in `z = a·X + b·Y` base `g`, then `gpred` maps the true
deeper state at `m+1` to the true state at `m` under the input digits
`(x_m, y_m)`. -/
theorem gchan_shadow (g : ℕ) (hg : 2 ≤ g) (ch : ZChannel) (X Y : ℝ) (m : ℕ)
    (_hpos : 1 ≤ ch.posSum) (hell : 1 ≤ ch.ell)
    (hword : ∀ d ∈ ch.word, d < g)
    (hnocc : ¬ OccursAt g (ch.a * X + ch.b * Y) ch.word m) :
    ch.gpred g (gdigit g X m).toNat (gdigit g Y m).toNat (gchanCode g ch X Y (m + 1))
      = some (gchanCode g ch X Y m) := by
  set z : ℝ := ch.a * X + ch.b * Y with hz
  have hg1 : 1 ≤ g := by omega
  have hwpos := ch.gwinSize_pos g hg1
  -- decompose the deeper code
  have hwlt : winCodeG g z (m + 1) (ch.ell - 1) < ch.gwinSize g :=
    winCodeG_lt g hg1 z (m + 1) _
  have hdiv : gchanCode g ch X Y (m + 1) / ch.gwinSize g
      = (carryTG g ch.a ch.b X Y (m + 1) + ch.off).toNat := by
    unfold gchanCode
    rw [← hz, Nat.add_comm, Nat.add_mul_div_right _ _ hwpos, Nat.div_eq_of_lt hwlt,
      Nat.zero_add]
  have hmod : gchanCode g ch X Y (m + 1) % ch.gwinSize g
      = winCodeG g z (m + 1) (ch.ell - 1) := by
    unfold gchanCode
    rw [← hz, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hwlt]
  -- the column value
  set v : ℤ := ch.a * (gdigit g X m).toNat + ch.b * (gdigit g Y m).toNat
      + (gchanCode g ch X Y (m + 1) / ch.gwinSize g : ℕ) - (ch.off : ℤ) with hv
  have hT1lo := carryTG_nonneg' g ch.a ch.b X Y (m + 1)
  have hoff : (ch.off : ℤ) = ((-ch.a).toNat + (-ch.b).toNat : ℕ) := by
    unfold ZChannel.off; push_cast; ring
  have hveq : v = gdigit g z m + g * carryTG g ch.a ch.b X Y m := by
    have hx : ((gdigit g X m).toNat : ℤ) = gdigit g X m :=
      Int.toNat_of_nonneg (gdigit_nonneg g hg1 X m)
    have hy : ((gdigit g Y m).toNat : ℤ) = gdigit g Y m :=
      Int.toNat_of_nonneg (gdigit_nonneg g hg1 Y m)
    have hcast : ((carryTG g ch.a ch.b X Y (m + 1) + ch.off).toNat : ℤ)
        = carryTG g ch.a ch.b X Y (m + 1) + ch.off := by omega
    have hcol := carryG_column g ch.a ch.b X Y m
    rw [← hz] at hcol
    rw [hv, hdiv, hcast, hx, hy]
    linarith
  have hzd0 := gdigit_nonneg g hg1 z m
  have hzd1 := gdigit_lt g hg1 z m
  have hgne : (g : ℤ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hvmodZ : v % (g : ℤ) = gdigit g z m := by
    rw [hveq, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hzd0 hzd1]
  have hvmod : (v % (g : ℤ)).toNat = (gdigit g z m).toNat := by rw [hvmodZ]
  have hvdiv : v / (g : ℤ) = carryTG g ch.a ch.b X Y m := by
    rw [hveq, Int.add_mul_ediv_left _ _ hgne, Int.ediv_eq_zero_of_lt hzd0 hzd1,
      zero_add]
  -- the formed ℓ-digit window is the full window at m
  have hformed : (v % (g : ℤ)).toNat + g * (gchanCode g ch X Y (m + 1) % ch.gwinSize g)
      = winCodeG g z m ch.ell := by
    rw [hvmod, hmod]
    unfold winCodeG
    rw [show ch.ell = (ch.ell - 1) + 1 from by omega, Finset.sum_range_succ']
    rw [Finset.mul_sum]
    have : ∀ j ∈ Finset.range (ch.ell - 1),
        g * ((gdigit g z (m + 1 + j)).toNat * g ^ j)
          = (gdigit g z (m + (j + 1))).toNat * g ^ (j + 1) := by
      intro j _
      rw [show m + (j + 1) = m + 1 + j from by omega, pow_succ]
      ring
    simp only [Nat.add_sub_cancel, Nat.add_zero, pow_zero, mul_one] at *
    rw [Finset.sum_congr rfl this]
    omega
  -- the formed window differs from the word (else the word occurs at m)
  have hne : (v % (g : ℤ)).toNat + g * (gchanCode g ch X Y (m + 1) % ch.gwinSize g)
      ≠ ch.gwordVal g := by
    rw [hformed]
    intro heq
    apply hnocc
    rw [occursAt_iff_winListG g hg]
    refine digitsValG_inj g (by omega) _ ch.word ?_ hword (by simp) ?_
    · intro d hd
      simp only [List.mem_map, List.mem_range] at hd
      obtain ⟨j, _, rfl⟩ := hd
      exact gdigit_toNat_lt g hg1 z (m + j)
    · rw [digitsValG_map_range]
      have hwv : ch.gwordVal g = digitsValG g ch.word := rfl
      rw [hwv] at heq
      simpa [winCodeG, ZChannel.ell] using heq
  -- reduce the emitted window mod gwinSize
  have hmodwin : winCodeG g z m ch.ell % ch.gwinSize g = winCodeG g z m (ch.ell - 1) := by
    have hsplit : winCodeG g z m ch.ell
        = winCodeG g z m (ch.ell - 1)
          + g ^ (ch.ell - 1) * (gdigit g z (m + (ch.ell - 1))).toNat := by
      conv_lhs => rw [show ch.ell = (ch.ell - 1) + 1 from by omega]
      unfold winCodeG
      rw [Finset.sum_range_succ]
      ring
    rw [hsplit]
    unfold ZChannel.gwinSize
    rw [Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (winCodeG_lt g hg1 z m (ch.ell - 1))]
  -- assemble
  unfold ZChannel.gpred
  rw [← hv, if_neg hne]
  congr 1
  rw [hvdiv, hformed, hmodwin]
  unfold gchanCode
  rw [← hz]

/-! ## The base-g signed family -/

/-- The base-`g` family state count (mixed radix, channel 0 least
significant). -/
def gfamSize (g : ℕ) : List ZChannel → ℕ
  | [] => 1
  | ch :: rest => ch.gsize g * gfamSize g rest

/-- Base-`g` family-level predecessor: componentwise `gpred`. -/
def gfamPred (g : ℕ) (chs : List ZChannel) (x y : ℕ) (s' : ℕ) : Option ℕ :=
  match chs with
  | [] => some 0
  | ch :: rest =>
    match ch.gpred g x y (s' % ch.gsize g), gfamPred g rest x y (s' / ch.gsize g) with
    | some c, some r => some (c + ch.gsize g * r)
    | _, _ => none

theorem gfamPred_lt (g : ℕ) (hg : 2 ≤ g) (chs : List ZChannel) (x y : ℕ)
    (hx : x < g) (hy : y < g) (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) (s' : ℕ) {s : ℕ}
    (h : gfamPred g chs x y s' = some s) : s < gfamSize g chs := by
  have hg1 : 1 ≤ g := by omega
  induction chs generalizing s' s with
  | nil =>
    simp only [gfamPred, Option.some.injEq] at h
    simp [gfamSize, ← h]
  | cons ch rest ih =>
    simp only [gfamPred] at h
    have hchsz : 0 < ch.gsize g := ch.gsize_pos g hg1
    rcases hp : ch.gpred g x y (s' % ch.gsize g) with _ | c <;> rw [hp] at h
    · exact absurd h (by simp)
    rcases hr : gfamPred g rest x y (s' / ch.gsize g) with _ | r <;> rw [hr] at h
    · exact absurd h (by simp)
    simp only [Option.some.injEq] at h
    subst h
    have hc : c < ch.gsize g :=
      ZChannel.gpred_lt g ch x y (s' % ch.gsize g) hg hx hy (hpos ch (by simp))
        (Nat.mod_lt _ hchsz) hp
    have hrlt : r < gfamSize g rest := ih (fun c hc => hpos c (by simp [hc])) _ hr
    calc c + ch.gsize g * r < ch.gsize g + ch.gsize g * r := by omega
      _ = ch.gsize g * (r + 1) := by ring
      _ ≤ ch.gsize g * gfamSize g rest := Nat.mul_le_mul_left _ (by omega)
      _ = gfamSize g (ch :: rest) := rfl

/-- The base-`g` family's true state. -/
noncomputable def gfamState (g : ℕ) : List ZChannel → ℝ → ℝ → ℕ → ℕ
  | [], _, _, _ => 0
  | ch :: rest, X, Y, m => gchanCode g ch X Y m + ch.gsize g * gfamState g rest X Y m

theorem gfamState_lt (g : ℕ) (hg : 1 ≤ g) (chs : List ZChannel) (X Y : ℝ) (m : ℕ)
    (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) :
    gfamState g chs X Y m < gfamSize g chs := by
  induction chs with
  | nil => simp [gfamState, gfamSize]
  | cons ch rest ih =>
    have h₀ : gchanCode g ch X Y m < ch.gsize g :=
      gchanCode_lt g hg ch X Y m (hpos ch (by simp))
    have h₁ : gfamState g rest X Y m < gfamSize g rest :=
      ih (fun c hc => hpos c (by simp [hc]))
    show gchanCode g ch X Y m + ch.gsize g * gfamState g rest X Y m
        < ch.gsize g * gfamSize g rest
    calc gchanCode g ch X Y m + ch.gsize g * gfamState g rest X Y m
        < ch.gsize g + ch.gsize g * gfamState g rest X Y m := by omega
      _ = ch.gsize g * (gfamState g rest X Y m + 1) := by ring
      _ ≤ ch.gsize g * gfamSize g rest := Nat.mul_le_mul_left _ (by omega)

/-- **Base-`g` signed shadowing** (family level). -/
theorem gfamState_shadow (g : ℕ) (hg : 2 ≤ g) (chs : List ZChannel) (X Y : ℝ) (m : ℕ)
    (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d < g)
    (hnocc : ∀ ch ∈ chs, ¬ OccursAt g (ch.a * X + ch.b * Y) ch.word m) :
    gfamPred g chs (gdigit g X m).toNat (gdigit g Y m).toNat (gfamState g chs X Y (m + 1))
      = some (gfamState g chs X Y m) := by
  have hg1 : 1 ≤ g := by omega
  induction chs with
  | nil => rfl
  | cons ch rest ih =>
    have hpos₀ : 1 ≤ ch.posSum := hpos ch (by simp)
    have hclt : gchanCode g ch X Y (m + 1) < ch.gsize g :=
      gchanCode_lt g hg1 ch X Y (m + 1) hpos₀
    show gfamPred g (ch :: rest) _ _ _ = _
    simp only [gfamPred, gfamState]
    have hmod : (gchanCode g ch X Y (m + 1) + ch.gsize g * gfamState g rest X Y (m + 1))
          % ch.gsize g
        = gchanCode g ch X Y (m + 1) := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hclt]
    have hdiv : (gchanCode g ch X Y (m + 1) + ch.gsize g * gfamState g rest X Y (m + 1))
          / ch.gsize g
        = gfamState g rest X Y (m + 1) := by
      rw [Nat.add_mul_div_left _ _ (ch.gsize_pos g hg1), Nat.div_eq_of_lt hclt,
        Nat.zero_add]
    rw [hmod, hdiv,
      gchan_shadow g hg ch X Y m hpos₀ (hell ch (by simp)) (hword ch (by simp))
        (hnocc ch (by simp)),
      ih (fun c hc => hpos c (by simp [hc])) (fun c hc => hell c (by simp [hc]))
        (fun c hc => hword c (by simp [hc])) (fun c hc => hnocc c (by simp [hc]))]

/-- Base-`g` shadowing in `HStepA` form, with the packed input `σ = x + g·y`. -/
theorem ghstep_gfamState (g : ℕ) (hg : 2 ≤ g) (chs : List ZChannel) (X Y : ℝ) (m : ℕ)
    (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d < g)
    (hnocc : ∀ ch ∈ chs, ¬ OccursAt g (ch.a * X + ch.b * Y) ch.word m) :
    HStepA (fun σ s' => gfamPred g chs (σ % g) (σ / g) s') (gfamState g chs X Y m)
      ((gdigit g X m).toNat + g * (gdigit g Y m).toNat)
      (gfamState g chs X Y (m + 1)) := by
  have hg1 : 1 ≤ g := by omega
  have hx : (gdigit g X m).toNat < g := gdigit_toNat_lt g hg1 X m
  show gfamPred g chs
      (((gdigit g X m).toNat + g * (gdigit g Y m).toNat) % g)
      (((gdigit g X m).toNat + g * (gdigit g Y m).toNat) / g)
      (gfamState g chs X Y (m + 1)) = some (gfamState g chs X Y m)
  have h₁ : ((gdigit g X m).toNat + g * (gdigit g Y m).toNat) % g
      = (gdigit g X m).toNat := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have h₂ : ((gdigit g X m).toNat + g * (gdigit g Y m).toNat) / g
      = (gdigit g Y m).toNat := by
    rw [Nat.add_mul_div_left _ _ (show 0 < g by omega), Nat.div_eq_of_lt hx,
      Nat.zero_add]
  rw [h₁, h₂]
  exact gfamState_shadow g hg chs X Y m hpos hell hword hnocc

/-! ## Endgame, base b -/

/-- Two reals of `[0,1)` with identical base-`b` digit streams are equal. -/
theorem eq_of_digitOf_eq_g (b : ℕ) (hb : 2 ≤ b) {u v : ℝ} (hu : u ∈ Set.Ico (0:ℝ) 1)
    (hv : v ∈ Set.Ico (0:ℝ) 1) (h : ∀ j, digitOf b u j = digitOf b v j) :
    u = v := by
  have hb1 : (1:ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb0 : (0:ℝ) < b := by linarith
  by_contra hne
  have habs : 0 < |u - v| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one habs
    (show (1:ℝ)/b < 1 from (div_lt_one hb0).2 hb1)
  set w : List ℕ := (List.range k).map (digitOf b u) with hw
  have hwlt : ∀ d ∈ w, d < b := by
    intro d hd
    simp only [hw, List.mem_map, List.mem_range] at hd
    obtain ⟨j, _, rfl⟩ := hd
    exact digitOf_lt b hb u j
  have hlen : w.length = k := by simp [hw]
  have hupre : ∀ j (hj : j < w.length), digitOf b u j = w[j] := by
    intro j hj
    simp [hw]
  have hvpre : ∀ j (hj : j < w.length), digitOf b v j = w[j] := by
    intro j hj
    rw [← h j]
    simp [hw]
  have hu' := (digits_prefix_iff b hb u hu w hwlt).1 hupre
  have hv' := (digits_prefix_iff b hb v hv w hwlt).1 hvpre
  rw [hlen] at hu' hv'
  have hpow : (0:ℝ) < ((b:ℕ):ℝ) ^ k := by positivity
  have h₁ : u - v < 1 / ((b:ℕ):ℝ) ^ k := by
    have e : ((blockNatVal b w : ℝ) + 1) / ((b:ℕ):ℝ) ^ k
        - (blockNatVal b w : ℝ) / ((b:ℕ):ℝ) ^ k = 1 / ((b:ℕ):ℝ) ^ k := by
      ring
    have := hu'.2
    have := hv'.1
    linarith
  have h₂ : v - u < 1 / ((b:ℕ):ℝ) ^ k := by
    have e : ((blockNatVal b w : ℝ) + 1) / ((b:ℕ):ℝ) ^ k
        - (blockNatVal b w : ℝ) / ((b:ℕ):ℝ) ^ k = 1 / ((b:ℕ):ℝ) ^ k := by
      ring
    have := hv'.2
    have := hu'.1
    linarith
  have h₃ : |u - v| < 1 / ((b:ℕ):ℝ) ^ k := abs_sub_lt_iff.2 ⟨h₁, h₂⟩
  have h₄ : ((1:ℝ)/b) ^ k = 1 / ((b:ℕ):ℝ) ^ k := by
    rw [div_pow, one_pow]
  linarith [hk, h₃, h₄ ▸ hk]

/-- Eventually periodic base-`b` digits force rationality. -/
theorem not_irrational_of_periodic_digits_g (b : ℕ) (hb : 2 ≤ b) (L : ℝ) (N p : ℕ)
    (hp : 0 < p)
    (h : ∀ m, N ≤ m → digitOf b (Int.fract L) (m + p) = digitOf b (Int.fract L) m) :
    ¬ Irrational L := by
  intro hirr
  set x : ℝ := Int.fract L with hxdef
  have hx : x ∈ Set.Ico (0:ℝ) 1 := ⟨Int.fract_nonneg L, Int.fract_lt_one L⟩
  have heq : orbit b x N = orbit b x (N + p) := by
    apply eq_of_digitOf_eq_g b hb (orbit_mem_Ico b x N) (orbit_mem_Ico b x (N + p))
    intro j
    rw [digitOf_orbit b hb x hx.1 N j, digitOf_orbit b hb x hx.1 (N + p) j]
    have := h (N + j) (by omega)
    rw [show N + p + j = N + j + p from by omega]
    exact this.symm
  unfold orbit at heq
  rw [Int.fract_eq_fract] at heq
  obtain ⟨z, hz⟩ := heq
  have h2 : x * (((b:ℕ):ℝ) ^ N - ((b:ℕ):ℝ) ^ (N + p)) = (z : ℝ) := by
    rw [← hz]; ring
  have hb1 : (1:ℝ) < ((b:ℕ):ℝ) := by exact_mod_cast (show 1 < b by omega)
  have hlt : ((b:ℕ):ℝ) ^ N < ((b:ℕ):ℝ) ^ (N + p) :=
    pow_lt_pow_right₀ hb1 (by omega)
  have hden : (((b:ℕ):ℝ) ^ N - ((b:ℕ):ℝ) ^ (N + p)) ≠ 0 := by linarith
  have hxrat : ¬ Irrational x := by
    intro hxi
    refine hxi ⟨(z : ℚ) / ((b:ℚ) ^ N - (b:ℚ) ^ (N + p)), ?_⟩
    push_cast
    rw [eq_comm, eq_div_iff (by convert hden using 2)]
    linarith [h2]
  apply hxrat
  have hfr : x = L - (⌊L⌋ : ℝ) := (Int.self_sub_floor L).symm
  rw [hfr]
  exact Irrational.sub_intCast hirr ⌊L⌋

/-! ## The base-g engine meta-theorem -/

/-- Uniformize per-channel "eventually never occurs" bounds over the list. -/
theorem gexists_uniform_no_occurrence (g : ℕ) (chs : List ZChannel) (X Y : ℝ)
    (h : ∀ ch ∈ chs, ∃ N, ∀ n, N ≤ n → ¬ OccursAt g (ch.a * X + ch.b * Y) ch.word n) :
    ∃ N₀, ∀ ch ∈ chs, ∀ n, N₀ ≤ n → ¬ OccursAt g (ch.a * X + ch.b * Y) ch.word n := by
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

/-- Unpacking `σ = x + g·y` with `x, x' < g` is injective. -/
theorem pack_inj (g : ℕ) (hg : 0 < g) {x y x' y' : ℕ} (hx : x < g) (hx' : x' < g)
    (h : x + g * y = x' + g * y') : x = x' ∧ y = y' := by
  have h1 : x = x' := by
    have hmod := congrArg (· % g) h
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx']
      using hmod
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hg (Nat.add_left_cancel h)⟩

/-- **The base-`g` engine meta-theorem**: for any finite signed family with a
passing alphabet-`g²` certificate and any reals `X, Y` not both rational, some
channel word occurs infinitely often in the base-`g` expansion of its
channel's linear form. -/
theorem signed_engine_g (g : ℕ) (hg : 2 ≤ g) (chs : List ZChannel) {S : ℕ}
    {live : ℕ → Bool} {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (hS : S = gfamSize g chs)
    (hcert : checkCertA (fun σ s' => gfamPred g chs (σ % g) (σ / g) s')
      (g ^ 2) S live rho omega forced = true)
    (X Y : ℝ) (hXY : Irrational X ∨ Irrational Y)
    (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d < g) :
    ∃ ch ∈ chs, ∀ N, ∃ n, N ≤ n ∧ OccursAt g (ch.a * X + ch.b * Y) ch.word n := by
  have hg1 : 1 ≤ g := by omega
  by_contra hcon
  push Not at hcon
  have h : ∀ ch ∈ chs, ∃ N, ∀ n, N ≤ n → ¬ OccursAt g (ch.a * X + ch.b * Y) ch.word n := by
    intro ch hch
    obtain ⟨N, hN⟩ := hcon ch hch
    exact ⟨N, fun n hn hocc => hN n hn hocc⟩
  obtain ⟨N₀, hN₀⟩ := gexists_uniform_no_occurrence g chs X Y h
  have hσ : ∀ m, (gdigit g X (N₀ + m)).toNat + g * (gdigit g Y (N₀ + m)).toNat < g ^ 2 := by
    intro m
    have h₁ := gdigit_toNat_lt g hg1 X (N₀ + m)
    have h₂ := gdigit_toNat_lt g hg1 Y (N₀ + m)
    have hsq : g + g * (g - 1) = g ^ 2 := by
      have e : g + g * (g - 1) = g * (1 + (g - 1)) := by ring
      rw [e, show 1 + (g - 1) = g from by omega]
      ring
    calc (gdigit g X (N₀ + m)).toNat + g * (gdigit g Y (N₀ + m)).toNat
        < g + g * (gdigit g Y (N₀ + m)).toNat := by omega
      _ ≤ g + g * (g - 1) := Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
      _ = g ^ 2 := hsq
  have hst : ∀ m, gfamState g chs X Y (N₀ + m) < S :=
    fun m => hS ▸ gfamState_lt g hg1 chs X Y (N₀ + m) hpos
  have hstep : ∀ m, HStepA (fun σ s' => gfamPred g chs (σ % g) (σ / g) s')
      (gfamState g chs X Y (N₀ + m))
      ((gdigit g X (N₀ + m)).toNat + g * (gdigit g Y (N₀ + m)).toNat)
      (gfamState g chs X Y (N₀ + (m + 1))) := by
    intro m
    exact ghstep_gfamState g hg chs X Y (N₀ + m) hpos hell hword
      (fun ch hch => hN₀ ch hch (N₀ + m) (by omega))
  obtain ⟨N, p, hp, hper⟩ := inputA_eventually_periodic
    (st := fun k => gfamState g chs X Y (N₀ + k))
    (σi := fun k => (gdigit g X (N₀ + k)).toNat + g * (gdigit g Y (N₀ + k)).toNat)
    hcert hσ hst hstep
  have hsplit : ∀ m, N₀ + N ≤ m →
      (gdigit g X (m + p)).toNat = (gdigit g X m).toNat ∧
      (gdigit g Y (m + p)).toNat = (gdigit g Y m).toNat := by
    intro m hm
    have hk := hper (m - N₀) (by omega)
    rw [show N₀ + (m - N₀ + p) = m + p from by omega,
      show N₀ + (m - N₀) = m from by omega] at hk
    exact pack_inj g (by omega) (gdigit_toNat_lt g hg1 X (m + p))
      (gdigit_toNat_lt g hg1 X m) hk
  rcases hXY with hX | hY
  · refine not_irrational_of_periodic_digits_g g hg X (N₀ + N) p hp ?_ hX
    intro m hm
    rw [digitOf_g_fract g hg, digitOf_g_fract g hg]
    exact (hsplit m hm).1
  · refine not_irrational_of_periodic_digits_g g hg Y (N₀ + N) p hp ?_ hY
    intro m hm
    rw [digitOf_g_fract g hg, digitOf_g_fract g hg]
    exact (hsplit m hm).2

/-- The base-`g` digits of the real `0` are all `0`. -/
theorem gdigit_zero (g : ℕ) (m : ℕ) : gdigit g (0 : ℝ) m = 0 := by
  unfold gdigit
  simp

/-- **The single-track base-`g` engine**: channels are linear forms in `X`
alone (`Y := 0`, so the joint input digit is just `x_m < g` and the swept
alphabet shrinks to `g`).  Channels keep their `ZChannel` shape; since
`b·0 = 0` the `b`-coefficients are inert and the conclusion reads on
`a·X`.  Per BRIEF-adder-tower phase B: single-track claims come free —
"for every irrational X some channel word occurs i.o. base g". -/
theorem signed_engine_g_single (g : ℕ) (hg : 2 ≤ g) (chs : List ZChannel) {S : ℕ}
    {live : ℕ → Bool} {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (hS : S = gfamSize g chs)
    (hcert : checkCertA (fun σ s' => gfamPred g chs (σ % g) (σ / g) s')
      g S live rho omega forced = true)
    (X : ℝ) (hX : Irrational X)
    (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d < g) :
    ∃ ch ∈ chs, ∀ N, ∃ n, N ≤ n ∧ OccursAt g (ch.a * X) ch.word n := by
  have hg1 : 1 ≤ g := by omega
  by_contra hcon
  push Not at hcon
  have h : ∀ ch ∈ chs, ∃ N, ∀ n, N ≤ n
      → ¬ OccursAt g (ch.a * X + ch.b * (0:ℝ)) ch.word n := by
    intro ch hch
    obtain ⟨N, hN⟩ := hcon ch hch
    refine ⟨N, fun n hn hocc => hN n hn ?_⟩
    rw [show ch.a * X + ch.b * (0:ℝ) = ch.a * X from by ring] at hocc
    exact hocc
  obtain ⟨N₀, hN₀⟩ := gexists_uniform_no_occurrence g chs X 0 h
  have hzero : ∀ m, (gdigit g (0 : ℝ) m).toNat = 0 := fun m => by
    rw [gdigit_zero]; rfl
  have hσ : ∀ m, (gdigit g X (N₀ + m)).toNat < g :=
    fun m => gdigit_toNat_lt g hg1 X (N₀ + m)
  have hst : ∀ m, gfamState g chs X 0 (N₀ + m) < S :=
    fun m => hS ▸ gfamState_lt g hg1 chs X 0 (N₀ + m) hpos
  have hstep : ∀ m, HStepA (fun σ s' => gfamPred g chs (σ % g) (σ / g) s')
      (gfamState g chs X 0 (N₀ + m)) ((gdigit g X (N₀ + m)).toNat)
      (gfamState g chs X 0 (N₀ + (m + 1))) := by
    intro m
    have h₀ := ghstep_gfamState g hg chs X 0 (N₀ + m) hpos hell hword
      (fun ch hch => hN₀ ch hch (N₀ + m) (by omega))
    rw [hzero (N₀ + m), Nat.mul_zero, Nat.add_zero] at h₀
    exact h₀
  obtain ⟨N, p, hp, hper⟩ := inputA_eventually_periodic
    (st := fun k => gfamState g chs X 0 (N₀ + k))
    (σi := fun k => (gdigit g X (N₀ + k)).toNat)
    hcert hσ hst hstep
  refine not_irrational_of_periodic_digits_g g hg X (N₀ + N) p hp ?_ hX
  intro m hm
  rw [digitOf_g_fract g hg, digitOf_g_fract g hg]
  have hk := hper (m - N₀) (by omega)
  rw [show N₀ + (m - N₀ + p) = m + p from by omega,
    show N₀ + (m - N₀) = m from by omega] at hk
  exact hk

end NormalNumbers.Adder
