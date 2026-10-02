/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDigitLaw
import NormalNumbers.GaussErgodic
import NormalNumbers.Headline

/-!
# Quadratic irrationals have bounded partial quotients — elementarily

Leg 1 of the frozen §7 target is `AffineImageIrrational q r₀`: the image of a CF-normal number is
irrational.  For `q = φ` it says `φ x ∉ ℚ`, and the reason is that `φ x ∈ ℚ` makes `Int.fract x`
a **quadratic irrational**, whose partial quotients are bounded, while a CF-normal number has
every digit appearing with positive frequency.

The textbook route is Lagrange's theorem (eventually periodic CF) via reduced forms.  That is not
needed.  The following is self-contained and gives an *explicit* bound:

Let `z ∈ (0,1)` be irrational with `A z² + B z + C = 0`, `A, B, C : ℤ`, `A ≠ 0`.  Write the `n`-th
tail `t = Gⁿ z` and the `n`-th continuant matrix `qMat (digitWord z n) = (a b ; c d)`, so that
`z = (a t + b)/(c t + d)` with `0 ≤ b ≤ d`, `0 ≤ a`, `0 ≤ c`, `0 < d` and `a d − b c = ±1`.  Then

* `b / d ∈ [0,1]` is rational, so `P(b/d) ≠ 0`, so the integer `A b² + B b d + C d²` has `|·| ≥ 1`;
* `|z − b/d| = t / (d (c t + d)) ≤ t / d²` — this is where unimodularity is used;
* `A b² + B b d + C d² = d² (P(b/d) − P(z)) = d² (b/d − z) (A (b/d + z) + B)`, so
  `1 ≤ |A b² + B b d + C d²| ≤ t · (2|A| + |B|)`.

Hence `Gⁿ z ≥ 1/(2|A| + |B|)` for **every** `n`, so every digit is at most `2|A| + |B|`.  No
discriminant, no conjugate root, no reduced forms, no periodicity.

## Guard rule

Content locator: `qMat_det` and `z_eq_qApply` — the two facts the estimate rests on, both proved by
induction on the word; `bddDigits_of_quadratic` is the headline.  Degenerate cases: `qMat_nil` (the
empty word gives the identity, so the `n = 0` case reads `z = z`), and
`not_isCFNormal_of_bddDigits` shows the conclusion is genuinely incompatible with CF-normality
rather than merely unusual.
-/

namespace NormalNumbers.VandeheyS7

open Filter

/-! ## The integer continuant matrix -/

/-- A `2×2` integer matrix, acting as the Möbius map `t ↦ (a t + b)/(c t + d)`. -/
structure QMat where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

namespace QMat

/-- The action on the reals. -/
noncomputable def app (m : QMat) (t : ℝ) : ℝ :=
  ((m.a : ℝ) * t + (m.b : ℝ)) / ((m.c : ℝ) * t + (m.d : ℝ))

/-- `m.det = a d − b c`. -/
def det (m : QMat) : ℤ := m.a * m.d - m.b * m.c

end QMat

/-- The integer matrix of the word `w`, acting as `t ↦ (a t + b)/(c t + d)`.  One Gauss branch
`t ↦ 1/(A + t)`, i.e. the matrix `(0 1 ; 1 A)`, per letter, multiplied on the left. -/
def qMat : List ℕ → QMat
  | [] => ⟨1, 0, 0, 1⟩
  | a :: w =>
      let m := qMat w
      ⟨m.c, m.d, m.a + (max 1 a : ℕ) * m.c, m.b + (max 1 a : ℕ) * m.d⟩

@[simp] theorem qMat_nil : qMat [] = ⟨1, 0, 0, 1⟩ := rfl

theorem qMat_cons (a : ℕ) (w : List ℕ) :
    qMat (a :: w) =
      ⟨(qMat w).c, (qMat w).d,
        (qMat w).a + (max 1 a : ℕ) * (qMat w).c, (qMat w).b + (max 1 a : ℕ) * (qMat w).d⟩ := rfl

/-- **Unimodularity**: each Gauss branch has determinant `−1`. -/
theorem qMat_det (w : List ℕ) : (qMat w).det = (-1) ^ w.length := by
  induction w with
  | nil => simp [QMat.det]
  | cons a w ih =>
      rw [qMat_cons, QMat.det]
      simp only [List.length_cons, pow_succ]
      rw [QMat.det] at ih
      ring_nf
      ring_nf at ih
      linarith [ih]

/-- The entry bounds: `0 ≤ a`, `0 ≤ c`, `0 ≤ b ≤ d` and `0 < d`. -/
theorem qMat_bounds (w : List ℕ) :
    0 ≤ (qMat w).a ∧ 0 ≤ (qMat w).c ∧ 0 ≤ (qMat w).b ∧ (qMat w).b ≤ (qMat w).d
      ∧ 0 < (qMat w).d := by
  induction w with
  | nil => simp
  | cons a w ih =>
      obtain ⟨ha, hc, hb, hbd, hd⟩ := ih
      have hA : (1:ℤ) ≤ ((max 1 a : ℕ) : ℤ) := by exact_mod_cast le_max_left 1 a
      rw [qMat_cons]
      refine ⟨hc, by positivity, hd.le, ?_, ?_⟩
      · simp only
        nlinarith
      · simp only
        nlinarith

/-! ## The continued-fraction representation -/

theorem qMat_den_pos (w : List ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 < ((qMat w).c : ℝ) * t + ((qMat w).d : ℝ) := by
  obtain ⟨-, hc, -, -, hd⟩ := qMat_bounds w
  have hc' : (0:ℝ) ≤ ((qMat w).c : ℝ) := by exact_mod_cast hc
  have hd' : (0:ℝ) < ((qMat w).d : ℝ) := by exact_mod_cast hd
  positivity

theorem qMat_num_nonneg (w : List ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ((qMat w).a : ℝ) * t + ((qMat w).b : ℝ) := by
  obtain ⟨ha, -, hb, -, -⟩ := qMat_bounds w
  have ha' : (0:ℝ) ≤ ((qMat w).a : ℝ) := by exact_mod_cast ha
  have hb' : (0:ℝ) ≤ ((qMat w).b : ℝ) := by exact_mod_cast hb
  positivity

/-- One Gauss branch, as pure `ℤ`-cast algebra. -/
theorem QMat.app_branch (m : QMat) (k : ℤ) (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t)
    (ha : 0 ≤ m.a) (hb : 0 ≤ m.b) (hc : 0 ≤ m.c) (hd : 0 < m.d) :
    (⟨m.c, m.d, m.a + k * m.c, m.b + k * m.d⟩ : QMat).app t = 1 / ((k:ℝ) + m.app t) := by
  have ha' : (0:ℝ) ≤ (m.a : ℝ) := by exact_mod_cast ha
  have hb' : (0:ℝ) ≤ (m.b : ℝ) := by exact_mod_cast hb
  have hc' : (0:ℝ) ≤ (m.c : ℝ) := by exact_mod_cast hc
  have hd' : (0:ℝ) < (m.d : ℝ) := by exact_mod_cast hd
  have hk' : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hN : (0:ℝ) < (m.c : ℝ) * t + (m.d : ℝ) := by positivity
  have hM : (0:ℝ) ≤ (m.a : ℝ) * t + (m.b : ℝ) := by positivity
  have happ : m.app t = ((m.a : ℝ) * t + (m.b : ℝ)) / ((m.c : ℝ) * t + (m.d : ℝ)) := rfl
  have hq : (0:ℝ) ≤ ((m.a : ℝ) * t + (m.b : ℝ)) / ((m.c : ℝ) * t + (m.d : ℝ)) :=
    div_nonneg hM hN.le
  have hR : (0:ℝ) < (k:ℝ) + m.app t := by rw [happ]; linarith
  rw [happ] at hR
  rw [QMat.app, happ]
  simp only [Int.cast_add, Int.cast_mul]
  rw [div_eq_div_iff (by
      have h1 : (0:ℝ) ≤ (k:ℝ) * ((m.c : ℝ) * t + (m.d : ℝ)) :=
        mul_nonneg (by linarith) hN.le
      have : (0:ℝ) < ((m.a : ℝ) + (k:ℝ) * (m.c : ℝ)) * t + ((m.b : ℝ) + (k:ℝ) * (m.d : ℝ)) := by
        nlinarith
      exact ne_of_gt this) (ne_of_gt hR)]
  field_simp
  ring

theorem qMat_app_cons (a : ℕ) (w : List ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (qMat (a :: w)).app t = 1 / (((max 1 a : ℕ) : ℝ) + (qMat w).app t) := by
  obtain ⟨ha, hc, hb, -, hd⟩ := qMat_bounds w
  have hk : (1:ℤ) ≤ ((max 1 a : ℕ) : ℤ) := by exact_mod_cast le_max_left 1 a
  rw [qMat_cons, QMat.app_branch (qMat w) ((max 1 a : ℕ) : ℤ) hk ht ha hb hc hd]
  norm_cast

theorem digitWord_succ_cons (x : ℝ) (n : ℕ) :
    digitWord x (n + 1) = cfDigit x 0 :: digitWord (gaussMap x) n := by
  simp [digitWord, List.range_succ_eq_map, List.map_map, Function.comp_def, cfDigit_succ]

/-- **The representation.**  `z` is the image of its `n`-th tail under the `n`-th continuant
matrix. -/
theorem z_eq_qApp : ∀ (n : ℕ) (z : ℝ), Irrational z → z ∈ Set.Ioo (0:ℝ) 1 →
    z = (qMat (digitWord z n)).app (gaussMap^[n] z)
  | 0, z, _, _ => by simp [digitWord, QMat.app]
  | (n + 1), z, hirr, hz => by
      have hd1 : 1 ≤ cfDigit z 0 := one_le_cfDigit z hirr hz 0
      have hmax : ((max 1 (cfDigit z 0) : ℕ) : ℝ) = (cfDigit z 0 : ℝ) := by
        rw [max_eq_right hd1]
      obtain ⟨hgirr, hgz⟩ := irrational_gaussMap hirr hz
      have hIH := z_eq_qApp n (gaussMap z) hgirr hgz
      have hstep : z = 1 / ((cfDigit z 0 : ℝ) + gaussMap z) := by
        have h := gaussMap_eq_inv_sub hz
        have : (cfDigit z 0 : ℝ) + gaussMap z = z⁻¹ := by rw [h]; ring
        rw [this, one_div, inv_inv]
      rw [digitWord_succ_cons, qMat_app_cons _ _ (le_of_lt (by
        have := irrational_orbit (gaussMap z) hgirr hgz n
        exact this.2.1)), hmax, Function.iterate_succ_apply, ← hIH]
      exact hstep

/-! ## No rational root -/

/-- If `z` is irrational and a root of `A X² + B X + C`, no rational is a root: otherwise the sum
of the two roots, `−B/A`, would make `z` rational. -/
theorem quad_ne_zero_of_irrational {A B C : ℤ} (hA : A ≠ 0) {z : ℝ} (hirr : Irrational z)
    (hroot : (A:ℝ) * z ^ 2 + (B:ℝ) * z + (C:ℝ) = 0) (b d : ℤ) (hd : d ≠ 0) :
    A * b ^ 2 + B * b * d + C * d ^ 2 ≠ 0 := by
  intro h
  have hA' : (A:ℝ) ≠ 0 := Int.cast_ne_zero.2 hA
  have hd' : (d:ℝ) ≠ 0 := Int.cast_ne_zero.2 hd
  set r : ℝ := (b:ℝ) / (d:ℝ) with hrdef
  have hcast : (A:ℝ) * (b:ℝ) ^ 2 + (B:ℝ) * (b:ℝ) * (d:ℝ) + (C:ℝ) * (d:ℝ) ^ 2 = 0 := by
    have : ((A * b ^ 2 + B * b * d + C * d ^ 2 : ℤ) : ℝ) = 0 := by rw [h]; norm_num
    push_cast at this
    linarith
  have hrroot : (A:ℝ) * r ^ 2 + (B:ℝ) * r + (C:ℝ) = 0 := by
    rw [hrdef]
    field_simp
    linarith
  have hrat : ∀ s : ℝ, s = r → ¬ Irrational s := by
    intro s hs hirrs
    exact hirrs ⟨(b : ℚ) / (d : ℚ), by rw [hs, hrdef]; push_cast; ring⟩
  have hne : z ≠ r := fun hzr => hrat z hzr hirr
  have hfac : (z - r) * ((A:ℝ) * (z + r) + (B:ℝ)) = 0 := by
    have : (z - r) * ((A:ℝ) * (z + r) + (B:ℝ))
        = ((A:ℝ) * z ^ 2 + (B:ℝ) * z + (C:ℝ)) - ((A:ℝ) * r ^ 2 + (B:ℝ) * r + (C:ℝ)) := by ring
    rw [this, hroot, hrroot, sub_zero]
  have hsum : (A:ℝ) * (z + r) + (B:ℝ) = 0 := by
    rcases mul_eq_zero.1 hfac with h1 | h2
    · exact absurd (by linarith [sub_eq_zero.1 h1] : z = r) hne
    · exact h2
  have hz : z = (-(B:ℝ) - (A:ℝ) * r) / (A:ℝ) := by
    field_simp
    linarith
  refine hirr ⟨(-(B : ℚ) - (A : ℚ) * ((b : ℚ) / (d : ℚ))) / (A : ℚ), ?_⟩
  rw [hz, hrdef]
  push_cast
  ring

/-! ## The digit bound -/

/-- **Every tail of a quadratic irrational is bounded away from `0`.**  The heart of the argument:
the integer `A b² + B b d + C d²` is nonzero, hence `≥ 1` in absolute value, while it equals
`d² (b/d − z)(A (b/d + z) + B)` and `|z − b/d| ≤ t/d²`. -/
theorem tail_lower_bound {A B C : ℤ} (hA : A ≠ 0) {z : ℝ} (hirr : Irrational z)
    (hz : z ∈ Set.Ioo (0:ℝ) 1) (hroot : (A:ℝ) * z ^ 2 + (B:ℝ) * z + (C:ℝ) = 0) (n : ℕ) :
    1 ≤ gaussMap^[n] z * (2 * |(A:ℝ)| + |(B:ℝ)|) := by
  obtain ⟨htirr, ht0, ht1⟩ := irrational_orbit z hirr hz n
  set t : ℝ := gaussMap^[n] z with htdef
  set m : QMat := qMat (digitWord z n) with hm
  obtain ⟨ha, hc, hb, hbd, hd⟩ := qMat_bounds (digitWord z n)
  rw [← hm] at ha hc hb hbd hd
  have hdR : (0:ℝ) < (m.d : ℝ) := by exact_mod_cast hd
  have hcR : (0:ℝ) ≤ (m.c : ℝ) := by exact_mod_cast hc
  have haR : (0:ℝ) ≤ (m.a : ℝ) := by exact_mod_cast ha
  have hbR : (0:ℝ) ≤ (m.b : ℝ) := by exact_mod_cast hb
  have hbdR : (m.b : ℝ) ≤ (m.d : ℝ) := by exact_mod_cast hbd
  have hden : (0:ℝ) < (m.c : ℝ) * t + (m.d : ℝ) := by positivity
  have hrep : z = ((m.a : ℝ) * t + (m.b : ℝ)) / ((m.c : ℝ) * t + (m.d : ℝ)) := by
    rw [hm, htdef]
    exact z_eq_qApp n z hirr hz
  set r : ℝ := (m.b : ℝ) / (m.d : ℝ) with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hdR]; exact hbdR
  -- the determinant is ±1
  have hdet : |(m.a * m.d - m.b * m.c : ℤ)| = 1 := by
    have := qMat_det (digitWord z n)
    rw [QMat.det, ← hm] at this
    rw [this]
    simp [abs_pow]
  have hdetR : |(m.a : ℝ) * (m.d : ℝ) - (m.b : ℝ) * (m.c : ℝ)| = 1 := by
    have : ((|(m.a * m.d - m.b * m.c : ℤ)| : ℤ) : ℝ) = 1 := by rw [hdet]; norm_num
    rw [Int.cast_abs] at this
    push_cast at this
    exact this
  -- the displacement
  have hdisp : z - r = t * ((m.a : ℝ) * (m.d : ℝ) - (m.b : ℝ) * (m.c : ℝ))
      / ((m.d : ℝ) * ((m.c : ℝ) * t + (m.d : ℝ))) := by
    rw [hrep, hrdef]
    field_simp
    ring
  have hdispabs : |z - r| ≤ t / (m.d : ℝ) ^ 2 := by
    have hd2 : (0:ℝ) < (m.d:ℝ) ^ 2 := by positivity
    have hDD : (m.d:ℝ) ^ 2 ≤ (m.d : ℝ) * ((m.c : ℝ) * t + (m.d : ℝ)) := by
      nlinarith [mul_nonneg (mul_nonneg hdR.le hcR) ht0.le]
    have heq : |z - r| = t / ((m.d : ℝ) * ((m.c : ℝ) * t + (m.d : ℝ))) := by
      rw [hdisp, abs_div, abs_mul, hdetR, mul_one, abs_of_pos ht0,
        abs_of_pos (by positivity : (0:ℝ) < (m.d : ℝ) * ((m.c : ℝ) * t + (m.d : ℝ)))]
    rw [heq, div_le_div_iff₀ (by positivity) hd2]
    nlinarith [ht0.le]
  -- the integer value
  set K : ℤ := A * m.b ^ 2 + B * m.b * m.d + C * m.d ^ 2 with hK
  have hKne : K ≠ 0 := quad_ne_zero_of_irrational hA hirr hroot m.b m.d (ne_of_gt hd)
  have hK1 : (1:ℝ) ≤ |(K:ℝ)| := by
    have : (1:ℤ) ≤ |K| := Int.one_le_abs (by omega)
    have h2 : ((|K| : ℤ) : ℝ) = |(K:ℝ)| := by push_cast; ring
    rw [← h2]
    exact_mod_cast this
  have hKeq : (K:ℝ) = (m.d : ℝ) ^ 2 * ((r - z) * ((A:ℝ) * (r + z) + (B:ℝ))) := by
    have hsub : (r - z) * ((A:ℝ) * (r + z) + (B:ℝ))
        = ((A:ℝ) * r ^ 2 + (B:ℝ) * r + (C:ℝ)) - ((A:ℝ) * z ^ 2 + (B:ℝ) * z + (C:ℝ)) := by ring
    rw [hsub, hroot, sub_zero, hK]
    push_cast
    rw [hrdef]
    field_simp
  -- assemble
  have hfacbd : |(A:ℝ) * (r + z) + (B:ℝ)| ≤ 2 * |(A:ℝ)| + |(B:ℝ)| := by
    have h1 : |(A:ℝ) * (r + z)| ≤ 2 * |(A:ℝ)| := by
      rw [abs_mul]
      have : |r + z| ≤ 2 := by
        rw [abs_of_nonneg (by linarith [hz.1.le] : (0:ℝ) ≤ r + z)]
        linarith [hz.2.le]
      nlinarith [abs_nonneg ((A:ℝ))]
    calc |(A:ℝ) * (r + z) + (B:ℝ)| ≤ |(A:ℝ) * (r + z)| + |(B:ℝ)| := abs_add_le _ _
      _ ≤ 2 * |(A:ℝ)| + |(B:ℝ)| := by linarith
  have hchain : (1:ℝ) ≤ (m.d:ℝ) ^ 2 * (t / (m.d:ℝ) ^ 2) * (2 * |(A:ℝ)| + |(B:ℝ)|) := by
    calc (1:ℝ) ≤ |(K:ℝ)| := hK1
      _ = (m.d:ℝ) ^ 2 * (|r - z| * |(A:ℝ) * (r + z) + (B:ℝ)|) := by
          rw [hKeq, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (m.d:ℝ) ^ 2)]
      _ ≤ (m.d:ℝ) ^ 2 * ((t / (m.d:ℝ) ^ 2) * (2 * |(A:ℝ)| + |(B:ℝ)|)) := by
          have habs : |r - z| ≤ t / (m.d : ℝ) ^ 2 := by rw [abs_sub_comm]; exact hdispabs
          have h0 : (0:ℝ) ≤ 2 * |(A:ℝ)| + |(B:ℝ)| := by positivity
          have := mul_le_mul habs hfacbd (abs_nonneg _) (by positivity)
          nlinarith [sq_nonneg ((m.d:ℝ))]
      _ = (m.d:ℝ) ^ 2 * (t / (m.d:ℝ) ^ 2) * (2 * |(A:ℝ)| + |(B:ℝ)|) := by ring
  have hcancel : (m.d:ℝ) ^ 2 * (t / (m.d:ℝ) ^ 2) = t := by
    field_simp
  rw [hcancel] at hchain
  exact hchain

/-- **Bounded partial quotients, with an explicit bound.**  Every digit of a quadratic irrational
of `(0,1)` is at most `⌊2|A| + |B|⌋`. -/
theorem cfDigit_le_of_quadratic {A B C : ℤ} (hA : A ≠ 0) {z : ℝ} (hirr : Irrational z)
    (hz : z ∈ Set.Ioo (0:ℝ) 1) (hroot : (A:ℝ) * z ^ 2 + (B:ℝ) * z + (C:ℝ) = 0) (n : ℕ) :
    cfDigit z n ≤ ⌊2 * |(A:ℝ)| + |(B:ℝ)|⌋₊ := by
  obtain ⟨-, ht0, -⟩ := irrational_orbit z hirr hz n
  have h := tail_lower_bound hA hirr hz hroot n
  have hinv : (gaussMap^[n] z)⁻¹ ≤ 2 * |(A:ℝ)| + |(B:ℝ)| := by
    rw [inv_eq_one_div, div_le_iff₀ ht0]
    linarith
  rw [cfDigit]
  exact Nat.floor_le_floor hinv

/-! ## Bounded digits contradict CF-normality -/

theorem countOccurrences_eq_zero_of_not_mem {k : ℕ} {l : List ℕ} (h : k ∉ l) :
    countOccurrences [k] l = 0 := by
  rw [countOccurrences, List.countP_eq_zero]
  intro u hu hpre
  refine h ?_
  have hsuf : u <:+ l := (List.mem_tails _ _).1 hu
  have hk : k ∈ u := by
    cases u with
    | nil => simp [List.isPrefixOf] at hpre
    | cons c u' =>
        have : k = c := by
          simpa [List.isPrefixOf] using hpre
        simp [this]
  exact hsuf.subset hk

/-- **Bounded digits are incompatible with CF-normality.**  The word `[M+1]` never occurs, so its
frequency is `0`, while the Gauss measure of its cylinder is positive. -/
theorem not_isCFNormal_of_bddDigits {y : ℝ} {M : ℕ} (h : ∀ n, cfDigit y n ≤ M) :
    ¬ IsCFNormal y := by
  intro hnorm
  have hpos : 1 ≤ M + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hlim := hnorm [M + 1] (by simp) (by
    intro a ha
    simp only [List.mem_singleton] at ha
    omega)
  have hzero : ∀ p : ℕ,
      (countOccurrences [M + 1] ((List.range p).map (cfDigit y)) : ℝ) / p = 0 := by
    intro p
    rw [countOccurrences_eq_zero_of_not_mem (k := M + 1)]
    · simp
    · intro hmem
      obtain ⟨i, -, hi⟩ := List.mem_map.1 hmem
      have := h i
      omega
  rw [tendsto_congr hzero] at hlim
  have h0 : (gaussMeasure (cfCylinder [M + 1])).toReal = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim |>.symm
  rw [gaussMeasure_digit_cylinder (M + 1) hpos] at h0
  push_cast at h0
  have harg : (1:ℝ) < 1 + 1 / (((M:ℝ) + 1) * ((M:ℝ) + 1 + 2)) := by
    have : (0:ℝ) < ((M:ℝ) + 1) * ((M:ℝ) + 1 + 2) := by positivity
    have : (0:ℝ) < 1 / (((M:ℝ) + 1) * ((M:ℝ) + 1 + 2)) := by positivity
    linarith
  have hlogpos : 0 < Real.logb 2 (1 + 1 / (((M:ℝ) + 1) * ((M:ℝ) + 1 + 2))) :=
    Real.logb_pos (by norm_num) harg
  rw [ENNReal.toReal_ofReal hlogpos.le] at h0
  linarith

section Audit

#print axioms qMat_det
#print axioms qMat_bounds
#print axioms z_eq_qApp
#print axioms quad_ne_zero_of_irrational
#print axioms tail_lower_bound
#print axioms cfDigit_le_of_quadratic
#print axioms countOccurrences_eq_zero_of_not_mem
#print axioms not_isCFNormal_of_bddDigits

end Audit

end NormalNumbers.VandeheyS7
