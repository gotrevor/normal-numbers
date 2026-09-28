/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyNormalForm

/-!
# Raney's balanced normal form — the working replacement for Vandehey's §2

Vandehey 2017 Lemma 2.1 asserts that his state set `M_D` (`VandeheyNormalForm.lean`) absorbs
an ingested digit:  `M · J A_j = A_{d₀} J A_{d₁} ⋯ J A_{d_m} · M'` with `M' ∈ M_D`.  His proof
(pp. 6–7) runs a Euclidean descent with the digit `d = min(⌊α/γ⌋, ⌊β/δ⌋)`.

**That descent does not terminate** — see `probes/vandehey_lemma21.py`.  The smallest
counterexample is `D = 3`, `M = [[0,3],[1,1]]` (Type III), `j = 1`:  the prescribed `d₀ = 1`
produces `M₀ = [[2,1],[1,2]]`, and from there the prescribed rule alternates
`[[2,1],[1,2]] ↦ [[1,2],[2,1]] ↦ [[2,1],[1,2]]` forever, because `⌊1/2⌋ = 0` kills the `min`.
Neither matrix lies in `M_D`.  The *statement* survives (a brute-force search over digit
strings rescues every stalled start), but the prescribed rule does not, so the proof cannot be
transcribed.

This module takes the classical route instead, which terminates for a one-line reason.
Write

  `L = [[1,0],[1,1]]`,   `R = [[1,1],[0,1]]`,

the two generators of the monoid of nonnegative determinant-`1` matrices.  Call a nonnegative
matrix **balanced** when neither row dominates the other entrywise, i.e. when

  `γ < α ∧ β < δ`   or   `α < γ ∧ δ < β`.

Equivalently: neither `L⁻¹M` nor `R⁻¹M` is nonnegative — you cannot strip a generator off the
left.  For fixed `|det| = D` the balanced matrices form a **finite** set (`raneyEntry_le`,
`finite_isRD`), because `|det| ≥ α + δ − 1` on the first branch.

The descent is then trivial: if `M` is nonnegative, has nonzero determinant and is *not*
balanced, then one of `L⁻¹M`, `R⁻¹M` is nonnegative and its entry sum is **strictly smaller**
(you subtract one whole row from the other, and that row is nonzero or the determinant would
vanish).  So `exists_balanced_decomp`: every nonnegative `N` of determinant `±D` factors as
`N = (an L/R word) · M'` with `M'` balanced of determinant `±D`.

Since the ingest matrix `B j = [[0,1],[1,j]]` is itself nonnegative, this gives the closure
property Lemma 2.1 was for (`isRD_ingest`), with no `d₀ ≥ −1` side condition at all: the whole
emitted string has nonnegative digits, because nothing here ever leaves the nonnegative cone.
`A_{d₀} J A_{d₁} J ⋯ J A_{d_m} = R^{d₀} L^{d₁} R^{d₂} ⋯`, so an `L/R` word *is* a CF string.
-/

namespace NormalNumbers

namespace Mat2

/-! ## The nonnegative cone and the two generators -/

/-- All four entries are `≥ 0`. -/
def Nonneg (M : Mat2) : Prop := 0 ≤ M.a ∧ 0 ≤ M.b ∧ 0 ≤ M.c ∧ 0 ≤ M.d

/-- `L = [[1,0],[1,1]]`: add row 1 to row 2. -/
def lrL : Mat2 := ⟨1, 0, 1, 1⟩

/-- `R = [[1,1],[0,1]]`: add row 2 to row 1. -/
def lrR : Mat2 := ⟨1, 1, 0, 1⟩

@[simp] lemma det_lrL : lrL.det = 1 := by simp [det, lrL]
@[simp] lemma det_lrR : lrR.det = 1 := by simp [det, lrR]

/-- A word in `L` and `R` (`true = L`, `false = R`), read left to right. -/
def lrProd : List Bool → Mat2
  | [] => 1
  | b :: w => (if b then lrL else lrR) * lrProd w

@[simp] lemma lrProd_nil : lrProd [] = 1 := rfl

lemma lrProd_cons (b : Bool) (w : List Bool) :
    lrProd (b :: w) = (if b then lrL else lrR) * lrProd w := rfl

lemma det_lrProd (w : List Bool) : (lrProd w).det = 1 := by
  induction w with
  | nil => simp
  | cons b w ih => rw [lrProd_cons, det_mul, ih]; cases b <;> simp

/-! ## Balanced matrices -/

/-- **Balanced** (Raney): nonnegative, and neither row dominates the other.  Equivalently,
neither `L⁻¹M` nor `R⁻¹M` is nonnegative. -/
def Balanced (M : Mat2) : Prop :=
  Nonneg M ∧ ((M.c < M.a ∧ M.b < M.d) ∨ (M.a < M.c ∧ M.d < M.b))

/-- **The Raney state set**: balanced of determinant `±D`.  This is the replacement for
Vandehey's `M_D`. -/
def IsRD (D : ℕ) (M : Mat2) : Prop :=
  (M.det = (D : ℤ) ∨ M.det = -(D : ℤ)) ∧ Balanced M

/-- **The entry bound.**  A balanced matrix of determinant `±D` has all entries in `[0, D]`.
The mechanism: on the branch `γ < α`, `β < δ` one has `D = αδ − βγ ≥ α + δ − 1`. -/
theorem raneyEntry_le {D : ℕ} {M : Mat2} (h : IsRD D M) :
    0 ≤ M.a ∧ M.a ≤ (D : ℤ) ∧ 0 ≤ M.b ∧ M.b ≤ (D : ℤ) ∧
      0 ≤ M.c ∧ M.c ≤ (D : ℤ) ∧ 0 ≤ M.d ∧ M.d ≤ (D : ℤ) := by
  obtain ⟨hdet, ⟨ha0, hb0, hc0, hd0⟩, hsplit⟩ := h
  rw [det] at hdet
  rcases hsplit with ⟨hca, hbd⟩ | ⟨hac, hdb⟩
  · -- `det = αδ − βγ ≥ α + δ − 1 > 0`, so `det = D`
    have hkey : M.a + M.d - 1 ≤ M.a * M.d - M.b * M.c := by nlinarith
    have hDpos : M.a * M.d - M.b * M.c = (D : ℤ) := by
      rcases hdet with h | h
      · exact h
      · exfalso; nlinarith [Int.natCast_nonneg D]
    refine ⟨ha0, by omega, hb0, by omega, hc0, by omega, hd0, by omega⟩
  · have hkey : M.c + M.b - 1 ≤ M.b * M.c - M.a * M.d := by nlinarith
    have hDpos : M.b * M.c - M.a * M.d = (D : ℤ) := by
      rcases hdet with h | h
      · exfalso; nlinarith [Int.natCast_nonneg D]
      · omega
    refine ⟨ha0, by omega, hb0, by omega, hc0, by omega, hd0, by omega⟩

/-- **The Raney state set is finite** — the transducer really is a finite-state machine. -/
theorem finite_isRD (D : ℕ) : {M : Mat2 | IsRD D M}.Finite := by
  have hinj : Function.Injective (fun M : Mat2 => (M.a, M.b, M.c, M.d)) := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
    simp only [Prod.mk.injEq] at h
    simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine Set.Finite.subset (((Set.finite_Icc (0 : ℤ) (D : ℤ)).prod
    ((Set.finite_Icc (0 : ℤ) (D : ℤ)).prod
      ((Set.finite_Icc (0 : ℤ) (D : ℤ)).prod (Set.finite_Icc (0 : ℤ) (D : ℤ)))))) ?_
  rintro ⟨a, b, c, d⟩ ⟨M, hM, hEq⟩
  simp only [Prod.mk.injEq] at hEq
  obtain ⟨ha, hb, hc, hd⟩ := hEq
  subst ha; subst hb; subst hc; subst hd
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := raneyEntry_le hM
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩

/-! ## The descent -/

/-- Stripping `L` on the left: `L * stripL N = N`, and `stripL N` is nonnegative when row 1
is dominated by row 2. -/
def stripL (N : Mat2) : Mat2 := ⟨N.a, N.b, N.c - N.a, N.d - N.b⟩

/-- Stripping `R` on the left. -/
def stripR (N : Mat2) : Mat2 := ⟨N.a - N.c, N.b - N.d, N.c, N.d⟩

@[simp] lemma lrL_mul_stripL (N : Mat2) : lrL * stripL N = N := by
  cases N; simp [mul_def, mul, lrL, stripL]

@[simp] lemma lrR_mul_stripR (N : Mat2) : lrR * stripR N = N := by
  cases N; simp [mul_def, mul, lrR, stripR]

@[simp] lemma det_stripL (N : Mat2) : (stripL N).det = N.det := by
  simp only [stripL, det]; ring

@[simp] lemma det_stripR (N : Mat2) : (stripR N).det = N.det := by
  simp only [stripR, det]; ring

/-- The entry sum, the descent measure. -/
def entrySum (N : Mat2) : ℤ := N.a + N.b + N.c + N.d

/-- **The descent.**  Every nonnegative matrix of determinant `±D` (`D > 0`) is an `L/R` word
times a balanced matrix of the same determinant.  This is the replacement for Vandehey's
Lemma 2.1, and its termination is the strict drop of `entrySum`. -/
theorem exists_balanced_decomp_aux (D : ℕ) (hD : 0 < D) :
    ∀ n : ℕ, ∀ N : Mat2, Nonneg N → (N.det = (D : ℤ) ∨ N.det = -(D : ℤ)) →
      entrySum N ≤ (n : ℤ) →
      ∃ (w : List Bool) (M' : Mat2), IsRD D M' ∧ N = lrProd w * M' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N hN hdet hle
    by_cases hbal : Balanced N
    · exact ⟨[], N, ⟨hdet, hbal⟩, by simp⟩
    · -- not balanced: one row dominates the other
      obtain ⟨ha0, hb0, hc0, hd0⟩ := hN
      have hDne : N.det ≠ 0 := by
        rcases hdet with h | h <;> rw [h] <;> [skip; simp] <;> omega
      have hdom : (N.a ≤ N.c ∧ N.b ≤ N.d) ∨ (N.c ≤ N.a ∧ N.d ≤ N.b) := by
        by_contra hcon
        exact hbal ⟨⟨ha0, hb0, hc0, hd0⟩, by omega⟩
      rcases hdom with ⟨hac, hbd⟩ | ⟨hca, hdb⟩
      · -- strip `L`
        have hab : 0 < N.a + N.b := by
          rcases lt_or_eq_of_le ha0 with h | h
          · omega
          · rcases lt_or_eq_of_le hb0 with h' | h'
            · omega
            · exact absurd (by rw [det, ← h, ← h']; ring) hDne
        set N' := stripL N with hN'
        have hN'nn : Nonneg N' := ⟨ha0, hb0, by simp [hN', stripL]; omega,
          by simp [hN', stripL]; omega⟩
        have hsum : entrySum N' = N.c + N.d := by simp [hN', stripL, entrySum]; ring
        have hn1 : 1 ≤ n := by
          have : (1 : ℤ) ≤ (n : ℤ) := le_trans (by unfold entrySum at hle ⊢; omega) hle
          exact_mod_cast this
        have hlt : (n - 1) < n := by omega
        have hle' : entrySum N' ≤ ((n - 1 : ℕ) : ℤ) := by
          have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
          rw [this, hsum]
          unfold entrySum at hle
          omega
        obtain ⟨w, M', hM', hEq⟩ :=
          ih (n - 1) hlt N' hN'nn (by rw [hN', det_stripL]; exact hdet) hle'
        exact ⟨true :: w, M', hM', by
          rw [lrProd_cons, if_pos rfl, mul_assoc', ← hEq, hN', lrL_mul_stripL]⟩
      · -- strip `R`
        have hcd : 0 < N.c + N.d := by
          rcases lt_or_eq_of_le hc0 with h | h
          · omega
          · rcases lt_or_eq_of_le hd0 with h' | h'
            · omega
            · exact absurd (by rw [det, ← h, ← h']; ring) hDne
        set N' := stripR N with hN'
        have hN'nn : Nonneg N' := ⟨by simp [hN', stripR]; omega, by simp [hN', stripR]; omega,
          hc0, hd0⟩
        have hsum : entrySum N' = N.a + N.b := by simp [hN', stripR, entrySum]; ring
        have hn1 : 1 ≤ n := by
          have : (1 : ℤ) ≤ (n : ℤ) := le_trans (by unfold entrySum at hle ⊢; omega) hle
          exact_mod_cast this
        have hlt : (n - 1) < n := by omega
        have hle' : entrySum N' ≤ ((n - 1 : ℕ) : ℤ) := by
          have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
          rw [this, hsum]
          unfold entrySum at hle
          omega
        obtain ⟨w, M', hM', hEq⟩ :=
          ih (n - 1) hlt N' hN'nn (by rw [hN', det_stripR]; exact hdet) hle'
        exact ⟨false :: w, M', hM', by
          rw [lrProd_cons, if_neg (by simp), mul_assoc', ← hEq, hN', lrR_mul_stripR]⟩

/-- **The descent**, in the form downstream wants. -/
theorem exists_balanced_decomp {D : ℕ} (hD : 0 < D) {N : Mat2} (hN : Nonneg N)
    (hdet : N.det = (D : ℤ) ∨ N.det = -(D : ℤ)) :
    ∃ (w : List Bool) (M' : Mat2), IsRD D M' ∧ N = lrProd w * M' := by
  obtain ⟨ha, hb, hc, hd⟩ := hN
  exact exists_balanced_decomp_aux D hD (entrySum N).toNat N ⟨ha, hb, hc, hd⟩ hdet
    (by rw [Int.toNat_of_nonneg (by unfold entrySum; omega)])

/-! ## Lemma 2.1, the closure property -/

@[simp] lemma nonneg_B (j : ℕ) : Nonneg (B j) := by
  refine ⟨le_refl 0, zero_le_one, zero_le_one, ?_⟩
  exact Int.natCast_nonneg j

lemma Nonneg.mul {M N : Mat2} (hM : Nonneg M) (hN : Nonneg N) : Nonneg (M * N) := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  obtain ⟨k1, k2, k3, k4⟩ := hN
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [mul_def]
  · exact add_nonneg (mul_nonneg h1 k1) (mul_nonneg h2 k3)
  · exact add_nonneg (mul_nonneg h1 k2) (mul_nonneg h2 k4)
  · exact add_nonneg (mul_nonneg h3 k1) (mul_nonneg h4 k3)
  · exact add_nonneg (mul_nonneg h3 k2) (mul_nonneg h4 k4)

/-- **Lemma 2.1 (Raney form).**  Ingesting a digit into a Raney state re-normalizes: there is
an `L/R` word (a CF string, by `A_{d₀} J A_{d₁} J ⋯ = R^{d₀} L^{d₁} ⋯`) and a Raney state `M'`
with `M · B j = word · M'`.  No `d₀ ≥ −1` side condition: everything stays in the nonnegative
cone. -/
theorem isRD_ingest {D : ℕ} (hD : 0 < D) {M : Mat2} (hM : IsRD D M) (j : ℕ) :
    ∃ (w : List Bool) (M' : Mat2), IsRD D M' ∧ M * B j = lrProd w * M' := by
  obtain ⟨hdet, hbal⟩ := hM
  refine exists_balanced_decomp hD (hbal.1.mul (nonneg_B j)) ?_
  rw [det_mul, det_B]
  rcases hdet with h | h
  · right; rw [h]; ring
  · left; rw [h]; ring

/-! ## Guard rule -/

/-- **Content locator**: `diag(D,1)`, the start state of the transducer for `x ↦ D·x`, is a
Raney state.  So the state set is never empty, and the descent has somewhere to start. -/
theorem isRD_diag {D : ℕ} (hD : 0 < D) : IsRD D ⟨(D : ℤ), 0, 0, 1⟩ := by
  have hD' : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  exact ⟨Or.inl (by simp [det]), ⟨⟨hD'.le, le_refl 0, le_refl 0, zero_le_one⟩,
    Or.inl ⟨hD', zero_lt_one⟩⟩⟩

/-- **Degenerate-case verdict**: the singular state set is empty.  A balanced matrix has
nonzero determinant, so `D = 0` carries no states — the nonsingularity hypothesis of
Theorem 1.1 is exactly what makes the transducer exist. -/
theorem not_isRD_zero {M : Mat2} : ¬ IsRD 0 M := by
  rintro ⟨hdet, ⟨ha, hb, hc, hd⟩, hsplit⟩
  have h0 : M.a * M.d - M.b * M.c = 0 := by
    rcases hdet with h | h <;> simpa [det] using h
  rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> nlinarith

/-- **Degenerate-case verdict**: the *empty word* case of the descent is real — a state that
is already balanced is returned untouched.  Taken with `isRD_ingest`, this says `m = 0` is
allowed, matching Vandehey's remark that `M J A_j = M'` can happen. -/
theorem exists_balanced_decomp_nil {D : ℕ} {M : Mat2} (_hM : IsRD D M) :
    M = lrProd [] * M := by simp

/-- **Degenerate-case verdict**: the descent is *not* vacuous — an unbalanced nonnegative
matrix really does need a nonempty word.  `[[2,1],[1,1]]` (determinant `1`, row 2 dominated
by row 1) is nonnegative and not balanced. -/
theorem not_balanced_of_dominates : ¬ Balanced ⟨2, 1, 1, 1⟩ := by
  rintro ⟨-, h | h⟩ <;> simp at h


/-! ## From `L/R` words to CF strings

`A_{d₀} J A_{d₁} J ⋯ J A_{d_m} = A_{d₀} · B_{d₁} ⋯ B_{d_m}` (since `B_d = J A_d`), and in
`L/R` coordinates this is `R^{d₀} L^{d₁} R^{d₂} ⋯`.  So an `L/R` word *is* a CF string, with
an even number of `B` factors — the parity is forced, because `det (lrProd w) = 1` while each
`B` contributes `−1`.  Trailing `R^0 = 1` makes the parity work out in every case.
-/

/-- `A n = [[1,n],[0,1]]`, Vandehey's `A_n`. -/
def A (n : ℕ) : Mat2 := ⟨1, (n : ℤ), 0, 1⟩

/-- `B d₁ ⋯ B d_m`. -/
def bProd : List ℕ → Mat2
  | [] => 1
  | d :: ds => B d * bProd ds

@[simp] lemma bProd_nil : bProd [] = 1 := rfl

lemma bProd_cons (d : ℕ) (ds : List ℕ) : bProd (d :: ds) = B d * bProd ds := rfl

@[simp] lemma A_zero : A 0 = 1 := by
  simp only [A, Nat.cast_zero]
  rfl

lemma lrL_mul_A (n : ℕ) : lrL * A n = B 1 * B n := by
  simp only [mul_def, mul, lrL, A, B, Mat2.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

lemma lrR_mul_A (n : ℕ) : lrR * A n = A (1 + n) := by
  simp only [mul_def, mul, lrR, A, Mat2.mk.injEq]
  refine ⟨by ring, by push_cast; ring, by ring, by ring⟩

/-- **An `L/R` word is a CF string.**  `lrProd w = A_{d₀} · B_{d₁} ⋯ B_{d_m}` with `m` even,
i.e. `lrProd w = A_{d₀} J A_{d₁} J ⋯ J A_{d_m}` — the right-hand side of Vandehey's (5). -/
theorem exists_cfString_of_lrProd (w : List Bool) :
    ∃ (d₀ : ℕ) (ds : List ℕ), ds.length % 2 = 0 ∧ lrProd w = A d₀ * bProd ds := by
  induction w with
  | nil => exact ⟨0, [], rfl, by simp⟩
  | cons b w ih =>
    obtain ⟨d₀, ds, hlen, hEq⟩ := ih
    cases b
    · refine ⟨1 + d₀, ds, hlen, ?_⟩
      rw [lrProd_cons, if_neg (by simp), hEq, ← mul_assoc', lrR_mul_A]
    · refine ⟨0, 1 :: d₀ :: ds, by simp only [List.length_cons]; omega, ?_⟩
      rw [lrProd_cons, if_pos rfl, hEq, ← mul_assoc', lrL_mul_A, A_zero, one_mul',
        bProd_cons, bProd_cons, mul_assoc']

/-- **Lemma 2.1, in Vandehey's own shape.**  For a Raney state `M` and an ingested digit `j`,

  `M · J A_j = A_{d₀} J A_{d₁} J ⋯ J A_{d_m} · M'`,   `M' ∈ RaneyState D`,

with every `d_i ∈ ℕ` — no `d₀ ≥ −1` escape hatch is needed, because the Raney cone is stable
under everything in sight.  Contrast Vandehey's Lemma 2.1, whose prescribed descent does not
terminate (see the module docstring). -/
theorem isRD_ingest_cfString {D : ℕ} (hD : 0 < D) {M : Mat2} (hM : IsRD D M) (j : ℕ) :
    ∃ (d₀ : ℕ) (ds : List ℕ) (M' : Mat2), IsRD D M' ∧ ds.length % 2 = 0 ∧
      M * B j = A d₀ * bProd ds * M' := by
  obtain ⟨w, M', hM', hEq⟩ := isRD_ingest hD hM j
  obtain ⟨d₀, ds, hlen, hw⟩ := exists_cfString_of_lrProd w
  exact ⟨d₀, ds, M', hM', hlen, by rw [hEq, hw]⟩

#print axioms finite_isRD
#print axioms exists_balanced_decomp
#print axioms isRD_ingest_cfString

/-! ## The refutation: Vandehey's prescribed descent does not terminate

Kernel witness for the Maze row `hall_vandehey_lemma21_min_rule`.  The rule of Lemma 2.1's
proof, applied to the state `M_i = [[α,β],[γ,δ]]`, emits
`d = min(⌊γ/α⌋, ⌊δ/β⌋)` and passes to `M_{i+1} = A_d⁻¹ J M_i = [[γ − dα, δ − dβ],[α,β]]`.
Started from `M = [[0,3],[1,1]] ∈ M_3` and `j = 1`, the paper's own `d₀ = 1` lands on
`[[2,1],[1,2]]`, and from there the rule has a **two-cycle** through `[[1,2],[2,1]]`, neither
member of which is in `M_3`.  The `min` is what kills it: one of the two floors is `0`.
-/

/-- One step of Vandehey's prescribed descent: `M ↦ A_d⁻¹ J M` with `d = min(⌊γ/α⌋, ⌊δ/β⌋)`. -/
def vandeheyStep (N : Mat2) : Mat2 :=
  let d := min (N.c / N.a) (N.d / N.b)
  ⟨N.c - d * N.a, N.d - d * N.b, N.a, N.b⟩

/-- **The prescribed descent of Vandehey 2017 Lemma 2.1 does not terminate.**  Six conjuncts:
the start `[[0,3],[1,1]]` is a genuine `M_3` state; ingesting `j = 1` and stripping the
paper's `d₀ = 1` gives `[[2,1],[1,2]]`; that matrix and its image form a two-cycle of the
prescribed step; and neither lies in `M_3`.  Hence the transcription of the paper's proof is
impossible, and `exists_balanced_decomp` (Raney) replaces it. -/
theorem vandeheyStep_not_terminating :
    IsMD 3 ⟨0, 3, 1, 1⟩ ∧
      (⟨0, 3, 1, 1⟩ : Mat2) * B 1 = A 1 * (⟨2, 1, 1, 2⟩ : Mat2) ∧
      vandeheyStep ⟨2, 1, 1, 2⟩ = ⟨1, 2, 2, 1⟩ ∧
      vandeheyStep ⟨1, 2, 2, 1⟩ = ⟨2, 1, 1, 2⟩ ∧
      ¬ IsMD 3 ⟨2, 1, 1, 2⟩ ∧ ¬ IsMD 3 ⟨1, 2, 2, 1⟩ := by
  refine ⟨⟨Or.inr (by norm_num [det]), Or.inr (Or.inr (Or.inl ⟨rfl, by norm_num, by norm_num,
      by norm_num, by norm_num⟩))⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mul_def, mul, A, B, Mat2.mk.injEq]; norm_num
  · simp only [vandeheyStep, Mat2.mk.injEq]; norm_num
  · simp only [vandeheyStep, Mat2.mk.injEq]; norm_num
  · rintro ⟨-, h⟩
    simp only [TypeI, TypeII, TypeIII, TypeIV, TypeV, TypeVI] at h
    norm_num at h
  · rintro ⟨-, h⟩
    simp only [TypeI, TypeII, TypeIII, TypeIV, TypeV, TypeVI] at h
    norm_num at h

#print axioms vandeheyStep_not_terminating

end Mat2

end NormalNumbers
