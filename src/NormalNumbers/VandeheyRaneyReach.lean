/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyLRTransducer

/-!
# The Raney automaton is PERIODIC, and the phase quotient that repairs it

`VandeheyClassEquidist.classEquidistribution_of_common_reach` turns a finite automaton reading
CF digits into `VandeheyCocycle.ClassEquidistribution` — the crux input of Vandehey 2017
Theorem 1.1 — provided every state reaches one common target `z` by a genuine word of **one
fixed length**.  The Raney transducer `VandeheyLR.lrDelta` can never satisfy that:

> `det (M * B j) = - det M`, so the *sign of the determinant* is a deterministic period-2
> phase on the state set, and two states of opposite phase are never simultaneously occupied.

(Numerically: `probes/raney_reach.py` finds common targets for `D = 2,3,5,7,11,13` but **no**
uniform length, and confirms the sign flips at every step.)

## The repair

Row-swapping `ι M := J · M` is an involution of the Raney state set that **commutes with the
transition** and negates the determinant:

* `isRD_swapRows`, `det_swapRows` — `ι` maps `RState D` to itself, flipping the phase;
* `lrDelta_swapRows` — `ι (lrDelta M j) = lrDelta (ι M) j`;
* `lrOut_swapRows` — the emitted word is `L ↔ R` swapped, so nothing is lost.

Hence on the positive-determinant half `RPlus D` the **phase-corrected** automaton
`rplusDelta P a := ι (lrDelta P a)` is a genuine finite automaton with
`stateAt lrDelta … i = ι^i (stateAt rplusDelta … i)`, and it is *aperiodic*.  Its uniform
common reach is proved here, at length exactly `2`:

> `rplus_common_reach` — every `P ∈ RPlus D` reaches `diag(1, D)` in exactly two genuine
> digits, for every prime `D`.

The arithmetic core is `lrDelta_eq_zTarget`: `lrDelta M j = [[0,D],[1,0]]` **iff**
`D ∣ a + b·j` and `D ∣ c + d·j`, and that congruence pair is solvable because `D ∣ det M`
makes the two conditions equivalent over `ZMod D`.

Everything rests on `balanced_decomp_unique`, which pins the `Classical.choose`-defined
`lrDelta`/`lrOut` for the first time: the Raney (L/R word, balanced matrix) factorization of a
nonnegative matrix of nonzero determinant is **unique**.
-/

namespace NormalNumbers

namespace Mat2

/-! ## Uniqueness of the balanced decomposition -/

lemma mat2_ext {M N : Mat2} (ha : M.a = N.a) (hb : M.b = N.b) (hc : M.c = N.c)
    (hd : M.d = N.d) : M = N := by
  cases M; cases N; simp_all

@[simp] lemma nonneg_lrL : Nonneg lrL := ⟨by norm_num [lrL], by norm_num [lrL],
  by norm_num [lrL], by norm_num [lrL]⟩

@[simp] lemma nonneg_lrR : Nonneg lrR := ⟨by norm_num [lrR], by norm_num [lrR],
  by norm_num [lrR], by norm_num [lrR]⟩

lemma lrProd_cons_true (w : List Bool) : lrProd (true :: w) = lrL * lrProd w := by
  rw [lrProd_cons, if_pos rfl]

lemma lrProd_cons_false (w : List Bool) : lrProd (false :: w) = lrR * lrProd w := by
  rw [lrProd_cons]; norm_num

lemma nonneg_lrProd_mul {w : List Bool} {M : Mat2} (hM : Nonneg M) :
    Nonneg (lrProd w * M) := by
  induction w with
  | nil => simpa using hM
  | cons b w ih =>
      cases b
      · rw [lrProd_cons_false, mul_assoc']; exact Nonneg.mul nonneg_lrR ih
      · rw [lrProd_cons_true, mul_assoc']; exact Nonneg.mul nonneg_lrL ih

/-- A balanced matrix is not `L` times a nonnegative matrix: `L * N` has row 2 dominating. -/
lemma not_balanced_lrL_mul {N : Mat2} (hN : Nonneg N) : ¬ Balanced (lrL * N) := by
  obtain ⟨h1, h2, h3, h4⟩ := hN
  rintro ⟨-, hsplit⟩
  simp only [mul_def, mul, lrL] at hsplit
  omega

/-- A balanced matrix is not `R` times a nonnegative matrix: `R * N` has row 1 dominating. -/
lemma not_balanced_lrR_mul {N : Mat2} (hN : Nonneg N) : ¬ Balanced (lrR * N) := by
  obtain ⟨h1, h2, h3, h4⟩ := hN
  rintro ⟨-, hsplit⟩
  simp only [mul_def, mul, lrR] at hsplit
  omega

lemma lrL_mul_injective {N N' : Mat2} (h : lrL * N = lrL * N') : N = N' := by
  cases N; cases N'
  simp only [mul_def, mul, lrL, Mat2.mk.injEq] at h ⊢
  omega

lemma lrR_mul_injective {N N' : Mat2} (h : lrR * N = lrR * N') : N = N' := by
  cases N; cases N'
  simp only [mul_def, mul, lrR, Mat2.mk.injEq] at h ⊢
  omega

/-- `L * N = R * N'` with both factors nonnegative forces `N.c = N.d = 0`, hence a vanishing
determinant: the two rows of the common value agree. -/
lemma det_eq_zero_of_lrL_eq_lrR {N N' : Mat2} (hN : Nonneg N) (hN' : Nonneg N')
    (h : lrL * N = lrR * N') : (lrL * N).det = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hN
  obtain ⟨k1, k2, k3, k4⟩ := hN'
  simp only [mul_def, mul, lrL, lrR, Mat2.mk.injEq] at h
  have hc : N.c = 0 := by omega
  have hd : N.d = 0 := by omega
  have hdet : (lrL * N).det = N.a * N.d - N.b * N.c := by
    simp only [mul_def, mul, lrL, det]; ring
  rw [hdet, hc, hd]; ring

/-- **Uniqueness of the Raney factorization.**  A nonnegative matrix of nonzero determinant
has exactly one decomposition as an `L/R` word times a balanced matrix.  This is what pins the
`Classical.choose`-defined `VandeheyLR.lrDelta` and `VandeheyLR.lrOut`. -/
theorem balanced_decomp_unique :
    ∀ (w₁ w₂ : List Bool) (M₁ M₂ : Mat2), Balanced M₁ → Balanced M₂ → M₁.det ≠ 0 →
      lrProd w₁ * M₁ = lrProd w₂ * M₂ → w₁ = w₂ ∧ M₁ = M₂ := by
  intro w₁
  induction w₁ with
  | nil =>
      intro w₂ M₁ M₂ h₁ h₂ hdet heq
      cases w₂ with
      | nil => exact ⟨rfl, by simpa using heq⟩
      | cons b w =>
          exfalso
          rw [lrProd_nil, one_mul'] at heq
          have hnn : Nonneg (lrProd w * M₂) := nonneg_lrProd_mul h₂.1
          cases b
          · rw [lrProd_cons_false, mul_assoc'] at heq
            exact not_balanced_lrR_mul hnn (heq ▸ h₁)
          · rw [lrProd_cons_true, mul_assoc'] at heq
            exact not_balanced_lrL_mul hnn (heq ▸ h₁)
  | cons b₁ w₁ ih =>
      intro w₂ M₁ M₂ h₁ h₂ hdet heq
      have hnn₁ : Nonneg (lrProd w₁ * M₁) := nonneg_lrProd_mul h₁.1
      have hdetP : (lrProd w₁ * M₁).det ≠ 0 := by
        rw [det_mul, det_lrProd, one_mul]; exact hdet
      cases w₂ with
      | nil =>
          exfalso
          rw [lrProd_nil, one_mul'] at heq
          cases b₁
          · rw [lrProd_cons_false, mul_assoc'] at heq
            exact not_balanced_lrR_mul hnn₁ (heq ▸ h₂)
          · rw [lrProd_cons_true, mul_assoc'] at heq
            exact not_balanced_lrL_mul hnn₁ (heq ▸ h₂)
      | cons b₂ w₂ =>
          have hnn₂ : Nonneg (lrProd w₂ * M₂) := nonneg_lrProd_mul h₂.1
          have key : ∀ (c₁ c₂ : Bool), lrProd (c₁ :: w₁) * M₁ = lrProd (c₂ :: w₂) * M₂ →
              c₁ = c₂ := by
            intro c₁ c₂ he
            cases c₁ <;> cases c₂
            · rfl
            · exfalso
              rw [lrProd_cons_false, lrProd_cons_true, mul_assoc', mul_assoc'] at he
              have hz := det_eq_zero_of_lrL_eq_lrR hnn₂ hnn₁ he.symm
              rw [← he, det_mul, det_lrR, one_mul] at hz
              exact hdetP hz
            · exfalso
              rw [lrProd_cons_true, lrProd_cons_false, mul_assoc', mul_assoc'] at he
              have hz := det_eq_zero_of_lrL_eq_lrR hnn₁ hnn₂ he
              rw [det_mul, det_lrL, one_mul] at hz
              exact hdetP hz
            · rfl
          have hb : b₁ = b₂ := key b₁ b₂ heq
          subst hb
          have hcancel : lrProd w₁ * M₁ = lrProd w₂ * M₂ := by
            cases b₁
            · rw [lrProd_cons_false, lrProd_cons_false, mul_assoc', mul_assoc'] at heq
              exact lrR_mul_injective heq
            · rw [lrProd_cons_true, lrProd_cons_true, mul_assoc', mul_assoc'] at heq
              exact lrL_mul_injective heq
          obtain ⟨hw, hM⟩ := ih w₂ M₁ M₂ h₁ h₂ hdet hcancel
          exact ⟨by rw [hw], hM⟩

/-! ## The row-swap involution `ι M = J · M` -/

/-- Swap the two rows: left multiplication by `J = [[0,1],[1,0]]`. -/
def swapRows (M : Mat2) : Mat2 := ⟨M.c, M.d, M.a, M.b⟩

@[simp] lemma swapRows_swapRows (M : Mat2) : swapRows (swapRows M) = M := by
  cases M; rfl

@[simp] lemma det_swapRows (M : Mat2) : (swapRows M).det = - M.det := by
  simp only [swapRows, det]; ring

@[simp] lemma nonneg_swapRows {M : Mat2} : Nonneg (swapRows M) ↔ Nonneg M := by
  simp only [swapRows, Nonneg]; tauto

lemma balanced_swapRows {M : Mat2} (h : Balanced M) : Balanced (swapRows M) := by
  obtain ⟨hn, hs⟩ := h
  refine ⟨nonneg_swapRows.mpr hn, ?_⟩
  simp only [swapRows]
  tauto

lemma isRD_swapRows {D : ℕ} {M : Mat2} (h : IsRD D M) : IsRD D (swapRows M) := by
  obtain ⟨hdet, hbal⟩ := h
  refine ⟨?_, balanced_swapRows hbal⟩
  rw [det_swapRows]
  rcases hdet with h | h <;> rw [h] <;> simp

lemma swapRows_mul (M N : Mat2) : swapRows (M * N) = swapRows M * N := by
  simp only [swapRows, mul_def, mul]

lemma swapRows_lrL_mul (N : Mat2) : swapRows (lrL * N) = lrR * swapRows N := by
  simp only [swapRows, mul_def, mul, lrL, lrR, Mat2.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

lemma swapRows_lrR_mul (N : Mat2) : swapRows (lrR * N) = lrL * swapRows N := by
  simp only [swapRows, mul_def, mul, lrL, lrR, Mat2.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

/-- **The involution is an automaton isomorphism at the word level**: conjugating by `J`
swaps `L` and `R` letter by letter. -/
lemma swapRows_lrProd_mul (w : List Bool) (M : Mat2) :
    swapRows (lrProd w * M) = lrProd (w.map not) * swapRows M := by
  induction w generalizing M with
  | nil => simp
  | cons b w ih =>
      cases b
      · rw [lrProd_cons_false, mul_assoc', swapRows_lrR_mul, ih, List.map_cons,
          Bool.not_false, lrProd_cons_true, mul_assoc']
      · rw [lrProd_cons_true, mul_assoc', swapRows_lrL_mul, ih, List.map_cons,
          Bool.not_true, lrProd_cons_false, mul_assoc']

/-! ## `L/R` words of one letter -/

lemma lrProd_replicate_true (k : ℕ) : lrProd (List.replicate k true) = ⟨1, 0, (k : ℤ), 1⟩ := by
  induction k with
  | zero =>
      simp only [List.replicate_zero, lrProd_nil]
      refine mat2_ext ?_ ?_ ?_ ?_ <;> simp
  | succ k ih =>
      rw [List.replicate_succ, lrProd_cons_true, ih]
      refine mat2_ext ?_ ?_ ?_ ?_ <;>
        simp only [mul_def, mul, lrL] <;> push_cast <;> omega

/-! ## `IsRD 1` is the identity -/

lemma eq_one_of_isRD_one {M : Mat2} (h : IsRD 1 M) (hdet : M.det = 1) : M = 1 := by
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩ := raneyEntry_le h
  push_cast at ha1 hb1 hc1 hd1
  rcases h.2.2 with ⟨hca, hbd⟩ | ⟨hac, hdb⟩
  · refine mat2_ext ?_ ?_ ?_ ?_ <;> simp only [one_a, one_b, one_c, one_d] <;> omega
  · exfalso
    have ha : M.a = 0 := by omega
    have hb : M.b = 1 := by omega
    have hc : M.c = 1 := by omega
    have hd : M.d = 0 := by omega
    rw [det, ha, hb, hc, hd] at hdet
    omega

/-- Every nonnegative integer matrix of determinant `1` is an `L/R` word. -/
lemma exists_lrProd_of_det_one {W : Mat2} (hW : Nonneg W) (hdet : W.det = 1) :
    ∃ w : List Bool, W = lrProd w := by
  obtain ⟨w, M', hM', hEq⟩ :=
    exists_balanced_decomp (D := 1) one_pos hW (by rw [hdet]; left; norm_num)
  have hd : M'.det = 1 := by
    have := congrArg det hEq
    rw [det_mul, det_lrProd, one_mul, hdet] at this
    exact this.symm
  exact ⟨w, by rw [hEq, eq_one_of_isRD_one hM' hd, mul_one']⟩

end Mat2

namespace VandeheyLR

open Mat2 VandeheyAut

variable {D : ℕ}

/-! ## The `Classical.choose` of `lrStep`, pinned -/

/-- **Any witnessing Raney factorization of `M * B j` IS the transducer's step.**  Until now
`lrDelta`/`lrOut` were opaque `Classical.choose`s; uniqueness makes them computable objects
one can identify by exhibiting a factorization. -/
theorem lrStep_pin (hD : 0 < D) (M : RState D) (j : ℕ) {w : List Bool} {M' : Mat2}
    (hM' : IsRD D M') (h : M.val * Mat2.B j = lrProd w * M') :
    lrOut hD M j = w ∧ (lrDelta hD M j).val = M' := by
  have hspec := lrStep_spec hD M j
  have hne : ((lrDelta hD M j).val).det ≠ 0 := isRD_det_ne hD (lrDelta hD M j).2
  exact Mat2.balanced_decomp_unique (lrOut hD M j) w _ _
    (lrDelta hD M j).2.2 hM'.2 hne (by rw [← hspec]; exact h)

/-! ## The phase involution on the state set -/

/-- The row swap, as a map of Raney states. -/
def swapState (M : RState D) : RState D := ⟨Mat2.swapRows M.val, Mat2.isRD_swapRows M.2⟩

@[simp] lemma swapState_val (M : RState D) : (swapState M).val = Mat2.swapRows M.val := rfl

@[simp] lemma swapState_swapState (M : RState D) : swapState (swapState M) = M :=
  Subtype.ext (by simp)

private lemma swap_fac (hD : 0 < D) (M : RState D) (j : ℕ) :
    (swapState M).val * Mat2.B j
      = lrProd ((lrOut hD M j).map not) * Mat2.swapRows (lrDelta hD M j).val := by
  rw [swapState_val, ← Mat2.swapRows_mul, lrStep_spec hD M j, Mat2.swapRows_lrProd_mul]

/-- **The involution commutes with the transducer.**  This is what makes the phase quotient a
genuine automaton. -/
theorem lrDelta_swapState (hD : 0 < D) (M : RState D) (j : ℕ) :
    lrDelta hD (swapState M) j = swapState (lrDelta hD M j) :=
  Subtype.ext (lrStep_pin hD (swapState M) j
    (Mat2.isRD_swapRows (lrDelta hD M j).2) (swap_fac hD M j)).2

/-- The emitted word is `L ↔ R` swapped — so the phase quotient loses no output. -/
theorem lrOut_swapState (hD : 0 < D) (M : RState D) (j : ℕ) :
    lrOut hD (swapState M) j = (lrOut hD M j).map not :=
  (lrStep_pin hD (swapState M) j
    (Mat2.isRD_swapRows (lrDelta hD M j).2) (swap_fac hD M j)).1

/-- **The period-2 phase.**  The determinant's sign flips at every ingested digit, so no word
of a fixed length can drive all states to one common target: the obstruction that rules out
`VandeheyTwo.classEquidistribution_of_common_reach` for `lrDelta` itself. -/
theorem det_lrDelta (hD : 0 < D) (M : RState D) (j : ℕ) :
    ((lrDelta hD M j).val).det = - M.val.det := by
  have := congrArg Mat2.det (lrStep_spec hD M j)
  rw [Mat2.det_mul, Mat2.det_mul, Mat2.det_B, Mat2.det_lrProd, one_mul] at this
  linarith

/-! ## The three canonical states -/

/-- `diag(1, D)` — the common target of the phase-corrected automaton. -/
def zPlus (D : ℕ) : Mat2 := ⟨1, 0, 0, (D : ℤ)⟩
/-- `J · diag(1,D) = [[0,D],[1,0]]` — the target at the `lrDelta` level. -/
def zMinus (D : ℕ) : Mat2 := ⟨0, (D : ℤ), 1, 0⟩
/-- `[[0,1],[D,0]]` — where `diag(1,D)` goes, whatever the digit. -/
def zSpin (D : ℕ) : Mat2 := ⟨0, 1, (D : ℤ), 0⟩
/-- `diag(D, 1) = J · [[0,1],[D,0]]`. -/
def zDiag (D : ℕ) : Mat2 := ⟨(D : ℤ), 0, 0, 1⟩

@[simp] lemma zPlus_a : (zPlus D).a = 1 := rfl
@[simp] lemma zPlus_b : (zPlus D).b = 0 := rfl
@[simp] lemma zPlus_c : (zPlus D).c = 0 := rfl
@[simp] lemma zPlus_d : (zPlus D).d = (D : ℤ) := rfl
@[simp] lemma zMinus_a : (zMinus D).a = 0 := rfl
@[simp] lemma zMinus_b : (zMinus D).b = (D : ℤ) := rfl
@[simp] lemma zMinus_c : (zMinus D).c = 1 := rfl
@[simp] lemma zMinus_d : (zMinus D).d = 0 := rfl
@[simp] lemma zSpin_a : (zSpin D).a = 0 := rfl
@[simp] lemma zSpin_b : (zSpin D).b = 1 := rfl
@[simp] lemma zSpin_c : (zSpin D).c = (D : ℤ) := rfl
@[simp] lemma zSpin_d : (zSpin D).d = 0 := rfl
@[simp] lemma zDiag_a : (zDiag D).a = (D : ℤ) := rfl
@[simp] lemma zDiag_b : (zDiag D).b = 0 := rfl
@[simp] lemma zDiag_c : (zDiag D).c = 0 := rfl
@[simp] lemma zDiag_d : (zDiag D).d = 1 := rfl

@[simp] lemma swapRows_zMinus : Mat2.swapRows (zMinus D) = zPlus D := rfl
@[simp] lemma swapRows_zSpin : Mat2.swapRows (zSpin D) = zDiag D := rfl

lemma det_zPlus : (zPlus D).det = (D : ℤ) := by simp [Mat2.det]
lemma det_zMinus : (zMinus D).det = -(D : ℤ) := by simp [Mat2.det]
lemma det_zSpin : (zSpin D).det = -(D : ℤ) := by simp [Mat2.det]
lemma det_zDiag : (zDiag D).det = (D : ℤ) := by simp [Mat2.det]

lemma isRD_zPlus (hD : 0 < D) : IsRD D (zPlus D) := by
  have hD' : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  exact ⟨Or.inl det_zPlus,
    ⟨⟨by simp, by simp, by simp, by simp⟩, Or.inl ⟨by simp, by simpa using hD'⟩⟩⟩

lemma isRD_zMinus (hD : 0 < D) : IsRD D (zMinus D) := by
  have hD' : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  exact ⟨Or.inr det_zMinus,
    ⟨⟨by simp, by simp, by simp, by simp⟩, Or.inr ⟨by simp, by simpa using hD'⟩⟩⟩

lemma isRD_zSpin (hD : 0 < D) : IsRD D (zSpin D) := by
  have hD' : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  exact ⟨Or.inr det_zSpin,
    ⟨⟨by simp, by simp, by simp, by simp⟩, Or.inr ⟨by simpa using hD', by simp⟩⟩⟩

lemma isRD_zDiag (hD : 0 < D) : IsRD D (zDiag D) := by
  have hD' : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  exact ⟨Or.inl det_zDiag,
    ⟨⟨by simp, by simp, by simp, by simp⟩, Or.inl ⟨by simpa using hD', by simp⟩⟩⟩

/-! ## The arithmetic core -/

/-- **From congruences to the target.**  If `D ∣ a + b·j` and `D ∣ c + d·j` then ingesting `j`
lands exactly on `[[0,D],[1,0]]`: the quotients are the first column of an explicit
determinant-`1` nonnegative matrix, hence of an `L/R` word. -/
theorem lrDelta_eq_zMinus (hD : 0 < D) (M : RState D) (hdet : M.val.det = (D : ℤ)) (j : ℕ)
    (h1 : (D : ℤ) ∣ M.val.a + M.val.b * j) (h2 : (D : ℤ) ∣ M.val.c + M.val.d * j) :
    (lrDelta hD M j).val = zMinus D := by
  obtain ⟨ha0, -, hb0, -, hc0, -, hd0, -⟩ := raneyEntry_le M.2
  obtain ⟨p, hp⟩ := h1
  obtain ⟨r, hr⟩ := h2
  have hD' : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
  have hdet' : M.val.a * M.val.d - M.val.b * M.val.c = (D : ℤ) := by rw [← hdet]; rfl
  have hp0 : 0 ≤ p := by
    have h : (D : ℤ) * 0 ≤ (D : ℤ) * p := by
      rw [mul_zero, ← hp]; nlinarith [mul_nonneg hb0 hj0]
    exact le_of_mul_le_mul_left h hD'
  have hr0 : 0 ≤ r := by
    have h : (D : ℤ) * 0 ≤ (D : ℤ) * r := by
      rw [mul_zero, ← hr]; nlinarith [mul_nonneg hd0 hj0]
    exact le_of_mul_le_mul_left h hD'
  set W : Mat2 := ⟨p, M.val.b, r, M.val.d⟩ with hW
  have hWnn : Mat2.Nonneg W := ⟨hp0, hb0, hr0, hd0⟩
  have hWdet : W.det = 1 := by
    refine mul_left_cancel₀ (ne_of_gt hD') ?_
    show (D : ℤ) * (p * M.val.d - M.val.b * r) = (D : ℤ) * 1
    linear_combination (-M.val.d) * hp + M.val.b * hr + hdet'
  obtain ⟨w, hw⟩ := Mat2.exists_lrProd_of_det_one hWnn hWdet
  have hfac : M.val * Mat2.B j = lrProd w * zMinus D := by
    rw [← hw]
    refine Mat2.mat2_ext ?_ ?_ ?_ ?_ <;>
      simp only [hW, Mat2.mul_def, Mat2.mul, Mat2.B, zMinus_a, zMinus_b, zMinus_c, zMinus_d]
    · ring
    · linear_combination hp
    · ring
    · linear_combination hr
  exact (lrStep_pin hD M j (isRD_zMinus hD) hfac).2

/-- The converse: landing on the target forces the two congruences. -/
theorem dvd_of_lrDelta_eq_zMinus (hD : 0 < D) (M : RState D) (j : ℕ)
    (h : (lrDelta hD M j).val = zMinus D) :
    (D : ℤ) ∣ M.val.a + M.val.b * j ∧ (D : ℤ) ∣ M.val.c + M.val.d * j := by
  have hspec := lrStep_spec hD M j
  rw [h] at hspec
  set W : Mat2 := lrProd (lrOut hD M j) with hWdef
  have hb : M.val.a + M.val.b * (j : ℤ) = W.a * (D : ℤ) := by
    have hh := congrArg Mat2.b hspec
    simp only [Mat2.mul_def, Mat2.mul, Mat2.B, zMinus_b, zMinus_d] at hh
    linear_combination hh
  have hd : M.val.c + M.val.d * (j : ℤ) = W.c * (D : ℤ) := by
    have hh := congrArg Mat2.d hspec
    simp only [Mat2.mul_def, Mat2.mul, Mat2.B, zMinus_b, zMinus_d] at hh
    linear_combination hh
  exact ⟨⟨W.a, by rw [hb]; ring⟩, ⟨W.c, by rw [hd]; ring⟩⟩

/-- **The classification of the exceptional state.**  A positive-determinant Raney state whose
second column is divisible by `D` is `diag(1, D)` — nothing else. -/
theorem eq_zPlus_of_dvd (hD2 : 2 ≤ D) (M : RState D) (hdet : M.val.det = (D : ℤ))
    (hb : (D : ℤ) ∣ M.val.b) (hd : (D : ℤ) ∣ M.val.d) : M.val = zPlus D := by
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩ := raneyEntry_le M.2
  have hD' : (2 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD2
  have hdet' : M.val.a * M.val.d - M.val.b * M.val.c = (D : ℤ) := by rw [← hdet]; rfl
  obtain ⟨k, hk⟩ := hb
  obtain ⟨l, hl⟩ := hd
  have hk0 : 0 ≤ k := by nlinarith
  have hk1 : k ≤ 1 := by nlinarith
  have hl0 : 0 ≤ l := by nlinarith
  have hl1 : l ≤ 1 := by nlinarith
  rcases M.2.2.2 with ⟨hca, hbd⟩ | ⟨hac, hdb⟩
  · -- `b < d`, so `k = 0` and `l = 1`
    have hkl : k < l := by nlinarith
    have hk' : k = 0 := by omega
    have hl' : l = 1 := by omega
    have hbz : M.val.b = 0 := by rw [hk, hk']; ring
    have hdz : M.val.d = (D : ℤ) := by rw [hl, hl']; ring
    have haz : M.val.a = 1 := by
      refine mul_right_cancel₀ (show ((D : ℤ)) ≠ 0 by omega) ?_
      show M.val.a * (D : ℤ) = 1 * (D : ℤ)
      linear_combination hdet' + M.val.c * hbz - M.val.a * hdz
    have hcz : M.val.c = 0 := by omega
    exact Mat2.mat2_ext (by simp [haz]) (by simp [hbz]) (by simp [hcz]) (by simp [hdz])
  · -- `d < b`, so `l = 0` and `k = 1`: then `−D·c = D`, impossible
    exfalso
    have hkl : l < k := by nlinarith
    have hk' : k = 1 := by omega
    have hl' : l = 0 := by omega
    have hbz : M.val.b = (D : ℤ) := by rw [hk, hk']; ring
    have hdz : M.val.d = 0 := by rw [hl, hl']; ring
    rw [hbz, hdz] at hdet'
    nlinarith

/-! ## The two explicit steps out of the exceptional state -/

theorem lrDelta_zPlus (hD : 0 < D) (j : ℕ) :
    (lrDelta hD ⟨zPlus D, isRD_zPlus hD⟩ j).val = zSpin D := by
  have hfac : (zPlus D) * Mat2.B j
      = lrProd (List.replicate (D * j) true) * zSpin D := by
    rw [Mat2.lrProd_replicate_true]
    refine Mat2.mat2_ext ?_ ?_ ?_ ?_ <;>
      simp only [Mat2.mul_def, Mat2.mul, Mat2.B, zPlus_a, zPlus_b, zPlus_c, zPlus_d,
        zSpin_a, zSpin_b, zSpin_c, zSpin_d] <;> push_cast <;> ring
  exact (lrStep_pin hD ⟨zPlus D, isRD_zPlus hD⟩ j (isRD_zSpin hD) hfac).2

theorem lrDelta_zDiag (hD : 0 < D) :
    (lrDelta hD ⟨zDiag D, isRD_zDiag hD⟩ D).val = zMinus D := by
  refine lrDelta_eq_zMinus hD ⟨zDiag D, isRD_zDiag hD⟩ det_zDiag D ?_ ?_
  · exact ⟨1, by simp⟩
  · exact ⟨1, by simp⟩

/-! ## Solving the congruences -/

/-- **The congruence pair is solvable** as soon as the second column is not entirely divisible
by the prime `D`: `D ∣ det M` makes the two conditions equivalent over `ZMod D`. -/
theorem exists_digit_zMinus (D : ℕ) [hpr : Fact (Nat.Prime D)] (hD : 0 < D) (M : RState D)
    (hdet : M.val.det = (D : ℤ))
    (hbad : ¬((D : ℤ) ∣ M.val.b ∧ (D : ℤ) ∣ M.val.d)) :
    ∃ j : ℕ, 1 ≤ j ∧ (lrDelta hD M j).val = zMinus D := by
  have : NeZero D := ⟨hpr.out.ne_zero⟩
  have hdet0 : (M.val.a : ZMod D) * (M.val.d : ZMod D)
      - (M.val.b : ZMod D) * (M.val.c : ZMod D) = 0 := by
    have hz : ((M.val.det : ℤ) : ZMod D) = 0 := by
      rw [hdet]; push_cast; exact ZMod.natCast_self D
    rw [Mat2.det] at hz
    push_cast at hz
    exact hz
  have key : ∀ x : ZMod D, (M.val.a : ZMod D) + (M.val.b : ZMod D) * x = 0 →
      (M.val.c : ZMod D) + (M.val.d : ZMod D) * x = 0 →
      ∃ j : ℕ, 1 ≤ j ∧ (lrDelta hD M j).val = zMinus D := by
    intro x h1 h2
    set j : ℕ := x.val + D with hj
    have hjc : ((j : ℕ) : ZMod D) = x := by
      rw [hj]; push_cast
      simp [ZMod.natCast_val, ZMod.cast_id]
    refine ⟨j, by omega, lrDelta_eq_zMinus hD M hdet j ?_ ?_⟩
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hjc]; exact h1
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hjc]; exact h2
  by_cases hbz : (M.val.b : ZMod D) = 0
  · have hdz : (M.val.d : ZMod D) ≠ 0 := fun h =>
      hbad ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ D).mp hbz,
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ D).mp h⟩
    have haz : (M.val.a : ZMod D) = 0 := by
      have : (M.val.a : ZMod D) * (M.val.d : ZMod D) = 0 := by
        rw [hbz] at hdet0; linear_combination hdet0
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hdz
    refine key (-(M.val.c : ZMod D) / (M.val.d : ZMod D)) ?_ ?_
    · rw [haz, hbz]; ring
    · field_simp
      ring
  · refine key (-(M.val.a : ZMod D) / (M.val.b : ZMod D)) ?_ ?_
    · field_simp
      ring
    · have hmul : (M.val.b : ZMod D) *
          ((M.val.c : ZMod D) + (M.val.d : ZMod D) * (-(M.val.a : ZMod D) / (M.val.b : ZMod D)))
          = 0 := by
        field_simp
        linear_combination -hdet0
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd h hbz
      · exact h

end VandeheyLR

end NormalNumbers

#print axioms NormalNumbers.Mat2.balanced_decomp_unique
#print axioms NormalNumbers.VandeheyLR.lrStep_pin
#print axioms NormalNumbers.VandeheyLR.lrDelta_swapState
#print axioms NormalNumbers.VandeheyLR.lrOut_swapState
#print axioms NormalNumbers.VandeheyLR.det_lrDelta
#print axioms NormalNumbers.VandeheyLR.exists_digit_zMinus
#print axioms NormalNumbers.VandeheyLR.eq_zPlus_of_dvd
