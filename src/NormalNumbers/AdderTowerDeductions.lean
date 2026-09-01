/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Bridge
import NormalNumbers.Disjunctive
import NormalNumbers.AdderTowerC1

/-!
# Tower deductions: the floor under the hitting-set claims, and C5 sharpened 🗼

`docs/tower-novelty-audit-2026-08-29.md` §"Short deductions that change the ranking"
records two elementary observations about the C-tower that are *theorems*, not
certificates, and were not yet in Lean.  This module lands them.

## 1.  A single multiplier never forces a digit (the floor)

For every base `b ≥ 3`, every digit `d` and every nonzero natural multiplier `m` there
is an irrational `X` whose multiple `m·X` never shows the digit `d` in base `b`
(`exists_irrational_mul_omits_digit`).  Witness: pick two digits `e₁ ≠ e₂` different
from `d` with `e₁ ≠ b − 1`, encode an arbitrary set `A ⊆ ℕ` as the digit sequence
`e₂` at position `2k` iff `k ∈ A`, `e₁` elsewhere (`setDigits`), and take
`X := realOfDigits b (setDigits …) / m`.  The encoding is injective (`digitOf_realOfDigits`
reads the digits back), `Set ℕ` is uncountable (Cantor), and `ℚ` is countable, so some
encoded real is irrational.  Consequences:

* **C2 has optimal cardinality** (`no_single_multiplier_all_digits`): no singleton
  `{m}` makes every ternary digit recur in `m·X` for every irrational `X`, so the
  `{2, 11}` product block of `AdderTowerC2` cannot be shrunk to one multiplier.  (It
  says nothing about *which* pair; coefficient-optimality of `{2, 11}` is open.)
* **Berend–Boshernitzan `M(3,1) = 2`, the LOWER half**
  (`Literature.berendBoshernitzan_M31_lower` + `_holds`): multiplier `1` alone does
  not suffice — the half the ledger entry `berendBoshernitzan_M31` recorded as "not
  transcribed".  With `berendBoshernitzan_M31_holds` (= C1) both halves of
  `M(3,1) = 2` are now kernel-checked.  The same argument gives `M(g,1) ≥ 2` for every
  `g ≥ 3` (`single_multiplier_insufficient`); B–B's stronger `M(g,1) ≥ g − 1` is NOT
  proved here.

## 2.  C5 is a C1 corollary, and the `X + 4Y` channel is unnecessary

`c5_sharp`: for `X, Y` not both rational, ternary digit `1` recurs in one of
`Y, 2Y, 2X, 4X` — the C5 disjunction (`AdderTowerC45.c5_disjunction_universal`)
*without* its middle channel.  Proof: if `Y` is irrational apply C1 to `Y`; otherwise
`X`, hence `2X`, is irrational and C1 applies to `2X`.  So the dossier's 80-state C5
certificate certifies a statement two applications of the 2-state C1 already imply,
and the sharper four-channel form is the one to cite.
-/

namespace NormalNumbers.Adder

open NormalNumbers Set
open scoped Classical

/-! ## The set-encoding digit sequence -/

/-- The digit sequence encoding a set `A ⊆ ℕ`: digit `e₂` at the even position `2k` iff
`k ∈ A`, digit `e₁` everywhere else (in particular at every odd position). -/
noncomputable def setDigits (e₁ e₂ : ℕ) (A : Set ℕ) : ℕ → ℕ :=
  fun i => if Even i ∧ i / 2 ∈ A then e₂ else e₁

theorem setDigits_even (e₁ e₂ : ℕ) (A : Set ℕ) (k : ℕ) :
    setDigits e₁ e₂ A (2 * k) = if k ∈ A then e₂ else e₁ := by
  unfold setDigits
  simp [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]

theorem setDigits_odd (e₁ e₂ : ℕ) (A : Set ℕ) (k : ℕ) :
    setDigits e₁ e₂ A (2 * k + 1) = e₁ := by
  unfold setDigits
  have : ¬ Even (2 * k + 1) := by
    rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one k
  simp [this]

theorem setDigits_mem (e₁ e₂ : ℕ) (A : Set ℕ) (i : ℕ) :
    setDigits e₁ e₂ A i = e₁ ∨ setDigits e₁ e₂ A i = e₂ := by
  unfold setDigits
  split_ifs <;> simp

theorem setDigits_lt (b e₁ e₂ : ℕ) (h₁ : e₁ < b) (h₂ : e₂ < b) (A : Set ℕ) (i : ℕ) :
    setDigits e₁ e₂ A i < b := by
  rcases setDigits_mem e₁ e₂ A i with h | h <;> rw [h] <;> assumption

/-- The odd positions carry `e₁ ≠ b − 1`, so the sequence is never eventually `b − 1`. -/
theorem setDigits_proper (b e₁ e₂ : ℕ) (h₁' : e₁ ≠ b - 1) (A : Set ℕ) :
    ProperDigits b (setDigits e₁ e₂ A) :=
  fun N => ⟨2 * N + 1, by omega, by rw [setDigits_odd]; exact h₁'⟩

/-- The real number in `[0,1)` with base-`b` digit sequence `setDigits e₁ e₂ A`. -/
noncomputable def setReal (b e₁ e₂ : ℕ) (A : Set ℕ) : ℝ :=
  realOfDigits b (setDigits e₁ e₂ A)

theorem digitOf_setReal (b e₁ e₂ : ℕ) (hb : 2 ≤ b) (h₁ : e₁ < b) (h₂ : e₂ < b)
    (h₁' : e₁ ≠ b - 1) (A : Set ℕ) :
    digitOf b (setReal b e₁ e₂ A) = setDigits e₁ e₂ A :=
  digitOf_realOfDigits b hb _ (setDigits_lt b e₁ e₂ h₁ h₂ A) (setDigits_proper b e₁ e₂ h₁' A)

theorem setReal_mem_Ico (b e₁ e₂ : ℕ) (hb : 2 ≤ b) (h₁ : e₁ < b) (h₂ : e₂ < b)
    (h₁' : e₁ ≠ b - 1) (A : Set ℕ) : setReal b e₁ e₂ A ∈ Set.Ico (0 : ℝ) 1 :=
  realOfDigits_mem_Ico b hb _ (setDigits_lt b e₁ e₂ h₁ h₂ A) (setDigits_proper b e₁ e₂ h₁' A)

/-- Distinct sets give distinct reals: the digit map reads the set back off `setReal`. -/
theorem setReal_injective (b e₁ e₂ : ℕ) (hb : 2 ≤ b) (h₁ : e₁ < b) (h₂ : e₂ < b)
    (h₁' : e₁ ≠ b - 1) (hne : e₁ ≠ e₂) : Function.Injective (setReal b e₁ e₂) := by
  intro A B hAB
  have hd : setDigits e₁ e₂ A = setDigits e₁ e₂ B := by
    rw [← digitOf_setReal b e₁ e₂ hb h₁ h₂ h₁' A, ← digitOf_setReal b e₁ e₂ hb h₁ h₂ h₁' B, hAB]
  ext k
  have := congrFun hd (2 * k)
  rw [setDigits_even, setDigits_even] at this
  constructor
  · intro hk
    by_contra hk'
    rw [if_pos hk, if_neg hk'] at this
    exact hne this.symm
  · intro hk
    by_contra hk'
    rw [if_neg hk', if_pos hk] at this
    exact hne this

/-- `Set ℕ` is uncountable (Cantor's theorem, `2 ^ ℵ₀ > ℵ₀`). -/
theorem not_countable_set_nat : ¬ Countable (Set ℕ) := by
  intro h
  have h1 : Cardinal.mk (Set ℕ) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.2 h
  rw [Cardinal.mk_set, Cardinal.mk_nat] at h1
  exact absurd h1 (not_le.2 (Cardinal.cantor _))

/-- Some `setReal b e₁ e₂ A` is irrational: the image of the uncountable `Set ℕ` under an
injective map cannot lie inside the countable set of rationals. -/
theorem exists_setReal_irrational (b e₁ e₂ : ℕ) (hb : 2 ≤ b) (h₁ : e₁ < b) (h₂ : e₂ < b)
    (h₁' : e₁ ≠ b - 1) (hne : e₁ ≠ e₂) : ∃ A : Set ℕ, Irrational (setReal b e₁ e₂ A) := by
  by_contra hcon
  push Not at hcon
  apply not_countable_set_nat
  rw [← Set.countable_univ_iff]
  have hpre : (setReal b e₁ e₂) ⁻¹' (Set.range ((↑) : ℚ → ℝ)) = Set.univ := by
    ext A; simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    have := hcon A
    unfold Irrational at this
    push Not at this
    exact this
  rw [← hpre]
  exact (Set.countable_range _).preimage_of_injOn
    (setReal_injective b e₁ e₂ hb h₁ h₂ h₁' hne).injOn

/-! ## The floor: a single multiplier never forces a digit -/

/-- **A single multiplier never forces a digit.**  For every base `b ≥ 3`, every digit
`d` and every nonzero natural multiplier `m`, there is an irrational `X` such that the
base-`b` expansion of `m·X` never contains `d` — not merely "not infinitely often".
(`d < b` is not even needed: a value `≥ b` is never a digit.) -/
theorem exists_irrational_mul_omits_digit (b : ℕ) (hb : 3 ≤ b) (d : ℕ)
    (m : ℕ) (hm : m ≠ 0) :
    ∃ X : ℝ, Irrational X ∧ ∀ n, ¬ OccursAt b ((m : ℝ) * X) [d] n := by
  -- two digits other than `d`, with the constant filler `e₁ ≠ b - 1`
  obtain ⟨e₁, e₂, h₁, h₂, h₁', hne, hd₁, hd₂⟩ : ∃ e₁ e₂ : ℕ, e₁ < b ∧ e₂ < b ∧ e₁ ≠ b - 1 ∧
      e₁ ≠ e₂ ∧ e₁ ≠ d ∧ e₂ ≠ d := by
    rcases Nat.lt_or_ge d 1 with hd0 | hd0
    · exact ⟨1, 2, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rcases Nat.lt_or_ge d 2 with hd1 | hd1
      · exact ⟨0, 2, by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨0, 1, by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨A, hA⟩ := exists_setReal_irrational b e₁ e₂ (by omega) h₁ h₂ h₁' hne
  refine ⟨setReal b e₁ e₂ A / m, hA.div_natCast hm, fun n hocc => ?_⟩
  have hmX : (m : ℝ) * (setReal b e₁ e₂ A / m) = setReal b e₁ e₂ A := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp
  have hocc' : digitOf b (Int.fract (setReal b e₁ e₂ A)) n = d := by
    have := hocc 0 (by simp)
    simpa [hmX] using this
  have hmem := setReal_mem_Ico b e₁ e₂ (by omega) h₁ h₂ h₁' A
  have hfr : Int.fract (setReal b e₁ e₂ A) = setReal b e₁ e₂ A :=
    Int.fract_eq_self.2 ⟨hmem.1, hmem.2⟩
  rw [hfr, digitOf_setReal b e₁ e₂ (by omega) h₁ h₂ h₁' A] at hocc'
  rcases setDigits_mem e₁ e₂ A n with h | h <;> rw [h] at hocc'
  · exact hd₁ hocc'
  · exact hd₂ hocc'

/-- **No singleton multiplier set hits a fixed digit** (per-digit form, i.o. shape as in
the tower statements): for `b ≥ 3`, any digit `d` and any `m ≠ 0`, it is NOT the case
that `d` recurs in `m·X` for every irrational `X`. -/
theorem no_single_multiplier_digit (b : ℕ) (hb : 3 ≤ b) (d : ℕ) (m : ℕ) (hm : m ≠ 0) :
    ¬ ∀ X : ℝ, Irrational X → ∀ N, ∃ n, N ≤ n ∧ OccursAt b ((m : ℝ) * X) [d] n := by
  intro H
  obtain ⟨X, hX, hnot⟩ := exists_irrational_mul_omits_digit b hb d m hm
  obtain ⟨n, _, hocc⟩ := H X hX 0
  exact hnot n hocc

/-- **C2 has optimal cardinality**: no single multiplier `m` makes EVERY ternary digit
recur in `m·X` for every irrational `X` (the singleton analogue of
`c2_product_block`'s all-digits clauses, any base `b ≥ 3`).  So a universal all-digits
hitting set needs at least two multipliers, and `{2, 11}` cannot be shrunk. -/
theorem no_single_multiplier_all_digits (b : ℕ) (hb : 3 ≤ b) (m : ℕ) (hm : m ≠ 0) :
    ¬ ∀ X : ℝ, Irrational X → ∀ d, d < b → ∀ N, ∃ n, N ≤ n ∧ OccursAt b ((m : ℝ) * X) [d] n :=
  fun H => no_single_multiplier_digit b hb 0 m hm fun X hX => H X hX 0 (by omega)

/-- **`M(g,1) ≥ 2` for every base `g ≥ 3`**: the multiplier `1` alone does not make every
digit recur in every irrational. -/
theorem single_multiplier_insufficient (b : ℕ) (hb : 3 ≤ b) :
    ¬ ∀ X : ℝ, Irrational X → ∀ d, d < b → ∀ N, ∃ n, N ≤ n ∧ OccursAt b X [d] n := by
  intro H
  apply no_single_multiplier_all_digits b hb 1 one_ne_zero
  intro X hX d hd N
  simpa using H X hX d hd N

/-! ## C5 sharpened: a C1 corollary without the `X + 4Y` channel -/

/-- **C5, sharpened** (`docs/tower-novelty-audit-2026-08-29.md`: "C5 is a C1 corollary";
the `X + 4Y` channel of `c5_disjunction_universal` is never needed): for reals `X, Y` not
both rational, ternary digit `1` occurs infinitely often in one of `Y, 2Y, 2X, 4X`.
Proof: `Y` irrational ⇒ C1 on `Y`; otherwise `X`, hence `2X`, is irrational ⇒ C1 on `2X`. -/
theorem c5_sharp (X Y : ℝ)
    (hXY : ¬ (∃ p : ℚ, (p:ℝ) = X) ∨ ¬ (∃ q : ℚ, (q:ℝ) = Y)) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 Y [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (2 * Y) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (2 * X) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (4 * X) [1] n) := by
  by_cases hY : Irrational Y
  · rcases c1_ternary_digit Y hY 1 (by norm_num) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hX : Irrational X := by
      rcases hXY with hX | hY'
      · exact fun ⟨p, hp⟩ => hX ⟨p, hp⟩
      · exact absurd (fun ⟨q, hq⟩ => hY' ⟨q, hq⟩) (fun h => hY h)
    have h2X : Irrational (2 * X) := by
      simpa using hX.natCast_mul (m := 2) (by norm_num)
    rcases c1_ternary_digit (2 * X) h2X 1 (by norm_num) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rwa [show (2 : ℝ) * (2 * X) = 4 * X by ring] at h

/-- The sharpened C5 implies the certified five-channel form. -/
theorem c5_disjunction_universal_of_sharp (X Y : ℝ)
    (hXY : ¬ (∃ p : ℚ, (p:ℝ) = X) ∨ ¬ (∃ q : ℚ, (q:ℝ) = Y)) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 Y [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (2 * Y) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (X + 4 * Y) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (2 * X) [1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 (4 * X) [1] n) := by
  rcases c5_sharp X Y hXY with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end NormalNumbers.Adder

namespace NormalNumbers.Literature

open NormalNumbers

/-- **Berend–Boshernitzan 1994, `M(3,1) = 2` (lower half)**: the single multiplier `1`
does NOT suffice — some irrational `x` has a ternary digit that fails to recur in `x`
itself.  Completes the ledger entry `berendBoshernitzan_M31` (upper half); this is the
"minimality — `{1}` does not suffice" clause that entry left untranscribed.

provenance: secondary (the M(3,1) = 2 statement, `docs/mahler-sets-2026-08-29.md`);
the proof here is elementary and independent of the paper. -/
def berendBoshernitzan_M31_lower : Prop :=
  ¬ ∀ (x : ℝ), Irrational x → ∀ d : ℕ, d < 3 →
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 3 x [d] n)

/-- **Wired edge**: the lower half of `M(3,1) = 2`, from the Cantor-set floor
(`Adder.single_multiplier_insufficient`). -/
theorem berendBoshernitzan_M31_lower_holds : berendBoshernitzan_M31_lower :=
  Adder.single_multiplier_insufficient 3 le_rfl

end NormalNumbers.Literature
