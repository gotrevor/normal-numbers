/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG

/-!
# Tower claim C10: the base-5 nine-channel single-digit family (kernel tier)

Brief: `BRIEF-adder-tower.md` (C10 was listed out of scope for the C1–C8
brief and is the last named tower claim); dossier
`EVIDENCE-2026-08-29-tower-formalization.md` §C10 ("largest certificate —
do LAST if at all", 540 396 live states in the dossier's encoding).

**Statement (dossier form).**  For `X, Y` not both rational, at least one
base-5 digit claim holds i.o.: 3 in `Y` · 4 in `2Y` · 2 in `3Y` · 0 in
`4Y` · 2 in `X+Y` · 3 in `X+4Y` · 2 in `2X+2Y` · 2 in `3X+3Y` · 2 in
`4X+4Y`.

**Audit disposition / REDUCTION FINDING (2026-09-01).**  The nine-channel
two-track automaton does collapse (our encoding: 46080 ambient states,
18 live, four 2-cycles — `adder_baseg_emit.py c10`, collapse verdict
agreeing with the dossier's `base_g_digit_hunt.py 5`), but the large
certificate is *not needed*: exactly as with C5, the family splits.
* If `Y` is irrational, the four **`Y`-only channels** `(0,1)/3 · (0,2)/4 ·
  (0,3)/2 · (0,4)/0` already collapse as a single-track family on `Y`
  (24 ambient, 5 live; `adder_baseg_emit.py c10y`).
* Otherwise `Y = q` is rational and `X` is irrational, so `Z := X + q` is
  irrational, and the four **diagonal channels** `(1,1)/2 · (2,2)/2 ·
  (3,3)/2 · (4,4)/2` are `Z, 2Z, 3Z, 4Z` all avoiding digit 2 — a
  single-track family on `Z` that also collapses (24 ambient, 6 live;
  `adder_baseg_emit.py c10z`).
The mixed channel `(1,4)/3` (`X+4Y`) is **unused**.  So C10 is a corollary
of two 24-state single-track collapses and should NOT be presented as an
independent nine-channel theorem; the dossier's 540 396-state certificate
certifies a statement that two `M(5,1)`-type single-track claims already
imply.  Both sub-certificates are checked here by kernel `decide` against
our own `gfamPred` (the other instrument re-verifies C1/C1'/C3' at
emission time).
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-! ## The `Y`-only sub-family: `Y, 2Y, 3Y, 4Y` avoiding `3, 4, 2, 0` -/

/-- Channels `(1,0)/3 · (2,0)/4 · (3,0)/2 · (4,0)/0` (base 5, single
track): the `Y`-only channels of C10 read on one real. -/
def c10yChans : List ZChannel :=
  [⟨1, 0, [3]⟩, ⟨2, 0, [4]⟩, ⟨3, 0, [2]⟩, ⟨4, 0, [0]⟩]

def c10ylive : ℕ → Bool := fun s => [0, 6, 8, 15, 23].contains s
def c10yrho : ℕ → ℕ := fun s =>
  (([(0, 3), (6, 2), (15, 1)] : List (ℕ × ℕ)).lookup s).getD 0
def c10yomega : ℕ → ℕ := fun s =>
  (([(2, 1), (9, 1)] : List (ℕ × ℕ)).lookup s).getD 0
def c10yforced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (1, 0)), (8, (1, 23)), (23, (4, 8))] : List (ℕ × ℕ × ℕ)).lookup s

/-- The `Y`-only certificate, kernel tier (24 ambient states, alphabet 5). -/
theorem c10y_cert : checkCertA (fun σ s' => gfamPred 5 c10yChans (σ % 5) (σ / 5) s')
    5 24 c10ylive c10yrho c10yomega c10yforced = true := by decide

/-! ## The diagonal sub-family: `Z, 2Z, 3Z, 4Z` all avoiding digit `2` -/

/-- Channels `(1,0)/2 · (2,0)/2 · (3,0)/2 · (4,0)/2` (base 5, single
track): the diagonal channels of C10 read on `Z = X + Y`. -/
def c10zChans : List ZChannel :=
  [⟨1, 0, [2]⟩, ⟨2, 0, [2]⟩, ⟨3, 0, [2]⟩, ⟨4, 0, [2]⟩]

def c10zlive : ℕ → Bool := fun s => [0, 6, 8, 15, 17, 23].contains s
def c10zrho : ℕ → ℕ := fun s =>
  (([(0, 1), (23, 1)] : List (ℕ × ℕ)).lookup s).getD 0
def c10zomega : ℕ → ℕ := fun s =>
  (([(2, 1), (21, 1)] : List (ℕ × ℕ)).lookup s).getD 0
def c10zforced : ℕ → Option (ℕ × ℕ) := fun s =>
  ([(0, (0, 0)), (6, (1, 15)), (8, (1, 17)), (15, (3, 6)), (17, (3, 8)),
    (23, (4, 23))] : List (ℕ × ℕ × ℕ)).lookup s

/-- The diagonal certificate, kernel tier (24 ambient states, alphabet 5). -/
theorem c10z_cert : checkCertA (fun σ s' => gfamPred 5 c10zChans (σ % 5) (σ / 5) s')
    5 24 c10zlive c10zrho c10zomega c10zforced = true := by decide

/-! ## The two single-track collapses as theorems -/

/-- **C10, `Y`-branch** (`M(5,1)`-type, mixed digits): for every irrational
`Y`, base-5 digit 3 occurs i.o. in `Y`, or 4 in `2Y`, or 2 in `3Y`, or 0
in `4Y`. -/
theorem c10_y_branch (Y : ℝ) (hY : Irrational Y) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 Y [3] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (2 * Y) [4] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (3 * Y) [2] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (4 * Y) [0] n) := by
  obtain ⟨ch, hch, hio⟩ := signed_engine_g_single 5 (by norm_num) c10yChans rfl
    c10y_cert Y hY (by decide) (by decide) (by decide)
  fin_cases hch
  · refine Or.inl ?_
    have h : ∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (((1:ℤ):ℝ) * Y) [3] n := hio
    rwa [show ((1:ℤ):ℝ) * Y = Y from by push_cast; ring] at h
  · refine Or.inr (Or.inl ?_)
    have h : ∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (((2:ℤ):ℝ) * Y) [4] n := hio
    rwa [show ((2:ℤ):ℝ) * Y = 2 * Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inl ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (((3:ℤ):ℝ) * Y) [2] n := hio
    rwa [show ((3:ℤ):ℝ) * Y = 3 * Y from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (((4:ℤ):ℝ) * Y) [0] n := hio
    rwa [show ((4:ℤ):ℝ) * Y = 4 * Y from by push_cast; ring] at h

/-- **C10, diagonal branch** (`M(5,1)`-type, digit 2): for every irrational
`Z`, base-5 digit 2 occurs i.o. in `Z`, or in `2Z`, or in `3Z`, or in
`4Z`. -/
theorem c10_z_branch (Z : ℝ) (hZ : Irrational Z) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 Z [2] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (2 * Z) [2] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (3 * Z) [2] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (4 * Z) [2] n) := by
  obtain ⟨ch, hch, hio⟩ := signed_engine_g_single 5 (by norm_num) c10zChans rfl
    c10z_cert Z hZ (by decide) (by decide) (by decide)
  fin_cases hch
  · refine Or.inl ?_
    have h : ∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (((1:ℤ):ℝ) * Z) [2] n := hio
    rwa [show ((1:ℤ):ℝ) * Z = Z from by push_cast; ring] at h
  · refine Or.inr (Or.inl ?_)
    have h : ∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (((2:ℤ):ℝ) * Z) [2] n := hio
    rwa [show ((2:ℤ):ℝ) * Z = 2 * Z from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inl ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (((3:ℤ):ℝ) * Z) [2] n := hio
    rwa [show ((3:ℤ):ℝ) * Z = 3 * Z from by push_cast; ring] at h
  · refine Or.inr (Or.inr (Or.inr ?_))
    have h : ∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (((4:ℤ):ℝ) * Z) [2] n := hio
    rwa [show ((4:ℤ):ℝ) * Z = 4 * Z from by push_cast; ring] at h

/-! ## C10 in the dossier's nine-disjunct form -/

/-- **C10 (base-5 nine-channel family), universal form** — in the dossier's
exact shape: for reals `X, Y` not both rational, base-5 digit 3 occurs
i.o. in `Y`, or 4 in `2Y`, or 2 in `3Y`, or 0 in `4Y`, or 2 in `X+Y`, or
3 in `X+4Y`, or 2 in `2X+2Y`, or 2 in `3X+3Y`, or 2 in `4X+4Y`.

Proved by the REDUCTION in the module docstring (`c10_y_branch` when `Y`
is irrational, `c10_z_branch` on `Z = X + Y` otherwise); the `X+4Y`
disjunct is never used. -/
theorem c10_disjunction_universal (X Y : ℝ)
    (hXY : ¬ (∃ p : ℚ, (p:ℝ) = X) ∨ ¬ (∃ q : ℚ, (q:ℝ) = Y)) :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 Y [3] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (2 * Y) [4] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (3 * Y) [2] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (4 * Y) [0] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (X + Y) [2] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (X + 4 * Y) [3] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (2 * X + 2 * Y) [2] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (3 * X + 3 * Y) [2] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 5 (4 * X + 4 * Y) [2] n) := by
  by_cases hY : Irrational Y
  · rcases c10_y_branch Y hY with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hY
    have hX : Irrational X := by
      rcases hXY with hX | hY'
      · exact fun ⟨p, hp⟩ => hX ⟨p, hp⟩
      · exact absurd ⟨q, hq.symm⟩ hY'
    have hZ : Irrational (X + Y) := by
      rw [hq]; exact hX.add_ratCast q
    rcases c10_z_branch (X + Y) hZ with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
      rwa [show 2 * X + 2 * Y = 2 * (X + Y) from by ring]
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
      rwa [show 3 * X + 3 * Y = 3 * (X + Y) from by ring]
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))))
      rwa [show 4 * X + 4 * Y = 4 * (X + Y) from by ring]

end NormalNumbers.Adder
