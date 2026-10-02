/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Approx
import NormalNumbers.VandeheyS7Emit

/-!
# The machine does not forget: the emitted digit is not a window function of the input

The 2026-09-29 handoff's next action was to define `F w := emitDigit (wordState w)` and prove
that the image digit at the position matching a window equals `F` of that window, citing
`spread_runWord_le` for "`s₀`-independence".  **Both halves are wrong, and this module proves the
second one false in the kernel.**

## What `spread_runWord_le` says, and what it does not

`spread_runWord_le s w` bounds the *diameter* of `(runWord s w).mob '' [0,1]`, uniformly in the
initial state `s`.  That is a statement about the image being SMALL.  It is not a statement about
the image being in the same PLACE for different `s`, and it cannot be: `runWord s w =
s.comp (wordState w)` (`runWord_eq_comp`), so the image is `s (I_w)` — the initial state moves
the tiny interval wherever it likes.  Input digits are appended on the RIGHT of the accumulated
matrix, so the recent input fixes the fine position inside the current interval while the far
past fixes the absolute position, which is what the emitted digit reads.  Memory is not lost.

## The refutation

`emitDigit_not_window_function`: two explicit states send all of `[0,1]` into the cylinders of
the digits `2` and `4` respectively, hence — after reading **any** input word whatsoever — still
emit, and emit `2` and `4`.  So for every window `w`, however long, the pair
(`CanEmit`, `emitDigit`) is not a function of `w` (`no_window_function`).

Two things make this a real obstruction rather than a technicality.

* The witnesses are `⟨1,3;0,8⟩` and `⟨1,7;0,32⟩`: both have **distortion `1`**, the minimum
  possible (`witness_distortion`).  So restricting to Route A's bounded-distortion compact fiber
  does not rescue the window claim.
* The word `w` is arbitrary and arbitrarily long, so no amount of merging helps; the statement
  fails uniformly in the window length.

## This is the synchronizing-word hall again

The plan is `hall_vandehey_synchronizing_transducer` (Maze, 2026-09-28) in new clothes.  That
row records `VandeheyAut.not_synchronizing_of_injective_quotient`: **no input word merges two
state classes** of the CF determinant-`D` transducer, because every letter acts bijectively on
the row-lattice quotient.  "The emitted digit is a function of a bounded input window" is
precisely the assertion that a long enough word does merge the states, so it contradicts a
theorem this build already contains.  The module below re-proves it without the `ℤ/D` quotient,
so the verdict does not depend on the integer structure that `ℤ[φ]` destroys.

## What this does and does not settle

Refuted: the digit is a function of the window **alone**, over all initial states — which is the
plan's `F w := emitDigit (wordState w)`.  NOT refuted here: that for one *fixed* affine map the
digit might be a window function of the input, which is in fact TRUE for the identity map (there
the image is the input).  Settling that for `M = φ` needs two reachable post-emission states with
different straddled endpoints, and is the open probe; the integer analogue is already settled
negatively by the synchronizing row above.

## What survives, and what the decomposition must therefore be indexed by

`cfDigit_mob_eq_emitDigit` is untouched: the emitted digit is a function **of the state**.  So
the decomposition that feeds `VandeheyS7Approx.sampledUniformCount_of_approxScheme` cannot be
indexed by input words alone.  It must be indexed by (state class, input word) pairs — which is
exactly what Vandehey's `JointStateFreq` does in the proved integer case, where the state classes
are finite.  Over `ℤ[φ]` the classes are infinite, and Route A's job is to replace the finite sum
over classes by an integral against a stationary measure on the compact bounded-distortion fiber
(`VandeheyS7Distortion`), with `VandeheyS7Birkhoff`'s contraction supplying uniqueness.

## Guard rule

Content locator: `canEmit_runWord_of_const` — the whole refutation rests on one positive fact,
that a state whose image already lies in a single cylinder keeps emitting that digit forever, so
the content is in exhibiting two such states with different digits.  Degenerate case:
`no_window_function []` — the claim already fails at window length `0`, i.e. this is not a
"not enough merging yet" phenomenon, and `witness_distortion` shows it is not a state-shape
phenomenon either.
-/

namespace NormalNumbers.VandeheyS7

open NormalNumbers

namespace MobState

/-! ## The word state maps `[0,1]` into `[0,1]` -/

theorem gaussBranch_mob_mem_Icc (a : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (gaussBranch a).mob u ∧ (gaussBranch a).mob u ≤ 1 := by
  have hA : (1:ℝ) ≤ ((max 1 a : ℕ) : ℝ) := by exact_mod_cast le_max_left 1 a
  rw [gaussBranch_mob]
  refine ⟨div_nonneg zero_le_one (by linarith), ?_⟩
  rw [div_le_one (by linarith)]
  linarith

theorem idState_mob (y : ℝ) : idState.mob y = y := by
  simp [mob, idState]

/-- Reading a word never leaves `[0,1]`: the branches are the Gauss inverse branches. -/
theorem wordState_mob_mem_Icc (w : List ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ (wordState w).mob y ∧ (wordState w).mob y ≤ 1 := by
  induction w with
  | nil => rw [wordState_nil, idState_mob]; exact ⟨hy0, hy1⟩
  | cons a w ih =>
      rw [wordState_cons, mob_comp _ _ hy0]
      exact gaussBranch_mob_mem_Icc a ih.1

/-! ## A state already inside one cylinder emits forever -/

/-- **The one positive fact behind the refutation.**  If `s` maps all of `[0,1]` into a single
depth-one cylinder then, after reading ANY input word, it still does — so it can emit, and it
emits that cylinder's digit.  No hypothesis on the word: the totalised branches keep `[0,1]`
inside `[0,1]`, and `s` does the rest. -/
theorem canEmit_runWord_of_const {s : MobState} {n : ℕ}
    (hs : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → cfDigit (s.mob u) 0 = n) (w : List ℕ) :
    (runWord s w).CanEmit ∧ (runWord s w).emitDigit = n := by
  obtain ⟨h00, h01⟩ := wordState_mob_mem_Icc w (le_refl (0:ℝ)) zero_le_one
  obtain ⟨h10, h11⟩ := wordState_mob_mem_Icc w zero_le_one (le_refl (1:ℝ))
  have e0 : (runWord s w).mob 0 = s.mob ((wordState w).mob 0) := by
    rw [runWord_eq_comp, mob_comp _ _ (le_refl (0:ℝ))]
  have e1 : (runWord s w).mob 1 = s.mob ((wordState w).mob 1) := by
    rw [runWord_eq_comp, mob_comp _ _ zero_le_one]
  refine ⟨?_, ?_⟩
  · show cfDigit ((runWord s w).mob 0) 0 = cfDigit ((runWord s w).mob 1) 0
    rw [e0, e1, hs _ h00 h01, hs _ h10 h11]
  · show cfDigit ((runWord s w).mob 0) 0 = n
    rw [e0, hs _ h00 h01]

/-! ## The two witnesses -/

/-- `y ↦ (y+3)/8`, whose image `[3/8, 1/2]` sits inside the digit-`2` cylinder. -/
noncomputable def witness₂ : MobState :=
  ⟨1, 3, 0, 8, zero_le_one, by norm_num, le_refl 0, by norm_num, by norm_num⟩

/-- `y ↦ (y+7)/32`, whose image `[7/32, 1/4]` sits inside the digit-`4` cylinder. -/
noncomputable def witness₄ : MobState :=
  ⟨1, 7, 0, 32, zero_le_one, by norm_num, le_refl 0, by norm_num, by norm_num⟩

theorem witness₂_mob (u : ℝ) : witness₂.mob u = (u + 3) / 8 := by
  simp only [mob, witness₂]; ring_nf

theorem witness₄_mob (u : ℝ) : witness₄.mob u = (u + 7) / 32 := by
  simp only [mob, witness₄]; ring_nf

theorem witness₂_digit {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    cfDigit (witness₂.mob u) 0 = 2 := by
  have hpos : (0:ℝ) < u + 3 := by linarith
  have hinv : (witness₂.mob u)⁻¹ = 8 / (u + 3) := by rw [witness₂_mob, inv_div]
  rw [cfDigit_zero, hinv, Nat.floor_eq_iff (div_nonneg (by norm_num) hpos.le)]
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_ofNat, le_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; push_cast; linarith

theorem witness₄_digit {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    cfDigit (witness₄.mob u) 0 = 4 := by
  have hpos : (0:ℝ) < u + 7 := by linarith
  have hinv : (witness₄.mob u)⁻¹ = 32 / (u + 7) := by rw [witness₄_mob, inv_div]
  rw [cfDigit_zero, hinv, Nat.floor_eq_iff (div_nonneg (by norm_num) hpos.le)]
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_ofNat, le_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; push_cast; linarith

/-- Both witnesses have the MINIMUM possible distortion, so the refutation is not about badly
shaped states and Route A's compact bounded-distortion fiber does not evade it. -/
theorem witness_distortion : witness₂.distortion = 1 ∧ witness₄.distortion = 1 := by
  constructor <;> · simp [distortion, witness₂, witness₄]

/-! ## The refutation -/

/-- **The emitted digit is not a function of the input window.**  Two states of distortion `1`
both emit after reading any word whatsoever, and they always emit different digits. -/
theorem emitDigit_not_window_function (w : List ℕ) :
    (runWord witness₂ w).CanEmit ∧ (runWord witness₄ w).CanEmit ∧
      (runWord witness₂ w).emitDigit ≠ (runWord witness₄ w).emitDigit := by
  obtain ⟨hc2, he2⟩ := canEmit_runWord_of_const (fun _ h0 h1 => witness₂_digit h0 h1) w
  obtain ⟨hc4, he4⟩ := canEmit_runWord_of_const (fun _ h0 h1 => witness₄_digit h0 h1) w
  exact ⟨hc2, hc4, by rw [he2, he4]; norm_num⟩

/-- **The refuted statement, verbatim.**  For every window `w` — of every length — there is no
value the machine must emit after reading `w`.  So `F w := emitDigit (wordState w)` cannot be the
window function of the assembly, and no other choice of `F` can either. -/
theorem no_window_function (w : List ℕ) :
    ¬ ∃ F : ℕ, ∀ s : MobState, (runWord s w).CanEmit → (runWord s w).emitDigit = F := by
  rintro ⟨F, hF⟩
  obtain ⟨hc2, hc4, hne⟩ := emitDigit_not_window_function w
  exact hne ((hF witness₂ hc2).trans (hF witness₄ hc4).symm)

/-- The same, with the window length made explicit: the failure is uniform in the length, so it
is not a "the window is not long enough yet" phenomenon. -/
theorem no_window_function_of_length (n : ℕ) :
    ∃ w : List ℕ, w.length = n ∧ (∀ a ∈ w, 1 ≤ a) ∧
      ¬ ∃ F : ℕ, ∀ s : MobState, (runWord s w).CanEmit → (runWord s w).emitDigit = F :=
  ⟨List.replicate n 1, List.length_replicate .., fun a ha => by
    simpa using (List.eq_of_mem_replicate ha).ge, no_window_function _⟩

end MobState

section Audit

#print axioms MobState.wordState_mob_mem_Icc
#print axioms MobState.canEmit_runWord_of_const
#print axioms MobState.witness_distortion
#print axioms MobState.emitDigit_not_window_function
#print axioms MobState.no_window_function
#print axioms MobState.no_window_function_of_length

end Audit

end NormalNumbers.VandeheyS7
