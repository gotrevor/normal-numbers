/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.VandeheyRunBound

/-!
# `hK` and `hkK` for the concrete `L/R` transducer

The trigger hypotheses of `VandeheyAssembly.mobiusUniformFreq_of_transducer` are stated for an
output alphabet `ℕ`, so the `L/R` transducer is read through the injective letter encoding
`L ↦ 1`, `R ↦ 0`.  Three facts already in the kernel then close them for every non-constant
target word `v`:

* `VandeheyAltCount.occIn_le_numAlt_add` — occurrences of `v` starting in the first emitted
  block are at most `numAlt (that block) + 2 + |v|`, whatever the block's length;
* `VandeheyRunBound.numAlt_lrOut_le_two_mul` — a block has at most `2D` alternations
  (Vandehey Lemma 2.2), uniformly in the state and the ingested digit;
* `VandeheyAltCount.trigger_bounds_of_occIn_le` — `hK` and `hkK` are that one bound.

So `K = 2D + 2 + |v|`.  The hypothesis that `v` alternates somewhere is exactly the place where
the run↔CF-digit translation will plug in: a genuine CF word's `L/R` pattern contains both
letters.
-/

namespace NormalNumbers.VandeheyLR

open Mat2 VandeheyOut VandeheyAut

/-- The letter encoding into the output alphabet `ℕ` of the assembly: `L ↦ 1`, `R ↦ 0`. -/
def encLetter (b : Bool) : ℕ := if b then 1 else 0

lemma encLetter_injective : Function.Injective encLetter := by
  intro b c h
  cases b <;> cases c <;> simp_all [encLetter]

/-- An injective relabelling of letters preserves the alternation count. -/
lemma numAlt_map_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β] {g : α → β}
    (hg : Function.Injective g) : ∀ L : List α, numAlt (L.map g) = numAlt L
  | [] => rfl
  | [_] => rfl
  | (x :: y :: t) => by
      have ih : numAlt (g y :: List.map g t) = numAlt (y :: t) := by
        simpa [List.map_cons] using numAlt_map_of_injective hg (y :: t)
      rw [List.map_cons, List.map_cons, numAlt, numAlt, ih]
      congr 1
      by_cases h : x = y
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun hc => h (hg hc))]

variable {D : ℕ}

/-- The transducer's output, in the assembly's alphabet. -/
noncomputable def lrOutN (hD : 0 < D) (M : RState D) (j : ℕ) : List ℕ :=
  (lrOut hD M j).map encLetter

/-- The first block of a run is the output of its first ingested digit. -/
lemma blocksOf_take_one {S : Type*} [DecidableEq S] (δ : S → ℕ → S) (out : S → ℕ → List ℕ)
    (t : S) (q : List ℕ) :
    blocksOf δ out t (q.take 1) = (q.head?).elim [] (fun a => out t a) := by
  cases q with
  | nil => simp
  | cons a q => simp [blocksOf]

/-- **Lemma 2.2 through the encoding**: the first block of any run of the `L/R` transducer has
at most `2D` alternations. -/
lemma numAlt_blocksOf_take_one_le (hD : 0 < D) (t : RState D) (q : List ℕ) :
    numAlt (blocksOf (lrDelta hD) (lrOutN hD) t (q.take 1)) ≤ 2 * D := by
  rw [blocksOf_take_one]
  cases q with
  | nil => simp
  | cons a q =>
    simp only [List.head?_cons, Option.elim_some, lrOutN]
    rw [numAlt_map_of_injective encLetter_injective]
    exact numAlt_lrOut_le_two_mul hD t a

/-- **`occIn` for the concrete machine.**  Uniform in the state, the ingested word and the
ingested digits — only the target word's length enters. -/
theorem occIn_lrOutN_le (hD : 0 < D) (v : List ℕ) (i₀ : ℕ) (hi : i₀ + 1 < v.length)
    (hne : v[i₀]? ≠ v[i₀ + 1]?) (t : RState D) (q : List ℕ) :
    occIn (lrDelta hD) (lrOutN hD) v t q ≤ 2 * D + 2 + v.length := by
  have h1 := occIn_le_numAlt_add (lrDelta hD) (lrOutN hD) v i₀ hi hne t q
  have h2 := numAlt_blocksOf_take_one_le hD t q
  omega

/-- **`hkK` and `hK` for the `L/R` transducer**, with `K = 2D + 2 + |v|`.  This discharges two of
the six named hypotheses of `mobiusUniformFreq_of_transducer` for every word that alternates
somewhere — i.e. for every genuine CF trigger pattern. -/
theorem lr_trigger_bounds (hD : 0 < D) (v : List ℕ) (i₀ : ℕ) (hi : i₀ + 1 < v.length)
    (hne : v[i₀]? ≠ v[i₀ + 1]?) :
    (∀ q (t : RState D), kOut (lrDelta hD) (lrOutN hD) v q t ≤ 2 * D + 2 + v.length) ∧
      (∀ (t : RState D) (y : ℝ) (J : ℕ),
        ∑ j ∈ Finset.Icc 1 J, kOut (lrDelta hD) (lrOutN hD) v (cfWord y j) t
          ≤ 2 * D + 2 + v.length) :=
  trigger_bounds_of_occIn_le (lrDelta hD) (lrOutN hD) v
    (fun t q => occIn_lrOutN_le hD v i₀ hi hne t q)

end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms numAlt_map_of_injective
#print axioms numAlt_blocksOf_take_one_le
#print axioms occIn_lrOutN_le
#print axioms lr_trigger_bounds
end
