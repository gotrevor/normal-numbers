/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs

/-!
# John M. Campbell's 2026 papers: a question we answer, and a priority citation

Tier P (read from the arXiv PDFs on 2026-10-02).

* **arXiv:2605.24160** (*On the binary digits of the Erdős–Borwein constant*) proves Crandall's
  "11 occurs infinitely often in binary `E`" and closes (§4) with: "one might consider the problem
  of determining whether or not every binary string appears infinitely often in the base-2
  expansion of E."  `CampbellEQuestion` states that question; `CampbellAnswer.lean` answers it from
  `jointWords_quantitative`.
* **arXiv:2603.04396** (*Abelian-normal decimal expansions*), Theorem 1: the constant `Ξ₁₀` is
  abelian-normal in base 10 but not normal in base 10.  It predates our binary
  `exists_abelianNormal_not_normal` (`AbelianBinaryExample.lean`), so it is the priority reference.
  `IsAbelianNormalB` is Campbell's Definition 2, transcribed for digit sequences; the bridge to our
  binary `IsAbelianNormalTwo` (a different normalization: window one-counts) is not claimed here.
-/

namespace NormalNumbers.Literature.Campbell

/-- The Erdős–Borwein constant `E = Σ_{n≥1} 1/(2ⁿ − 1)` (the `n = 0` term is `1/0 = 0`). -/
noncomputable def erdosBorweinE : ℝ := ∑' n : ℕ, (1 : ℝ) / (2 ^ n - 1)

/-- **Campbell's question (arXiv:2605.24160, §4).**  Every binary string appears infinitely often
in the base-2 expansion of `E`.  (Read through `Int.fract`; the integer part `1` is a single
leading digit and does not affect "infinitely often".) -/
def CampbellEQuestion : Prop :=
  ∀ w : List ℕ, (∀ d ∈ w, d < 2) → ∀ N : ℕ, ∃ n, N ≤ n ∧
    ∀ j (hj : j < w.length), digitOf 2 (Int.fract erdosBorweinE) (n + j) = w[j]

open Classical in
/-- `B_E(s, n)`: positions `i < n` whose length-`|E|` factor of `s` is a permutation of `E`. -/
noncomputable def abelianCount (s : ℕ → ℕ) (E : List ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => ((List.range E.length).map (fun j => s (i + j))).Perm E)).card

open Classical in
/-- `|[E]∼|`: the number of distinct words that are permutations of `E`. -/
noncomputable def permClassSize (E : List ℕ) : ℕ :=
  (E.permutations.toFinset).card

/-- **Abelian normality in base `B`** (Campbell, arXiv:2603.04396, Definition 2):
`(1/|[E]∼|)·B_E(s, n)/n → B^{−|E|}` for every nonempty block `E` of base-`B` digits. -/
def IsAbelianNormalB (B : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ E : List ℕ, E ≠ [] → (∀ d ∈ E, d < B) →
    Filter.Tendsto (fun n => (abelianCount s E n : ℝ) / (permClassSize E * n))
      Filter.atTop (nhds ((B : ℝ) ^ E.length)⁻¹)

/-- **Campbell (arXiv:2603.04396), Theorem 1**, digit-sequence form: some base-10 digit sequence is
abelian-normal but not normal.  Cited, not proved here. -/
def Campbell2026AbelianThm1 : Prop :=
  ∃ s : ℕ → ℕ, (∀ i, s i < 10) ∧ IsAbelianNormalB 10 s ∧ ¬ IsNormalSequence 10 s

end NormalNumbers.Literature.Campbell
