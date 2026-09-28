/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.VandeheyTrigger
import NormalNumbers.VandeheyLeafReduction

/-!
# The capstone: a transducer with the right properties gives `MobiusUniformFreq`

Every analytic and combinatorial step of Vandehey's §4-§6 is now in the kernel:

* `VandeheyOutputFreq.exists_tendsto_trigTotal` — the trigger count has an `x`-independent Cesàro
  limit (Lemma 4.3 + the §6 sandwich);
* `VandeheyTrigger.fireTotal_kOut_eq_fireOut` — the trigger family `kOut v` counts exactly the
  occurrences of `v` starting in each output block (§5);
* `VandeheyOutputWord.tendsto_countOccurrences_outWord_of_fireOut` — those bucket to the
  occurrence count in the output word, up to `O(1)`;
* `VandeheyRescale.tendsto_div_of_tendsto_comp_of_monotone` — input indices rescale to output
  indices through `ℓ(n) = c·n(1+o(1))` (Lemma 6.1).

`mobiusUniformFreq_of_transducer` chains them.  Its hypotheses are exactly, and only, what the
concrete automaton must supply; nothing analytic is left.  `VandeheyLeafReduction` then turns
`MobiusUniformFreq` into `MobiusCFN` and, for `x ↦ p·x`, into Vandehey 2017 Theorem 1.1.
-/

namespace NormalNumbers.VandeheyOut

open Filter VandeheyAut Literature

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- **The whole output side, as one reduction.**  A finite-state transducer `(δ, out)` whose

* joint (window, state) frequencies factorize (`hjs`, supplied by
  `VandeheyCocycle.tendsto_jointCount_of_classEquidistribution`),
* output is unbounded (`hcof`) and grows linearly with a common rate (`hlen`, Lemma 6.1),
* trigger multiplicities are uniformly bounded (`hkK`, `hK`, Lemma 2.2) and supported on genuine
  words (`hgen`),
* trigger tails are Gauss-null (`htail`, Lemma 4.3 condition (2)),
* and whose output stream IS the CF expansion of the image (`hout`, the transducer's correctness)

satisfies the per-matrix uniform-frequency statement.  No value of the limit is asserted — the
either-or endgame of `VandeheyLeafReduction` pins it. -/
theorem mobiusUniformFreq_of_transducer
    (δ : S → ℕ → S) (out : S → ℕ → List ℕ) (s₀ : S) {ν : S → ℝ} {K : ℕ} {c : ℝ}
    {A B C D : ℤ}
    (hjs : JointStateFreq δ s₀ ν) (hν : ∀ t, 0 ≤ ν t)
    (hcof : ∀ y : ℝ, ∀ j, ∃ n, j < outLen δ out s₀ y n)
    (hkK : ∀ v q t, kOut δ out v q t ≤ K)
    (hK : ∀ (v : List ℕ) (t : S) (y : ℝ) (J : ℕ),
      ∑ j ∈ Finset.Icc 1 J, kOut δ out v (cfWord y j) t ≤ K)
    (hgen : ∀ v q t, kOut δ out v q t ≠ 0 → ∀ e ∈ q, 1 ≤ e)
    (htail : ∀ v, Tendsto (tailMass (kOut δ out v) ν) atTop (nhds 0))
    (hc : 0 < c)
    (hlen : ∀ y : ℝ, IsCFNormal y →
      Tendsto (fun n => (outLen δ out s₀ y n : ℝ) / n) atTop (nhds c))
    (hout : ∀ x : ℝ, (C : ℝ) * x + D ≠ 0 → IsCFNormal (Int.fract x) → ∀ j,
      outDigit (Int.fract x) (hcof (Int.fract x)) j
        = cfDigit (Int.fract (((A : ℝ) * x + B) / ((C : ℝ) * x + D))) j) :
    MobiusUniformFreq A B C D := by
  classical
  intro v hne _hpos
  obtain ⟨L, hL⟩ := exists_tendsto_trigTotal (k := kOut δ out v) (K := K) δ s₀ hjs hν
    (hkK v) (hK v) (hgen v) (htail v)
  refine ⟨L / c, fun x hden hx => ?_⟩
  set y : ℝ := Int.fract x with hy
  -- the trigger count IS the block occurrence count
  have hsum : ∀ n, trigTotal (kOut δ out v) δ s₀ y n
      = ((∑ i ∈ Finset.range n, fireOut y (hcof y) v i : ℕ) : ℝ) := by
    intro n
    rw [trigTotal, Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [fireTotal_kOut_eq_fireOut δ out s₀ y (hcof y) v i]
  have h1 : Tendsto (fun n => ((∑ i ∈ Finset.range n, fireOut y (hcof y) v i : ℕ) : ℝ) / n)
      atTop (nhds L) := by
    refine (hL y hx).congr ?_
    intro n
    rw [hsum n]
  -- hence the occurrence count in the output word, and then in the output stream
  have h2 := tendsto_countOccurrences_outWord_of_fireOut (δ := δ) (out := out) (s₀ := s₀)
    y (hcof y) hne h1
  have h3 := tendsto_outCount_div (δ := δ) (out := out) (s₀ := s₀) y (hcof y) v hc
    (hlen y hx) h2
  -- and the output stream is the CF expansion of the image
  have hmap : ∀ m : ℕ, (List.range m).map (outDigit y (hcof y))
      = (List.range m).map (cfDigit (Int.fract (((A : ℝ) * x + B) / ((C : ℝ) * x + D)))) :=
    fun m => List.map_congr_left fun j _ => hout x hden hx j
  refine h3.congr ?_
  intro m
  rw [outCount, hmap m]

end NormalNumbers.VandeheyOut

section
open NormalNumbers.VandeheyOut
#print axioms mobiusUniformFreq_of_transducer
end
