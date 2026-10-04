/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LinearFormsScales
import NormalNumbers.Stoneham

/-!
# Stretch conjectures beside the E4 freeze

Each is a `def … : Prop` with no proof and no `sorry`: a frozen STATEMENT, never a truth claim.
Audit: `docs/LINEAR-FORMS-AUDIT-2026-10-04.md`.

* `FurstenbergLogOptimal`: the converse side of the headline, that no irrational point beats
  `(log q)^{−(1−δ)}` along `Σ`.  This is effective ×2×3 at polylogarithmic scale; the best known
  density rate is `(log log log q)^{−κ}` (Bourgain–Lindenstrauss–Michel–Venkatesh, ETDS 29 (2009),
  for Diophantine-generic points).  Confidence true 60%, provable 1%.
* `StonehamBase3Normal`: Bailey–Borwein, *Nonnormality of Stoneham constants*, Ramanujan J. 29
  (2012) §5, verbatim (davidhbailey.com copy, as quoted in `docs/OPEN-PROBLEMS-SWEEP-2026-10-04.md`):
  "it is not known at the present time whether or not α2,3 is 3-normal, although it appears to
  be. … But there is no proof of 3-normality."  Confidence true 85%, provable 2%.
* `StonehamBase18Normal`: the smallest base divisible by 6 outside the Bailey–Borwein
  non-normality region `B < 8^{v₂(B)}` (Theorem 2 there).  At every position two Stoneham terms
  are live and the later one is a high-bit readout of `9ˣ mod 2^{Θ(3ᵐ)}`.  Confidence true 80%,
  provable 2%.
* `ShortPowerOrbitEquidist`: the missing estimate behind both Stoneham rows, the reopen
  condition of the Maze row "Stoneham profile beyond the Bailey–Borwein region": the points
  `3ⁿ / 2ᶜ mod 1`, `c ≤ n < 2c`, equidistribute as `c → ∞`.  The window is exponentially shorter
  than the period `2^{c−2}` of `3 mod 2ᶜ` (the Korobov / Erdős #406 regime).  Linear forms in
  logarithms say nothing about it.  Confidence true 75%, provable 1%.
-/

namespace NormalNumbers.LinearFormsScales

open NormalNumbers.UniformBad Filter Topology

/-- No irrational point avoids `0` along `Σ` at any rate `c / (log q)^{1−δ}`, `0 < δ < 1`. -/
def FurstenbergLogOptimal : Prop :=
  ∀ α : ℝ, Irrational α → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ c : ℝ, 0 < c →
    ∃ q ∈ furstenbergSet, 2 ≤ q ∧ dnear (q * α) < c / Real.log q ^ (1 - δ)

/-- Bailey–Borwein 2012 §5: is `α₂,₃` normal in base 3? -/
def StonehamBase3Normal : Prop := IsNormal 3 stoneham23

/-- Is `α₂,₃` normal in base 18 (outside the Bailey–Borwein region)? -/
def StonehamBase18Normal : Prop := IsNormal 18 stoneham23

/-- Equidistribution of the short power orbit `{3ⁿ / 2ᶜ}`, `c ≤ n < 2c`. -/
def ShortPowerOrbitEquidist : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    Tendsto (fun c : ℕ => (((Finset.Ico c (2 * c)).filter
        (fun n => a ≤ Int.fract ((3 : ℝ) ^ n / 2 ^ c) ∧ Int.fract ((3 : ℝ) ^ n / 2 ^ c) < b)).card
        : ℝ) / c) atTop (𝓝 (b - a))

end NormalNumbers.LinearFormsScales
