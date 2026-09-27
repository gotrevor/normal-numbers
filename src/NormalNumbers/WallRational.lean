/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Wall
import NormalNumbers.WeylCriterion

/-!
# Wall: rational affine maps preserve normality

D. D. Wall (1949 thesis): if `x` is normal in base `b` and `q ≠ 0`, `r` are rational, then
`q * x + r` is normal in base `b`.  `Maze.lean` cited this ("normality survives rational
multiplication") as a `.cited` row; this file proves it.

## The decomposition

Everything is transported through Wall's theorem
(`isNormal_iff_equidistributed_orbit`), so the working currency is
`Equidistributed (orbit b ·)`.  Writing `q = u/v`, `r = p/w` and `V = v*w`,

    q * x + r = ((u*w) * x + v*p) / V,

so it suffices to handle an integer dilation, an integer translation, and a division by
a positive integer `V`.  Three of the four moves are cheap:

* **integer translation is free**: `orbit b (x + M) = orbit b x` for `M : ℤ`
  (`orbit_add_intCast`), because `b^n * M` is an integer;
* **integer dilation** is an interval decomposition: the preimage of `[a, c)` under
  `t ↦ {m t}` is the disjoint union of the `m` intervals `[(j+a)/m, (j+c)/m)`
  (`equidistributed_natMul`), plus a reflection for negative multipliers
  (`equidistributed_negFract`);
* **division by a `b`-smooth factor is free**: if `A ∣ b^κ`, `b^κ = A*c`, then
  `x / A = (c*x) / b^κ` and dividing by `b^κ` only shifts the orbit by `κ`
  (`equidistributed_of_shift`).

Splitting `V = A * B` with `A ∣ b^κ` and `gcd(B, b) = 1` (`exists_smooth_coprime_split`)
therefore reduces the whole theorem to one irreducible statement, the **crux**:

    IsNormal b x  →  gcd(B, b) = 1  →  IsNormal b ((x + M) / B).

## Why the crux is the crux

`orbit b ((x + M)/B) n = (r n + orbit b x n) / B` where
`r n = (⌊b^n x⌋ + b^n M) mod B` is the state of the long-division automaton.  So the
crux is exactly the *joint* equidistribution of the automaton state `r n` with the
future digits of `x` — and `r n` depends on the entire digit prefix, not on a bounded
window, which is what makes it inaccessible to a direct block count.  Weyl's criterion
does **not** linearise it: the Fourier test at frequency `h` for `(x+M)/B` is the
Fourier test at the *rational* frequency `h/B` for `x`, i.e. the same problem again.

The intended attack (recorded here so it survives the lap): since `gcd(B, b) = 1` there
is `T` with `b^T ≡ 1 (mod B)`, and then

    r (n + T*k) = r n + W (T*k) n   (mod B),   W l n = value of the digit block x[n, n+l),

so for a nontrivial additive character `χ` mod `B` the Cesàro mean
`A = lim (1/N) ∑_{n<N} χ (r n) * f (orbit b x n)` is, by shift invariance in `n`,
equal to `lim (1/N) ∑_n χ (r n) * (1/K) ∑_{k≤K} χ (W (T*k) n) * f (orbit b x (n+T*k))`.
Cauchy–Schwarz then reduces `|A|` to the off-diagonal block correlations
`(1/N) ∑_n χ (W (T*k) n) * conj (χ (W (T*k') n)) * …`, each of which is a *fixed-depth*
block average, hence computable from normality alone, and equal to a character sum over
a free digit range — geometrically small, `O(B * b^{-T*(k'-k)})`.  The engine for that
step is `tendsto_blockAverage` below.
-/

namespace NormalNumbers

open Filter Topology

namespace WallRational

/-! ### Cheap moves: translation, dilation, reflection, shift -/

/-- Fractional parts only see the fractional part, through an integer dilation. -/
theorem fract_intMul_fract (m : ℤ) (y : ℝ) :
    Int.fract ((m : ℝ) * y) = Int.fract ((m : ℝ) * Int.fract y) := by
  sorry

/-- **Integer translations are free**: the orbit of `x + M` is the orbit of `x`. -/
theorem orbit_add_intCast (b : ℕ) (x : ℝ) (M : ℤ) (n : ℕ) :
    orbit b (x + (M : ℝ)) n = orbit b x n := by
  sorry

/-- The orbit of `m * x` is the `m`-dilation of the orbit of `x`. -/
theorem orbit_intMul (b : ℕ) (x : ℝ) (m : ℤ) (n : ℕ) :
    orbit b ((m : ℝ) * x) n = Int.fract ((m : ℝ) * orbit b x n) := by
  sorry

/-- Dilating an equidistributed `[0,1)`-valued sequence by a positive integer, modulo
one, preserves equidistribution: the preimage of `[a, c)` is the disjoint union of the
`m` intervals `[(j+a)/m, (j+c)/m)`. -/
theorem equidistributed_natMul {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1)
    (h : Equidistributed u) {m : ℕ} (hm : 0 < m) :
    Equidistributed (fun k => Int.fract ((m : ℝ) * u k)) := by
  sorry

/-- Level sets of an equidistributed sequence have density zero. -/
theorem density_level_zero {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1)
    (h : Equidistributed u) (t : ℝ) :
    Tendsto (fun n => (((Finset.range n).filter fun k => u k = t).card : ℝ) / n)
      atTop (𝓝 0) := by
  sorry

/-- Reflection `t ↦ {-t}` preserves equidistribution (the two exceptional endpoints and
the fixed point `0` form density-zero level sets). -/
theorem equidistributed_negFract {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1)
    (h : Equidistributed u) :
    Equidistributed (fun k => Int.fract (-(u k))) := by
  sorry

/-- Dropping the first `κ` terms cannot create equidistribution, and cannot destroy it. -/
theorem equidistributed_of_shift {u : ℕ → ℝ} (κ : ℕ)
    (h : Equidistributed fun n => u (n + κ)) : Equidistributed u := by
  sorry

/-! ### Normality-level consequences -/

/-- Integer translations preserve normality. -/
theorem isNormal_add_intCast (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (M : ℤ) (hx : IsNormal b x) :
    IsNormal b (x + (M : ℝ)) := by
  sorry

/-- Nonzero integer dilations preserve normality. -/
theorem isNormal_intMul (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (m : ℤ) (hm : m ≠ 0)
    (hx : IsNormal b x) : IsNormal b ((m : ℝ) * x) := by
  sorry

/-- Division by a power of the base preserves normality (it shifts the orbit). -/
theorem isNormal_div_pow (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (κ : ℕ) (hx : IsNormal b x) :
    IsNormal b (x / (b : ℝ) ^ κ) := by
  sorry

/-! ### The arithmetic split of the denominator -/

/-- Every positive `V` factors as a `b`-smooth part times a part coprime to `b`. -/
theorem exists_smooth_coprime_split (b : ℕ) (hb : 2 ≤ b) (V : ℕ) (hV : 0 < V) :
    ∃ A B κ : ℕ, 0 < A ∧ 0 < B ∧ V = A * B ∧ A ∣ b ^ κ ∧ Nat.Coprime B b := by
  sorry

/-! ### The crux: division by a modulus coprime to the base -/

/-- The block of `l` digits of `x` starting at position `n`, as a natural number. -/
noncomputable def blockVal (b : ℕ) (x : ℝ) (n l : ℕ) : ℕ :=
  blockNatVal b ((List.range l).map fun i => digitOf b (Int.fract x) (n + i))

/-- **Engine for the crux.** For a normal `x`, the average of any function of the
length-`l` digit block at position `n` converges to its mean over all `b^l` blocks.
This is `IsNormalSequence` plus linearity, and it is what feeds the off-diagonal
estimate in the Cauchy–Schwarz step. -/
theorem tendsto_blockAverage (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsNormal b x)
    (l : ℕ) (hl : 0 < l) (F : ℕ → ℝ) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, F (blockVal b x n l)) / N) atTop
      (𝓝 (((b : ℝ) ^ l)⁻¹ * ∑ v ∈ Finset.range (b ^ l), F v)) := by
  sorry

/-- **CRUX (open).** Normality survives `x ↦ (x + M)/B` when `gcd(B, b) = 1`.

This is the one irreducible step of Wall's theorem: `orbit b ((x+M)/B) n` is
`(r n + orbit b x n)/B` with `r n = (⌊b^n x⌋ + b^n M) mod B` the long-division state,
and the statement is the joint equidistribution of that state with the future digits.
The state depends on the unbounded digit prefix, so no fixed-depth block count reaches
it and Weyl's criterion only reproduces the same problem at a rational frequency; see
the module docstring for the shift-average + Cauchy–Schwarz attack that
`tendsto_blockAverage` is meant to power. -/
theorem isNormal_add_int_div_coprime (b B : ℕ) (hb : 2 ≤ b) (hB : 0 < B)
    (hcop : Nat.Coprime B b) (x : ℝ) (M : ℤ) (hx : IsNormal b x) :
    IsNormal b ((x + (M : ℝ)) / B) := by
  sorry

end WallRational

/-- **Wall (1949)**: rational affine maps preserve base-`b` normality. -/
theorem isNormal_rat_mul_add (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (q r : ℚ) (hq : q ≠ 0)
    (hx : IsNormal b x) : IsNormal b ((q : ℝ) * x + r) := by
  sorry

end NormalNumbers
