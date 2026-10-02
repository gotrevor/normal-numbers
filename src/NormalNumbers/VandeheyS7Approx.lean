/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Assemble

/-!
# The ε-approximation engine for the sampled count

`VandeheyS7Assemble.cfCount_tendsto_of_decomposition` reduced `SampledUniformCount` to a single
hypothesis: the image's occurrence count of `v` agrees with the total occurrence count of a
**finite** family `S` of input words **up to a bounded error `C`**.  This module records that the
bounded-error form is *unattainable on this route*, and replaces it with the form the route
actually delivers.

## Why the bounded error cannot be met

The window function of `VandeheyS7Emit` computes the image digit from a bounded window of the
input **off an exceptional set** — the set where `cfDigit_agree_depth` fails, i.e. where the
orbit comes within `δ` of a cylinder endpoint at some level below the cutoff, or where the
accumulated scale exceeds the cutoff.  `VandeheyS7Boundary.gaussMeasure_exceptional_le` bounds
that set's Gauss mass by a small **positive** quantity; it is not null.  A CF-normal input visits
a set of positive Gauss mass with *positive frequency*, so the number of positions at which the
window function is wrong grows like `c·p` with `c > 0`.  The decomposition error is therefore
`Θ(p)` with a small constant, never `O(1)`.  Shrinking `δ` and raising the cutoff `K` shrinks the
constant to `0` (that is what `VandeheyS7Budget` buys) but enlarges the finite family `S`.

So the honest shape of the input is a *scheme*: a sequence of finite families `S k` and errors
`ε k → 0`, with the `k`-th family accounting for the image count up to `ε k · p`.  That is
`ApproxScheme` below, and `tendsto_div_of_approxScheme` is the engine that consumes it.

`approxScheme_sqrt` is the separation witness, in the kernel: an error of `√p` admits a scheme
and admits no bound, so this is a strict weakening of the hypothesis and not a repackaging.

## Why the limit is still `x`-independent

The scheme's families `S k` and errors `ε k` are chosen **before** `x`.  Each family's limit
`sumGauss (S k) = ∑_{u ∈ S k} γ(I_u)` is therefore a number attached to the *scheme*, with no `x`
in it.  `abs_sub_le_of_approx` shows any two of these limits are within `ε k + ε j`, so the
sequence `k ↦ sumGauss (S k)` is Cauchy as soon as one CF-normal witness exists, and its limit
`L` is the common value for every `x`.  `sampledUniformCount_of_approxScheme` packages exactly
that, and it needs no witness hypothesis: if no CF-normal number existed, the crux would hold
vacuously.

## Guard rule

Content locator: `approxScheme_exact` — an exact decomposition is the scheme with `ε ≡ 0` and a
constant family, and the engine then returns plain CF-normality (`famCount_tendsto`); so the
engine adds nothing in that case and all its content is in letting `ε` be positive.  Degenerate
cases: `tendsto_div_of_approxScheme_empty` (the empty family at every level forces the limit `0`),
`approxScheme_of_bddError` (the old bounded-error hypothesis is subsumed, so nothing proved
against it is lost), and `approxScheme_sqrt` (the converse fails, so the weakening is strict).
-/

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers

/-- A finite family of input words is **genuine** when every member is a nonempty word of CF
digits, i.e. exactly the words `IsCFNormal` speaks about. -/
def Genuine (S : Finset (List ℕ)) : Prop := ∀ u ∈ S, u ≠ [] ∧ ∀ a ∈ u, 1 ≤ a

theorem genuine_empty : Genuine ∅ := by simp [Genuine]

/-- The Gauss mass of a finite family of cylinders: the Cesàro limit the family contributes.
It mentions no real number, which is the whole reason the crux's limit is `x`-independent. -/
noncomputable def sumGauss (S : Finset (List ℕ)) : ℝ :=
  ∑ u ∈ S, (gaussMeasure (cfCylinder u)).toReal

@[simp] theorem sumGauss_empty : sumGauss ∅ = 0 := by simp [sumGauss]

/-- The total number of occurrences, among the first `p` CF digits of `y`, of the words of `S`. -/
noncomputable def famCount (S : Finset (List ℕ)) (y : ℝ) (p : ℕ) : ℝ :=
  ∑ u ∈ S, (countOccurrences u ((List.range p).map (cfDigit y)) : ℝ)

@[simp] theorem famCount_empty (y : ℝ) (p : ℕ) : famCount ∅ y p = 0 := by simp [famCount]

/-- Finite additivity on top of CF-normality: a genuine finite family has a joint frequency. -/
theorem famCount_tendsto {y : ℝ} (hy : IsCFNormal y) {S : Finset (List ℕ)} (hS : Genuine S) :
    Tendsto (fun p => famCount S y p / p) atTop (nhds (sumGauss S)) :=
  cfFreq_finset_sum hy S hS

/-- **An ε-approximation scheme.**  For every level `k`, the family `S k` accounts for `f`
up to an error `ε k · p`.  The families and the errors do not depend on the input; only the
threshold beyond which the bound holds may. -/
def ApproxScheme (f : ℕ → ℝ) (y : ℝ) (S : ℕ → Finset (List ℕ)) (ε : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ᶠ p : ℕ in atTop, |f p - famCount (S k) y p| ≤ ε k * p

/-! ## The two limits of a scheme are close -/

/-- **Two families that both approximate `f` have close Gauss masses.**  The bound is
`δ + δ'` — no `f`, no `y`.  This is what makes the scheme's limit a number attached to the
scheme. -/
theorem abs_sub_le_of_approx {f : ℕ → ℝ} {y : ℝ} (hy : IsCFNormal y)
    {S S' : Finset (List ℕ)} (hS : Genuine S) (hS' : Genuine S') {δ δ' : ℝ}
    (h : ∀ᶠ p : ℕ in atTop, |f p - famCount S y p| ≤ δ * p)
    (h' : ∀ᶠ p : ℕ in atTop, |f p - famCount S' y p| ≤ δ' * p) :
    |sumGauss S - sumGauss S'| ≤ δ + δ' := by
  have hA := famCount_tendsto hy hS
  have hB := famCount_tendsto hy hS'
  have hlim : Tendsto (fun p : ℕ => |famCount S y p / p - famCount S' y p / p|) atTop
      (nhds |sumGauss S - sumGauss S'|) := (hA.sub hB).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [h, h', eventually_gt_atTop 0] with p hp hp' hp0
  have hpr : (0:ℝ) < p := by exact_mod_cast hp0
  have hsplit : famCount S y p - famCount S' y p
      = (f p - famCount S' y p) - (f p - famCount S y p) := by ring
  have key : |famCount S y p - famCount S' y p| ≤ (δ + δ') * p := by
    have := abs_sub (f p - famCount S' y p) (f p - famCount S y p)
    calc |famCount S y p - famCount S' y p|
        ≤ |f p - famCount S' y p| + |f p - famCount S y p| := by
          rw [hsplit]; exact abs_sub _ _
      _ ≤ δ' * p + δ * p := add_le_add hp' hp
      _ = (δ + δ') * p := by ring
  have heq : |famCount S y p / p - famCount S' y p / p|
      = |famCount S y p - famCount S' y p| / p := by
    rw [div_sub_div_same, abs_div, abs_of_pos hpr]
  rw [heq, div_le_iff₀ hpr]
  exact key

/-! ## The engine -/

/-- **The ε-approximation engine.**  A scheme whose errors tend to `0`, together with a limit `L`
for the scheme's own masses, forces `f p / p → L`.  The point is that `L` is supplied by the
scheme (`hL` mentions neither `f` nor `y`), so the same `L` serves every input. -/
theorem tendsto_div_of_approxScheme {f : ℕ → ℝ} {y : ℝ} (hy : IsCFNormal y)
    {S : ℕ → Finset (List ℕ)} (hS : ∀ k, Genuine (S k)) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (nhds 0)) {L : ℝ}
    (hL : Tendsto (fun k => sumGauss (S k)) atTop (nhds L))
    (happrox : ApproxScheme f y S ε) :
    Tendsto (fun p => f p / p) atTop (nhds L) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have h3 : (0:ℝ) < η / 3 := by linarith
  obtain ⟨K1, hK1⟩ := Metric.tendsto_atTop.mp hε (η / 3) h3
  obtain ⟨K2, hK2⟩ := Metric.tendsto_atTop.mp hL (η / 3) h3
  set k := max K1 K2 with hkdef
  have hek : ε k < η / 3 := by
    have hd := hK1 k (le_max_left _ _)
    rw [Real.dist_eq, sub_zero] at hd
    exact lt_of_le_of_lt (le_abs_self _) hd
  have hLk : |sumGauss (S k) - L| < η / 3 := by
    have hd := hK2 k (le_max_right _ _)
    rwa [Real.dist_eq] at hd
  obtain ⟨P1, hP1⟩ := Metric.tendsto_atTop.mp (famCount_tendsto hy (hS k)) (η / 3) h3
  obtain ⟨P2, hP2⟩ := eventually_atTop.mp ((happrox k).and (eventually_gt_atTop 0))
  refine ⟨max P1 P2, fun p hp => ?_⟩
  obtain ⟨hpa, hp0⟩ := hP2 p (le_of_max_le_right hp)
  have hpr : (0:ℝ) < p := by exact_mod_cast hp0
  have h1 : |f p / p - famCount (S k) y p / p| ≤ ε k := by
    rw [div_sub_div_same, abs_div, abs_of_pos hpr, div_le_iff₀ hpr]
    exact hpa
  have h2 : |famCount (S k) y p / p - sumGauss (S k)| < η / 3 := by
    have hd := hP1 p (le_of_max_le_left hp)
    rwa [Real.dist_eq] at hd
  rw [Real.dist_eq]
  have t1 := abs_sub_le (f p / p) (famCount (S k) y p / p) (sumGauss (S k))
  have t2 := abs_sub_le (f p / p) (sumGauss (S k)) L
  linarith

/-- **The scheme pins its own limit.**  One CF-normal witness is enough to make the scheme's
masses Cauchy, and the resulting `L` is then the limit of `f p / p` for that witness. -/
theorem exists_tendsto_of_approxScheme {f : ℕ → ℝ} {y : ℝ} (hy : IsCFNormal y)
    {S : ℕ → Finset (List ℕ)} (hS : ∀ k, Genuine (S k)) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (nhds 0)) (happrox : ApproxScheme f y S ε) :
    ∃ L : ℝ, Tendsto (fun k => sumGauss (S k)) atTop (nhds L) ∧
      Tendsto (fun p => f p / p) atTop (nhds L) := by
  have hcau : CauchySeq (fun k => sumGauss (S k)) := by
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hε (δ / 2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hm' : |ε m| < δ / 2 := by
      have hd := hN m hm; rwa [Real.dist_eq, sub_zero] at hd
    have hn' : |ε n| < δ / 2 := by
      have hd := hN n hn; rwa [Real.dist_eq, sub_zero] at hd
    have hkey := abs_sub_le_of_approx hy (hS m) (hS n) (happrox m) (happrox n)
    rw [Real.dist_eq]
    have e1 : ε m ≤ |ε m| := le_abs_self _
    have e2 : ε n ≤ |ε n| := le_abs_self _
    linarith
  obtain ⟨L, hLtend⟩ := cauchySeq_tendsto_of_complete hcau
  exact ⟨L, hLtend, tendsto_div_of_approxScheme hy hS hε hLtend happrox⟩

/-! ## The crux, from a scheme -/

/-- **`SampledUniformCount` from a uniform ε-approximation scheme.**  For each word `v` a scheme
`S v` with errors `ε v → 0` that works for *every* CF-normal input gives the crux outright.  No
witness hypothesis is needed: with no CF-normal number the statement is vacuous, and with one the
scheme's masses converge and supply the common limit. -/
theorem sampledUniformCount_of_approxScheme {q r₀ : ℝ} {ℓ : ℝ → ℕ → ℕ}
    (S : List ℕ → ℕ → Finset (List ℕ)) (hS : ∀ v k, Genuine (S v k))
    (ε : List ℕ → ℕ → ℝ) (hε : ∀ v, Tendsto (ε v) atTop (nhds 0))
    (happrox : ∀ v : List ℕ, v ≠ [] → (∀ e ∈ v, 1 ≤ e) → ∀ x : ℝ, IsCFNormal (Int.fract x) →
      ApproxScheme (fun p => VandeheyOut.cfCount v (Int.fract (q * x + r₀)) (ℓ x p))
        (Int.fract x) (S v) (ε v)) :
    SampledUniformCount q r₀ ℓ := by
  intro v hne hpos
  by_cases hex : ∃ x : ℝ, IsCFNormal (Int.fract x)
  · obtain ⟨x₀, hx₀⟩ := hex
    obtain ⟨L, hLS, -⟩ :=
      exists_tendsto_of_approxScheme hx₀ (hS v) (hε v) (happrox v hne hpos x₀ hx₀)
    exact ⟨L, fun x hxn =>
      tendsto_div_of_approxScheme hxn (hS v) (hε v) hLS (happrox v hne hpos x hxn)⟩
  · exact ⟨0, fun x hxn => absurd ⟨x, hxn⟩ hex⟩

/-! ## Guard rule: locator, degenerate cases, and the strictness witness -/

/-- Content locator: an exact decomposition is the scheme with `ε ≡ 0`, and the engine then
returns exactly `famCount_tendsto`, i.e. plain CF-normality.  All the content is in `ε > 0`. -/
theorem approxScheme_exact {f : ℕ → ℝ} {y : ℝ} {S₀ : Finset (List ℕ)}
    (h : ∀ p, f p = famCount S₀ y p) : ApproxScheme f y (fun _ => S₀) (fun _ => 0) := by
  intro k
  filter_upwards with p
  simp [h p]

/-- Degenerate case: the empty family at every level forces the limit `0`. -/
theorem tendsto_div_of_approxScheme_empty {f : ℕ → ℝ} {y : ℝ} (hy : IsCFNormal y) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (nhds 0)) (happrox : ApproxScheme f y (fun _ => ∅) ε) :
    Tendsto (fun p => f p / p) atTop (nhds 0) :=
  tendsto_div_of_approxScheme hy (fun _ => genuine_empty) hε
    (by simp only [sumGauss_empty]; exact tendsto_const_nhds) happrox

/-- `C / (k+1) → 0`. -/
theorem tendsto_const_div_succ (C : ℝ) :
    Tendsto (fun k : ℕ => C / (k + 1)) atTop (nhds 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

/-- Degenerate case / subsumption: the old **bounded-error** hypothesis of
`cfCount_tendsto_of_decomposition` is a scheme with the constant family and `ε k = C/(k+1)`.  So
nothing that hypothesis could prove is lost. -/
theorem approxScheme_of_bddError {f : ℕ → ℝ} {y : ℝ} {S₀ : Finset (List ℕ)} {C : ℝ}
    (hC : ∀ p : ℕ, |f p - famCount S₀ y p| ≤ C) :
    ApproxScheme f y (fun _ => S₀) (fun k => C / (k + 1)) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  intro k
  filter_upwards [eventually_ge_atTop (k + 1)] with p hp
  refine (hC p).trans ?_
  have hk : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hpk : ((k : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [div_mul_eq_mul_div, le_div_iff₀ hk]
  nlinarith

/-- **The weakening is strict.**  An error of `√p` admits a scheme (with `ε k = 1/(k+1)`) and
admits no bound whatsoever, so `ApproxScheme` is genuinely weaker than the bounded-error
hypothesis it replaces, not a repackaging of it. -/
theorem approxScheme_sqrt (y : ℝ) (S₀ : Finset (List ℕ)) :
    ApproxScheme (fun p => famCount S₀ y p + Real.sqrt p) y (fun _ => S₀) (fun k => 1 / (k + 1))
      ∧ ¬ ∃ C : ℝ, ∀ p : ℕ,
          |(famCount S₀ y p + Real.sqrt p) - famCount S₀ y p| ≤ C := by
  constructor
  · intro k
    filter_upwards [eventually_ge_atTop ((k + 1) * (k + 1))] with p hp
    have hk : (0:ℝ) < (k : ℝ) + 1 := by positivity
    have hp0 : (0:ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hcast : ((k : ℝ) + 1) * ((k : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast hp
    have hsq : ((k : ℝ) + 1) ≤ Real.sqrt p := by
      rw [show ((k:ℝ) + 1) = Real.sqrt (((k:ℝ) + 1) * ((k:ℝ) + 1)) by
        rw [Real.sqrt_mul_self hk.le]]
      exact Real.sqrt_le_sqrt hcast
    have ht : Real.sqrt p * Real.sqrt p = (p : ℝ) := Real.mul_self_sqrt hp0
    have : |famCount S₀ y p + Real.sqrt p - famCount S₀ y p| = Real.sqrt p := by
      rw [show famCount S₀ y p + Real.sqrt p - famCount S₀ y p = Real.sqrt p by ring,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [this, div_mul_eq_mul_div, le_div_iff₀ hk]
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  · rintro ⟨C, hC⟩
    obtain ⟨n, hn⟩ := exists_nat_gt C
    have := hC (n * n)
    rw [show famCount S₀ y (n * n) + Real.sqrt ((n * n : ℕ) : ℝ) - famCount S₀ y (n * n)
      = Real.sqrt ((n * n : ℕ) : ℝ) by ring, abs_of_nonneg (Real.sqrt_nonneg _)] at this
    rw [show (((n * n : ℕ)) : ℝ) = (n : ℝ) * (n : ℝ) by push_cast; ring,
      Real.sqrt_mul_self (Nat.cast_nonneg n)] at this
    linarith

section Audit

#print axioms famCount_tendsto
#print axioms abs_sub_le_of_approx
#print axioms tendsto_div_of_approxScheme
#print axioms exists_tendsto_of_approxScheme
#print axioms sampledUniformCount_of_approxScheme
#print axioms approxScheme_of_bddError
#print axioms approxScheme_sqrt

end Audit

end NormalNumbers.VandeheyS7
