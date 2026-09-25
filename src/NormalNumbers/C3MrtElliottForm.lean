/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtRungOne
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The crux is a LEGITIMATE Elliott instance: multiplicativity and non-pretentiousness

`C3MrtSchedule` reduced `ConjC3` to `QuantDepthElliott`, a bound on the twisted `D`-point
correlation `(1/N) ∑_{n<N} e(jn/Q) ∏_{i<D} f_i(n+1+i)` with `f_i = ζ_i^{ω_{>P}}`,
`ζ_i = e(h/b^{i+1})`.  For that to *be* an instance of Elliott's conjecture, rather than a
degenerate statement, the `f_i` must satisfy Elliott's hypotheses.  This file proves them:

* `depthFun_mul_coprime` — each `f_i` is **multiplicative** (on coprime arguments).
* `norm_depthFun` — each `f_i` is **unimodular** on `m ≠ 0`.
* `re_depthRoot_lt_one` — `Re ζ_i < 1` whenever `ζ_i ≠ 1`.
* `tendsto_principalPretentiousDist_atTop` — the **non-pretentiousness witness at the principal
  twist**: `∑_{P<p≤x} (1 − Re ζ_0)/p → ∞`.  This is the divergence Halász/Elliott needs, and it
  is what makes the `D = 1` rung (`depthAvg_one_tendsto`) true.

## The remaining gap in the non-pretentiousness certificate

Full non-pretentiousness asks divergence of `∑_{p≤x}(1 − Re(ζ_0 χ̄(p) p^{-it}))/p` for every
Dirichlet character `χ` and every real `t`, not just `χ = 1, t = 0`.  Both remaining cases are
true and standard, but neither is in this repo yet:

* `t = 0`, `χ` nonprincipal mod `q ≥ 2`: `χ(p) = ζ_0` for a `1/p`-full-density set of primes
  contradicts Dirichlet's theorem (each value class has density `1/φ(q)`), so the sum diverges.
  The repo's `WeakPNT_AP` is the right input.
* `t ≠ 0`: `∑_p χ(p)p^{it}/p = log L(1+it,χ) + O(1)` is bounded, so the sum is
  `∑_p 1/p − O(1) → ∞`.  Needs `L(1+it,χ) ≠ 0` with uniformity in `t`.

Since `ζ_0` is a *constant* on all primes `> P`, both are cases of "a constant cannot pretend to
be `χ(p)p^{it}`", which is the softest possible instance of non-pretentiousness — there is no
conspiracy available.  That is why the `D = 1` rung was provable outright.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- `f_i(m) = ζ_i^{ω_{>P}(m)}`: the `i`-th multiplicative function of the correlation. -/
noncomputable def depthFun (b : ℕ) (h : ℤ) (P i m : ℕ) : ℂ :=
  depthRoot b h i ^ omegaLarge P m

/-- **Each `f_i` is multiplicative.** -/
theorem depthFun_mul_coprime (b : ℕ) (h : ℤ) (P i : ℕ) {m m' : ℕ} (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hco : Nat.Coprime m m') :
    depthFun b h P i (m * m') = depthFun b h P i m * depthFun b h P i m' := by
  simp only [depthFun, omegaLarge_eq_delange]
  rw [DelangeSlot.omegaLarge_mul_of_coprime hm hm' hco P, pow_add]

/-- **Each `f_i` is unimodular.** -/
theorem norm_depthFun (b : ℕ) (h : ℤ) (P i m : ℕ) : ‖depthFun b h P i m‖ = 1 := by
  rw [depthFun, norm_pow, norm_depthRoot, one_pow]

/-- The depth-`D` phase, in Elliott normal form. -/
theorem ee_tailDepth_eq_prod_depthFun (b P D n : ℕ) (h : ℤ) :
    ee ((((h : ℝ) * tailDepth P b D n : ℝ) : ℂ))
      = ∏ i ∈ range D, depthFun b h P i (n + i + 1) := by
  rw [ee_tailDepth_eq_prod]; rfl

/-! ### Non-pretentiousness at the principal twist -/

/-- A unimodular `z ≠ 1` has `Re z < 1`. -/
lemma re_lt_one_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : z.re < 1 := by
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h1 : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
    rw [hz, Complex.normSq_apply] at h1
    nlinarith [h1]
  have hle : z.re ≤ 1 := by nlinarith [sq_nonneg z.im, sq_nonneg (z.re - 1)]
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    apply hz1
    have him : z.im = 0 := by nlinarith [hsq, h]
    exact Complex.ext (by rw [h]; rfl) (by rw [him]; rfl)

lemma re_depthRoot_lt_one {b : ℕ} {h : ℤ} {i : ℕ} (hz : depthRoot b h i ≠ 1) :
    (depthRoot b h i).re < 1 :=
  re_lt_one_of_norm_one (norm_depthRoot b h i) hz

/-- The `1/p`-weighted principal pretentious distance of `f_0` to `1`, truncated at `x`. -/
noncomputable def principalDist (b : ℕ) (h : ℤ) (P x : ℕ) : ℝ :=
  ∑ p ∈ range x, (if p.Prime ∧ P < p then (1 - (depthRoot b h 0).re) / (p : ℝ) else 0)

/-- **The non-pretentiousness witness.**  `∑_{P<p≤x} (1 − Re ζ_0)/p → ∞` whenever `ζ_0 ≠ 1`:
`f_0 = ζ_0^{ω_{>P}}` does not pretend to be `1`.  This is the divergence that Halász needs, and
the reason the `D = 1` rung `depthAvg_one_tendsto` holds. -/
theorem tendsto_principalDist_atTop {b : ℕ} {h : ℤ} {P : ℕ} (hz : depthRoot b h 0 ≠ 1) :
    Tendsto (fun x : ℕ => principalDist b h P x) atTop atTop := by
  set c : ℝ := 1 - (depthRoot b h 0).re with hc
  have hc0 : 0 < c := by
    have := re_depthRoot_lt_one (b := b) (h := h) (i := 0) hz
    rw [hc]; linarith
  set g : ℕ → ℝ := fun p => if p.Prime ∧ P < p then c / (p : ℝ) else 0 with hg
  have hgnn : ∀ p, 0 ≤ g p := by
    intro p
    rw [hg]
    dsimp only
    split_ifs with hp
    · positivity
    · exact le_rfl
  have hnot : ¬ Summable g := by
    intro hsum
    -- rescale to `1/p` on primes `> P`
    have h1 : Summable (fun p : ℕ => if p.Prime ∧ P < p then (1 : ℝ) / (p : ℝ) else 0) := by
      have := hsum.mul_left (1 / c)
      refine this.congr fun p => ?_
      rw [hg]; dsimp only; split_ifs with hp
      · field_simp
      · ring
    -- the finitely many small primes
    have h2 : Summable (fun p : ℕ => if p.Prime ∧ p ≤ P then (1 : ℝ) / (p : ℝ) else 0) := by
      refine summable_of_ne_finset_zero (s := range (P + 1)) fun p hp => ?_
      have hne : ¬ (p.Prime ∧ p ≤ P) := by
        intro hpp
        exact hp (Finset.mem_range.2 (by omega))
      rw [if_neg hne]
    have h3 : Summable (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n)) := by
      refine (h1.add h2).congr fun p => ?_
      by_cases hp : p.Prime
      · by_cases hle : p ≤ P
        · simp [Set.indicator_apply, hp, hle, not_lt.2 hle]
        · simp [Set.indicator_apply, hp, hle, lt_of_not_ge hle]
      · simp [Set.indicator_apply, hp]
    exact not_summable_one_div_on_primes h3
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg hgnn).1 hnot

end CastingOut

end NormalNumbers
