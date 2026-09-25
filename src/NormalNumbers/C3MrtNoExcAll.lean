/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtSlowSched

/-!
# Narrowing the `K`-point input: what it may assume, and what it may NOT

After `C3MrtSlowSched`, `ConjC3` rests on exactly one open statement,
`KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K` for every `K` (`conjC3_of_geom_input`).  This
file asks how much weaker that statement can be made.

**Two answers, one positive and one negative.**

*Positive.*  `kPointNoExcWith_mono`: the input is monotone — shrinking the saving exponent `cK`
and growing the constant `CstK` both weaken it, because the two hypotheses `W ≤ L^{cK K}`,
`hsh i ≤ L^{cK K}` tighten exactly when the conclusion `≤ CstK K · L^{-cK K}` loosens (`L ≥ 1`).
So the geometric profile is **not** an extra assumption beyond `∀ K, KPointNaturalCorrelationNoExc
K`: it is precisely the statement that the per-`K` constants that statement already produces
existentially degrade no faster than `c_K ≳ c₀ b^{-θK}`, `Cst_K ≲ exp((K+1)^m)`.

*Negative — and route-decisive.*  `KPointNoExcWith` hypothesises that **one** of the `K` factors
is non-pretentious.  One might hope to assume only the weaker `KPointNoExcAllWith`, where **all**
`K` factors are: the C3 chain feeds in `zOmegaNat (depthRoot b h' i)`, and
`depthRoot_ne_one_of_not_dvd_all` shows *every* one of those roots is `≠ 1`, hence every factor
is non-pretentious by the unconditional `ttNonPretentious_zOmegaNat`.  **That hope is false**, and
the obstruction is quantitative, not bookkeeping: `TTNonPretentious (zOmegaNat z) X L` is
certified only for `L ≤ (log X)^{ttExponent z}`, and

    ttExponent (depthRoot b h' i) → 0   as  i → ∞

(`tendsto_ttExponent_depthRoot`), because `depthRoot b h' i = e(h'/b^{i+1}) → 1`.  The `K`-point
statement has ONE cutoff `L` shared by all `K` factors, so the `∀ i` form would force
`κ ≤ inf_i ttExponent (depthRoot b h' i) = 0`, and no positive `κ` exists
(`no_uniform_ttExponent_depthRoot`).  Quantitatively `ttExponent (depthRoot b h' i) ≍ b^{-2i}`,
so at the diagonal level `K = D_N` even the threshold condition `L^{c_K} ≥ K+1` reads
`b^{-(2+θ)K} log log X ≳ log K`, i.e. `u^{-1-θ}(log u)^{-(2+θ)} ≳ log log u` — false.

So the `∃ i` in `KPointNoExcWith` is not slack: the deep digits of the Lambert constant are
quantitatively *almost* pretentious, and only the leading root carries usable
non-pretentiousness.  Recorded as refuted; do not re-attempt.
-/

open Filter Topology

namespace NormalNumbers

namespace CastingOut

/-! ### Every depth root is nontrivial -/

/-- **All the twist levels of a primitive `h'` have a nontrivial root**, not just the leading one:
`depthRoot b h' i = 1` would force `b^{i+1} ∣ h'`, hence `b ∣ h'`. -/
theorem depthRoot_ne_one_of_not_dvd_all {b : ℕ} (hb : 0 < b) {h' : ℤ}
    (hnd : ¬ ((b : ℤ) ∣ h')) (i : ℕ) : depthRoot b h' i ≠ 1 := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbpow : ((b : ℝ)) ^ (i + 1) ≠ 0 := by positivity
  rw [depthRoot]
  intro hone
  obtain ⟨M, hM⟩ := ee_eq_one_iff_int.1 hone
  have hreal : (h' : ℝ) = (M : ℝ) * (b : ℝ) ^ (i + 1) := by
    field_simp at hM
    linarith [hM]
  have hR : ((h' : ℤ) : ℝ) = ((M * (b : ℤ) ^ (i + 1) : ℤ) : ℝ) := by
    push_cast
    exact hreal
  have hZ : h' = M * (b : ℤ) ^ (i + 1) := by exact_mod_cast hR
  exact hnd ⟨M * (b : ℤ) ^ i, by rw [hZ]; ring⟩

/-! ### The input is monotone in its two constants -/

/-- **`KPointNoExcWith` is monotone: down in the saving, up in the constant.**  Both the two
hypotheses (`W ≤ L^{cK K}`, `hsh i ≤ L^{cK K}`) and the conclusion (`≤ CstK K · L^{-cK K}`) move
the right way when `cK` shrinks, because `L ≥ 1`.

Consequence for the ledger: asking for the geometric profile
`KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K` is exactly asking that the constants
`KPointNaturalCorrelationNoExc K` already provides existentially degrade no faster than
`c₀ b^{-θK}` and `exp((K+1)^m)`.  It is a *rate* hypothesis, not a new statement. -/
theorem kPointNoExcWith_mono {cK cK' CstK CstK' : ℕ → ℝ} {K : ℕ}
    (hc : cK' K ≤ cK K) (hC0 : 0 ≤ CstK K) (hC : CstK K ≤ CstK' K)
    (h : KPointNoExcWith cK CstK K) : KPointNoExcWith cK' CstK' K := by
  intro g hmult hbd X L hX hL hLlog hnp N hNl hNu W bb hsh hW hWL hshL hinj
  have hL0 : (0 : ℝ) < L := by linarith
  have hLmono : L ^ cK' K ≤ L ^ cK K := Real.rpow_le_rpow_of_exponent_le hL hc
  have hmain := h g hmult hbd X L hX hL hLlog hnp N hNl hNu W bb hsh hW
    (le_trans hWL hLmono) (fun i => le_trans (hshL i) hLmono) hinj
  refine le_trans hmain ?_
  have h1 : L ^ (-(cK K)) ≤ L ^ (-(cK' K)) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h2 : (0 : ℝ) < L ^ (-(cK K)) := Real.rpow_pos_of_pos hL0 _
  nlinarith [h1, h2, hC0, hC]

/-! ### The `∀ i` form, and why the C3 chain cannot use it -/

/-- `KPointNoExcWith` with the hypothesis `∃ i, TTNonPretentious (g i) X L` weakened to
`∀ i, TTNonPretentious (g i) X L`.  A strictly weaker `Prop` to assume. -/
def KPointNoExcAllWith (cK CstK : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ g : Fin K → ℕ → ℂ, (∀ i, IsCoprimeMultiplicativeNat (g i)) →
    (∀ i n, ‖g i n‖ ≤ 1) →
    ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X →
      (∀ i, TTNonPretentious (g i) X L) →
        ∀ N : ℕ, Real.sqrt X ≤ (N : ℝ) → (N : ℝ) ≤ X →
          ∀ (W b : ℕ) (hsh : Fin K → ℕ), 0 < W → (W : ℝ) ≤ L ^ cK K →
            (∀ i, (hsh i : ℝ) ≤ L ^ cK K) → Function.Injective hsh →
            ‖((W : ℝ) / (N : ℝ) : ℝ) •
                ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = b % W),
                  ∏ i : Fin K, g i (n + hsh i)‖
              ≤ CstK K * L ^ (-(cK K))

/-- Nothing is lost: the `∃ i` form implies the `∀ i` form (at `K > 0`). -/
theorem kPointNoExcAllWith_of_with {cK CstK : ℕ → ℝ} {K : ℕ} (hK : 0 < K)
    (h : KPointNoExcWith cK CstK K) : KPointNoExcAllWith cK CstK K :=
  fun g hmult hbd X L hX hL hLlog hnp N hNl hNu W bb hsh hW hWL hshL hinj =>
    h g hmult hbd X L hX hL hLlog ⟨⟨0, hK⟩, hnp ⟨0, hK⟩⟩ N hNl hNu W bb hsh hW hWL hshL hinj

/-- The depth roots converge to `1`: `depthRoot b h i = e(h/b^{i+1})` and `h/b^{i+1} → 0`. -/
theorem tendsto_depthRoot_one {b : ℕ} (hb : 2 ≤ b) (h : ℤ) :
    Tendsto (fun i : ℕ => depthRoot b h i) atTop (𝓝 1) := by
  have hbR : (1 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hgeo : Tendsto (fun i : ℕ => ((1 : ℝ) / (b : ℝ)) ^ i) atTop (𝓝 0) := by
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    rw [div_lt_one hb0]; linarith
  have hshift : Tendsto (fun i : ℕ => ((1 : ℝ) / (b : ℝ)) ^ (i + 1)) atTop (𝓝 0) :=
    hgeo.comp (Filter.tendsto_add_atTop_nat 1)
  have hx : Tendsto (fun i : ℕ => ((h : ℝ) / (b : ℝ) ^ (i + 1))) atTop (𝓝 0) := by
    have := hshift.const_mul ((h : ℝ))
    rw [mul_zero] at this
    refine this.congr fun i => ?_
    rw [div_pow, one_pow]
    ring
  have hxC : Tendsto (fun i : ℕ => (((h : ℝ) / (b : ℝ) ^ (i + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp hx
    simpa [Function.comp_def] using this
  have hee : Continuous ee := by
    unfold ee
    exact Complex.continuous_exp.comp (continuous_const.mul continuous_id)
  have h1 : ee (0 : ℂ) = 1 := by unfold ee; simp
  have := (hee.tendsto (0 : ℂ)).comp hxC
  rw [h1] at this
  exact this.congr fun i => rfl

/-- **The certified non-pretentiousness exponent of the depth roots collapses to `0`.**  This is
the quantitative obstruction to assuming only `KPointNoExcAllWith`: `ttNonPretentious_zOmegaNat`
certifies `zOmegaNat (depthRoot b h i)` only up to `L ≤ (log X)^{ttExponent (depthRoot b h i)}`,
and that exponent tends to `0`. -/
theorem tendsto_ttExponent_depthRoot {b : ℕ} (hb : 2 ≤ b) (h : ℤ) :
    Tendsto (fun i : ℕ => ttExponent (depthRoot b h i)) atTop (𝓝 0) := by
  have harg : Tendsto (fun i : ℕ => (depthRoot b h i).arg) atTop (𝓝 0) := by
    have hslit : (1 : ℂ) ∈ Complex.slitPlane := by
      left; norm_num
    have hc : ContinuousAt Complex.arg (1 : ℂ) := Complex.continuousAt_arg hslit
    have := hc.tendsto.comp (tendsto_depthRoot_one hb h)
    simpa [Function.comp_def] using this
  have hres : Tendsto (fun i : ℕ => resEps (depthRoot b h i)) atTop (𝓝 0) := by
    have := (harg.abs).div_const 2
    simpa [resEps] using this
  have heps : Tendsto (fun i : ℕ => ttEps (depthRoot b h i)) atTop (𝓝 0) := by
    have hmin : Tendsto (fun i : ℕ => min (resEps (depthRoot b h i)) (1 / 256 : ℝ))
        atTop (𝓝 (min (0 : ℝ) (1 / 256))) := hres.min tendsto_const_nhds
    rw [show min (0 : ℝ) (1 / 256) = 0 by norm_num] at hmin
    simpa [ttEps] using hmin
  have hcos : Tendsto (fun i : ℕ => 1 - Real.cos (ttEps (depthRoot b h i))) atTop (𝓝 0) := by
    have := (Real.continuous_cos.tendsto (0 : ℝ)).comp heps
    have h2 : Tendsto (fun i : ℕ => Real.cos (ttEps (depthRoot b h i))) atTop (𝓝 1) := by
      simpa [Function.comp_def] using this
    have h3 := tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ)) |>.sub h2
    simpa using h3
  have hlin : Tendsto
      (fun i : ℕ => 1 - (126 / 125 : ℝ) * (100 * ttEps (depthRoot b h i))) atTop (𝓝 1) := by
    have := (heps.const_mul (100 : ℝ)).const_mul ((126 : ℝ) / 125)
    rw [mul_zero, mul_zero] at this
    have h3 := tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ)) |>.sub this
    simpa using h3
  have := hcos.mul hlin
  rw [zero_mul] at this
  simpa [ttExponent] using this

/-- **REFUTED: no single positive exponent certifies every depth root.**  Hence a consumer of
`KPointNoExcAllWith` cannot discharge its `∀ i` non-pretentiousness hypothesis at a fixed `κ`,
and the `∃ i` of `KPointNoExcWith` is load-bearing.  (`C3MrtSlowSched`'s chain fixes
`κ = ttExponent (depthRoot b h' 0)` once and for all, for every `K`.) -/
theorem no_uniform_ttExponent_depthRoot {b : ℕ} (hb : 2 ≤ b) (h : ℤ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ i : ℕ, ttExponent (depthRoot b h i) < κ := by
  have := (tendsto_ttExponent_depthRoot hb h).eventually
    (eventually_lt_nhds (by simpa using hκ) : ∀ᶠ x : ℝ in 𝓝 0, x < κ)
  exact this.exists

#print axioms NormalNumbers.CastingOut.depthRoot_ne_one_of_not_dvd_all
#print axioms NormalNumbers.CastingOut.kPointNoExcWith_mono
#print axioms NormalNumbers.CastingOut.kPointNoExcAllWith_of_with
#print axioms NormalNumbers.CastingOut.tendsto_depthRoot_one
#print axioms NormalNumbers.CastingOut.tendsto_ttExponent_depthRoot
#print axioms NormalNumbers.CastingOut.no_uniform_ttExponent_depthRoot

end CastingOut

end NormalNumbers
