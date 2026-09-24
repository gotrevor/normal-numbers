import NormalNumbers.SwingC1Katai

/-!
# The crux in its second, route-independent form: Elliott at slowly growing depth

`SwingC1Katai.lean` pinned the crux to leaf (D) `PairDecorr` **along the Daboussi–Kátai route**,
at the cost of two named KNOWN theorems (`DelangeMean`, `KataiOrthogonality`).  This file states
the crux in a form that uses NO external theorem at all, so the two forms can be compared.

By `norm_fullMean_phase_sub_head` (lap 28) the Weyl mean of the orbit equals its depth-`L`
truncation up to `4π·depthBound b h M L`, and `depthBound_tendsto_zero_of_pow_div_atTop` says
that error vanishes along any schedule with `b^{L(M)} / log₂ M → ∞`, i.e. `L(M) ≍ log_b log₂ M`.
Hence:

`weylMean_tendsto_zero_of_head` : the Weyl mean vanishes as soon as the **head mean**

`headMean b h L M = mean_{n<M} e( h · Σ_{i<L} ω(n+1+i) b^{−1−i} )`

vanishes along one such schedule.  Unfolding the exponential, the head mean is

`mean_{n<M} Π_{i<L} f_i(n+1+i)`,  `f_i(m) = e(h b^{−1−i} ω(m))` multiplicative,

an **`L`-point correlation of bounded multiplicative functions at `L` consecutive shifts**, with
`L = L(M) → ∞` slowly.  At `L = 1` this is exactly Delange's theorem (`DelangeMean`, known).  For
`L ≥ 2` it is Elliott's conjecture territory, known unconditionally only in logarithmic density
and only for two points (Tao 2015, Tao–Teräväinen).

So the two named forms of the crux are
* `PairDecorr` — no multiplicative function, but needs `KataiOrthogonality` + `DelangeMean`;
* `headMean → 0` — needs nothing external, but is an `L`-point Elliott correlation.

Sorry-free.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- The depth-`L` head mean `mean_{n<M} e(h·Σ_{i<L} ω(n+1+i) b^{−1−i})`. -/
noncomputable def headMean (b : ℕ) (h : ℝ) (L M : ℕ) : ℂ :=
  fullMean (fun n => phase (h * ((omegaHead b L n : ℤ) : ℝ) / (b : ℝ) ^ L)) M

/-- **The crux, route-independently.**  If the depth-`L(M)` head mean vanishes along any schedule
whose truncation error vanishes, the Weyl mean of the orbit vanishes. -/
theorem weylMean_tendsto_zero_of_head (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun M => (b : ℝ) ^ (L M) / ((Nat.log 2 (M + L M) : ℝ) + 1)) atTop atTop)
    (hH : Tendsto (fun M => headMean b h (L M) M) atTop (𝓝 0)) :
    Tendsto (fun M => weylMean b h M) atTop (𝓝 0) := by
  have hD : Tendsto (fun M => depthBound b h M (L M)) atTop (𝓝 0) :=
    depthBound_tendsto_zero_of_pow_div_atTop b hb h L hL
  have h2pi : Tendsto (fun M => 2 * Real.pi * depthBound b h M (L M)) atTop (𝓝 0) := by
    simpa using hD.const_mul (2 * Real.pi)
  have hb4 : Tendsto (fun M => 4 * Real.pi * depthBound b h M (L M)) atTop (𝓝 0) := by
    simpa using hD.const_mul (4 * Real.pi)
  have hev : ∀ᶠ M in atTop, 2 * Real.pi * depthBound b h M (L M) ≤ 1 :=
    h2pi.eventually_le_const (by norm_num)
  have hdiff : Tendsto (fun M => weylMean b h M - headMean b h (L M) M) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall fun M => norm_nonneg _) ?_ hb4)
    filter_upwards [hev] with M hM
    exact norm_fullMean_phase_sub_head b hb h M (L M) hM
  have hfin := hdiff.add hH
  rw [add_zero] at hfin
  exact hfin.congr fun M => by ring

end NormalNumbers.CastingOut
