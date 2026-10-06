/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.QSpanNormal
import NormalNumbers.DecayAeNormal

/-!
# What the digits of a rational combination can look like

Campaign `KICKOFF-2026-10-05-qspan.md`.  The digits of `(a x + c y)/q` are read off from the joint
digit stream of `(x, y)` through bounded carries and a finite remainder, and by Wall
(`isNormal_rat_mul_add`) the divisor `q` never matters for normality.  Frozen here:

* `span_jointDim_budget`: a normal combination forces joint finite-state dimension `≥ 1/2`
  (entropy `log b` out of `2 log b`).  Implies `QSpan.span_dimension_budget` by subadditivity.
* `isNormal_span_of_jointNormal`: a jointly normal pair has every nonzero combination normal.
* `ae_isNormal_combo_iff`: for independent i.i.d. digits, `a x + c y` is a.e. normal iff every
  nonzero frequency `h` meets a zero of a digit polynomial, `φ_X(a h / bⁱ) · φ_Y(c h / bⁱ) = 0`
  for some `i ≥ 1` (the stationary law of `bⁿ(a x + c y) mod 1` has Fourier coefficients
  `∏ᵢ φ_X(a h/bⁱ) φ_Y(c h/bⁱ)`; a.e. orbits are generic for it).  Otherwise a.e. not normal.
* `ae_not_qSpanNormal_fiveDigits` with `ae_jointDim_fiveDigits`: digits uniform in `{0,…,4}`
  give joint dimension `log 25 / log 100 ≈ 0.70 > 1/2`, yet no combination is normal: `h = 5^N`
  defeats every `(a, c)`.  So the entropy budget is necessary, not sufficient.

Evidence: `experiments/qspan_digit_probe.py` (exact `ν̂` product and empirical coefficients;
`4x + 5y` has `|ν̂(25)| ≈ 0.0113` measured, `≈ 0.012` by hand).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace NormalNumbers.QSpanCriterion

open QSpan FiniteState

/-- The joint base-`b` digit stream of `(x, y)`, letters `Fin (b * b)`. -/
noncomputable def digitPair (b : ℕ) (hb : 0 < b) (x y : ℝ) : ℕ → Fin (b * b) :=
  fun i => finProdFinEquiv (digitSeq b hb x i, digitSeq b hb y i)

/-- **Joint entropy budget.**  Confidence 85%.  English proof: `QSpan.span_dimension_budget`,
stopped before the subadditivity step. -/
theorem span_jointDim_budget (b : ℕ) (hb : 2 ≤ b) (x y : ℝ) (c₁ c₂ : ℚ)
    (hz : IsNormal b ((c₁ : ℝ) * x + c₂ * y)) :
    1 / 2 ≤ fsDim (digitPair b (by omega) x y) := by
  sorry

/-- **Jointly normal ⇒ the whole span is normal.**  Confidence 95%.  English proof: joint
normality is equidistribution of `(bⁿx, bⁿy)` in `𝕋²` (b-adic boxes); `bⁿ(a x + c y) mod 1` is the
image under `(u, v) ↦ a u + c v`, which pushes Lebesgue to Lebesgue for `(a, c) ≠ 0`; rational
coefficients by Wall. -/
theorem isNormal_span_of_jointNormal (b : ℕ) (hb : 2 ≤ b) (x y : ℝ)
    (hJ : IsNormalSequence (b * b) (fun i => (digitPair b (by omega) x y i : ℕ)))
    (c₁ c₂ : ℚ) (hne : c₁ ≠ 0 ∨ c₂ ≠ 0) : IsNormal b ((c₁ : ℝ) * x + c₂ * y) := by
  sorry

/-- Independent uniform letters of `Fin m × Fin m`. -/
noncomputable def pairs (m : ℕ) [NeZero m] : Measure (ℕ → Fin m × Fin m) :=
  Measure.infinitePi (fun _ => (PMF.uniformOfFintype (Fin m × Fin m)).toMeasure)

/-- The real with base-`b` digits `dX (ω i).1`. -/
noncomputable def realX {m : ℕ} (b : ℕ) (dX : Fin m → ℕ) (ω : ℕ → Fin m × Fin m) : ℝ :=
  ∑' i, (dX (ω i).1 : ℝ) / (b : ℝ) ^ (i + 1)

/-- The real with base-`b` digits `dY (ω i).2`. -/
noncomputable def realY {m : ℕ} (b : ℕ) (dY : Fin m → ℕ) (ω : ℕ → Fin m × Fin m) : ℝ :=
  ∑' i, (dY (ω i).2 : ℝ) / (b : ℝ) ^ (i + 1)

/-- Digit polynomial `φ(t) = (1/m) Σ_j e(t · d j)`. -/
noncomputable def digitPoly {m : ℕ} (d : Fin m → ℕ) (t : ℝ) : ℂ :=
  (∑ j, Complex.exp (2 * Real.pi * Complex.I * (t * d j))) / m


/-! ### Leaves of the Fourier-zero criterion

The proof runs through one fixed law: `bᵏ · combo ω ≡ combo (shift^k ω) (mod 1)` (integer
coefficients), the Weyl means of the orbit converge a.e. to `nuHat h = 𝔼 e(h · combo)`
(`ae_tendsto_nuHat`), and `nuHat h` is the product of the digit polynomials, which vanishes iff a
factor does (`nuHat_eq_zero_iff`).  Weyl's criterion in both directions closes the loop. -/

open DecayAeNormal in
/-- The integer combination `a X + c Y`. -/
noncomputable def combo {m : ℕ} (b : ℕ) (dX dY : Fin m → ℕ) (a c : ℤ)
    (ω : ℕ → Fin m × Fin m) : ℝ :=
  a * realX b dX ω + c * realY b dY ω

open DecayAeNormal in
/-- The `h`-th Fourier coefficient of the law of `combo`. -/
noncomputable def nuHat {m : ℕ} [NeZero m] (b : ℕ) (dX dY : Fin m → ℕ) (a c : ℤ) (h : ℤ) : ℂ :=
  ∫ ω, ee (h * combo b dX dY a c ω) ∂pairs m

open DecayAeNormal in
/-- The Weyl mean of the `×b` orbit at frequency `h`, raw phases. -/
noncomputable def weylAvg (b : ℕ) (z : ℝ) (h : ℤ) (N : ℕ) : ℂ :=
  (∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * z)) / N

open DecayAeNormal in
/-- The Fourier mean of the orbit is the raw-phase Weyl mean. -/
theorem fourierMean_orbit_eq (b : ℕ) (z : ℝ) (h : ℤ) (N : ℕ) :
    fourierMean (orbit b z) h N = weylAvg b z h N := by
  unfold fourierMean weylAvg
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have := ee_int_mul_fract h (z * (b : ℝ) ^ k)
  unfold ee at this
  unfold orbit
  push_cast at this ⊢
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * ((Int.fract (z * (b : ℝ) ^ k) : ℝ) : ℂ)
      = 2 * Real.pi * Complex.I * ((h : ℂ) * ((Int.fract (z * (b : ℝ) ^ k) : ℝ) : ℂ)) by ring, this]
  unfold ee; push_cast; ring_nf

open DecayAeNormal in
/-- Lipschitz bound for `e(·)`. -/
theorem norm_ee_sub_le (s t : ℝ) : ‖ee s - ee t‖ ≤ 2 * Real.pi * |s - t| := by
  have : ee s - ee t = ee t * (Complex.exp (Complex.I * ((2 * Real.pi * (s - t) : ℝ) : ℂ)) - 1) := by
    unfold ee; rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [this, norm_mul, norm_ee, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]

open DecayAeNormal in
/-- Roots of unity `e(h j / M)` sum to zero when `M > |h| > 0`. -/
theorem sum_ee_root (h : ℤ) (hh : h ≠ 0) (M : ℕ) (hM : (h.natAbs : ℕ) < M) :
    ∑ j ∈ Finset.range M, ee (h * j / M) = 0 := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * h / M) with hz
  have hpow : ∀ j : ℕ, ee (h * j / M) = z ^ j := fun j => by
    rw [hz, ← Complex.exp_nat_mul]; unfold ee; congr 1; push_cast; ring
  have hzM : z ^ M = 1 := by
    rw [hz, ← Complex.exp_nat_mul]
    rw [show (M : ℂ) * (2 * Real.pi * Complex.I * h / M) = h * (2 * Real.pi * Complex.I) by
      field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I h
  have hz1 : z ≠ 1 := by
    intro h1
    rw [hz, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hn' : (h : ℂ) = n * M := by
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      field_simp at hn
      rw [hn]; ring
    have : h = n * M := by exact_mod_cast hn'
    have : h.natAbs = n.natAbs * M := by rw [this, Int.natAbs_mul]; simp
    rcases Nat.eq_zero_or_pos n.natAbs with h0 | h0
    · rw [h0, zero_mul] at this; omega
    · have : M ≤ n.natAbs * M := Nat.le_mul_of_pos_left M h0
      omega
  rw [Finset.sum_congr rfl fun j _ => hpow j, geom_sum_eq hz1, hzM, sub_self, zero_div]

open DecayAeNormal in
/-- Equidistribution ⇒ vanishing Weyl means of `u`. -/
theorem weyl_of_equidistributed (u : ℕ → ℝ) (hu : ∀ k, u k ∈ Set.Ico (0 : ℝ) 1)
    (he : Equidistributed u) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, ee (h * u k)) / N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℕ := ⌈4 * Real.pi * |(h : ℝ)| / ε⌉₊ + h.natAbs + 1 with hMdef
  have hMh : h.natAbs < M := by omega
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMerr : 2 * Real.pi * |(h : ℝ)| / M ≤ ε / 2 := by
    rw [div_le_iff₀ hMR]
    have h1 : 4 * Real.pi * |(h : ℝ)| / ε ≤ M := by
      refine (Nat.le_ceil _).trans ?_
      rw [hMdef]; push_cast; linarith [(Nat.cast_nonneg h.natAbs : (0:ℝ) ≤ h.natAbs)]
    rw [div_le_iff₀ hε] at h1
    linarith
  -- block index of a point
  set g : ℕ → ℕ := fun k => ⌊(M : ℝ) * u k⌋₊ with hg
  have hgM : ∀ k, g k < M := fun k => by
    have : (M : ℝ) * u k < M := by nlinarith [(hu k).2]
    exact_mod_cast (Nat.floor_lt (by nlinarith [(hu k).1])).2 this
  have hmem : ∀ k (j : ℕ), u k ∈ Set.Ico ((j : ℝ) / M) (((j : ℝ) + 1) / M) ↔ g k = j := fun k j => by
    show _ ↔ ⌊(M : ℝ) * u k⌋₊ = j
    rw [Set.mem_Ico, div_le_iff₀ hMR, lt_div_iff₀ hMR, Nat.floor_eq_iff (by nlinarith [(hu k).1])]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  -- the main term
  set A : ℕ → ℂ := fun N => ∑ j ∈ Finset.range M,
    ((visitCount u (j / M) ((j + 1) / M) N : ℝ) / N : ℝ) * ee (h * j / M) with hA
  have hAlim : Tendsto A atTop (𝓝 0) := by
    have : Tendsto A atTop (𝓝 (∑ j ∈ Finset.range M, ((1 / M : ℝ) : ℂ) * ee (h * j / M))) := by
      refine tendsto_finsetSum _ fun j hj => ?_
      refine Tendsto.mul_const _ ?_
      refine (Complex.continuous_ofReal.tendsto _).comp ?_
      have hj' : j < M := Finset.mem_range.1 hj
      have := he (j / M) ((j + 1) / M) (by positivity)
        (by rw [div_le_div_iff_of_pos_right hMR]; linarith)
        (by rw [div_le_one hMR]; exact_mod_cast hj')
      convert this using 2
      field_simp; ring
    rwa [← Finset.mul_sum, sum_ee_root h hh M hMh, mul_zero] at this
  have hfib : ∀ N : ℕ, (∑ k ∈ Finset.range N, ee (h * (g k : ℝ) / M))
      = ∑ j ∈ Finset.range M, (visitCount u (j / M) ((j + 1) / M) N : ℂ) * ee (h * j / M) := by
    intro N
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range N) (t := Finset.range M) (g := g)
      (fun k _ => Finset.mem_range.2 (hgM k))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]),
      Finset.sum_const, nsmul_eq_mul, visitCount]
    congr 3
    exact Finset.filter_congr fun k _ => (hmem k j).symm
  rcases (Metric.tendsto_atTop.1 hAlim) (ε / 2) (by linarith) with ⟨N₀, hN₀⟩
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hAN := hN₀ N (le_of_max_le_left hN)
  rw [dist_zero_right] at hAN ⊢
  have hAN' : A N = (∑ k ∈ Finset.range N, ee (h * (g k : ℝ) / M)) / N := by
    rw [hfib, Finset.sum_div, hA]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  have hdiff : ∀ k, ‖ee (h * u k) - ee (h * (g k : ℝ) / M)‖ ≤ 2 * Real.pi * |(h : ℝ)| / M := by
    intro k
    refine (norm_ee_sub_le _ _).trans ?_
    have hfl := (hmem k (g k)).2 rfl
    rw [Set.mem_Ico, div_le_iff₀ hMR, lt_div_iff₀ hMR] at hfl
    have h1 : |u k - (g k : ℝ) / M| ≤ 1 / M := by
      rw [abs_le]; constructor
      · have : (g k : ℝ) / M ≤ u k := by rw [div_le_iff₀ hMR]; linarith
        have : 0 ≤ 1 / (M : ℝ) := by positivity
        linarith
      · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hMR]; linarith
    rw [show (h : ℝ) * u k - h * (g k : ℝ) / M = h * (u k - (g k : ℝ) / M) by ring, abs_mul,
      mul_div_assoc]
    have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (h : ℝ))
    rw [mul_one_div] at this
    have hp : 0 ≤ 2 * Real.pi := by positivity
    nlinarith
  have hsum : ‖∑ k ∈ Finset.range N, (ee (h * u k) - ee (h * (g k : ℝ) / M))‖
      ≤ N * (2 * Real.pi * |(h : ℝ)| / M) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hdiff k).trans ?_
    simp
  have hsplit : (∑ k ∈ Finset.range N, ee (h * u k)) / N
      = (∑ k ∈ Finset.range N, (ee (h * u k) - ee (h * (g k : ℝ) / M))) / N + A N := by
    rw [hAN', Finset.sum_sub_distrib]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans_lt ?_
  have : ‖(∑ k ∈ Finset.range N, (ee (h * u k) - ee (h * (g k : ℝ) / M))) / (N : ℂ)‖
      ≤ 2 * Real.pi * |(h : ℝ)| / M := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hNpos]
    linarith
  linarith

/-- **Leaf (Weyl, easy direction).**  A normal number has vanishing Weyl means.  Confidence 99%
(equidistribution ⇒ Riemann sums of `e(h·)` against step functions). -/
theorem weylAvg_tendsto_zero_of_isNormal (b : ℕ) (hb : 2 ≤ b) (z : ℝ) (hz : IsNormal b z)
    (h : ℤ) (hh : h ≠ 0) : Tendsto (weylAvg b z h) atTop (nhds 0) := by
  rw [isNormal_iff_equidistributed_orbit b hb] at hz
  refine (weyl_of_equidistributed _ (fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) hz h
    hh).congr fun N => ?_
  rw [← fourierMean_orbit_eq, fourierMean]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold DecayAeNormal.ee orbit; push_cast; ring_nf

/-- **Leaf (Weyl, wired direction).**  From `equidistributed_of_weyl` and Wall.  Confidence 99%. -/
theorem isNormal_of_weylAvg (b : ℕ) (hb : 2 ≤ b) (z : ℝ)
    (hW : ∀ h : ℤ, h ≠ 0 → Tendsto (weylAvg b z h) atTop (nhds 0)) : IsNormal b z := by
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_weyl _ (fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) ?_
  intro h hh
  exact (hW h hh).congr fun N => (fourierMean_orbit_eq b z h N).symm

section Generic
variable {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-! ### Genericity for integer-digit expansions on a Bernoulli shift -/

/-- Base-`b` expansion with integer "digits" `T (ω j)`. -/
noncomputable def digS (b : ℕ) (T : α → ℤ) (ω : ℕ → α) : ℝ :=
  ∑' j, (T (ω j) : ℝ) / (b : ℝ) ^ (j + 1)

/-- Shift by `k`. -/
def shiftK (k : ℕ) (ω : ℕ → α) : ℕ → α := fun j => ω (k + j)

end Generic

section Generic
variable {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- Truncation of `digS` to its first `K` terms. -/
noncomputable def digSK (b : ℕ) (T : α → ℤ) (K : ℕ) (ω : ℕ → α) : ℝ :=
  ∑ j ∈ Finset.range K, (T (ω j) : ℝ) / (b : ℝ) ^ (j + 1)

/-- A digit is bounded by the total digit mass. -/
theorem abs_T_le (T : α → ℤ) (a : α) : |(T a : ℝ)| ≤ ∑ a, |(T a : ℝ)| :=
  Finset.single_le_sum (f := fun a => |(T a : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)

/-- The expansion converges. -/
theorem summable_digS (b : ℕ) (hb : 2 ≤ b) (T : α → ℤ) (ω : ℕ → α) :
    Summable fun j => (T (ω j) : ℝ) / (b : ℝ) ^ (j + 1) := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  refine Summable.of_norm_bounded (g := fun j => (∑ a, |(T a : ℝ)|) * ((b : ℝ)⁻¹ ^ j)) ?_ ?_
  · exact (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb')).mul_left _
  · intro j
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < (b:ℝ) ^ (j+1)),
      div_le_iff₀ (by positivity), pow_succ, inv_pow]
    have := abs_T_le T (ω j)
    have hbj : (0:ℝ) < (b:ℝ)^j := by positivity
    calc |(T (ω j) : ℝ)| ≤ (∑ a, |(T a : ℝ)|) * 1 := by linarith
      _ ≤ (∑ a, |(T a : ℝ)|) * b := by
        gcongr
      _ = (∑ a, |(T a : ℝ)|) * ((b:ℝ) ^ j)⁻¹ * ((b:ℝ) ^ j * b) := by field_simp

open DecayAeNormal in
/-- **Leaf G1.**  Integer digits: `e(h bᵏ S(ω)) = e(h S(σᵏ ω))`. -/
theorem ee_pow_mul_digS (b : ℕ) (hb : 2 ≤ b) (T : α → ℤ) (h : ℤ) (k : ℕ) (ω : ℕ → α) :
    ee (h * (b : ℝ) ^ k * digS b T ω) = ee (h * digS b T (shiftK k ω)) := by
  have hs := summable_digS b hb T ω
  have hb0 : (b:ℝ) ≠ 0 := by positivity
  have key : (b : ℝ) ^ k * digS b T ω
      = ((∑ j ∈ Finset.range k, T (ω j) * (b : ℤ) ^ (k - 1 - j) : ℤ) : ℝ) + digS b T (shiftK k ω) := by
    unfold digS
    rw [← hs.sum_add_tsum_nat_add k, mul_add, Finset.mul_sum, ← tsum_mul_left]
    push_cast
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj := Finset.mem_range.1 hj
      have hk : (b:ℝ)^k = (b:ℝ)^(k-1-j) * (b:ℝ)^(j+1) := by rw [← pow_add]; congr 1; omega
      rw [hk]; field_simp
    · congr 1; funext j
      simp only [shiftK]
      rw [show j + k + 1 = k + (j + 1) by ring, pow_add, add_comm j k]
      field_simp
  rw [mul_assoc, key, mul_add, ee_add]
  have : ee (h * ((∑ j ∈ Finset.range k, T (ω j) * (b : ℤ) ^ (k - 1 - j) : ℤ) : ℝ)) = 1 := by
    unfold ee
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (((h * ((∑ j ∈ Finset.range k, T (ω j) * (b : ℤ) ^ (k - 1 - j) : ℤ) : ℝ)) : ℝ) : ℂ)
        = ((h * ∑ j ∈ Finset.range k, T (ω j) * (b : ℤ) ^ (k - 1 - j) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [this, one_mul]

/-- **Leaf G2.**  Truncation error. -/
theorem abs_digS_sub_digSK (b : ℕ) (hb : 2 ≤ b) (T : α → ℤ) (K : ℕ) (ω : ℕ → α) :
    |digS b T ω - digSK b T K ω| ≤ (∑ a, |(T a : ℝ)|) / (b : ℝ) ^ K := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  set B := ∑ a, |(T a : ℝ)|
  have hs := summable_digS b hb T ω
  unfold digS digSK
  rw [← hs.sum_add_tsum_nat_add K, add_sub_cancel_left]
  have hs2 : Summable fun j => B / (b:ℝ) ^ (j + K + 1) := by
    have : (fun j => B / (b:ℝ) ^ (j + K + 1)) = fun j => (B / (b:ℝ)^(K+1)) * ((b:ℝ)⁻¹ ^ j) := by
      funext j; rw [inv_pow, pow_add, pow_add]; field_simp; ring
    rw [this]
    exact (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb')).mul_left _
  calc |∑' j, (T (ω (j + K)) : ℝ) / (b:ℝ) ^ (j + K + 1)|
      ≤ ∑' j, B / (b:ℝ) ^ (j + K + 1) := by
        refine (norm_tsum_le_tsum_norm ((summable_nat_add_iff K).2 hs).norm).trans ?_
        refine Summable.tsum_le_tsum (fun j => ?_) ((summable_nat_add_iff K).2 hs).norm hs2
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < (b:ℝ) ^ (j + K + 1))]
        gcongr
        exact abs_T_le T _
    _ = B / (b:ℝ)^(K+1) * (1 - (b:ℝ)⁻¹)⁻¹ := by
        have : (fun j => B / (b:ℝ) ^ (j + K + 1)) = fun j => (B / (b:ℝ)^(K+1)) * ((b:ℝ)⁻¹ ^ j) := by
          funext j; rw [inv_pow, pow_add, pow_add]; field_simp; ring
        rw [this, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb')]
    _ ≤ B / (b:ℝ) ^ K := by
        have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
        rw [show (1 - (b:ℝ)⁻¹)⁻¹ = b / (b - 1) by field_simp, pow_succ]
        rw [div_mul_div_comm, div_le_div_iff₀ (by have : (0:ℝ) < b - 1 := by linarith
                                                  positivity) (by positivity)]
        have hbK : (0:ℝ) < (b:ℝ)^K := by positivity
        have : B * b * (b:ℝ)^K ≤ B * ((b:ℝ)^K * b * (b - 1)) := by
          have hb2 : (2:ℝ) ≤ b := by exact_mod_cast hb
          have : (b:ℝ) ≤ b * (b - 1) := by nlinarith
          calc B * b * (b:ℝ)^K = B * (b:ℝ)^K * b := by ring
            _ ≤ B * (b:ℝ)^K * (b * (b-1)) := by gcongr
            _ = _ := by ring
        linarith

/-- **Leaf G3.**  The shift preserves the product measure. -/
theorem measurePreserving_shiftK (P : Measure α) [IsProbabilityMeasure P] (k : ℕ) :
    MeasurePreserving (shiftK (α := α) k) (Measure.infinitePi fun _ : ℕ => P)
      (Measure.infinitePi fun _ : ℕ => P) := by
  classical
  have hm : Measurable (shiftK (α := α) k) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (k + j)
  refine ⟨hm, ?_⟩
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hpre : shiftK k ⁻¹' (Set.pi (s : Set ℕ) t)
      = Set.pi ((s.image (k + ·) : Finset ℕ) : Set ℕ) (fun i => t (i - k)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_image, shiftK]
    constructor
    · rintro h i ⟨j, hj, rfl⟩
      simpa using h j hj
    · intro h j hj
      simpa using h (k + j) ⟨j, hj, rfl⟩
  rw [hpre]
  have := Measure.infinitePi_pi (μ := fun _ : ℕ => P) (s := s.image (k + ·))
    (t := fun i => t (i - k)) (fun i _ => ht _)
  rw [this, Finset.prod_image (fun a _ b _ hab => by simpa using hab)]
  simp

open DecayAeNormal in
/-- **Leaf G4.**  Windows `[k, k+K)` and `[l, l+K)` are disjoint for `k + K ≤ l`: independence. -/
theorem integral_ee_digSK_indep (P : Measure α) [IsProbabilityMeasure P] (b : ℕ) (T : α → ℤ)
    (h : ℤ) (K k l : ℕ) (hkl : k + K ≤ l) :
    ∫ ω, ee (h * digSK b T K (shiftK k ω)) * (starRingEnd ℂ) (ee (h * digSK b T K (shiftK l ω)))
        ∂Measure.infinitePi (fun _ : ℕ => P) =
      (∫ ω, ee (h * digSK b T K ω) ∂Measure.infinitePi (fun _ : ℕ => P)) *
        (starRingEnd ℂ) (∫ ω, ee (h * digSK b T K ω) ∂Measure.infinitePi (fun _ : ℕ => P)) := by
  sorry

end Generic

/-- **Leaf G5a.**  `K`-dependent unit-bounded sequence with constant mean: linear second moment. -/
theorem second_moment_le_of_indep {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (z : ℕ → Ω → ℂ) (hzm : ∀ k, Measurable (z k))
    (hz1 : ∀ k ω, ‖z k ω‖ ≤ 1) (c : ℂ) (hc : ∀ k, ∫ ω, z k ω ∂μ = c) (K : ℕ)
    (hind : ∀ k l, k + K ≤ l → ∫ ω, z k ω * (starRingEnd ℂ) (z l ω) ∂μ = c * (starRingEnd ℂ) c)
    (N : ℕ) : ∫ ω, ‖∑ k ∈ Finset.range N, (z k ω - c)‖ ^ 2 ∂μ ≤ (8 * K + 4) * N := by
  set w : ℕ → Ω → ℂ := fun k ω => z k ω - c with hw
  have hwm : ∀ k, Measurable (w k) := fun k => (hzm k).sub_const _
  have hc1 : ‖c‖ ≤ 1 := by
    rw [← hc 0]
    refine (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall (hz1 0))).trans ?_
    simp
  have hw2 : ∀ k ω, ‖w k ω‖ ≤ 2 := fun k ω =>
    (norm_sub_le _ _).trans (by linarith [hz1 k ω])
  have hint : ∀ k l, Integrable (fun ω => w k ω * (starRingEnd ℂ) (w l ω)) μ := fun k l =>
    Integrable.of_bound ((hwm k).mul (Complex.continuous_conj.measurable.comp (hwm l))).aestronglyMeasurable 4
      (Eventually.of_forall fun ω => by
        rw [norm_mul, Complex.norm_conj]
        nlinarith [hw2 k ω, hw2 l ω, norm_nonneg (w k ω), norm_nonneg (w l ω)])
  have hzint : ∀ k, Integrable (z k) μ := fun k =>
    Integrable.of_bound (hzm k).aestronglyMeasurable 1 (Eventually.of_forall (hz1 k))
  -- covariance vanishes far from the diagonal
  have hfar : ∀ k l, k + K ≤ l → ∫ ω, w k ω * (starRingEnd ℂ) (w l ω) ∂μ = 0 := by
    intro k l hkl
    have e : ∀ ω, w k ω * (starRingEnd ℂ) (w l ω)
        = z k ω * (starRingEnd ℂ) (z l ω) - (starRingEnd ℂ) c * z k ω
          - c * (starRingEnd ℂ) (z l ω) + c * (starRingEnd ℂ) c := fun ω => by
      simp only [hw, map_sub]; ring
    simp_rw [e]
    have i1 : Integrable (fun ω => z k ω * (starRingEnd ℂ) (z l ω)) μ :=
      Integrable.of_bound ((hzm k).mul (Complex.continuous_conj.measurable.comp (hzm l))).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by
          rw [norm_mul, Complex.norm_conj]
          nlinarith [hz1 k ω, hz1 l ω, norm_nonneg (z k ω), norm_nonneg (z l ω)])
    have i2 : Integrable (fun ω => (starRingEnd ℂ) (z l ω)) μ :=
      Integrable.of_bound (Complex.continuous_conj.measurable.comp (hzm l)).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by rw [Complex.norm_conj]; exact hz1 l ω)
    have i3 : Integrable (fun ω => (starRingEnd ℂ) c * z k ω) μ := (hzint k).const_mul _
    have i4 : Integrable (fun ω => c * (starRingEnd ℂ) (z l ω)) μ := i2.const_mul _
    have i6 : Integrable (fun ω => z k ω * (starRingEnd ℂ) (z l ω) - (starRingEnd ℂ) c * z k ω) μ :=
      i1.sub i3
    have i5 : Integrable (fun ω => z k ω * (starRingEnd ℂ) (z l ω) - (starRingEnd ℂ) c * z k ω
        - c * (starRingEnd ℂ) (z l ω)) μ := i6.sub i4
    rw [integral_add i5 (integrable_const _),
      integral_sub i6 i4, integral_sub i1 i3, integral_const_mul, integral_const_mul,
      integral_conj, hc, hc, hind k l hkl]
    simp; ring
  have hfar' : ∀ k l, l + K ≤ k → ∫ ω, w k ω * (starRingEnd ℂ) (w l ω) ∂μ = 0 := by
    intro k l hkl
    have := hfar l k hkl
    have e : (fun ω => w k ω * (starRingEnd ℂ) (w l ω))
        = fun ω => (starRingEnd ℂ) (w l ω * (starRingEnd ℂ) (w k ω)) := by
      funext ω; simp [mul_comm]
    rw [e, integral_conj, this, map_zero]
  have hnear : ∀ k l, ‖∫ ω, w k ω * (starRingEnd ℂ) (w l ω) ∂μ‖ ≤ 4 := fun k l => by
    refine (norm_integral_le_of_norm_le_const (C := 4) (Eventually.of_forall fun ω => ?_)).trans ?_
    · rw [norm_mul, Complex.norm_conj]
      nlinarith [hw2 k ω, hw2 l ω, norm_nonneg (w k ω), norm_nonneg (w l ω)]
    · simp
  -- expand the square
  have hsq : ∀ ω, ‖∑ k ∈ Finset.range N, w k ω‖ ^ 2
      = (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, w k ω * (starRingEnd ℂ) (w l ω)).re := by
    intro ω
    rw [← Finset.sum_mul_sum, ← map_sum, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hdi : ∀ ω, (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, w k ω * (starRingEnd ℂ) (w l ω))
      = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, w k ω * (starRingEnd ℂ) (w l ω) := fun _ => rfl
  have hI : Integrable (fun ω => ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
      w k ω * (starRingEnd ℂ) (w l ω)) μ :=
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => hint k l
  calc ∫ ω, ‖∑ k ∈ Finset.range N, (z k ω - c)‖ ^ 2 ∂μ
      = ∫ ω, RCLike.re (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          w k ω * (starRingEnd ℂ) (w l ω)) ∂μ := integral_congr_ae (Eventually.of_forall fun ω => hsq ω)
    _ = RCLike.re (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          ∫ ω, w k ω * (starRingEnd ℂ) (w l ω) ∂μ) := by
        rw [integral_re hI, integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => hint k l]
        congr 1
        exact Finset.sum_congr rfl fun k _ => integral_finset_sum _ fun l _ => hint k l
    _ ≤ ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, ‖∫ ω, w k ω * (starRingEnd ℂ) (w l ω) ∂μ‖ := by
        refine (RCLike.re_le_norm _).trans ?_
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _)
    _ ≤ ∑ k ∈ Finset.range N, (8 * K + 4 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← Finset.sum_filter_of_ne (p := fun l => l ∈ Finset.Ico (k + 1 - K) (k + K))]
        · calc _ ≤ ∑ l ∈ (Finset.range N).filter (fun l => l ∈ Finset.Ico (k + 1 - K) (k + K)),
                  (4 : ℝ) := Finset.sum_le_sum fun l _ => hnear k l
            _ ≤ ((Finset.Ico (k + 1 - K) (k + K)).card : ℝ) * 4 := by
                rw [Finset.sum_const, nsmul_eq_mul]
                gcongr
                exact fun l hl => (Finset.mem_filter.1 hl).2
            _ ≤ 8 * K + 4 := by
                rw [Nat.card_Ico]
                have : k + K - (k + 1 - K) ≤ 2 * K := by omega
                have : ((k + K - (k + 1 - K) : ℕ) : ℝ) ≤ 2 * K := by exact_mod_cast this
                linarith
        · intro l _ hne
          by_contra hl
          apply hl
          rw [Finset.mem_Ico]
          by_contra hout
          rcases not_and_or.1 hout with h1 | h1
          · exact hne (by rw [hfar' k l (by omega), norm_zero])
          · exact hne (by rw [hfar k l (by omega), norm_zero])
    _ = (8 * K + 4) * N := by simp; ring

/-- **Leaf G5b.**  Linear second moment ⇒ a.e. convergence of the means (`j²` subsequence and
interpolation, as in `DecayAeNormal.ae_tendsto_weyl`). -/
theorem ae_tendsto_of_second_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (z : ℕ → Ω → ℂ) (hzm : ∀ k, Measurable (z k))
    (hz1 : ∀ k ω, ‖z k ω‖ ≤ 1) (c : ℂ) (hc1 : ‖c‖ ≤ 1) (C : ℝ)
    (hm : ∀ N, ∫ ω, ‖∑ k ∈ Finset.range N, (z k ω - c)‖ ^ 2 ∂μ ≤ C * N) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, z k ω) / N) atTop (𝓝 c) := by
  set K : ℝ := |C| with hKdef
  have hK : 0 ≤ K := abs_nonneg _
  set S : ℕ → Ω → ℂ := fun N ω => ∑ k ∈ Finset.range N, (z k ω - c) with hSdef
  have hSm : ∀ N, Measurable (S N) := fun N =>
    Finset.measurable_sum _ fun k _ => (hzm k).sub_const _
  have hSb : ∀ N ω, ‖S N ω‖ ≤ 2 * N := fun N ω => by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => (norm_sub_le _ _).trans (add_le_add (hz1 k ω) hc1)).trans ?_
    simp; linarith
  set f : ℕ → Ω → ℝ := fun j ω => ‖S ((j + 1) ^ 2) ω‖ ^ 2 / (((j + 1) ^ 2 : ℕ) : ℝ) ^ 2
    with hfdef
  have hf0 : ∀ j ω, 0 ≤ f j ω := fun j ω => by positivity
  have hfm : ∀ j, Measurable (f j) := fun j =>
    (((hSm _).norm.pow_const 2).div_const _)
  have hfi : ∀ j, Integrable (f j) μ := fun j =>
    Integrable.of_bound (hfm j).aestronglyMeasurable 4 (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hf0 j ω)]
      have hpos : (0 : ℝ) < (((j + 1) ^ 2 : ℕ) : ℝ) := by positivity
      rw [div_le_iff₀ (by positivity)]
      have := pow_le_pow_left₀ (norm_nonneg _) (hSb ((j + 1) ^ 2) ω) 2
      nlinarith)
  have hfI : ∀ j, ∫ ω, f j ω ∂μ ≤ K * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j
    have hM := hm ((j + 1) ^ 2)
    simp only [hfdef]
    rw [integral_div]
    set M : ℝ := (((j + 1) ^ 2 : ℕ) : ℝ)
    have hM1 : (1 : ℝ) ≤ M := by simp only [M]; exact_mod_cast Nat.one_le_pow _ _ (by omega)
    have hMe : M = ((j : ℝ) + 1) ^ 2 := by simp [M]
    rw [div_le_iff₀ (by positivity)]
    calc ∫ ω, ‖S ((j + 1) ^ 2) ω‖ ^ 2 ∂μ ≤ C * M := hM
      _ ≤ K * M := by gcongr; exact le_abs_self C
      _ = K * (1 / M) * M ^ 2 := by field_simp
      _ = _ := by rw [hMe]
  have hsumm : Summable fun j : ℕ => K * (1 / ((j : ℝ) + 1) ^ 2) := by
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    simpa using this
  have hlin : ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun j => (hfm j).ennreal_ofReal.aemeasurable]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
      (r := ∑' j : ℕ, K * (1 / ((j : ℝ) + 1) ^ 2))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsumm]
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi j) (Eventually.of_forall (hf0 j))]
    exact ENNReal.ofReal_le_ofReal (hfI j)
  have hae := ae_lt_top' (AEMeasurable.tsum fun j =>
    (hfm j).ennreal_ofReal.aemeasurable) hlin
  filter_upwards [hae] with ω hω
  have h1 : Tendsto (fun j => ENNReal.ofReal (f j ω)) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun j => f j ω) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, ENNReal.toReal_ofReal (hf0 _ ω)] using this
  have h3 : Tendsto (fun j : ℕ => S ((j + 1) ^ 2) ω / (((j + 1) ^ 2 : ℕ) : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := h2.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr fun j => ?_
    simp only [hfdef]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity),
      norm_div, Complex.norm_natCast]
  have h4 : Tendsto (fun j : ℕ => S (j ^ 2) ω / ((j ^ 2 : ℕ) : ℂ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).1 h3
  have h5 := DecayAeNormal.tendsto_of_tendsto_sq (fun k => (z k ω - c) / 2)
    (fun k => by
      rw [norm_div]; simp
      linarith [(norm_sub_le (z k ω) c), hz1 k ω])
    (by
      have := h4.div_const 2
      rw [zero_div] at this
      refine this.congr fun j => ?_
      simp only [hSdef]; rw [← Finset.sum_div]; ring)
  have h6 := (h5.const_mul 2).add_const c
  rw [mul_zero, zero_add] at h6
  refine h6.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring


section Generic
variable {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- `digSK` is measurable. -/
theorem measurable_digSK (b : ℕ) (T : α → ℤ) (K : ℕ) : Measurable (digSK b T K) := by
  unfold digSK
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_of_countable (fun a : α => ((T a : ℝ)))).comp (measurable_pi_apply j)).div_const _

/-- `digS` is measurable (limit of the truncations). -/
theorem measurable_digS (b : ℕ) (hb : 2 ≤ b) (T : α → ℤ) : Measurable (digS b T) := by
  refine measurable_of_tendsto_metrizable (fun K => measurable_digSK b T K) ?_
  rw [tendsto_pi_nhds]; intro ω
  rw [Metric.tendsto_atTop]; intro ε hε
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((∑ a, |(T a : ℝ)|) / ε) hb'
  refine ⟨K, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  refine (abs_digS_sub_digSK b hb T n ω).trans_lt ?_
  have hpos : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  rw [div_lt_iff₀ hpos]
  rw [div_lt_iff₀ hε] at hK
  have : (b : ℝ) ^ K ≤ (b : ℝ) ^ n := pow_le_pow_right₀ hb'.le hn
  nlinarith

open DecayAeNormal in
/-- **Generic genericity (crux).**  Assembled from G1–G5. -/
theorem ae_tendsto_digS (P : Measure α) [IsProbabilityMeasure P] (b : ℕ) (hb : 2 ≤ b)
    (T : α → ℤ) (h : ℤ) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => P),
      Tendsto (weylAvg b (digS b T ω) h) atTop
        (𝓝 (∫ ω, ee (h * digS b T ω) ∂Measure.infinitePi (fun _ : ℕ => P))) := by
  set μ := Measure.infinitePi (fun _ : ℕ => P) with hμ
  set B : ℝ := ∑ a, |(T a : ℝ)| with hB
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  set δ : ℕ → ℝ := fun K => 2 * Real.pi * |(h : ℝ)| * (B / (b : ℝ) ^ K) with hδ
  have hclose : ∀ K ω, ‖ee (h * digS b T ω) - ee (h * digSK b T K ω)‖ ≤ δ K := by
    intro K ω
    refine (norm_ee_sub_le _ _).trans ?_
    rw [← mul_sub, abs_mul]
    have := abs_digS_sub_digSK b hb T K ω
    have : 0 ≤ 2 * Real.pi * |(h : ℝ)| := by positivity
    rw [hδ, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (by assumption) this
  set z : ℕ → ℕ → (ℕ → α) → ℂ := fun K k ω => ee (h * digSK b T K (shiftK k ω)) with hz
  set c : ℕ → ℂ := fun K => ∫ ω, ee (h * digSK b T K ω) ∂μ with hc
  have hmK : ∀ K, Measurable fun ω => ee (h * digSK b T K ω) := fun K =>
    measurable_ee.comp ((measurable_digSK b T K).const_mul _)
  have hshm : ∀ k, Measurable (shiftK (α := α) k) := fun k =>
    measurable_pi_lambda _ fun j => measurable_pi_apply (k + j)
  have hzm : ∀ K k, Measurable (z K k) := fun K k => (hmK K).comp (hshm k)
  have hz1 : ∀ K k ω, ‖z K k ω‖ ≤ 1 := fun K k ω => (norm_ee _).le
  have hzc : ∀ K k, ∫ ω, z K k ω ∂μ = c K := by
    intro K k
    have hmp := measurePreserving_shiftK P k
    have := integral_map (μ := μ) (hshm k).aemeasurable (hmK K).aestronglyMeasurable
    rw [hmp.map_eq] at this
    exact this.symm
  have hc1 : ∀ K, ‖c K‖ ≤ 1 := fun K => by
    refine (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun ω => (norm_ee _).le)).trans ?_
    simp
  have hae : ∀ K, ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, z K k ω) / N) atTop
      (𝓝 (c K)) := fun K =>
    ae_tendsto_of_second_moment μ (z K) (hzm K) (hz1 K) (c K) (hc1 K) _
      (second_moment_le_of_indep μ (z K) (hzm K) (hz1 K) (c K) (hzc K) K
        (fun k l hkl => by rw [hz, hc]; exact integral_ee_digSK_indep P b T h K k l hkl))
  rw [← ae_all_iff] at hae
  filter_upwards [hae] with ω hω
  set ν := ∫ ω, ee (h * digS b T ω) ∂μ with hν
  have hνc : ∀ K, ‖ν - c K‖ ≤ δ K := fun K => by
    rw [hν, hc, ← integral_sub]
    · refine (norm_integral_le_of_norm_le_const (Eventually.of_forall fun ω => hclose K ω)).trans ?_
      simp
    · exact Integrable.of_bound (measurable_ee.comp ((measurable_digS b hb T).const_mul _)).aestronglyMeasurable 1 (Eventually.of_forall fun ω => (norm_ee _).le)
    · exact Integrable.of_bound (hmK K).aestronglyMeasurable 1 (Eventually.of_forall fun ω => (norm_ee _).le)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (6 * Real.pi * |(h : ℝ)| * B / ε) hb'
  have hδK : δ K < ε / 3 := by
    have hpos : (0 : ℝ) < (b : ℝ) ^ K := by positivity
    rw [div_lt_iff₀ hε] at hK
    show 2 * Real.pi * |(h : ℝ)| * (B / (b : ℝ) ^ K) < ε / 3
    rw [mul_div_assoc', div_lt_iff₀ hpos]
    nlinarith
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hω K) (ε / 3) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := le_of_max_le_right hN
    exact_mod_cast this
  have h1 := hN₀ N (le_of_max_le_left hN)
  rw [dist_eq_norm] at h1 ⊢
  have hw : weylAvg b (digS b T ω) h N - (∑ k ∈ Finset.range N, z K k ω) / N
      = (∑ k ∈ Finset.range N, (ee (h * digS b T (shiftK k ω)) - z K k ω)) / N := by
    rw [weylAvg, Finset.sum_sub_distrib, sub_div]
    congr 2
    exact Finset.sum_congr rfl fun k _ => ee_pow_mul_digS b hb T h k ω
  have hwb : ‖weylAvg b (digS b T ω) h N - (∑ k ∈ Finset.range N, z K k ω) / N‖ ≤ δ K := by
    rw [hw, norm_div, Complex.norm_natCast, div_le_iff₀ hNpos]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hclose K (shiftK k ω)).trans ?_
    simp [mul_comm]
  calc ‖weylAvg b (digS b T ω) h N - ν‖
      = ‖(weylAvg b (digS b T ω) h N - (∑ k ∈ Finset.range N, z K k ω) / N)
          + ((∑ k ∈ Finset.range N, z K k ω) / N - c K) + (c K - ν)‖ := by ring_nf
    _ ≤ ‖weylAvg b (digS b T ω) h N - (∑ k ∈ Finset.range N, z K k ω) / N‖
          + ‖(∑ k ∈ Finset.range N, z K k ω) / N - c K‖ + ‖c K - ν‖ := norm_add₃_le
    _ < ε := by
      have := hνc K
      rw [norm_sub_rev] at this
      linarith


end Generic

theorem combo_eq_digS {m : ℕ} (b : ℕ) (hb : 2 ≤ b) (dX dY : Fin m → ℕ) (a c : ℤ) (ω : ℕ → Fin m × Fin m) :
    combo b dX dY a c ω = digS b (fun p => a * dX p.1 + c * dY p.2) ω := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  have hsum : ∀ d : Fin m → ℕ, ∀ hc : Fin m × Fin m → Fin m, Summable fun i => (d (hc (ω i)) : ℝ) / (b : ℝ) ^ (i + 1) := by
    intro d hc
    obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ j, d j ≤ B := ⟨∑ j, d j, fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)⟩
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb')).mul_left (B : ℝ))
    rw [div_eq_mul_inv, ← inv_pow, pow_succ]
    have : (d (hc (ω i)) : ℝ) ≤ B := by exact_mod_cast hB _
    have h1 : (0:ℝ) ≤ (b:ℝ)⁻¹ ^ i := by positivity
    have h2 : (b:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb'.le
    have h3 : (0:ℝ) ≤ (b:ℝ)⁻¹ := by positivity
    calc (d (hc (ω i)) : ℝ) * ((b:ℝ)⁻¹ ^ i * (b:ℝ)⁻¹) ≤ B * ((b:ℝ)⁻¹ ^ i * 1) := by gcongr
      _ = B * (b:ℝ)⁻¹ ^ i := by ring
  unfold combo realX realY digS
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add ((hsum dX Prod.fst).mul_left _) ((hsum dY Prod.snd).mul_left _)]
  congr 1; funext i; push_cast; ring


/-- **Leaf (crux: genericity).**  A.e. orbit has Weyl means tending to the coefficient of the
stationary law.  Confidence 90%.  English proof: `ee(h bᵏ combo ω) = ee(h combo(σᵏω))`; the
correlation of `ee(h combo ∘ σᵏ)` and `ee(h combo ∘ σˡ)` is within `O(b^{-|k-l|})` of
`|nuHat h|²` (truncate the tail, independence of disjoint coordinates); so the second moment of
`Σ_{k<N} (ee(..) - nuHat)` is `O(N)`; `j²` subsequence and interpolation as in
`DecayAeNormal.ae_tendsto_weyl`. -/
theorem ae_tendsto_nuHat (b m : ℕ) [NeZero m] (hb : 2 ≤ b) (dX dY : Fin m → ℕ)
    (hX : ∀ j, dX j < b) (hY : ∀ j, dY j < b) (a c : ℤ) (h : ℤ) :
    ∀ᵐ ω ∂pairs m, Tendsto (weylAvg b (combo b dX dY a c ω) h) atTop
      (nhds (nuHat b dX dY a c h)) := by
  have := ae_tendsto_digS (PMF.uniformOfFintype (Fin m × Fin m)).toMeasure b hb
    (fun p => a * dX p.1 + c * dY p.2) h
  simp only [nuHat, combo_eq_digS b hb]
  exact this

/-- **Leaf (product formula).**  `nuHat h = 0` iff some digit-polynomial factor vanishes.
Confidence 95%: `nuHat h = ∏_{i≥1} φ_X(a h/bⁱ) φ_Y(c h/bⁱ)` by independence of coordinates and
dominated convergence; `|1 - φ(t)| ≤ 2π b |t|` makes the tail product converge to a nonzero
limit. -/
theorem nuHat_eq_zero_iff (b m : ℕ) [NeZero m] (hb : 2 ≤ b) (dX dY : Fin m → ℕ)
    (hX : ∀ j, dX j < b) (hY : ∀ j, dY j < b) (a c : ℤ) (h : ℤ) :
    nuHat b dX dY a c h = 0 ↔ ∃ i : ℕ, 1 ≤ i ∧
      digitPoly dX (a * h / (b : ℝ) ^ i) * digitPoly dY (c * h / (b : ℝ) ^ i) = 0 := by
  sorry

/-- A.e. not normal at a frequency with nonzero coefficient. -/
theorem ae_not_isNormal_of_nuHat_ne (b m : ℕ) [NeZero m] (hb : 2 ≤ b) (dX dY : Fin m → ℕ)
    (hX : ∀ j, dX j < b) (hY : ∀ j, dY j < b) (a c : ℤ) (h : ℤ) (hh : h ≠ 0)
    (hne : nuHat b dX dY a c h ≠ 0) :
    ∀ᵐ ω ∂pairs m, ¬ IsNormal b (a * realX b dX ω + c * realY b dY ω) := by
  filter_upwards [ae_tendsto_nuHat b m hb dX dY hX hY a c h] with ω hω hN
  exact hne (tendsto_nhds_unique hω (weylAvg_tendsto_zero_of_isNormal b hb _ hN h hh))

/-- **The Fourier-zero criterion.**  Confidence 80%.  English proof in the module doc: the
residue-free stationary law of `bⁿ(a x + c y) mod 1` is the law of `a X + c Y mod 1` with `X, Y`
independent self-similar; its `h`-th coefficient is the convergent product
`∏_{i ≥ 1} φ_X(a h / bⁱ) φ_Y(c h / bⁱ)`; the shift is Bernoulli, so a.e. orbits are generic for
it (Birkhoff on the digit shift, `frac(bⁿ z)` a continuous-a.e. function of the future digits and
the bounded carry); normal iff generic for Lebesgue iff every nonzero coefficient vanishes. -/
theorem ae_isNormal_combo_iff (b m : ℕ) [NeZero m] (hb : 2 ≤ b) (dX dY : Fin m → ℕ)
    (hX : ∀ j, dX j < b) (hY : ∀ j, dY j < b) (a c : ℤ) (hac : a ≠ 0 ∨ c ≠ 0) :
    (∀ᵐ ω ∂pairs m, IsNormal b (a * realX b dX ω + c * realY b dY ω)) ↔
      ∀ h : ℤ, h ≠ 0 → ∃ i : ℕ, 1 ≤ i ∧
        digitPoly dX (a * h / (b : ℝ) ^ i) * digitPoly dY (c * h / (b : ℝ) ^ i) = 0 := by
  constructor
  · intro hae h hh
    by_contra hcon
    push Not at hcon
    have hne : nuHat b dX dY a c h ≠ 0 := fun h0 => by
      obtain ⟨i, hi, hz⟩ := (nuHat_eq_zero_iff b m hb dX dY hX hY a c h).1 h0
      exact hcon i hi hz
    have hbad := ae_not_isNormal_of_nuHat_ne b m hb dX dY hX hY a c h hh hne
    have : ∀ᵐ ω ∂pairs m, False := by
      filter_upwards [hae, hbad] with ω h1 h2 using h2 h1
    have hP : IsProbabilityMeasure (pairs m) := by unfold pairs; infer_instance
    rw [ae_iff] at this
    simp at this
  · intro hall
    have hW : ∀ᵐ ω ∂pairs m, ∀ h : ℤ, h ≠ 0 →
        Tendsto (weylAvg b (combo b dX dY a c ω) h) atTop (nhds 0) := by
      rw [ae_all_iff]
      intro h
      by_cases hh : h = 0
      · exact Eventually.of_forall fun ω hne => absurd hh hne
      · have h0 := (nuHat_eq_zero_iff b m hb dX dY hX hY a c h).2 (hall h hh)
        filter_upwards [ae_tendsto_nuHat b m hb dX dY hX hY a c h] with ω hω _
        rwa [h0] at hω
    filter_upwards [hW] with ω hω
    exact isNormal_of_weylAvg b hb _ hω

/-- The 0–1 law beside the criterion: if the a.e. statement fails, a.e. point is not normal.
Confidence 85% (same proof: a.e. orbits are generic for one fixed law). -/
theorem ae_not_isNormal_combo_of_not (b m : ℕ) [NeZero m] (hb : 2 ≤ b) (dX dY : Fin m → ℕ)
    (hX : ∀ j, dX j < b) (hY : ∀ j, dY j < b) (a c : ℤ)
    (hbad : ∃ h : ℤ, h ≠ 0 ∧ ∀ i : ℕ, 1 ≤ i →
        digitPoly dX (a * h / (b : ℝ) ^ i) * digitPoly dY (c * h / (b : ℝ) ^ i) ≠ 0) :
    ∀ᵐ ω ∂pairs m, ¬ IsNormal b (a * realX b dX ω + c * realY b dY ω) := by
  obtain ⟨h, hh, hall⟩ := hbad
  refine ae_not_isNormal_of_nuHat_ne b m hb dX dY hX hY a c h hh fun h0 => ?_
  obtain ⟨i, hi, hz⟩ := (nuHat_eq_zero_iff b m hb dX dY hX hY a c h).1 h0
  exact hall i hi hz

/-- Digits `0, …, 4`. -/
def five : Fin 5 → ℕ := fun j => j

/-- **Necessary, not sufficient: enough joint entropy, no normal combination.**  Confidence 85%.
English proof: by Wall reduce to integer `(a, c) ≠ 0`; take `h = 5^N` with `N > v₅(a), v₅(c)`
(or the one nonzero coefficient's valuation).  `φ_five(t) = 0` iff `5t ∈ ℤ`, `t ∉ ℤ`; at
`t = a 5^N / 10ⁱ` this needs `i = v₅(a 5^N) + 1 ≤ v₂(a)`, false for large `N`.  So no factor
vanishes; `ae_not_isNormal_combo_of_not`, countably many `(a, c)`. -/
theorem ae_not_qSpanNormal_fiveDigits :
    ∀ᵐ ω ∂pairs 5, ¬ QSpanNormal 10 (realX 10 five ω) (realY 10 five ω) := by
  sorry

/-- The same pair has joint finite-state dimension above the budget `1/2`
(`log 25 / log 100 ≈ 0.70`).  Confidence 85% (Bernoulli entropy rate; the digits of `realX` are
the letters, no `9`-tails since digits are `≤ 4`). -/
theorem ae_jointDim_fiveDigits :
    ∀ᵐ ω ∂pairs 5, 1 / 2 < fsDim (digitPair 10 (by norm_num) (realX 10 five ω) (realY 10 five ω)) := by
  sorry

end NormalNumbers.QSpanCriterion
