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

/-! ### Leaves of the joint entropy budget

Route (no block-entropy characterization needed).  Reduce to integer `(a, c)` by Wall.  Suppose an
FST `T` describes `S↾n` in `ℓ ≤ (1/2 − ε) n` letters.  Cut the description into blocks of `L`
letters (`run_chunks`): `S↾n` is a concatenation of `≤ ℓ/L + 1` chunks, each the output of
(state, block).  A chunk of length `t` at position `p` pins the `z`-window at `p` of length `t` up
to a carry `|k| ≤ |a| + |c|` (`window_combo`), so long chunks (`t ≥ 2L(1 + ε')`) have `z`-windows
in a dictionary of size `≤ (m+1)(L+1) b^{2L} (2K+1) ≤ b^{t − 2Lε'}·poly(L)`.  Average chunk
length `≥ 2L/(1 − 2ε)`, so long chunks cover `≥ ε n` positions; `normal_thin_cover` caps that by
`δ n` with `δ → 0` as `L → ∞`. -/

/-- Value of the length-`t` window of a digit stream at position `p`. -/
def winVal (b : ℕ) (s : ℕ → ℕ) (p t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t, s (p + j) * b ^ (t - 1 - j)

/-- **Bounded carry.**  The `z`-window of `z = a x + c y` is the combination of the `x`- and
`y`-windows, up to an integer carry `|k| ≤ |a| + |c|`, reduced mod `bᵗ`.  Confidence 95%:
`⌊b^{p+t} z⌋ = a⌊b^{p+t}x⌋ + c⌊b^{p+t}y⌋ + ⌊a {b^{p+t}x} + c {b^{p+t}y}⌋` and each window value is
`⌊b^{p+t}·⌋ mod bᵗ`. -/
theorem window_combo (b : ℕ) (hb : 2 ≤ b) (a c : ℤ) (x y : ℝ) (p t : ℕ) :
    ∃ k : ℤ, |k| ≤ |a| + |c| ∧
      (winVal b (digitOf b (Int.fract (a * x + c * y))) p t : ℤ) =
        (a * winVal b (digitOf b (Int.fract x)) p t + c * winVal b (digitOf b (Int.fract y)) p t
          + k) % ((b ^ t : ℕ) : ℤ) := by
  sorry

/-- **Normal sequences admit no thin covers.**  Windows starting in `[0, n)` whose values lie in
thin dictionaries `V t` (lengths `t ∈ [t₀, t₁]`) cover at most `δ n` positions, once
`Σ t |V t| / bᵗ < δ`.  Distinct starts suffice; no disjointness.  Confidence 95%: each window value
has frequency `b^{-t}` by normality, and the sum is finite. -/
theorem normal_thin_cover (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ) (hs : IsNormalSequence b s)
    (t₀ t₁ : ℕ) (V : ℕ → Finset ℕ) (δ : ℝ)
    (hδ : ∑ t ∈ Finset.Icc t₀ t₁, (t : ℝ) * (V t).card / (b : ℝ) ^ t < δ) :
    ∀ᶠ n in atTop, ∀ (I : Finset ℕ) (ℓ : ℕ → ℕ),
      (∀ p ∈ I, p < n ∧ ℓ p ∈ Finset.Icc t₀ t₁ ∧ winVal b s p (ℓ p) ∈ V (ℓ p)) →
        (∑ p ∈ I, (ℓ p : ℝ)) ≤ δ * n := by
  sorry

/-- Output of an FST on a concatenation. -/
theorem runFrom_append {k : ℕ} (T : FST k) (q : Fin (T.m + 1)) (u v : List (Fin k)) :
    T.runFrom q (u ++ v) = T.runFrom q u ++ T.runFrom (u.foldl T.δ q) v := by
  induction u generalizing q with
  | nil => simp [FST.runFrom]
  | cons a u ih => simp [FST.runFrom, ih]

/-- **Chunking an FST run.**  The output of `T` on `π` is the concatenation of `≤ |π|/L + 1`
outputs of (state, input block of length `≤ L`).  Confidence 99%. -/
theorem run_chunks {k : ℕ} (T : FST k) (L : ℕ) (hL : 0 < L) (q : Fin (T.m + 1))
    (π : List (Fin k)) :
    ∃ cs : List (Fin (T.m + 1) × List (Fin k)), cs.length ≤ π.length / L + 1 ∧
      (∀ c ∈ cs, c.2.length ≤ L) ∧
      T.runFrom q π = (cs.map fun c => T.runFrom c.1 c.2).flatten := by
  induction h : π.length using Nat.strong_induction_on generalizing π q with
  | _ n ih =>
    by_cases hn : n ≤ L
    · exact ⟨[(q, π)], by simp, by simp; omega, by simp⟩
    · obtain ⟨cs, h1, h2, h3⟩ := ih (π.drop L).length (by simp; omega) (List.foldl T.δ q (π.take L))
        (π.drop L) rfl
      refine ⟨(q, π.take L) :: cs, ?_, ?_, ?_⟩
      · simp only [List.length_cons, List.length_drop] at h1 ⊢
        try rw [h] at h1
        have : (n - L) / L + 1 = n / L := (Nat.div_eq_sub_div hL (by omega)).symm
        omega
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · simp
        · exact h2 c hc
      · conv_lhs => rw [← List.take_append_drop L π]
        rw [runFrom_append, h3]; simp

/-- **Integer-coefficient budget.**  The assembly: `run_chunks`, `window_combo` and
`normal_thin_cover` with `L → ∞`.  Confidence 85%. -/
theorem span_jointDim_budget_int (b : ℕ) (hb : 2 ≤ b) (x y : ℝ) (a c : ℤ)
    (hz : IsNormal b (a * x + c * y)) :
    1 / 2 ≤ fsDim (digitPair b (by omega) x y) := by
  sorry

/-- **Joint entropy budget.**  Confidence 85%.  English proof: `QSpan.span_dimension_budget`,
stopped before the subadditivity step. -/
theorem span_jointDim_budget (b : ℕ) (hb : 2 ≤ b) (x y : ℝ) (c₁ c₂ : ℚ)
    (hz : IsNormal b ((c₁ : ℝ) * x + c₂ * y)) :
    1 / 2 ≤ fsDim (digitPair b (by omega) x y) := by
  set q : ℚ := ((c₁.den * c₂.den : ℕ) : ℚ) with hqdef
  have hq : q ≠ 0 := by
    rw [hqdef]; exact_mod_cast Nat.mul_ne_zero c₁.den_nz c₂.den_nz
  have hW := isNormal_rat_mul_add b hb _ q 0 hq hz
  refine span_jointDim_budget_int b hb x y (c₁.num * c₂.den) (c₂.num * c₁.den) ?_
  convert hW using 1
  have e1 : ((c₁.num : ℝ)) = (c₁ : ℝ) * c₁.den := by
    exact_mod_cast (Rat.mul_den_eq_num c₁).symm
  have e2 : ((c₂.num : ℝ)) = (c₂ : ℝ) * c₂.den := by
    exact_mod_cast (Rat.mul_den_eq_num c₂).symm
  simp only [hqdef]
  push_cast
  rw [e1, e2]; ring


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

open DecayAeNormal in
/-- Joint-normality step `weyl2_of_boxFreq`. -/
theorem weyl2_of_boxFreq (b : ℕ) (hb : 2 ≤ b) (u v : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Set.Ico (0 : ℝ) 1) (hv : ∀ n, v n ∈ Set.Ico (0 : ℝ) 1)
    (hbox : ∀ L : ℕ, 1 ≤ L → ∀ j₁ < b ^ L, ∀ j₂ < b ^ L, Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => ⌊((b ^ L : ℕ) : ℝ) * u n⌋₊ = j₁ ∧
        ⌊((b ^ L : ℕ) : ℝ) * v n⌋₊ = j₂).card : ℝ) / N) atTop
        (𝓝 ((((b ^ L : ℕ) : ℝ) ^ 2)⁻¹)))
    (a c h : ℤ) (hac : a ≠ 0 ∨ c ≠ 0) (hh : h ≠ 0) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, ee (h * (a * u n + c * v n))) / N) atTop
      (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  set A : ℝ := 2 * Real.pi * |(h : ℝ)| * (|(a : ℝ)| + |(c : ℝ)|) with hA
  have hA0 : 0 ≤ A := by positivity
  set L : ℕ := (h * a).natAbs + (h * c).natAbs + ⌈2 * A / ε⌉₊ with hLdef
  set M : ℕ := b ^ L with hMdef
  have hLM : L < M := Nat.lt_pow_self (by omega)
  have hL1 : 1 ≤ L := by
    have : 0 < (h * a).natAbs ∨ 0 < (h * c).natAbs := by
      rcases hac with ha | hc
      · exact Or.inl (Int.natAbs_pos.2 (mul_ne_zero hh ha))
      · exact Or.inr (Int.natAbs_pos.2 (mul_ne_zero hh hc))
    omega
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMh : (h * a).natAbs + (h * c).natAbs < M := by omega
  have hMerr : A / M ≤ ε / 2 := by
    rw [div_le_iff₀ hMR]
    have h1 : 2 * A / ε ≤ M := by
      refine (Nat.le_ceil _).trans ?_
      have : ⌈2 * A / ε⌉₊ ≤ M := by omega
      exact_mod_cast this
    rw [div_le_iff₀ hε] at h1
    linarith
  set g : ℕ → ℕ := fun n => ⌊(M : ℝ) * u n⌋₊ with hg
  set g' : ℕ → ℕ := fun n => ⌊(M : ℝ) * v n⌋₊ with hg'
  have hfl : ∀ (w : ℕ → ℝ), (∀ n, w n ∈ Set.Ico (0 : ℝ) 1) → ∀ n,
      ⌊(M : ℝ) * w n⌋₊ < M ∧ |w n - (⌊(M : ℝ) * w n⌋₊ : ℝ) / M| ≤ 1 / M := by
    intro w hw n
    have h0 : 0 ≤ (M : ℝ) * w n := by nlinarith [(hw n).1]
    refine ⟨?_, ?_⟩
    · have : (M : ℝ) * w n < M := by nlinarith [(hw n).2]
      exact_mod_cast (Nat.floor_lt h0).2 this
    · have h1 := Nat.floor_le h0
      have h2 := Nat.lt_floor_add_one ((M : ℝ) * w n)
      rw [abs_le]; constructor
      · have : (⌊(M : ℝ) * w n⌋₊ : ℝ) / M ≤ w n := by rw [div_le_iff₀ hMR]; linarith
        have : 0 ≤ 1 / (M : ℝ) := by positivity
        linarith
      · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hMR]; linarith
  -- main term
  set P : ℕ → ℂ := fun N => ∑ j₁ ∈ Finset.range M, ∑ j₂ ∈ Finset.range M,
    ((((Finset.range N).filter fun n => g n = j₁ ∧ g' n = j₂).card : ℝ) / N : ℝ) *
      ee (h * (a * j₁ + c * j₂) / M) with hP
  have hPlim : Tendsto P atTop (𝓝 0) := by
    have : Tendsto P atTop (𝓝 (∑ j₁ ∈ Finset.range M, ∑ j₂ ∈ Finset.range M,
        ((((M : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * ee (h * (a * j₁ + c * j₂) / M))) := by
      refine tendsto_finsetSum _ fun j₁ hj₁ => tendsto_finsetSum _ fun j₂ hj₂ => ?_
      refine Tendsto.mul_const _ ((Complex.continuous_ofReal.tendsto _).comp ?_)
      exact hbox L hL1 j₁ (Finset.mem_range.1 hj₁) j₂ (Finset.mem_range.1 hj₂)
    convert this using 1
    have hsplit : ∀ j₁ j₂ : ℕ, ee (h * (a * j₁ + c * j₂) / M)
        = ee (((h * a : ℤ) : ℝ) * j₁ / M) * ee (((h * c : ℤ) : ℝ) * j₂ / M) := by
      intro j₁ j₂; rw [← ee_add]; congr 1; push_cast; ring
    simp_rw [hsplit]
    have hfac : ∑ j₁ ∈ Finset.range M, ∑ j₂ ∈ Finset.range M,
        ((((M : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * (ee (((h * a : ℤ) : ℝ) * j₁ / M) * ee (((h * c : ℤ) : ℝ) * j₂ / M))
        = ((((M : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * ((∑ j₁ ∈ Finset.range M, ee (((h * a : ℤ) : ℝ) * j₁ / M))
          * (∑ j₂ ∈ Finset.range M, ee (((h * c : ℤ) : ℝ) * j₂ / M))) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
    rw [hfac]
    rcases hac with ha | hc
    · rw [sum_ee_root (h * a) (mul_ne_zero hh ha) M (by omega)]; simp
    · rw [sum_ee_root (h * c) (mul_ne_zero hh hc) M (by omega)]; simp
  have hfib : ∀ N : ℕ, (∑ n ∈ Finset.range N, ee (h * (a * g n + c * g' n) / M))
      = ∑ j₁ ∈ Finset.range M, ∑ j₂ ∈ Finset.range M,
        ((((Finset.range N).filter fun n => g n = j₁ ∧ g' n = j₂).card : ℕ) : ℂ) *
          ee (h * (a * j₁ + c * j₂) / M) := by
    intro N
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range N)
      (t := Finset.range M ×ˢ Finset.range M) (g := fun n => (g n, g' n))
      (fun n _ => Finset.mem_product.2 ⟨Finset.mem_range.2 (hfl u hu n).1,
        Finset.mem_range.2 (hfl v hv n).1⟩), Finset.sum_product]
    refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
    rw [Finset.sum_congr rfl (fun n hn => by
        have := (Finset.mem_filter.1 hn).2
        simp only [Prod.mk.injEq] at this
        rw [this.1, this.2]),
      Finset.sum_const, nsmul_eq_mul]
    congr 3
    exact Finset.filter_congr fun n _ => by simp only [Prod.mk.injEq]
  rcases (Metric.tendsto_atTop.1 hPlim) (ε / 2) (by linarith) with ⟨N₀, hN₀⟩
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hPN := hN₀ N (le_of_max_le_left hN)
  rw [dist_zero_right] at hPN ⊢
  have hPN' : P N = (∑ n ∈ Finset.range N, ee (h * (a * g n + c * g' n) / M)) / N := by
    rw [hfib, Finset.sum_div, hP]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    push_cast; ring
  have hdiff : ∀ n, ‖ee (h * (a * u n + c * v n)) - ee (h * (a * g n + c * g' n) / M)‖ ≤ A / M := by
    intro n
    refine (norm_ee_sub_le _ _).trans ?_
    have e : (h : ℝ) * (a * u n + c * v n) - h * (a * g n + c * g' n) / M
        = h * (a * (u n - g n / M) + c * (v n - g' n / M)) := by ring
    rw [e, abs_mul]
    have h1 := (hfl u hu n).2
    have h2 := (hfl v hv n).2
    have h3 : |(a : ℝ) * (u n - g n / M) + c * (v n - g' n / M)| ≤ (|(a:ℝ)| + |(c:ℝ)|) / M := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, add_div]
      have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (a : ℝ))
      have := mul_le_mul_of_nonneg_left h2 (abs_nonneg (c : ℝ))
      simp only [mul_one_div] at *
      linarith
    rw [hA, mul_div_assoc]
    have hp : 0 ≤ 2 * Real.pi * |(h : ℝ)| := by positivity
    calc 2 * Real.pi * (|(h:ℝ)| * |(a : ℝ) * (u n - g n / M) + c * (v n - g' n / M)|)
        = 2 * Real.pi * |(h:ℝ)| * |(a : ℝ) * (u n - g n / M) + c * (v n - g' n / M)| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hp
  have hsum : ‖∑ n ∈ Finset.range N, (ee (h * (a * u n + c * v n)) - ee (h * (a * g n + c * g' n) / M))‖
      ≤ N * (A / M) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun n _ => hdiff n).trans ?_
    simp
  have hsplit : (∑ n ∈ Finset.range N, ee (h * (a * u n + c * v n))) / N
      = (∑ n ∈ Finset.range N, (ee (h * (a * u n + c * v n)) - ee (h * (a * g n + c * g' n) / M))) / N
        + P N := by
    rw [hPN', Finset.sum_sub_distrib]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans_lt ?_
  have : ‖(∑ n ∈ Finset.range N, (ee (h * (a * u n + c * v n)) - ee (h * (a * g n + c * g' n) / M))) / (N : ℂ)‖
      ≤ A / M := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hNpos]
    linarith
  linarith

open DecayAeNormal in
/-- Joint-normality step `floor_orbit_iff_matchesAt`. -/
theorem floor_orbit_iff_matchesAt (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (L j : ℕ) (hj : j < b ^ L)
    (n : ℕ) :
    ⌊((b ^ L : ℕ) : ℝ) * orbit b x n⌋₊ = j ↔
      MatchesAt (digitOf b (Int.fract x)) (padWord b L j) n := by
  have hw := padWord_digits_lt hb L j
  have hlen := length_padWord hb hj
  have hmo : MatchesAt (digitOf b (Int.fract x)) (padWord b L j) n ↔ OccursAt b x (padWord b L j) n := by
    unfold MatchesAt OccursAt
    constructor
    · intro h t ht; have := h t ht; rwa [List.getD_eq_getElem _ 0 ht] at this
    · intro h t ht; have := h t ht; rwa [← List.getD_eq_getElem _ 0 ht] at this
  rw [hmo, occursAt_iff_orbit_mem b hb x _ hw n,
    blockNatVal_padWord hb, hlen]
  have := mem_Ico_div_pow_iff_floor_eq b hb (orbit b x n) L (j : ℤ)
  push_cast at this
  rw [this]
  have h0 : 0 ≤ orbit b x n := Int.fract_nonneg _
  have h0' : 0 ≤ ((b ^ L : ℕ) : ℝ) * orbit b x n := by positivity
  have e : orbit b x n * (b : ℝ) ^ L = ((b ^ L : ℕ) : ℝ) * orbit b x n := by push_cast; ring
  rw [e, ← Int.natCast_floor_eq_floor h0', Nat.cast_inj]

open DecayAeNormal in
/-- Joint-normality step `pair_val`. -/
theorem pair_val (b : ℕ) (hb : 0 < b) (x y : ℝ) (i : ℕ) :
    ((digitPair b hb x y i : Fin (b * b)) : ℕ)
      = digitOf b (Int.fract y) i + b * digitOf b (Int.fract x) i := rfl

open DecayAeNormal in
/-- Joint-normality step `matchesAt_pair_iff`. -/
theorem matchesAt_pair_iff (b : ℕ) (hb : 2 ≤ b) (x y : ℝ) (L j₁ j₂ : ℕ)
    (h₁ : j₁ < b ^ L) (h₂ : j₂ < b ^ L) (n : ℕ) :
    MatchesAt (fun i => ((digitPair b (by omega) x y i : Fin (b * b)) : ℕ))
        (List.zipWith (fun d e => e + b * d) (padWord b L j₁) (padWord b L j₂)) n ↔
      MatchesAt (digitOf b (Int.fract x)) (padWord b L j₁) n ∧
        MatchesAt (digitOf b (Int.fract y)) (padWord b L j₂) n := by
  have l1 := length_padWord hb h₁
  have l2 := length_padWord hb h₂
  have d1 := padWord_digits_lt hb L j₁
  have d2 := padWord_digits_lt hb L j₂
  unfold MatchesAt
  simp only [pair_val, List.length_zipWith, l1, l2, min_self]
  have key : ∀ t < L, (List.zipWith (fun d e => e + b * d) (padWord b L j₁) (padWord b L j₂)).getD t 0
      = (padWord b L j₂).getD t 0 + b * (padWord b L j₁).getD t 0 := by
    intro t ht
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_zipWith,
      List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  have hb0 : 0 < b := by omega
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have e := h t ht
      rw [key t ht] at e
      have ha := digitOf_lt b hb (Int.fract y) (n + t)
      have hc : (padWord b L j₂).getD t 0 < b := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact d2 _ (List.getElem_mem _)
      have := congrArg (· / b) e
      beta_reduce at this
      rwa [Nat.add_mul_div_left _ _ hb0, Nat.add_mul_div_left _ _ hb0, Nat.div_eq_of_lt ha,
        Nat.div_eq_of_lt hc, zero_add, zero_add] at this
    · have e := h t ht
      rw [key t ht] at e
      have ha := digitOf_lt b hb (Int.fract y) (n + t)
      have hc : (padWord b L j₂).getD t 0 < b := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact d2 _ (List.getElem_mem _)
      have := congrArg (· % b) e
      beta_reduce at this
      rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
        Nat.mod_eq_of_lt hc] at this
  · rintro ⟨h1, h2⟩ t ht
    rw [key t ht, h1 t ht, h2 t ht]

open DecayAeNormal in
/-- **Jointly normal ⇒ the whole span is normal.**  Confidence 95%.  English proof: joint
normality is equidistribution of `(bⁿx, bⁿy)` in `𝕋²` (b-adic boxes); `bⁿ(a x + c y) mod 1` is the
image under `(u, v) ↦ a u + c v`, which pushes Lebesgue to Lebesgue for `(a, c) ≠ 0`; rational
coefficients by Wall. -/
theorem isNormal_span_of_jointNormal (b : ℕ) (hb : 2 ≤ b) (x y : ℝ)
    (hJ : IsNormalSequence (b * b) (fun i => (digitPair b (by omega) x y i : ℕ)))
    (c₁ c₂ : ℚ) (hne : c₁ ≠ 0 ∨ c₂ ≠ 0) : IsNormal b ((c₁ : ℝ) * x + c₂ * y) := by
  have hint : ∀ a c : ℤ, (a ≠ 0 ∨ c ≠ 0) → IsNormal b (a * x + c * y) := by
    intro a c hac
    apply isNormal_of_weylAvg b hb
    intro h hh
    have hbox : ∀ L : ℕ, 1 ≤ L → ∀ j₁ < b ^ L, ∀ j₂ < b ^ L, Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => ⌊((b ^ L : ℕ) : ℝ) * orbit b x n⌋₊ = j₁ ∧
          ⌊((b ^ L : ℕ) : ℝ) * orbit b y n⌋₊ = j₂).card : ℝ) / N) atTop
          (𝓝 ((((b ^ L : ℕ) : ℝ) ^ 2)⁻¹)) := by
      intro L hL j₁ h₁ j₂ h₂
      set wp := List.zipWith (fun d e => e + b * d) (padWord b L j₁) (padWord b L j₂) with hwp
      have l1 := length_padWord hb h₁
      have l2 := length_padWord hb h₂
      have hlen : wp.length = L := by rw [hwp, List.length_zipWith, l1, l2, min_self]
      have hne : wp ≠ [] := by
        intro h0; rw [h0] at hlen; simp at hlen; omega
      have hlt : ∀ d ∈ wp, d < b * b := by
        intro d hd
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hd
        simp only [hwp, List.getElem_zipWith]
        have e1 := padWord_digits_lt hb L j₁ _ (List.getElem_mem (show t < (padWord b L j₁).length by omega))
        have e2 := padWord_digits_lt hb L j₂ _ (List.getElem_mem (show t < (padWord b L j₂).length by omega))
        nlinarith
      have hc := hJ wp hne hlt
      have hle := fun n => card_filter_matchesAt_le
        (fun i => ((digitPair b (by omega) x y i : Fin (b * b)) : ℕ)) wp hne n
      have ht := tendsto_div_of_bounded_diff (fun n => (hle n).1) (fun n => (hle n).2) hc
      rw [hlen] at ht
      convert ht using 3
      · congr 2
        refine Finset.filter_congr fun n _ => ?_
        rw [floor_orbit_iff_matchesAt b hb x L j₁ h₁, floor_orbit_iff_matchesAt b hb y L j₂ h₂,
          hwp, matchesAt_pair_iff b hb x y L j₁ j₂ h₁ h₂]
      · push_cast; ring
    have := weyl2_of_boxFreq b hb (orbit b x) (orbit b y)
      (fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
      (fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) hbox a c h hac hh
    refine this.congr fun N => ?_
    unfold weylAvg
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold orbit
    rw [show (h : ℝ) * (a * Int.fract (x * b ^ n) + c * Int.fract (y * b ^ n))
        = ((h * a : ℤ) : ℝ) * Int.fract (x * b ^ n) + ((h * c : ℤ) : ℝ) * Int.fract (y * b ^ n) by
          push_cast; ring, ee_add, ee_int_mul_fract, ee_int_mul_fract, ← ee_add]
    congr 1; push_cast; ring
  set q : ℚ := ((c₁.den * c₂.den : ℕ) : ℚ) with hqdef
  have hq : q ≠ 0 := by
    rw [hqdef]; exact_mod_cast Nat.mul_ne_zero c₁.den_nz c₂.den_nz
  have hN := hint (c₁.num * c₂.den) (c₂.num * c₁.den) (by
    rcases hne with h | h
    · left; exact mul_ne_zero (Rat.num_ne_zero.2 h) (by exact_mod_cast c₂.den_nz)
    · right; exact mul_ne_zero (Rat.num_ne_zero.2 h) (by exact_mod_cast c₁.den_nz))
  have hW := isNormal_rat_mul_add b hb _ q⁻¹ 0 (inv_ne_zero hq) hN
  convert hW using 1
  have e1 : ((c₁.num : ℝ)) = (c₁ : ℝ) * c₁.den := by
    exact_mod_cast (Rat.mul_den_eq_num c₁).symm
  have e2 : ((c₂.num : ℝ)) = (c₂ : ℝ) * c₂.den := by
    exact_mod_cast (Rat.mul_den_eq_num c₂).symm
  have hd1 : (c₁.den : ℝ) ≠ 0 := by exact_mod_cast c₁.den_nz
  have hd2 : (c₂.den : ℝ) ≠ 0 := by exact_mod_cast c₂.den_nz
  simp only [hqdef]
  push_cast
  rw [e1, e2]
  field_simp
  ring

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
/-- The window value read from the coordinates in `[k, k+K)`. -/
noncomputable def winF (b : ℕ) (T : α → ℤ) (h : ℤ) (k K : ℕ)
    (y : (Finset.Ico k (k + K)) → α) : ℂ :=
  ee (h * ∑ i : (Finset.Ico k (k + K)), (T (y i) : ℝ) / (b : ℝ) ^ ((i : ℕ) - k + 1))

omit [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α] in
open DecayAeNormal in
/-- `digSK` of the shifted point is the window function of its coordinates. -/
theorem winF_repr (b : ℕ) (T : α → ℤ) (h : ℤ) (k K : ℕ) (ω : ℕ → α) :
    ee (h * digSK b T K (shiftK k ω)) = winF b T h k K (fun i => ω i) := by
  unfold winF digSK shiftK
  congr 2
  rw [Finset.sum_coe_sort (Finset.Ico k (k + K)) (fun i => (T (ω i) : ℝ) / (b : ℝ) ^ (i - k + 1)),
    Finset.sum_Ico_eq_sum_range]
  simp

open DecayAeNormal ProbabilityTheory in
/-- **Leaf G4.**  Windows `[k, k+K)` and `[l, l+K)` are disjoint for `k + K ≤ l`: independence. -/
theorem integral_ee_digSK_indep (P : Measure α) [IsProbabilityMeasure P] (b : ℕ) (T : α → ℤ)
    (h : ℤ) (K k l : ℕ) (hkl : k + K ≤ l) :
    ∫ ω, ee (h * digSK b T K (shiftK k ω)) * (starRingEnd ℂ) (ee (h * digSK b T K (shiftK l ω)))
        ∂Measure.infinitePi (fun _ : ℕ => P) =
      (∫ ω, ee (h * digSK b T K ω) ∂Measure.infinitePi (fun _ : ℕ => P)) *
        (starRingEnd ℂ) (∫ ω, ee (h * digSK b T K ω) ∂Measure.infinitePi (fun _ : ℕ => P)) := by
  set μ := Measure.infinitePi (fun _ : ℕ => P)
  have hI : iIndepFun (fun i (ω : ℕ → α) => ω i) μ :=
    iIndepFun_infinitePi (P := fun _ : ℕ => P) (X := fun _ => id) (fun _ => measurable_id)
  have hD : Disjoint (Finset.Ico k (k + K)) (Finset.Ico l (l + K)) := by
    rw [Finset.disjoint_left]; intro i hi hi'
    simp only [Finset.mem_Ico] at hi hi'; omega
  have hind := (hI.indepFun_finset _ _ hD (fun i => measurable_pi_apply i)).comp
    (measurable_of_countable (winF b T h k K))
    (Complex.continuous_conj.measurable.comp (measurable_of_countable (winF b T h l K)))
  have hmK : Measurable fun ω => ee (h * digSK b T K ω) :=
    measurable_ee.comp ((measurable_digSK b T K).const_mul _)
  have hstat : ∀ k, ∫ ω, ee (h * digSK b T K (shiftK k ω)) ∂μ = ∫ ω, ee (h * digSK b T K ω) ∂μ := by
    intro k
    have hmp := measurePreserving_shiftK P k
    have := integral_map (μ := μ) hmp.measurable.aemeasurable hmK.aestronglyMeasurable
    rw [hmp.map_eq] at this
    exact this.symm
  simp_rw [winF_repr]
  have e := hind.integral_fun_mul_eq_mul_integral
    ((measurable_of_countable (winF b T h k K)).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)).aestronglyMeasurable
    ((Complex.continuous_conj.measurable.comp (measurable_of_countable (winF b T h l K))).comp
      (measurable_pi_lambda _ fun i => measurable_pi_apply _)).aestronglyMeasurable
  simp only [Function.comp_def] at e
  rw [e]
  rw [integral_conj]
  simp_rw [← winF_repr]
  rw [hstat k, hstat l]

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

section Product
variable {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

open DecayAeNormal ProbabilityTheory in
/-- Product-formula step `ee_finset_sum`. -/
theorem ee_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee; push_cast; rw [Finset.mul_sum, Complex.exp_sum]

open DecayAeNormal ProbabilityTheory in
/-- Product-formula step `integral_ee_digSK`. -/
theorem integral_ee_digSK (P : Measure α) [IsProbabilityMeasure P] (b : ℕ) (T : α → ℤ)
    (h : ℤ) (K : ℕ) :
    ∫ ω, ee (h * digSK b T K ω) ∂Measure.infinitePi (fun _ : ℕ => P) =
      ∏ j ∈ Finset.range K, ∫ a, ee (h * ((T a : ℝ) / (b : ℝ) ^ (j + 1))) ∂P := by
  set G : ℕ → α → ℂ := fun j a => ee (h * ((T a : ℝ) / (b : ℝ) ^ (j + 1)))
  have hG : ∀ j, Measurable (G j) := fun j => measurable_of_countable _
  have hI := (iIndepFun_infinitePi (P := fun _ : ℕ => P) (X := G) hG).precomp
    (g := fun j : Fin K => (j : ℕ)) Fin.val_injective
  have e1 : ∀ ω : ℕ → α, ee (h * digSK b T K ω) = ∏ j : Fin K, G j (ω j) := by
    intro ω
    unfold digSK
    rw [Finset.mul_sum, ee_finset_sum, ← Fin.prod_univ_eq_prod_range]
  simp_rw [e1]
  rw [hI.integral_fun_prod_eq_prod_integral (fun j => ((hG j).comp (measurable_pi_apply _)).aestronglyMeasurable),
    ← Fin.prod_univ_eq_prod_range (fun j => ∫ a, G j a ∂P)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => P) (j : ℕ)
  have := integral_map (μ := Measure.infinitePi (fun _ : ℕ => P)) hmp.measurable.aemeasurable
    (hG j).aestronglyMeasurable
  rw [hmp.map_eq] at this
  exact this.symm

open DecayAeNormal ProbabilityTheory in
/-- Product-formula step `norm_prod_ge`. -/
theorem norm_prod_ge {ι : Type*} (s : Finset ι) (F : ι → ℂ) (hF : ∀ i, ‖F i‖ ≤ 1) :
    1 - ∑ i ∈ s, ‖1 - F i‖ ≤ ‖∏ i ∈ s, F i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, norm_mul]
    have h1 : 1 - ‖1 - F i‖ ≤ ‖F i‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - F i)
      simp at this; linarith
    have hp : 0 ≤ ‖∏ i ∈ s, F i‖ := norm_nonneg _
    have hq : 0 ≤ ‖F i‖ := norm_nonneg _
    have he : 0 ≤ ‖1 - F i‖ := norm_nonneg _
    have hS : 0 ≤ ∑ i ∈ s, ‖1 - F i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    by_cases hA : 1 - ‖1 - F i‖ ≤ 0
    · nlinarith
    by_cases hB : 1 - ∑ i ∈ s, ‖1 - F i‖ ≤ 0
    · nlinarith
    push Not at hA hB
    nlinarith [mul_le_mul h1 ih hB.le hq]

open DecayAeNormal ProbabilityTheory in
/-- Product-formula step `tendsto_integral_ee_digSK`. -/
theorem tendsto_integral_ee_digSK (P : Measure α) [IsProbabilityMeasure P] (b : ℕ) (hb : 2 ≤ b)
    (T : α → ℤ) (h : ℤ) :
    Tendsto (fun K => ∫ ω, ee (h * digSK b T K ω) ∂Measure.infinitePi (fun _ : ℕ => P)) atTop
      (𝓝 (∫ ω, ee (h * digS b T ω) ∂Measure.infinitePi (fun _ : ℕ => P))) := by
  set μ := Measure.infinitePi (fun _ : ℕ => P)
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  set B : ℝ := ∑ a, |(T a : ℝ)|
  have hmK : ∀ K, Measurable fun ω => ee (h * digSK b T K ω) := fun K =>
    measurable_ee.comp ((measurable_digSK b T K).const_mul _)
  have hbound : ∀ K, ‖(∫ ω, ee (h * digSK b T K ω) ∂μ) - ∫ ω, ee (h * digS b T ω) ∂μ‖
      ≤ 2 * Real.pi * |(h : ℝ)| * (B / (b : ℝ) ^ K) := by
    intro K
    rw [← integral_sub]
    · refine (norm_integral_le_of_norm_le_const (C := 2 * Real.pi * |(h : ℝ)| * (B / (b : ℝ) ^ K)) (Eventually.of_forall fun ω => ?_)).trans ?_
      · refine (norm_ee_sub_le _ _).trans ?_
        rw [← mul_sub, abs_mul, abs_sub_comm]
        have := abs_digS_sub_digSK b hb T K ω
        have hp : 0 ≤ 2 * Real.pi * |(h : ℝ)| := by positivity
        have := mul_le_mul_of_nonneg_left this hp
        linarith
      · simp
    · exact Integrable.of_bound (hmK K).aestronglyMeasurable 1 (Eventually.of_forall fun ω => (norm_ee _).le)
    · exact Integrable.of_bound (measurable_ee.comp ((measurable_digS b hb T).const_mul _)).aestronglyMeasurable 1 (Eventually.of_forall fun ω => (norm_ee _).le)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun K => norm_nonneg _) hbound ?_
  have : Tendsto (fun K : ℕ => B / (b : ℝ) ^ K) atTop (𝓝 0) := by
    simp_rw [div_eq_mul_inv, ← inv_pow]
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb')
    simpa using this.const_mul B
  simpa using this.const_mul (2 * Real.pi * |(h : ℝ)|)

open DecayAeNormal ProbabilityTheory in
/-- Product-formula step `integral_ee_digS_eq_zero_iff`. -/
theorem integral_ee_digS_eq_zero_iff (P : Measure α) [IsProbabilityMeasure P] (b : ℕ) (hb : 2 ≤ b)
    (T : α → ℤ) (h : ℤ) :
    ∫ ω, ee (h * digS b T ω) ∂Measure.infinitePi (fun _ : ℕ => P) = 0 ↔
      ∃ j, ∫ a, ee (h * ((T a : ℝ) / (b : ℝ) ^ (j + 1))) ∂P = 0 := by
  set F : ℕ → ℂ := fun j => ∫ a, ee (h * ((T a : ℝ) / (b : ℝ) ^ (j + 1))) ∂P with hFdef
  have hlim := tendsto_integral_ee_digSK P b hb T h
  simp_rw [integral_ee_digSK] at hlim
  have hF1 : ∀ j, ‖F j‖ ≤ 1 := fun j =>
    (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun a => (norm_ee _).le)).trans
      (by simp)
  constructor
  · intro h0
    by_contra hne
    push Not at hne
    -- tail bound
    have hb' : (1 : ℝ) < b := by exact_mod_cast hb
    set B : ℝ := ∑ a, |(T a : ℝ)|
    have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
    set C : ℝ := 2 * Real.pi * |(h : ℝ)| * B
    have hC : 0 ≤ C := by positivity
    have he : ∀ j, ‖1 - F j‖ ≤ C * ((b : ℝ)⁻¹ ^ (j + 1)) := by
      intro j
      have : (1 : ℂ) - F j = ∫ a, (ee 0 - ee (h * ((T a : ℝ) / (b : ℝ) ^ (j + 1)))) ∂P := by
        rw [integral_sub (integrable_const _), integral_const]
        · simp [ee, hFdef]
        · exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
            (Eventually.of_forall fun a => (norm_ee _).le)
      rw [this]
      refine (norm_integral_le_of_norm_le_const (C := C * ((b : ℝ)⁻¹ ^ (j + 1)))
        (Eventually.of_forall fun a => ?_)).trans (by simp)
      refine (norm_ee_sub_le _ _).trans ?_
      rw [zero_sub, abs_neg, abs_mul, abs_div, abs_of_pos (by positivity : (0:ℝ) < (b:ℝ)^(j+1)),
        inv_pow, ← div_eq_mul_inv]
      have := abs_T_le T a
      have : |(h:ℝ)| * (|(T a : ℝ)| / (b:ℝ)^(j+1)) ≤ |(h:ℝ)| * (B / (b:ℝ)^(j+1)) := by gcongr
      calc 2 * Real.pi * (|(h:ℝ)| * (|(T a : ℝ)| / (b:ℝ)^(j+1)))
          ≤ 2 * Real.pi * (|(h:ℝ)| * (B / (b:ℝ)^(j+1))) := by gcongr
        _ = C / (b:ℝ)^(j+1) := by ring
    have hsum : Summable fun j : ℕ => C * ((b : ℝ)⁻¹ ^ (j + 1)) :=
      ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ hb'))).mul_left C
    obtain ⟨J, hJ⟩ : ∃ J, ∑' j, C * ((b : ℝ)⁻¹ ^ (j + J + 1)) ≤ 1 / 2 := by
      have := tendsto_sum_nat_add (fun j => C * ((b : ℝ)⁻¹ ^ (j + 1)))
      obtain ⟨J, hJ⟩ := (this.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1 / 2))).exists
      exact ⟨J, by simpa [add_right_comm] using hJ⟩
    set c0 := ‖∏ j ∈ Finset.range J, F j‖
    have hc0 : 0 < c0 := norm_pos_iff.2 (Finset.prod_ne_zero_iff.2 fun j _ => hne j)
    have hlow : ∀ K, J ≤ K → c0 / 2 ≤ ‖∏ j ∈ Finset.range K, F j‖ := by
      intro K hK
      rw [← Finset.prod_range_mul_prod_Ico _ hK, norm_mul]
      have h2 := norm_prod_ge (Finset.Ico J K) F hF1
      have h3 : ∑ i ∈ Finset.Ico J K, ‖1 - F i‖ ≤ 1 / 2 := by
        refine (Finset.sum_le_sum fun i _ => he i).trans ?_
        rw [Finset.sum_Ico_eq_sum_range]
        refine le_trans ?_ hJ
        have hs2 : Summable fun j => C * ((b : ℝ)⁻¹ ^ (j + J + 1)) := by
          have := (summable_nat_add_iff J).2 hsum
          simpa [add_right_comm] using this
        refine (Summable.sum_le_tsum (Finset.range (K - J)) (fun j _ => by positivity) hs2).trans_eq' ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        ring_nf
      have : 1 / 2 ≤ ‖∏ i ∈ Finset.Ico J K, F i‖ := by linarith
      nlinarith
    have := (continuous_norm.tendsto _).comp hlim
    rw [h0, norm_zero] at this
    have hev : ∀ᶠ K in atTop, c0 / 2 ≤ ‖∏ j ∈ Finset.range K, F j‖ :=
      eventually_atTop.2 ⟨J, hlow⟩
    have := ge_of_tendsto this hev
    linarith
  · rintro ⟨j, hj⟩
    refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_gt_atTop j] with K hK
    exact (Finset.prod_eq_zero (Finset.mem_range.2 hK) hj).symm

end Product

open DecayAeNormal in
/-- One factor of the product: the digit polynomials. -/
theorem integral_ee_pair_factor {m : ℕ} [NeZero m] (b : ℕ) (dX dY : Fin m → ℕ) (a c h : ℤ) (j : ℕ) :
    ∫ p, ee (h * ((((fun p : Fin m × Fin m => a * dX p.1 + c * dY p.2) p : ℤ) : ℝ) / (b : ℝ) ^ (j + 1)))
        ∂(PMF.uniformOfFintype (Fin m × Fin m)).toMeasure =
      digitPoly dX (a * h / (b : ℝ) ^ (j + 1)) * digitPoly dY (c * h / (b : ℝ) ^ (j + 1)) := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_fin]
  unfold digitPoly
  rw [div_mul_div_comm, Finset.sum_mul_sum, Fintype.sum_prod_type, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  rw [← Complex.exp_add]
  unfold ee
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul]
  push_cast
  field_simp


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
  have key := integral_ee_digS_eq_zero_iff (PMF.uniformOfFintype (Fin m × Fin m)).toMeasure b hb
    (fun p => a * dX p.1 + c * dY p.2) h
  simp only [integral_ee_pair_factor] at key
  have hn : nuHat b dX dY a c h = ∫ ω, DecayAeNormal.ee (h * digS b (fun p : Fin m × Fin m =>
      a * dX p.1 + c * dY p.2) ω) ∂Measure.infinitePi
        (fun _ : ℕ => (PMF.uniformOfFintype (Fin m × Fin m)).toMeasure) := by
    simp only [nuHat, combo_eq_digS b hb]; rfl
  rw [hn, key]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j + 1, by omega, hj⟩
  · rintro ⟨i, hi, hz⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact ⟨j, hz⟩

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

/-- `e(s) = 1` iff `s ∈ ℤ`. -/
theorem exp_eq_one_iff_int (s : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * s) = 1 ↔ ∃ n : ℤ, s = n := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have : (s : ℂ) = n := by
      apply mul_left_cancel₀ h2; rw [hn]; ring
    exact_mod_cast this
  · rintro ⟨n, rfl⟩; exact ⟨n, by push_cast; ring⟩

/-- `φ_five(t) ≠ 0` unless `5t ∈ ℤ` and `t ∉ ℤ`. -/
theorem digitPoly_five_ne_zero (t : ℝ) (ht : ∀ k : ℤ, 5 * t = k → ∃ n : ℤ, t = n) :
    digitPoly five t ≠ 0 := by
  unfold digitPoly five
  rw [Fin.sum_univ_eq_sum_range (fun d => Complex.exp (2 * Real.pi * Complex.I * (t * (d : ℂ)))) 5]
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * t) with hz
  have hpow : ∀ d : ℕ, Complex.exp (2 * Real.pi * Complex.I * (t * (d : ℂ))) = z ^ d := by
    intro d; rw [hz, ← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [hpow]
  refine div_ne_zero ?_ (by norm_num)
  by_cases hint : ∃ n : ℤ, t = n
  · have : z = 1 := (exp_eq_one_iff_int t).2 hint
    rw [this]; norm_num
  · have hz1 : z ≠ 1 := fun h => hint ((exp_eq_one_iff_int t).1 h)
    have hz5 : z ^ 5 ≠ 1 := by
      intro h
      rw [hz, ← Complex.exp_nat_mul] at h
      have : Complex.exp (2 * Real.pi * Complex.I * ((5 * t : ℝ) : ℂ)) = 1 := by
        rw [← h]; congr 1; push_cast; ring
      obtain ⟨k, hk⟩ := (exp_eq_one_iff_int _).1 this
      exact hint (ht k hk)
    rw [geom_sum_eq hz1]
    exact div_ne_zero (sub_ne_zero.2 hz5) (sub_ne_zero.2 hz1)

/-- For `h = 5^N` with `2^N > |a|`, no factor `φ_five(a h / 10^i)` vanishes. -/
theorem five_int_cond (a : ℤ) (N : ℕ) (hN : a.natAbs < 2 ^ N) (i : ℕ) (k : ℤ)
    (hk : 5 * ((a : ℝ) * ((5 ^ N : ℤ) : ℝ) / (10 : ℝ) ^ i) = k) :
    ∃ n : ℤ, (a : ℝ) * ((5 ^ N : ℤ) : ℝ) / (10 : ℝ) ^ i = n := by
  have h10 : (0:ℝ) < 10 ^ i := by positivity
  have hk' : (a * 5 ^ (N + 1) : ℤ) = k * 2 ^ i * 5 ^ i := by
    have : (5:ℝ) * (a * (5:ℝ) ^ N) = k * (10:ℝ) ^ i := by
      rw [← hk]; push_cast; field_simp
    have h' : ((a * 5 ^ (N + 1) : ℤ) : ℝ) = ((k * 2 ^ i * 5 ^ i : ℤ) : ℝ) := by
      push_cast; rw [show (10:ℝ)^i = 2^i * 5^i by rw [← mul_pow]; norm_num] at this
      linear_combination this
    exact_mod_cast h'
  have h2 : (2 : ℤ) ^ i ∣ a := by
    have : (2:ℤ) ^ i ∣ a * 5 ^ (N + 1) := ⟨k * 5 ^ i, by rw [hk']; ring⟩
    have hc : IsCoprime ((2:ℤ) ^ i) ((5:ℤ) ^ (N + 1)) :=
      IsCoprime.pow (Int.isCoprime_iff_gcd_eq_one.2 (by norm_num))
    exact hc.dvd_of_dvd_mul_right this
  obtain ⟨q, rfl⟩ := h2
  by_cases hq : q = 0
  · exact ⟨0, by simp [hq]⟩
  have hi : i < N := by
    have h1 : 2 ^ i ≤ (2 ^ i * q).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_pow]
      exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.2 hq)
    have : 2 ^ i < 2 ^ N := lt_of_le_of_lt h1 hN
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  refine ⟨q * 5 ^ (N - i), ?_⟩
  have hNi : N = (N - i) + i := by omega
  push_cast
  rw [hNi, pow_add, show (10:ℝ)^i = 2^i * 5^i by rw [← mul_pow]; norm_num]
  rw [show N - i + i - i = N - i by omega]
  field_simp

theorem factor_five_ne (a : ℤ) (N : ℕ) (hN : a.natAbs < 2 ^ N) (i : ℕ) :
    digitPoly five ((a : ℝ) * ((5 ^ N : ℤ) : ℝ) / ((10 : ℕ) : ℝ) ^ i) ≠ 0 := by
  have := digitPoly_five_ne_zero ((a : ℝ) * ((5 ^ N : ℤ) : ℝ) / (10 : ℝ) ^ i)
    (fun k hk => five_int_cond a N hN i k hk)
  simpa using this

/-- **Necessary, not sufficient: enough joint entropy, no normal combination.**  Confidence 85%.
English proof: by Wall reduce to integer `(a, c) ≠ 0`; take `h = 5^N` with `N > v₅(a), v₅(c)`
(or the one nonzero coefficient's valuation).  `φ_five(t) = 0` iff `5t ∈ ℤ`, `t ∉ ℤ`; at
`t = a 5^N / 10ⁱ` this needs `i = v₅(a 5^N) + 1 ≤ v₂(a)`, false for large `N`.  So no factor
vanishes; `ae_not_isNormal_combo_of_not`, countably many `(a, c)`. -/
theorem ae_not_qSpanNormal_fiveDigits :
    ∀ᵐ ω ∂pairs 5, ¬ QSpanNormal 10 (realX 10 five ω) (realY 10 five ω) := by
  have hfive : ∀ j, five j < 10 := fun j => by unfold five; omega
  have hall : ∀ᵐ ω ∂pairs 5, ∀ p : ℤ × ℤ, p ≠ 0 →
      ¬ IsNormal 10 (p.1 * realX 10 five ω + p.2 * realY 10 five ω) := by
    rw [ae_all_iff]; intro p
    by_cases hp : p = 0
    · exact Eventually.of_forall fun _ h => absurd hp h
    · set N := p.1.natAbs + p.2.natAbs
      have h1 : p.1.natAbs < 2 ^ N := lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self)
      have h2 : p.2.natAbs < 2 ^ N := lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self)
      have := ae_not_isNormal_combo_of_not 10 5 (by norm_num) five five hfive hfive p.1 p.2
        ⟨5 ^ N, by positivity, fun i _ => mul_ne_zero (factor_five_ne p.1 N h1 i)
          (factor_five_ne p.2 N h2 i)⟩
      filter_upwards [this] with ω hω _ using hω
  filter_upwards [hall] with ω hω
  rintro ⟨c₁, c₂, hne, hN⟩
  set q : ℚ := ((c₁.den * c₂.den : ℕ) : ℚ) with hqdef
  have hq : q ≠ 0 := by
    rw [hqdef]; exact_mod_cast Nat.mul_ne_zero c₁.den_nz c₂.den_nz
  have hW := isNormal_rat_mul_add 10 (by norm_num) _ q 0 hq hN
  apply hω (c₁.num * c₂.den, c₂.num * c₁.den)
  · intro h0
    simp only [Prod.mk_eq_zero, mul_eq_zero, Int.natCast_eq_zero, Rat.num_eq_zero] at h0
    rcases hne with h | h
    · exact h (h0.1.resolve_right c₂.den_nz)
    · exact h (h0.2.resolve_right c₁.den_nz)
  · convert hW using 1
    have e1 : ((c₁.num : ℝ)) = (c₁ : ℝ) * c₁.den := by
      exact_mod_cast (Rat.mul_den_eq_num c₁).symm
    have e2 : ((c₂.num : ℝ)) = (c₂ : ℝ) * c₂.den := by
      exact_mod_cast (Rat.mul_den_eq_num c₂).symm
    simp only [hqdef]
    push_cast
    rw [e1, e2]; ring

/-- Letters of `Fin 5 × Fin 5` as letters of `Fin 100`. -/
def emb5 (p : Fin 5 × Fin 5) : Fin (10 * 10) :=
  finProdFinEquiv (Fin.castLE (by norm_num) p.1, Fin.castLE (by norm_num) p.2)

theorem emb5_injective : Function.Injective emb5 := by
  intro p q h
  have := finProdFinEquiv.injective h
  simp only [Prod.mk.injEq] at this
  exact Prod.ext (Fin.castLE_injective _ this.1) (Fin.castLE_injective _ this.2)

theorem digitOf_realX_five (ω : ℕ → Fin 5 × Fin 5) (i : ℕ) :
    digitOf 10 (Int.fract (realX 10 five ω)) i = (ω i).1 := by
  have hs : ∀ i, five (ω i).1 < 10 := fun i => by unfold five; omega
  have hp : ProperDigits 10 fun i => five (ω i).1 := fun N => ⟨N, le_rfl, by have := (ω N).1.isLt; show five (ω N).1 ≠ 10 - 1; unfold five; omega⟩
  have hx : realX 10 five ω = realOfDigits 10 fun i => five (ω i).1 := rfl
  rw [hx, Int.fract_eq_self.mpr (realOfDigits_mem_Ico 10 (by norm_num) _ hs hp),
    digitOf_realOfDigits 10 (by norm_num) _ hs hp]
  rfl

theorem digitOf_realY_five (ω : ℕ → Fin 5 × Fin 5) (i : ℕ) :
    digitOf 10 (Int.fract (realY 10 five ω)) i = (ω i).2 := by
  have hs : ∀ i, five (ω i).2 < 10 := fun i => by unfold five; omega
  have hp : ProperDigits 10 fun i => five (ω i).2 := fun N => ⟨N, le_rfl, by have := (ω N).2.isLt; show five (ω N).2 ≠ 10 - 1; unfold five; omega⟩
  have hx : realY 10 five ω = realOfDigits 10 fun i => five (ω i).2 := rfl
  rw [hx, Int.fract_eq_self.mpr (realOfDigits_mem_Ico 10 (by norm_num) _ hs hp),
    digitOf_realOfDigits 10 (by norm_num) _ hs hp]
  rfl

theorem digitPair_five (ω : ℕ → Fin 5 × Fin 5) (i : ℕ) :
    digitPair 10 (by norm_num) (realX 10 five ω) (realY 10 five ω) i = emb5 (ω i) := by
  unfold digitPair emb5 digitSeq
  congr 2 <;> ext <;> simp [digitOf_realX_five, digitOf_realY_five]

/-- A fixed word of length `n` is a prefix with probability at most `25⁻ⁿ`. -/
theorem pairs_prefix_le (n : ℕ) (w : List (Fin (10 * 10))) :
    pairs 5 {ω | pre (fun i => emb5 (ω i)) n = w} ≤ (25 : ℝ≥0∞)⁻¹ ^ n := by
  classical
  let t : ℕ → Set (Fin 5 × Fin 5) := fun i => emb5 ⁻¹' {w.getD i 0}
  have hsub : {ω | pre (fun i => emb5 (ω i)) n = w} ⊆ Set.pi (Finset.range n : Set ℕ) t := by
    intro ω hω i hi
    simp only [Set.mem_setOf_eq] at hω
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    subst hω
    simp [t, pre, hi]
  refine (measure_mono hsub).trans ?_
  rw [pairs, Measure.infinitePi_pi (μ := fun _ : ℕ => (PMF.uniformOfFintype (Fin 5 × Fin 5)).toMeasure)
    (fun i _ => MeasurableSet.of_discrete)]
  refine (Finset.prod_le_prod' (s := Finset.range n) (g := fun _ => (25 : ℝ≥0∞)⁻¹)
    fun i _ => ?_).trans (by simp)
  by_cases h : ∃ p, emb5 p = w.getD i 0
  · obtain ⟨p, hp⟩ := h
    have : t i = {p} := by
      ext q; simp only [t, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hq => emb5_injective (hq.trans hp.symm), fun hq => hq ▸ hp⟩
    rw [this, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
      PMF.uniformOfFintype_apply]
    simp
  · have : t i = ∅ := by
      ext q; simp only [t, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      exact fun hq => h ⟨q, hq⟩
    simp [this]

theorem nat_key (l n : ℕ) (h : 5 * l < 3 * n) : 100 ^ l * 3 ^ n ≤ 50 ^ n := by
  have h1 : (100 ^ l * 3 ^ n) ^ 5 ≤ (50 ^ n) ^ 5 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
    have : 100 ^ (l * 5) ≤ 10 ^ (6 * n) := by
      rw [show (100 : ℕ) = 10 ^ 2 by norm_num, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 100 ^ (l * 5) * 3 ^ (n * 5) ≤ 10 ^ (6 * n) * 3 ^ (n * 5) := Nat.mul_le_mul_right _ this
      _ = (10 ^ 6 * 3 ^ 5) ^ n := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 5 n]
      _ ≤ (50 ^ 5) ^ n := Nat.pow_le_pow_left (by norm_num) _
      _ = 50 ^ (n * 5) := by rw [← pow_mul, mul_comm]
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1


instance countable_FST (k : ℕ) : Countable (FST k) := by
  let f : FST k → Σ m : ℕ, (Fin (m + 1) → Fin k → Fin (m + 1)) × (Fin (m + 1) → Fin k → List (Fin k)) :=
    fun T => ⟨T.m, T.δ, T.ν⟩
  refine Function.Injective.countable (f := f) ?_
  rintro ⟨m, δ, ν⟩ ⟨m', δ', ν'⟩ h
  simp only [f, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem term_le (l n : ℕ) (h : 5 * l < 3 * n) :
    (100 : ℝ≥0∞) ^ l * (25 : ℝ≥0∞)⁻¹ ^ n ≤ (((2 / 3 : NNReal) ^ n : NNReal) : ℝ≥0∞) := by
  have hk := nat_key l n h
  have h2 : ((100 : NNReal) ^ l * 3 ^ n) ≤ 25 ^ n * 2 ^ n := by
    rw [← mul_pow]; exact_mod_cast hk
  have h3 : (100 : NNReal) ^ l * (25 : NNReal)⁻¹ ^ n ≤ (2 / 3) ^ n := by
    rw [inv_pow, div_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 100 ^ l * 3 ^ n ≤ 25 ^ n * 2 ^ n := h2
      _ = 2 ^ n * 25 ^ n := mul_comm _ _
  calc (100 : ℝ≥0∞) ^ l * (25 : ℝ≥0∞)⁻¹ ^ n
      = (((100 : NNReal) ^ l * (25 : NNReal)⁻¹ ^ n : NNReal) : ℝ≥0∞) := by
        push_cast [ENNReal.coe_inv (by norm_num : (25 : NNReal) ≠ 0)]; rfl
    _ ≤ _ := by exact_mod_cast h3

/-- The bad event: a description shorter than `3n/5` letters. -/
def shortEv (T : FST (10 * 10)) (n : ℕ) : Set (ℕ → Fin 5 × Fin 5) :=
  {ω | ∃ π : List (Fin (10 * 10)), 5 * π.length < 3 * n ∧ T.run π = pre (fun i => emb5 (ω i)) n}

theorem shortEv_le (T : FST (10 * 10)) (n : ℕ) :
    pairs 5 (shortEv T n) ≤ ((n * (2 / 3 : NNReal) ^ n : NNReal) : ℝ≥0∞) := by
  classical
  have hsub : shortEv T n ⊆ ⋃ l ∈ (Finset.range n).filter (fun l => 5 * l < 3 * n),
      ⋃ v : Fin l → Fin (10 * 10), {ω | pre (fun i => emb5 (ω i)) n = T.run (List.ofFn v)} := by
    rintro ω ⟨π, hπ, hrun⟩
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_range]
    refine ⟨π.length, ⟨by omega, hπ⟩, fun i => π.get i, ?_⟩
    simp only [Set.mem_setOf_eq, List.ofFn_get]; exact hrun.symm
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ l ∈ (Finset.range n).filter (fun l => 5 * l < 3 * n), pairs 5 (⋃ v : Fin l → Fin (10 * 10),
        {ω | pre (fun i => emb5 (ω i)) n = T.run (List.ofFn v)})
      ≤ ∑ l ∈ (Finset.range n).filter (fun l => 5 * l < 3 * n),
          (((2 / 3 : NNReal) ^ n : NNReal) : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun l hl => ?_
        rw [Finset.mem_filter] at hl
        refine (measure_iUnion_fintype_le _ _).trans ?_
        refine (Finset.sum_le_sum fun v _ => pairs_prefix_le n _).trans ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        refine le_trans (le_of_eq ?_) (term_le l n hl.2)
        push_cast; ring
    _ ≤ ∑ l ∈ Finset.range n, (((2 / 3 : NNReal) ^ n : NNReal) : ℝ≥0∞) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = _ := by simp

theorem ae_eventually_not_shortEv (T : FST (10 * 10)) :
    ∀ᵐ ω ∂pairs 5, ∀ᶠ n in atTop, ω ∉ shortEv T n := by
  have hsum : ∑' n, pairs 5 (shortEv T n) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (shortEv_le T))
    rw [← ENNReal.coe_tsum]
    · exact ENNReal.coe_ne_top
    · rw [← NNReal.summable_coe]
      push_cast
      have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (2 / 3 : ℝ))
        (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)
      simpa using this
  exact ae_eventually_notMem hsum

theorem liminf_ge_of_eventually (T : FST (10 * 10)) (ω : ℕ → Fin 5 × Fin 5)
    (h : ∀ᶠ n in atTop, ω ∉ shortEv T n) :
    (3 / 5 : ℝ≥0∞) ≤ liminf (fun n : ℕ =>
      ((infoK T (pre (fun i => emb5 (ω i)) n) : ℕ∞) : ℝ≥0∞) / (n : ℝ≥0∞)) atTop := by
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  set c := (3 * n + 4) / 5
  have hc : (c : ℕ∞) ≤ infoK T (pre (fun i => emb5 (ω i)) n) := by
    refine le_iInf₂ fun π hπ => ?_
    have : ¬ 5 * π.length < 3 * n := fun h' => hn ⟨π, h', hπ⟩
    exact_mod_cast (by omega : c ≤ π.length)
  have hc' : ((c : ℕ) : ℝ≥0∞) ≤ ((infoK T (pre (fun i => emb5 (ω i)) n) : ℕ∞) : ℝ≥0∞) := by
    exact_mod_cast ENat.toENNReal_le.mpr hc
  refine le_trans ?_ (ENNReal.div_le_div_right hc' _)
  rw [ENNReal.le_div_iff_mul_le (by left; exact_mod_cast (by omega : n ≠ 0)) (by left; simp)]
  rw [div_eq_mul_inv, mul_comm, ← mul_assoc, ← div_eq_mul_inv,
    ENNReal.div_le_iff (by norm_num) (by norm_num)]
  exact_mod_cast (by omega : n * 3 ≤ c * 5)


/-- The same pair has joint finite-state dimension above the budget `1/2`
(`log 25 / log 100 ≈ 0.70`).  Confidence 85% (Bernoulli entropy rate; the digits of `realX` are
the letters, no `9`-tails since digits are `≤ 4`). -/
theorem ae_jointDim_fiveDigits :
    ∀ᵐ ω ∂pairs 5, 1 / 2 < fsDim (digitPair 10 (by norm_num) (realX 10 five ω) (realY 10 five ω)) := by
  have hall : ∀ᵐ ω ∂pairs 5, ∀ T : FST (10 * 10), ∀ᶠ n in atTop, ω ∉ shortEv T n :=
    ae_all_iff.mpr ae_eventually_not_shortEv
  filter_upwards [hall] with ω hω
  have hS : digitPair 10 (by norm_num) (realX 10 five ω) (realY 10 five ω) =
      fun i => emb5 (ω i) := funext (digitPair_five ω)
  rw [hS]
  refine lt_of_lt_of_le ?_ (le_iInf fun T => liminf_ge_of_eventually T ω (hω T))
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num), div_eq_mul_inv, mul_assoc,
    mul_comm _ (2 : ℝ≥0∞), ← mul_assoc, ← div_eq_mul_inv,
    ENNReal.lt_div_iff_mul_lt (by norm_num) (by norm_num)]
  norm_num


end NormalNumbers.QSpanCriterion
