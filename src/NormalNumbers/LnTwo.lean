/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs
import NormalNumbers.Wall

/-!
# The Bailey–Crandall reduction for `ln 2`

`ln 2 = Σ_{n≥1} 1/(n·2ⁿ)`, so `2^N·ln 2 mod 1` is shadowed, with `O(1/N)`
error, by the explicit orbit `x₀ = 0, xₙ = 2·xₙ₋₁ + 1/n mod 1`.  Bailey and
Crandall (Exp. Math. 10 (2001) 175–190): if that orbit is equidistributed
mod 1, then `ln 2` is normal in base 2.

The point of formalizing the reduction is that the hypothesis
(`Equidistributed lnTwoOrbit`) mentions no logarithm: it is a single
concrete statement in arithmetic dynamics, and this file welds it,
machine-checked, to the normality of `ln 2`.

The chain:
* `hasSum_lnTwoSeries` / `log_two_eq_tsum`: the series identity, from
  mathlib's `Real.hasSum_pow_div_log_of_abs_lt_one` at `x = 1/2`;
* `lnTwoOrbit_eq_fract`: the surrogate orbit is `2^n·(partial sum) mod 1`;
* `lnTwoTail_nonneg` / `lnTwoTail_le`: the scaled tail lies in `[0, 1/(n+1)]`;
* `orbit_log_two_eq`: the true orbit of `ln 2` is the surrogate orbit
  perturbed by the scaled tail;
* `equidistributed_of_fract_perturb`: equidistribution is stable under a
  nonnegative perturbation tending to `0` (wraparound handled);
* `isNormal_log_two_of_equidistributed`: the wiring, through Wall's theorem.
-/

namespace NormalNumbers

/-- The Bailey–Crandall surrogate orbit for `ln 2`:
`x₀ = 0, xₙ = 2·xₙ₋₁ + 1/n  (mod 1)`.  Explicitly,
`xₙ = Σ_{k=1}^{n} 2^(n−k)/k  mod 1`. -/
noncomputable def lnTwoOrbit : ℕ → ℝ
  | 0 => 0
  | n + 1 => Int.fract (2 * lnTwoOrbit n + 1 / (n + 1))

/-- Comparator non-vacuity anchor: the first nonzero surrogate-orbit value is `1/2`. -/
theorem lnTwoOrbit_two_anchor : lnTwoOrbit 2 = (1 : ℝ) / 2 := by
  norm_num [lnTwoOrbit, Int.fract]

/-! ### Target 1: the series identity -/

/-- The Mercator series at `x = 1/2`:
`Σ_{k≥0} 1/((k+1)·2^(k+1)) = ln 2`. -/
theorem hasSum_lnTwoSeries :
    HasSum (fun k : ℕ => 1 / ((k + 1 : ℝ) * 2 ^ (k + 1))) (Real.log 2) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := (1 : ℝ) / 2) (by rw [abs_of_nonneg] <;> norm_num)
  have h12 : (1 : ℝ) - 1 / 2 = 2⁻¹ := by norm_num
  rw [h12, Real.log_inv, neg_neg] at h
  have hfun : (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1) / (n + 1))
      = fun k : ℕ => 1 / ((k + 1 : ℝ) * 2 ^ (k + 1)) := by
    funext k
    rw [div_pow, one_pow, div_div, mul_comm ((2 : ℝ) ^ (k + 1)) ((k : ℝ) + 1)]
  rwa [hfun] at h

/-- **Series identity**: `ln 2 = Σ_{n≥0} 1/((n+1)·2^(n+1))`. -/
theorem log_two_eq_tsum : Real.log 2 = ∑' n : ℕ, 1 / ((n + 1 : ℝ) * 2 ^ (n + 1)) :=
  hasSum_lnTwoSeries.tsum_eq.symm

/-! ### Target 2: closed form of the surrogate orbit -/

/-- Partial sums of the `ln 2` series: `Σ_{k<n} 1/((k+1)·2^(k+1))`. -/
noncomputable def lnTwoPartial (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℝ) * 2 ^ (k + 1))

theorem lnTwoPartial_succ (n : ℕ) :
    lnTwoPartial (n + 1) = lnTwoPartial n + 1 / ((n + 1 : ℝ) * 2 ^ (n + 1)) :=
  Finset.sum_range_succ _ n

/-- `Int.fract (2·y + c)` sees `y` only through `Int.fract y`. -/
private lemma fract_two_mul_fract_add (y c : ℝ) :
    Int.fract (2 * Int.fract y + c) = Int.fract (2 * y + c) := by
  have h : 2 * Int.fract y + c = 2 * y + c - ((2 * ⌊y⌋ : ℤ) : ℝ) := by
    have h2 := Int.floor_add_fract y
    push_cast
    linarith
  rw [h, Int.fract_sub_intCast]

/-- `Int.fract (·+ d)` sees its argument only through `Int.fract`. -/
private lemma fract_fract_add (y d : ℝ) :
    Int.fract (Int.fract y + d) = Int.fract (y + d) := by
  have h : Int.fract y + d = y + d - ((⌊y⌋ : ℤ) : ℝ) := by
    have h2 := Int.floor_add_fract y
    linarith
  rw [h, Int.fract_sub_intCast]

/-- **Closed form**: the surrogate orbit is the doubling orbit of the
partial sums, `xₙ = 2ⁿ·(Σ_{k<n} 1/((k+1)·2^(k+1))) mod 1`. -/
theorem lnTwoOrbit_eq_fract (n : ℕ) :
    lnTwoOrbit n = Int.fract (2 ^ n * lnTwoPartial n) := by
  induction n with
  | zero => simp [lnTwoOrbit, lnTwoPartial]
  | succ n ih =>
    have hstep : (2 : ℝ) ^ (n + 1) * lnTwoPartial (n + 1)
        = 2 * (2 ^ n * lnTwoPartial n) + 1 / (n + 1) := by
      rw [lnTwoPartial_succ]
      have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((2 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
      field_simp
      ring
    rw [lnTwoOrbit, ih, fract_two_mul_fract_add, ← hstep]

/-! ### Target 3: the tail bound -/

/-- The tail of the `ln 2` series past the first `n` terms. -/
noncomputable def lnTwoTail (n : ℕ) : ℝ := Real.log 2 - lnTwoPartial n

theorem lnTwoPartial_le_log_two (n : ℕ) : lnTwoPartial n ≤ Real.log 2 := by
  rw [← hasSum_lnTwoSeries.tsum_eq]
  exact hasSum_lnTwoSeries.summable.sum_le_tsum (Finset.range n) (fun i _ => by positivity)

theorem lnTwoTail_nonneg (n : ℕ) : 0 ≤ lnTwoTail n := by
  rw [lnTwoTail, sub_nonneg]
  exact lnTwoPartial_le_log_two n

theorem pow_mul_lnTwoTail_nonneg (n : ℕ) : 0 ≤ 2 ^ n * lnTwoTail n :=
  mul_nonneg (by positivity) (lnTwoTail_nonneg n)

/-- **Tail bound**: `2ⁿ·(ln 2 − Σ_{k<n}) ≤ 1/(n+1)`. -/
theorem lnTwoTail_le (n : ℕ) : 2 ^ n * lnTwoTail n ≤ 1 / (n + 1) := by
  set f : ℕ → ℝ := fun k : ℕ => 1 / ((k + 1 : ℝ) * 2 ^ (k + 1)) with hf
  have hsummable : Summable f := hasSum_lnTwoSeries.summable
  have key := hsummable.sum_add_tsum_nat_add n
  have htail : lnTwoTail n = ∑' i : ℕ, f (i + n) := by
    have hpart : lnTwoPartial n = ∑ i ∈ Finset.range n, f i := rfl
    have hlog : Real.log 2 = ∑' i, f i := hasSum_lnTwoSeries.tsum_eq.symm
    rw [lnTwoTail, hpart, hlog, ← key]
    ring
  have hgeom : HasSum (fun i : ℕ => (1 / (n + 1 : ℝ)) * ((1 / 2 : ℝ) ^ (n + 1) * (1 / 2 : ℝ) ^ i))
      ((1 / (n + 1 : ℝ)) * ((1 / 2 : ℝ) ^ (n + 1) * ((1 : ℝ) - 1 / 2)⁻¹)) :=
    ((hasSum_geometric_of_lt_one (r := 1 / 2) (by norm_num) (by norm_num)).mul_left
      ((1 / 2 : ℝ) ^ (n + 1))).mul_left (1 / (n + 1 : ℝ))
  have hterm : ∀ i : ℕ, f (i + n)
      ≤ (1 / (n + 1 : ℝ)) * ((1 / 2 : ℝ) ^ (n + 1) * (1 / 2 : ℝ) ^ i) := by
    intro i
    show 1 / (((i + n : ℕ) + 1 : ℝ) * 2 ^ (i + n + 1)) ≤ _
    have h1 : ((n : ℝ) + 1) ≤ ((i + n : ℕ) : ℝ) + 1 := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) i]
    rw [show i + n + 1 = n + 1 + i by omega]
    rw [div_pow, div_pow, one_pow, one_pow, div_mul_div_comm, one_mul,
      div_mul_div_comm, one_mul, ← pow_add]
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hs1 : Summable fun i : ℕ => f (i + n) := (summable_nat_add_iff n).mpr hsummable
  have hle : (∑' i : ℕ, f (i + n))
      ≤ (1 / (n + 1 : ℝ)) * ((1 / 2 : ℝ) ^ (n + 1) * ((1 : ℝ) - 1 / 2)⁻¹) :=
    le_trans (Summable.tsum_le_tsum hterm hs1 hgeom.summable) (le_of_eq hgeom.tsum_eq)
  rw [htail]
  refine le_trans (mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 2 ^ n)) ?_
  rw [show ((1 : ℝ) - 1 / 2)⁻¹ = 2 by norm_num, div_pow, one_pow]
  apply le_of_eq
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((2 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
  field_simp
  ring

/-- The scaled tail tends to `0` (squeezed into `[0, 1/(n+1)]`). -/
theorem tendsto_pow_mul_lnTwoTail :
    Filter.Tendsto (fun n : ℕ => 2 ^ n * lnTwoTail n) Filter.atTop (nhds 0) :=
  squeeze_zero pow_mul_lnTwoTail_nonneg lnTwoTail_le tendsto_one_div_add_atTop_nhds_zero_nat

/-! ### Target 4: the orbit comparison -/

/-- **Orbit comparison**: the doubling orbit of `ln 2` is the surrogate
orbit perturbed by the scaled tail. -/
theorem orbit_log_two_eq (n : ℕ) :
    orbit 2 (Real.log 2) n = Int.fract (lnTwoOrbit n + 2 ^ n * lnTwoTail n) := by
  have hsplit : Real.log 2 * ((2 : ℕ) : ℝ) ^ n
      = 2 ^ n * lnTwoPartial n + 2 ^ n * lnTwoTail n := by
    rw [lnTwoTail]
    push_cast
    ring
  rw [orbit, hsplit, lnTwoOrbit_eq_fract, fract_fract_add]

/-! ### Target 5: equidistribution is stable under a vanishing perturbation

The counting core: `filter`-cardinal comparisons that tolerate a finite
initial segment where the pointwise implication may fail. -/

private lemma card_filter_le_card_filter_add {P Q : ℕ → Prop}
    [DecidablePred P] [DecidablePred Q] (N : ℕ)
    (h : ∀ k, N ≤ k → P k → Q k) (n : ℕ) :
    ((Finset.range n).filter P).card ≤ ((Finset.range n).filter Q).card + N := by
  have hsub : (Finset.range n).filter P ⊆ (Finset.range n).filter Q ∪ Finset.range N := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hk ⊢
    rcases le_or_gt N k with hNk | hNk
    · exact Or.inl ⟨hk.1, h k hNk hk.2⟩
    · exact Or.inr hNk
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((Finset.range n).filter Q) (Finset.range N)
  have h3 := Finset.card_range N
  omega

private lemma card_filter_le_card_filter_or_add {P Q R : ℕ → Prop}
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] (N : ℕ)
    (h : ∀ k, N ≤ k → P k → Q k ∨ R k) (n : ℕ) :
    ((Finset.range n).filter P).card
      ≤ ((Finset.range n).filter Q).card + ((Finset.range n).filter R).card + N := by
  have hsub : (Finset.range n).filter P
      ⊆ ((Finset.range n).filter Q ∪ (Finset.range n).filter R) ∪ Finset.range N := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hk ⊢
    rcases le_or_gt N k with hNk | hNk
    · rcases h k hNk hk.2 with hQ | hR
      · exact Or.inl (Or.inl ⟨hk.1, hQ⟩)
      · exact Or.inl (Or.inr ⟨hk.1, hR⟩)
    · exact Or.inr hNk
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le
    ((Finset.range n).filter Q ∪ (Finset.range n).filter R) (Finset.range N)
  have h3 := Finset.card_union_le ((Finset.range n).filter Q) ((Finset.range n).filter R)
  have h4 := Finset.card_range N
  omega

/-- Pointwise upper inclusion: if the perturbed point lands in `[a, c)`,
the original point lies in a slightly enlarged interval, or (wraparound)
in a short interval at the top of `[0, 1)`. -/
private lemma mem_Ico_of_fract_add_mem {a c e x d : ℝ} (he1 : e ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hd0 : 0 ≤ d) (hde : d < e)
    (hmem : Int.fract (x + d) ∈ Set.Ico a c) :
    x ∈ Set.Ico (max (a - e) 0) c ∨ x ∈ Set.Ico (min (a + 1 - e) 1) 1 := by
  rcases lt_or_ge (x + d) 1 with h1 | h1
  · left
    rw [Int.fract_eq_self.mpr ⟨by linarith, h1⟩] at hmem
    obtain ⟨hm1, hm2⟩ := hmem
    exact ⟨max_le (by linarith) hx0, by linarith⟩
  · right
    have hfr : Int.fract (x + d) = x + d - 1 := by
      have h2 : x + d - 1 + ((1 : ℤ) : ℝ) = x + d := by push_cast; ring
      rw [← h2, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
      push_cast
      ring
    rw [hfr] at hmem
    obtain ⟨hm1, hm2⟩ := hmem
    exact ⟨(min_le_left _ _).trans (by linarith), hx1⟩

/-- Pointwise lower inclusion: a point of `[a, max a (c−e))` stays inside
`[a, c)` after any perturbation `0 ≤ d < e` (no wraparound can occur). -/
private lemma fract_add_mem_Ico {a c e x d : ℝ} (hc1 : c ≤ 1)
    (hx0 : 0 ≤ x) (hd0 : 0 ≤ d) (hde : d < e)
    (hmem : x ∈ Set.Ico a (max a (c - e))) :
    Int.fract (x + d) ∈ Set.Ico a c := by
  obtain ⟨hm1, hm2⟩ := hmem
  have hxc : x < c - e := by
    rcases max_cases a (c - e) with ⟨heq, _⟩ | ⟨heq, _⟩ <;> rw [heq] at hm2
    · linarith
    · exact hm2
  rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  exact ⟨by linarith, by linarith⟩

/-- **Equidistribution stability**: perturbing an equidistributed sequence
in `[0, 1)` by a nonnegative vanishing amount (mod 1) preserves
equidistribution.  Wraparound is handled by covering with two intervals. -/
theorem equidistributed_of_fract_perturb (u δ : ℕ → ℝ)
    (hu : Equidistributed u) (hu01 : ∀ n, u n ∈ Set.Ico (0 : ℝ) 1)
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Equidistributed (fun n => Int.fract (u n + δ n)) := by
  intro a c ha hac hc1
  have hc0 : (0 : ℝ) ≤ c := ha.trans hac
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e : ℝ := min (ε / 8) 1 with he_def
  have he0 : 0 < e := lt_min (by positivity) one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have hee : e ≤ ε / 8 := min_le_left _ _
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hδ.eventually_lt_const he0)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp
    (hu (max (a - e) 0) c (le_max_right _ _) (max_le (by linarith) hc0) hc1) e he0
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp
    (hu (min (a + 1 - e) 1) 1 (le_min (by linarith) zero_le_one) (min_le_right _ _) le_rfl) e he0
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.mp
    (hu a (max a (c - e)) ha (le_max_left _ _) (max_le (hac.trans hc1) (by linarith))) e he0
  obtain ⟨N₄, hN₄⟩ := Metric.tendsto_atTop.mp
    (tendsto_const_div_atTop_nhds_zero_nat (N₀ : ℝ)) e he0
  have upper : ∀ m : ℕ, visitCount (fun k => Int.fract (u k + δ k)) a c m
      ≤ visitCount u (max (a - e) 0) c m + visitCount u (min (a + 1 - e) 1) 1 m + N₀ := by
    intro m
    unfold visitCount
    exact card_filter_le_card_filter_or_add N₀
      (fun k hk hP => mem_Ico_of_fract_add_mem he1 (hu01 k).1 (hu01 k).2 (hδ0 k) (hN₀ k hk) hP) m
  have lower : ∀ m : ℕ, visitCount u a (max a (c - e)) m
      ≤ visitCount (fun k => Int.fract (u k + δ k)) a c m + N₀ := by
    intro m
    unfold visitCount
    exact card_filter_le_card_filter_add N₀
      (fun k hk hP => fract_add_mem_Ico hc1 (hu01 k).1 (hδ0 k) (hN₀ k hk) hP) m
  refine ⟨max (max N₁ N₂) (max N₃ N₄), fun n hn => ?_⟩
  have b₁ := hN₁ n (by omega)
  have b₂ := hN₂ n (by omega)
  have b₃ := hN₃ n (by omega)
  have b₄ := hN₄ n (by omega)
  rw [Real.dist_eq, abs_sub_lt_iff] at b₁ b₂ b₃ b₄
  have hVle : (visitCount (fun k => Int.fract (u k + δ k)) a c n : ℝ) / n
      ≤ (visitCount u (max (a - e) 0) c n : ℝ) / n
        + (visitCount u (min (a + 1 - e) 1) 1 n : ℝ) / n + (N₀ : ℝ) / n := by
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast upper n) (Nat.cast_nonneg n)
  have hLle : (visitCount u a (max a (c - e)) n : ℝ) / n
      ≤ (visitCount (fun k => Int.fract (u k + δ k)) a c n : ℝ) / n + (N₀ : ℝ) / n := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast lower n) (Nat.cast_nonneg n)
  have hA1 : a - e ≤ max (a - e) 0 := le_max_left _ _
  have hA2 : 1 - e ≤ min (a + 1 - e) 1 := le_min (by linarith) (by linarith)
  have hC1 : c - e ≤ max a (c - e) := le_max_right _ _
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · linarith [b₁.1, b₂.1, b₄.1]
  · linarith [b₃.2, b₄.1]

/-! ### Target 6: the wiring -/

theorem lnTwoOrbit_mem_Ico (n : ℕ) : lnTwoOrbit n ∈ Set.Ico (0 : ℝ) 1 := by
  cases n with
  | zero =>
    rw [lnTwoOrbit]
    exact ⟨le_refl 0, zero_lt_one⟩
  | succ n =>
    rw [lnTwoOrbit]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **The Bailey–Crandall reduction** (2001, conditional): equidistribution
of the surrogate orbit implies `ln 2` is normal in base 2. -/
theorem isNormal_log_two_of_equidistributed
    (h : Equidistributed lnTwoOrbit) : IsNormal 2 (Real.log 2) := by
  rw [isNormal_iff_equidistributed_orbit 2 (by norm_num) (Real.log 2)]
  have horb : orbit 2 (Real.log 2) = fun n => Int.fract (lnTwoOrbit n + 2 ^ n * lnTwoTail n) :=
    funext orbit_log_two_eq
  rw [horb]
  exact equidistributed_of_fract_perturb lnTwoOrbit (fun n => 2 ^ n * lnTwoTail n) h
    lnTwoOrbit_mem_Ico pow_mul_lnTwoTail_nonneg tendsto_pow_mul_lnTwoTail

end NormalNumbers
