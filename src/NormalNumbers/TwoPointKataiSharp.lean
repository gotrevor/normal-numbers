import NormalNumbers.TwoPointKataiQuant

/-!
# The Kátai/BSZ inequality with its TRUE constants — and the gap this exposes

Lap 3 stated `KataiQuant` in the shape suggested by `KataiOrthogonalityAvg`
(`PairDecoupleAvg.lean`), namely `‖E f·a‖² ≲ 1/log log w + pairAvg a w N`.  Carrying out the
actual Cauchy–Schwarz shows that shape is **wrong**, and the correction is route-decisive.

## The derivation, with constants

Write `L(w) = Σ_{p ≤ w} 1/p` and `ω_w(n) = #{p ≤ w : p ∣ n}`.

1. Turán–Kubilius: `Σ_{n<N} |ω_w(n) − L(w)| ≤ √(N · Σ_n (ω_w − L)²) ≪ N √(L(w))`, so
   `L(w)·|Σ_{n<N} f(n)a(n)| ≤ |Σ_{n<N} ω_w(n) f(n) a(n)| + O(N √(L(w)))`.
2. Multiplicativity: `Σ_{n<N} ω_w(n) f(n)a(n) = Σ_{p≤w} f(p) Σ_{m<N/p} f(m) a(pm) + O(·)`.
3. Cauchy–Schwarz **in `m`**, over `m < N`:
   `|Σ_{p≤w} f(p) Σ_{m<N/p} f(m)a(pm)| ≤ √N · √( Σ_{m<N} |Σ_{p≤w} f(p) a(pm)|² )`.
   Expanding the inner square: the **diagonal** `p = q` contributes `Σ_{p≤w} N/p = N·L(w)`, and
   the off-diagonal contributes at most `Σ_{p≠q≤w} |Σ_{m} a(pm) conj a(qm)| = N · pairSum`.
   So the whole is `≤ N · √( L(w) + pairSum a w N )`.

Dividing by `N·L(w)` and squaring:

    ‖E_{n<N} f(n)a(n)‖²  ≲  1/L(w)  +  pairSum a w N / L(w)² .

**The pair term enters as a SUM against `L(w)²`, not as an average against `1`.**  Since
`pairSum = π(w)² · pairAvg`, the criterion the proof actually supplies is

    pairAvg a w N  ≪  L(w)² / π(w)²      (not merely `pairAvg → 0`),

and `L(w)² = (log log w + O(1))²` while `π(w)² ≍ (w/log w)²`.  That is a *vastly* stronger
requirement on the average than `PairMeanAvgZero` asks for.

## Consequence for the bet

`KataiOrthogonalityAvg` (repo, cited as "what BSZ actually prove") quantifies `∀ε, ∀ᶠw, ∀ᶠN,
pairAvg < ε`, with `ε` chosen **before** `w`.  Feeding that into the true inequality gives

    limsup_N ‖E f·a‖²  ≤  C·(1/L(w) + π(w)² ε / L(w)²),

and the second term cannot be made small, because `ε` was fixed before `π(w)` appeared.  The
qualitative BSZ statement survives only because there `w` is fixed and each of the finitely many
pairs is assumed to decorrelate *individually* — which makes `pairSum → 0` for that fixed `w`.

So: the averaging over multipliers is **not** free.  What is free is exactly
`pairSum a w N ≪ L(w)²`.  `KataiQuantSharp` below states the inequality honestly, and
`tendsto_fullMean_of_kataiQuantSharp` re-runs the swing on the honest hypothesis.

`tendsto_kataiPrimeRecip` (Mertens divergence, from mathlib's `not_summable_one_div_on_primes`)
is proved here in kernel: it is the only analytic input the wiring needs.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- `L(w) = Σ_{p ≤ w} 1/p`. -/
noncomputable def kataiPrimeRecip (w : ℕ) : ℝ := ∑ p ∈ primesLe w, (1 : ℝ) / p

/-- The pair **sum** (not average) that the Kátai/BSZ Cauchy–Schwarz actually produces. -/
noncomputable def pairSum (a : ℕ → ℂ) (w N : ℕ) : ℝ :=
  ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
    if p = q then 0 else ‖fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N‖

lemma pairAvg_eq_pairSum_div (a : ℕ → ℂ) (w N : ℕ) :
    pairAvg a w N = pairSum a w N / ((primesLe w).card : ℝ) ^ 2 := rfl

lemma pairSum_nonneg (a : ℕ → ℂ) (w N : ℕ) : 0 ≤ pairSum a w N := by
  refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => ?_
  split
  · exact le_rfl
  · exact norm_nonneg _

/-! ### Mertens divergence, in kernel -/

lemma kataiPrimeRecip_eq_range (w : ℕ) :
    kataiPrimeRecip w =
      ∑ n ∈ Finset.range (w + 1), Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n := by
  classical
  rw [kataiPrimeRecip, primesLe, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n.Prime
  · simp [hn, Set.indicator_of_mem]
  · simp [hn, Set.indicator_of_notMem]

/-- **Mertens divergence.**  `Σ_{p ≤ w} 1/p → ∞`. -/
theorem tendsto_kataiPrimeRecip : Tendsto kataiPrimeRecip atTop atTop := by
  classical
  have hnn : ∀ n : ℕ, 0 ≤ Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n := by
    intro n
    refine Set.indicator_nonneg (fun m _ => ?_) n
    positivity
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp
    not_summable_one_div_on_primes
  have := hdiv.comp (Filter.tendsto_add_atTop_nat 1)
  exact this.congr fun w => (kataiPrimeRecip_eq_range w).symm

/-! ### The honest inequality -/

/-- **The quantitative Kátai/BSZ inequality, with its true constants.**  The pair term is a SUM
against `L(w)²`.  Compare `KataiQuant`, whose shape silently drops the factor `π(w)²`. -/
def KataiQuantSharp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a f : ℕ → ℂ, (∀ n, ‖a n‖ ≤ 1) → (∀ n, ‖f n‖ ≤ 1) →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    ∀ w N : ℕ, 2 ≤ w → ((w : ℝ)) ^ 2 ≤ (N : ℝ) →
      ‖fullMean (fun n => f n * a n) N‖ ^ 2
        ≤ C * (1 / kataiPrimeRecip w + pairSum a w N / (kataiPrimeRecip w) ^ 2)

/-- **The honest hypothesis.**  The pair SUM is `o(L(w)²)` along a slowly growing cutoff. -/
def PairSumSmallGrowing (a : ℕ → ℂ) : Prop :=
  ∃ w : ℕ → ℕ, Tendsto w atTop atTop ∧
    (∀ᶠ N : ℕ in atTop, 2 ≤ w N ∧ ((w N : ℝ)) ^ 2 ≤ (N : ℝ)) ∧
    Tendsto (fun N => pairSum a (w N) N / (kataiPrimeRecip (w N)) ^ 2) atTop (𝓝 0)

/-- **The swing on the honest inequality.** -/
theorem tendsto_fullMean_of_kataiQuantSharp (hQ : KataiQuantSharp) (a f : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n)
    (hP : PairSumSmallGrowing a) :
    Tendsto (fun N => fullMean (fun n => f n * a n) N) atTop (𝓝 0) := by
  obtain ⟨C, hC, hineq⟩ := hQ
  obtain ⟨w, hw, hslow, hpair⟩ := hP
  set M : ℕ → ℂ := fun N => fullMean (fun n => f n * a n) N with hM
  have hL : Tendsto (fun N => 1 / kataiPrimeRecip (w N)) atTop (𝓝 0) := by
    simpa [Pi.inv_def] using (tendsto_kataiPrimeRecip.comp hw).inv_tendsto_atTop
  have hmaj : Tendsto
      (fun N => C * (1 / kataiPrimeRecip (w N)
        + pairSum a (w N) N / (kataiPrimeRecip (w N)) ^ 2)) atTop (𝓝 0) := by
    simpa using (hL.add hpair).const_mul C
  have hsq : Tendsto (fun N => ‖M N‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun N => by positivity) ?_ hmaj
    filter_upwards [hslow] with N hN
    exact hineq a f ha hf hmul (w N) N hN.1 hN.2
  have hs : Tendsto (fun N => Real.sqrt (‖M N‖ ^ 2)) atTop (𝓝 0) := by simpa using hsq.sqrt
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact hs.congr fun N => Real.sqrt_sq (norm_nonneg _)

/-! ### The gap: an average tending to `0` does NOT control the pair sum

The correction above says the Kátai step consumes `pairSum ≪ L(w)²`.  The `AvgShape` quantifier
order controls only `pairSum / π(w)²`.  The two are not comparable: the table below satisfies
`AvgShape` (its average is `≍ 2/π(w) → 0`) while its pair **sum** tends to infinity. -/

/-- Every pair that involves the prime `2` is fully correlated; all others are not. -/
noncomputable def hubTable (p q : ℕ) (_N : ℕ) : ℝ := if p = 2 ∨ q = 2 then 1 else 0

lemma hubTable_nonneg (p q N : ℕ) : 0 ≤ hubTable p q N := by
  unfold hubTable; split <;> norm_num

lemma hubTable_le_one (p q N : ℕ) : hubTable p q N ≤ 1 := by
  unfold hubTable; split <;> norm_num

/-- The hub table's pair sum is at least `π(w) − 1`. -/
lemma sum_hubTable_ge (w N : ℕ) (hw : 2 ≤ w) :
    ((primesLe w).card : ℝ) - 1
      ≤ ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, (if p = q then (0 : ℝ) else hubTable p q N) := by
  classical
  have h2 : (2 : ℕ) ∈ primesLe w :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  have hrow : ∑ q ∈ primesLe w, (if (2 : ℕ) = q then (0 : ℝ) else hubTable 2 q N)
      = ((primesLe w).card : ℝ) - 1 := by
    have hcongr : ∀ q ∈ primesLe w, (if (2 : ℕ) = q then (0 : ℝ) else hubTable 2 q N)
        = 1 - (if (2 : ℕ) = q then (1 : ℝ) else 0) := by
      intro q _
      by_cases h : (2 : ℕ) = q
      · simp [h]
      · simp [h, hubTable]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_sub_distrib,
      Finset.sum_ite_eq (primesLe w) 2 (fun _ => (1 : ℝ))]
    simp [h2]
  have hnn : ∀ p ∈ primesLe w, (0 : ℝ)
      ≤ ∑ q ∈ primesLe w, (if p = q then (0 : ℝ) else hubTable p q N) := by
    intro p _
    refine Finset.sum_nonneg fun q _ => ?_
    split
    · exact le_rfl
    · exact hubTable_nonneg p q N
  calc ((primesLe w).card : ℝ) - 1
      = ∑ q ∈ primesLe w, (if (2 : ℕ) = q then (0 : ℝ) else hubTable 2 q N) := hrow.symm
    _ ≤ _ := Finset.single_le_sum hnn h2

/-- The hub table's pair AVERAGE tends to `0`: it satisfies the `AvgShape` quantifier order. -/
theorem avgShape_hubTable : AvgShape hubTable := by
  classical
  intro ε hε
  have hbig : Tendsto (fun w => ((primesLe w).card : ℝ)) atTop atTop := tendsto_card_primesLe
  filter_upwards [hbig.eventually_gt_atTop (2 / ε), Filter.eventually_ge_atTop 2] with w hw hw2
  have hcpos : (0 : ℝ) < ((primesLe w).card : ℝ) := by
    exact_mod_cast card_primesLe_pos hw2
  refine Filter.Eventually.of_forall fun N => ?_
  have hub : ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, (if p = q then (0 : ℝ) else hubTable p q N)
      ≤ 2 * ((primesLe w).card : ℝ) := by
    calc ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, (if p = q then (0 : ℝ) else hubTable p q N)
        ≤ ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
            ((if p = 2 then (1:ℝ) else 0) + (if q = 2 then (1:ℝ) else 0)) := by
          refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
          by_cases hpq : p = q
          · simp only [if_pos hpq]; positivity
          · simp only [if_neg hpq, hubTable]
            by_cases hA : p = 2 <;> by_cases hB : q = 2 <;> simp [hA, hB]
      _ = 2 * ((primesLe w).card : ℝ) := by
          have h2 : (2 : ℕ) ∈ primesLe w :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
          have e1 : ∑ p ∈ primesLe w, ∑ _q ∈ primesLe w, (if p = 2 then (1:ℝ) else 0)
              = ((primesLe w).card : ℝ) := by
            have : ∀ p ∈ primesLe w, ∑ _q ∈ primesLe w, (if p = 2 then (1:ℝ) else 0)
                = if p = 2 then ((primesLe w).card : ℝ) else 0 := by
              intro p _
              by_cases hp : p = 2 <;> simp [hp]
            rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (primesLe w) 2
              (fun _ => ((primesLe w).card : ℝ))]
            simp [h2]
          have e2 : ∑ _p ∈ primesLe w, ∑ q ∈ primesLe w, (if q = 2 then (1:ℝ) else 0)
              = ((primesLe w).card : ℝ) := by
            rw [Finset.sum_ite_eq' (primesLe w) 2 (fun _ => (1:ℝ))]
            simp [h2]
          rw [Finset.sum_congr rfl (fun p _ => Finset.sum_add_distrib (s := primesLe w)
            (f := fun _ => (if p = 2 then (1:ℝ) else 0)) (g := fun q => if q = 2 then (1:ℝ) else 0)),
            Finset.sum_add_distrib, e1, e2]
          ring
  rw [avgTable, div_lt_iff₀ (by positivity : (0:ℝ) < ((primesLe w).card : ℝ) ^ 2)]
  have hεc : 2 < ε * ((primesLe w).card : ℝ) := by
    rw [div_lt_iff₀ hε] at hw; linarith
  nlinarith [hub, hcpos]

/-- **THE GAP, STATED.**  `hubTable` satisfies the `AvgShape` order — the exact hypothesis
`KataiOrthogonalityAvg` / `PairMeanAvgZero` impose — yet its pair SUM, the quantity the honest
Kátai inequality divides by `L(w)²`, tends to infinity.  So the averaged criterion as stated
does not supply what the Cauchy–Schwarz consumes. -/
theorem avgShape_hubTable_pairSum_atTop :
    AvgShape hubTable ∧
      ∀ N : ℕ, Tendsto
        (fun w => ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
          (if p = q then (0 : ℝ) else hubTable p q N)) atTop atTop := by
  refine ⟨avgShape_hubTable, fun N => ?_⟩
  refine tendsto_atTop_mono' atTop (f₁ := fun w => ((primesLe w).card : ℝ) - 1) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 2] with w hw
    exact sum_hubTable_ge w N hw
  · exact tendsto_atTop_add_const_right _ (-1) tendsto_card_primesLe |>.congr fun w => by ring

end NormalNumbers.CastingOut
