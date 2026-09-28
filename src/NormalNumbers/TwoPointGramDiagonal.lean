import NormalNumbers.TwoPointGramArith

/-!
# The diagonal reduction: fixed-pair decorrelation already closes the growing-`w` leaf

Laps 13–23 priced the leaf

    ∃ w(N) → ∞ with w(N)² ≤ N :  twoPointGramSum b t (w N) N = o(N · L(w N)²)

against the *trivial* bound and found the budget hopeless: `M(w)/L(w)² → ∞`
(`tendsto_maxRecipSum_div_sq`), so a bound of the shape
`‖twoPointTruncSum b p q t N‖ ≤ δ · N/max(p,q)` needs `δ ≍ L(w)²/π(w) → 0`
(`gramBudget_of_uniform_saving`).  Every route in laps 15–23 was an attempt to produce that
**uniform-in-`(p,q,w)`** saving.

That framing overshoots, and the wrap of laps 11–23 recorded the overshoot as a fact
("per-pair decorrelation does not imply the leaf, the budget is too small").  This file
**corrects** it.  The cutoff `w` is *existentially* quantified and may grow arbitrarily slowly,
so the leaf only ever has to be verified at ONE cutoff per `N`.  Diagonalising: for a FIXED `w`
the pair sum is a finite sum of `o(N)` terms and `L(w)²` is a positive constant, so the ratio
already tends to `0`; picking `w` to grow slowly along the resulting thresholds gives the leaf.

Consequences, all kernel-checked below.

* `exists_slow_cutoff` — the general diagonalisation: if `F w · → 0` for every fixed `w ≥ 2`,
  some `w(N) → ∞` with `w(N)² ≤ N` has `F (w N) N → 0`.  No uniformity in `w` is needed.
* `twoPointPairGramSmall_of_fixedPair` — fixed-pair `o(N)` decorrelation ⇒ the leaf.
* `conjC1_of_delange_pairwiseTwoPoint` — **`ConjC1` from Delange's theorem plus pairwise
  natural-density weighted two-point decorrelation, with no cited Kátai hypothesis.**  Compare
  `conjC1_of_delange_katai_twoPoint_decouple` (`PairDecoupleTwoPoint.lean`), which needs the
  *cited* `KataiOrthogonality`: here the Kátai/BSZ step is `katai_mean_sq`, a theorem.
* `conjC1_of_delange_twoPointElliott_weightDecouple` — the same with the per-pair hypothesis
  split into the two-point Elliott correlation and the leading-digit decoupling.

**What this settles, and what it does not.**  It settles the *upper* bound on the leaf's
difficulty: the leaf is no harder than natural-density two-point Elliott for `ζ^ω` along the
pairs of forms `pn+1`, `qn+1`, twisted by `peelWeight`.  It does not make the leaf easy — that
per-pair statement is open (Tao 2016 gives it in *logarithmic* average) — and it does not show
the leaf is *equivalent* to it: the leaf inherits only `o(N · L(w N)²)` per pair, which is
vacuous, so no per-pair information comes back out (`tendsto_maxRecipSum_div_sq` is still the
reason a *uniform* route cannot work).  What it does do is retire the uniform-saving programme
of laps 15–23 as **sufficient but far from necessary**, and re-point the attack at the per-pair
statement, where the literature actually lives.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-! ### A general slow-cutoff diagonalisation -/

/-- A strictly increasing majorant of `N₀`. -/
private def stairD (N₀ : ℕ → ℕ) : ℕ → ℕ
  | 0 => N₀ 0
  | (k + 1) => max (stairD N₀ k + 1) (N₀ (k + 1))

private lemma le_stairD (N₀ : ℕ → ℕ) : ∀ k, N₀ k ≤ stairD N₀ k
  | 0 => le_rfl
  | (_k + 1) => le_max_right _ _

private lemma self_le_stairD (N₀ : ℕ → ℕ) : ∀ k, k ≤ stairD N₀ k
  | 0 => Nat.zero_le _
  | (k + 1) => by
      have h1 := self_le_stairD N₀ k
      have h2 : stairD N₀ k + 1 ≤ stairD N₀ (k + 1) := le_max_left _ _
      omega

/-- **THE DIAGONALISATION.**  If a nonnegative two-parameter quantity tends to `0` in `N` for
every *fixed* cutoff `w ≥ 2`, then it tends to `0` along some cutoff `w(N) → ∞` slow enough that
`w(N)² ≤ N`.  No uniformity in `w` is required: this is why the growing-`w` leaf never needs the
uniform per-pair saving that `gramBudget_of_uniform_saving` asks for. -/
theorem exists_slow_cutoff (F : ℕ → ℕ → ℝ) (hF : ∀ w N, 0 ≤ F w N)
    (h : ∀ w : ℕ, 2 ≤ w → Tendsto (fun N => F w N) atTop (𝓝 0)) :
    ∃ w : ℕ → ℕ, Tendsto w atTop atTop ∧
      (∀ᶠ N : ℕ in atTop, 2 ≤ w N ∧ ((w N : ℝ)) ^ 2 ≤ (N : ℝ)) ∧
      Tendsto (fun N => F (w N) N) atTop (𝓝 0) := by
  classical
  have hspec : ∀ k : ℕ, ∀ᶠ N : ℕ in atTop, F (k + 2) N < 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    exact ((h (k + 2) (by omega)).eventually (gt_mem_nhds hpos)).mono fun N hN => hN
  choose N₀ hN₀ using fun k : ℕ => Filter.eventually_atTop.mp (hspec k)
  set N₁ : ℕ → ℕ := fun k => max (N₀ k) ((k + 2) ^ 2) with hN₁
  set S : ℕ → ℕ := stairD N₁ with hS
  have hSN₀ : ∀ k, N₀ k ≤ S k := fun k => le_trans (le_max_left _ _) (le_stairD N₁ k)
  have hSsq : ∀ k, (k + 2) ^ 2 ≤ S k := fun k => le_trans (le_max_right _ _) (le_stairD N₁ k)
  set kIdx : ℕ → ℕ := fun N => Nat.findGreatest (fun k => S k ≤ N) N with hkIdx
  have hk_ge : ∀ k₀ N : ℕ, S k₀ ≤ N → k₀ ≤ kIdx N := fun k₀ N hSN =>
    Nat.le_findGreatest (P := fun k => S k ≤ N) (le_trans (self_le_stairD N₁ k₀) hSN) hSN
  have hk_spec : ∀ k₀ N : ℕ, S k₀ ≤ N → S (kIdx N) ≤ N := fun k₀ N hSN =>
    Nat.findGreatest_spec (P := fun k => S k ≤ N) (m := k₀)
      (le_trans (self_le_stairD N₁ k₀) hSN) hSN
  refine ⟨fun N => kIdx N + 2, ?_, ?_, ?_⟩
  · refine tendsto_atTop.mpr fun M => ?_
    filter_upwards [Filter.eventually_ge_atTop (S M)] with N hN
    have := hk_ge M N hN
    omega
  · filter_upwards [Filter.eventually_ge_atTop (S 0)] with N hN
    refine ⟨by omega, ?_⟩
    have h1 : (kIdx N + 2) ^ 2 ≤ N := le_trans (hSsq (kIdx N)) (hk_spec 0 N hN)
    exact_mod_cast h1
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / ε)
    refine ⟨S k₀, fun N hN => ?_⟩
    have hk1 : k₀ ≤ kIdx N := hk_ge k₀ N hN
    have hspec : S (kIdx N) ≤ N := hk_spec k₀ N hN
    have hlt : F (kIdx N + 2) N < 1 / ((kIdx N : ℝ) + 1) :=
      hN₀ (kIdx N) N (le_trans (hSN₀ (kIdx N)) hspec)
    have hnn : 0 ≤ F (kIdx N + 2) N := hF _ _
    have hcast : ((k₀ : ℝ) + 1) ≤ ((kIdx N : ℝ) + 1) := by
      have : (k₀ : ℝ) ≤ (kIdx N : ℝ) := by exact_mod_cast hk1
      linarith
    have hεk : 1 / ((k₀ : ℝ) + 1) < ε := by
      have hk0 : (0 : ℝ) < (k₀ : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ hk0]
      have h' : 1 / ε < (k₀ : ℝ) := hk₀
      rw [div_lt_iff₀ hε] at h'
      nlinarith
    have hmono : 1 / ((kIdx N : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hcast
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith

/-! ### The fixed cutoff: a finite sum of `o(N)` terms -/

lemma twoPointGramSum_nonneg (b : ℕ) (t : ℝ) (w N : ℕ) : 0 ≤ twoPointGramSum b t w N := by
  classical
  unfold twoPointGramSum
  refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => ?_
  split
  · exact le_rfl
  · exact norm_nonneg _

/-- At a **fixed** cutoff the Kátai ratio already tends to `0`: the pair sum has finitely many
terms, each `o(N)`, and `L(w)² ≥ 1/4` is a positive constant. -/
lemma gramRatio_tendsto_of_fixedPair (b : ℕ) (t : ℝ) (w : ℕ) (_hw : 2 ≤ w)
    (h : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Tendsto (fun N => ‖twoPointTruncSum b p q t N‖ / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => twoPointGramSum b t w N / ((N : ℝ) * (kataiPrimeRecip w) ^ 2))
      atTop (𝓝 0) := by
  classical
  have hsum : Tendsto (fun N => ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
      (if p = q then (0 : ℝ) else ‖twoPointTruncSum b p q t N‖ / (N : ℝ))) atTop (𝓝 0) := by
    have hterm : ∀ p ∈ primesLe w, Tendsto (fun N => ∑ q ∈ primesLe w,
        (if p = q then (0 : ℝ) else ‖twoPointTruncSum b p q t N‖ / (N : ℝ))) atTop (𝓝 0) := by
      intro p hp
      have hz : Tendsto (fun N => ∑ q ∈ primesLe w,
          (if p = q then (0 : ℝ) else ‖twoPointTruncSum b p q t N‖ / (N : ℝ))) atTop
          (𝓝 (∑ _q ∈ primesLe w, (0 : ℝ))) := by
        refine tendsto_finsetSum _ fun q hq => ?_
        by_cases hpq : p = q
        · simp [hpq]
        · simpa [hpq] using h p q (prime_of_mem_primesLe hp) (prime_of_mem_primesLe hq) hpq
      simpa using hz
    simpa using tendsto_finsetSum (primesLe w) hterm
  have hdiv := hsum.div_const ((kataiPrimeRecip w) ^ 2)
  rw [zero_div] at hdiv
  refine hdiv.congr fun N => ?_
  have h1 : ∀ p q : ℕ, (if p = q then (0 : ℝ) else ‖twoPointTruncSum b p q t N‖ / (N : ℝ))
      = (if p = q then (0 : ℝ) else ‖twoPointTruncSum b p q t N‖) / (N : ℝ) := by
    intro p q; by_cases hpq : p = q <;> simp [hpq]
  unfold twoPointGramSum
  simp only [h1, ← Finset.sum_div, div_div]

/-! ### The leaf from fixed-pair decorrelation -/

/-- **THE CORRECTION.**  Fixed-pair `o(N)` decorrelation of the truncated weighted two-point
correlation closes the growing-`w` Kátai leaf.  No uniform-in-`(p,q,w)` saving is needed. -/
theorem twoPointPairGramSmall_of_fixedPair (b : ℕ) (hb : 2 ≤ b) (t : ℝ)
    (h : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Tendsto (fun N => ‖twoPointTruncSum b p q t N‖ / (N : ℝ)) atTop (𝓝 0)) :
    TwoPointPairGramSmall b t := by
  refine (twoPointPairGramSmall_iff b hb t).mpr ?_
  refine exists_slow_cutoff
    (fun w N => twoPointGramSum b t w N / ((N : ℝ) * (kataiPrimeRecip w) ^ 2))
    (fun w N => div_nonneg (twoPointGramSum_nonneg b t w N) (by positivity))
    (fun w hw => gramRatio_tendsto_of_fixedPair b t w hw h)

/-! ### The bridge from the ratified per-pair statement -/

/-- `TwoPointWeighted` (the natural-density per-pair crux) gives the `o(N)` hypothesis the
diagonalisation consumes.  The truncated range `m ≤ min(⌊N/p⌋, ⌊N/q⌋)` is a *shorter* range than
`N`, so this direction is free. -/
lemma truncSum_div_tendsto_of_twoPointWeighted (b p q : ℕ) (hp : 0 < p) (hq : 0 < q) (t : ℝ)
    (h : TwoPointWeighted b p q t) :
    Tendsto (fun N => ‖twoPointTruncSum b p q t N‖ / (N : ℝ)) atTop (𝓝 0) := by
  classical
  set F : ℕ → ℂ := fun m => twoPointFactor b p q t m * peelWeight b p q t m with hFdef
  have hFmean : Tendsto (fun R => fullMean F R) atTop (𝓝 0) := by
    refine h.congr fun R => ?_
    refine congrArg (fun z => z / (R : ℂ)) (Finset.sum_congr rfl fun m _ => ?_)
    simp only [hFdef, twoPointFactor]
  have hFnorm : ∀ m, ‖F m‖ = 1 := by
    intro m
    rw [hFdef]
    simp [norm_twoPointFactor, norm_peelWeight]
  -- the truncated sum, as a full range sum minus its `m = 0` term
  have hIoc : ∀ n : ℕ, ∑ m ∈ Finset.Ioc 0 n, F m = (∑ m ∈ Finset.range (n + 1), F m) - F 0 := by
    intro n
    rw [range_eq_insert_Ioc, Finset.sum_insert (by simp)]
    ring
  have hM : Tendsto (fun N : ℕ => min (N / p) (N / q) + 1) atTop atTop := by
    refine tendsto_atTop.mpr fun M => ?_
    filter_upwards [Filter.eventually_ge_atTop (max p q * M)] with N hN
    have hple : M ≤ N / p := by
      rw [Nat.le_div_iff_mul_le hp]
      calc M * p ≤ M * max p q := Nat.mul_le_mul_left M (le_max_left p q)
        _ = max p q * M := by ring
        _ ≤ N := hN
    have hqle : M ≤ N / q := by
      rw [Nat.le_div_iff_mul_le hq]
      calc M * q ≤ M * max p q := Nat.mul_le_mul_left M (le_max_right p q)
        _ = max p q * M := by ring
        _ ≤ N := hN
    omega
  have hcomp : Tendsto (fun N : ℕ => ‖fullMean F (min (N / p) (N / q) + 1)‖) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero.mp hFmean).comp hM
  have hmaj : Tendsto (fun N : ℕ =>
      2 * ‖fullMean F (min (N / p) (N / q) + 1)‖ + 1 / (N : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using (hcomp.const_mul (2 : ℝ)).add h1
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => by positivity) ?_ hmaj
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
  set M := min (N / p) (N / q) with hMdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  -- `‖Σ_{Ioc 0 M} F‖ ≤ (M+1)·‖fullMean F (M+1)‖ + 1`
  have hMR : ((M : ℝ) + 1) = ((M + 1 : ℕ) : ℝ) := by push_cast; ring
  have hfull : ∑ m ∈ Finset.range (M + 1), F m = ((M + 1 : ℕ) : ℂ) * fullMean F (M + 1) := by
    rw [fullMean, mul_div_cancel₀]
    exact_mod_cast Nat.succ_ne_zero M
  have hnormsum : ‖twoPointTruncSum b p q t N‖ ≤ ((M : ℝ) + 1) * ‖fullMean F (M + 1)‖ + 1 := by
    have hts : twoPointTruncSum b p q t N = ∑ m ∈ Finset.Ioc 0 M, F m := by
      rw [twoPointTruncSum, hFdef, hMdef]
    rw [hts, hIoc, hfull]
    calc ‖((M + 1 : ℕ) : ℂ) * fullMean F (M + 1) - F 0‖
        ≤ ‖((M + 1 : ℕ) : ℂ) * fullMean F (M + 1)‖ + ‖F 0‖ := norm_sub_le _ _
      _ = ((M : ℝ) + 1) * ‖fullMean F (M + 1)‖ + 1 := by
          have hn : ‖((M + 1 : ℕ) : ℂ)‖ = (M : ℝ) + 1 := by rw [Complex.norm_natCast]; push_cast; ring
          rw [norm_mul, hFnorm 0, hn]
  have hMle : (M : ℝ) + 1 ≤ 2 * (N : ℝ) := by
    have : M ≤ N := le_trans (min_le_left _ _) (Nat.div_le_self N p)
    have hMN : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  rw [div_le_iff₀ hNpos]
  have hfm : 0 ≤ ‖fullMean F (M + 1)‖ := norm_nonneg _
  calc ‖twoPointTruncSum b p q t N‖
      ≤ ((M : ℝ) + 1) * ‖fullMean F (M + 1)‖ + 1 := hnormsum
    _ ≤ 2 * (N : ℝ) * ‖fullMean F (M + 1)‖ + 1 := by nlinarith
    _ = (2 * ‖fullMean F (M + 1)‖ + 1 / (N : ℝ)) * (N : ℝ) := by
        field_simp

/-! ### The swing, with no cited Kátai hypothesis -/

/-- **`ConjC1` FROM DELANGE PLUS THE PER-PAIR CRUX.**  Every hypothesis is either Delange's
theorem or the natural-density weighted two-point decorrelation for one pair of distinct primes.
The Kátai/BSZ step is `katai_mean_sq`, a theorem — compare
`conjC1_of_delange_katai_twoPoint_decouple`, which still cites `KataiOrthogonality`. -/
theorem conjC1_of_delange_pairwiseTwoPoint
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hE : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → TwoPointWeighted b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_pairGramSmall hD fun b hb m hm hdvd =>
    twoPointPairGramSmall_of_fixedPair b (by omega) _ fun p q hp hq hpq =>
      truncSum_div_tendsto_of_twoPointWeighted b p q hp.pos hq.pos _
        (hE b hb m hm hdvd p q hp hq hpq)

/-- The same, with the per-pair crux split into the unweighted two-point Elliott correlation and
the leading-digit decoupling (`twoPointWeighted_of_split`). -/
theorem conjC1_of_delange_twoPointElliott_weightDecouple
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hE : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → TwoPointElliott b p q (((m : ℤ) : ℝ) / b))
    (hW : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → WeightDecouple b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_pairwiseTwoPoint hD fun b hb m hm hdvd p q hp hq hpq =>
    twoPointWeighted_of_split b p q _ (hE b hb m hm hdvd p q hp hq hpq)
      (hW b hb m hm hdvd p q hp hq hpq)

/-- **`conjC1_of_delange_katai` WITH THE CITED KÁTAI HYPOTHESIS DELETED.**  The canonical node
`PairDecorr` (`SwingC1Katai.lean`) plus Delange's theorem give `ConjC1` outright: the
Daboussi–Kátai orthogonality criterion is no longer assumed, it is `katai_mean_sq` applied along
the diagonal cutoff.  This is the sharpest unconditional reduction of C1 the development has. -/
theorem conjC1_of_delange_pairDecorr
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → PairDecorr b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_pairwiseTwoPoint hD fun b hb m hm hdvd =>
    (pairDecorr_iff_twoPointWeighted b (by omega) _).mp (hP b hb m hm hdvd)

end NormalNumbers.CastingOut
