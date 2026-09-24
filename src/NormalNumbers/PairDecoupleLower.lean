import NormalNumbers.SwingC1Decouple

/-!
# Lower bounds on `pairDefect` — the refutation side of leaf (D)

`SwingC1Decouple.lean` bounds the pair mean ABOVE by `model + pairDefect`.  To *refute*
`PairDecouple` one needs the opposite: a way to certify that `pairDefect` is LARGE.  This file
supplies two such certificates and uses them to pin the degenerate cases of the frozen
statement.

## The test-function certificate

`norm_test_le_classDeviation`: for every `χ : ℕ → ℂ` with `‖χ c‖ ≤ 1` on `range Q` and
`∑_{c<Q} χ c = 0`,

`‖(1/Q) ∑_{c<Q} χ(c) · progMean B Q R c‖ ≤ (1/Q) ∑_{c<Q} ‖progMean B Q R c − fullMean B (QR)‖`.

Taking `χ(c) = e(−ac/Q)` for `a ≢ 0` gives `Q − 1` numerically computable lower bounds on
`pairDefect b P p q t R`.  A refutation of `PairDecouple` is exactly one cut `P` and one
character `a` whose correlation stays away from `0` as `R → ∞`.
`probes/pair_defect.py` scans them (column `maxLB`); they all decay, see
`probes/data-2026-09-24-pair-defect.txt`.

## The twist identity

`progMean_pairRemainder`: on the class `c` the truncation is the CONSTANT `truncPairTail c`, so

`progMean B Q R c = e(−t·truncPairTail c) · progMean f Q R c`,  `f n = e(t·pairTail n)`.

Hence the defect is the class deviation of the *twisted* class means of the real object `f`, and
the second certificate is finitary and two-sided:

`‖fullMean f (QR)‖ ≤ 2·pairDefect + ‖∏_{r≤P} pairLocalFactor‖`     (`norm_fullMean_pairTail_le`)

whose contrapositive, `not_pairDecouple_of_pairCorr_ge`, is the refuter's entry point: a pair
correlation bounded below along multiples of primorials refutes `PairDecouple`.

## Degenerate cases of the frozen statement (all machine-checked here)

* `P < 2` ⟹ `Q = 1` ⟹ `pairDefect ≡ 0`.  **A counterexample needs `P ≥ 2`.**
* `p ≡ q (mod r)` ⟹ `pairLocalFactor b t r p q = 1` EXACTLY.  So the separation bound
  `norm_pairLocalFactor_le` genuinely needs its `∀ᶠ r`: at the finitely many primes `r ∣ p − q`
  the local factor has modulus `1` and there is no gain.
* `p ≡ q (mod r)` for every prime `r ≤ P` ⟹ the model term is exactly `1` and
  `pairDefect b P p q t R` is the *raw* class deviation of `f` mod `Q`
  (`pairDefect_eq_classDev_of_congr`).  For such pairs the model/decoupling split of
  `SwingC1Decouple` is vacuous at that cut: the whole of `PairDecorr` sits in the defect.  These
  pairs exist at every cut (`p = 5, q = 11` at `P = 3`; `p = 7, q = 37` at `P = 5`;
  `p = 11, q = 431` at `P = 7`), so they are the sharpest place to look for a counterexample.
* `P = 2` with `p, q` odd: `pairDefect b 2 p q t R = ‖progMean f 2 R 0 − progMean f 2 R 1‖/2`.
  The smallest nontrivial instance of `PairDecouple` is exactly "the even-`n` and odd-`n` means
  of the pair correlation agree asymptotically".
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-! ### The test-function certificate -/

/-- **A mean-zero test function on `ℤ/Q` certifies the class deviation from below.**  Purely
finite: no arithmetic, no analysis. -/
theorem norm_test_le_classDeviation (B : ℕ → ℂ) (χ : ℕ → ℂ) (Q R : ℕ) (hQ : 0 < Q)
    (hχ : ∀ c ∈ range Q, ‖χ c‖ ≤ 1) (hχ0 : ∑ c ∈ range Q, χ c = 0) :
    ‖(∑ c ∈ range Q, χ c * progMean B Q R c) / Q‖
      ≤ (∑ c ∈ range Q, ‖progMean B Q R c - fullMean B (Q * R)‖) / Q := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  set β : ℂ := fullMean B (Q * R) with hβ
  have key : ∑ c ∈ range Q, χ c * progMean B Q R c
      = ∑ c ∈ range Q, χ c * (progMean B Q R c - β) := by
    have h1 : ∀ c ∈ range Q, χ c * progMean B Q R c
        = χ c * (progMean B Q R c - β) + χ c * β := fun c _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_mul, hχ0, zero_mul,
      add_zero]
  rw [key, norm_div, Complex.norm_natCast, div_le_div_iff_of_pos_right hQr]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c hc => ?_)
  rw [norm_mul]
  nlinarith [norm_nonneg (progMean B Q R c - β), hχ c hc, norm_nonneg (χ c)]

/-- The same certificate, read off against `pairDefect`. -/
theorem norm_test_le_pairDefect (b P p q : ℕ) (t : ℝ) (R : ℕ) (χ : ℕ → ℂ)
    (hχ : ∀ c ∈ range (primorialLe P), ‖χ c‖ ≤ 1)
    (hχ0 : ∑ c ∈ range (primorialLe P), χ c = 0) :
    ‖(∑ c ∈ range (primorialLe P), χ c *
        progMean (fun n => phase (t * pairRemainder b P p q n)) (primorialLe P) R c)
        / primorialLe P‖ ≤ pairDefect b P p q t R := by
  rw [pairDefect]
  exact norm_test_le_classDeviation _ χ _ R (primorialLe_pos P) hχ hχ0

lemma pairDefect_nonnegR (b P p q : ℕ) (t : ℝ) (R : ℕ) : 0 ≤ pairDefect b P p q t R := by
  rw [pairDefect]; positivity

/-! ### The twist identity -/

/-- On the class `c mod Q` the truncation is the constant `truncPairTail c`. -/
lemma pairRemainder_add_mul_primorial (b P p q c r : ℕ) :
    pairRemainder b P p q (c + r * primorialLe P)
      = pairTail b p q (c + r * primorialLe P) - truncPairTail b P p q c := by
  rw [pairRemainder, truncPairTail_add_mul_primorial]

/-- **The twist.**  The progression mean of the remainder phase is the progression mean of the
full pair phase, rotated by the deterministic small-prime factor of the class. -/
theorem progMean_pairRemainder (b P p q : ℕ) (t : ℝ) (R c : ℕ) :
    progMean (fun n => phase (t * pairRemainder b P p q n)) (primorialLe P) R c
      = phase (-(t * truncPairTail b P p q c))
        * progMean (fun n => phase (t * pairTail b p q n)) (primorialLe P) R c := by
  rw [progMean, progMean, ← mul_div_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  show phase (t * pairRemainder b P p q (c + r * primorialLe P)) = _
  rw [pairRemainder_add_mul_primorial,
    show t * (pairTail b p q (c + r * primorialLe P) - truncPairTail b P p q c)
      = -(t * truncPairTail b P p q c) + t * pairTail b p q (c + r * primorialLe P) from by ring,
    phase_add]

/-! ### The finitary two-sided pin -/

set_option maxHeartbeats 1000000 in
/-- **The pair mean is controlled BELOW by the defect.**  The reverse of
`pairDecorr_of_pairDecouple`'s inequality, with a factor `2`: the pair correlation over `Q·R`
terms cannot exceed twice the defect plus the model term.  Finitary — no limits. -/
theorem norm_fullMean_pairTail_le (b P p q : ℕ) (t : ℝ) (R : ℕ) (hR : 0 < R) :
    ‖fullMean (fun n => phase (t * pairTail b p q n)) (primorialLe P * R)‖
      ≤ 2 * pairDefect b P p q t R + ‖∏ r ∈ primesLe P, pairLocalFactor b t r p q‖ := by
  classical
  set Q : ℕ := primorialLe P with hQdef
  have hQ : 0 < Q := primorialLe_pos P
  have hQc : ((Q : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set f : ℕ → ℂ := fun n => phase (t * pairTail b p q n) with hf
  set B : ℕ → ℂ := fun n => phase (t * pairRemainder b P p q n) with hB
  set A : ℕ → ℂ := fun c => phase (t * truncPairTail b P p q c) with hA
  set μ : ℂ := periodMean A Q with hμ
  have hμmodel : μ = ∏ r ∈ primesLe P, pairLocalFactor b t r p q := by
    rw [hμ, hA, hQdef, periodMean_phase_truncPairTail]
  -- the test function
  set χ : ℕ → ℂ := fun c => (A c - μ) / 2 with hχdef
  have hAnorm : ∀ c, ‖A c‖ = 1 := fun c => norm_phase _
  have hμ1 : ‖μ‖ ≤ 1 := by
    rw [hμ, periodMean, norm_div, Complex.norm_natCast, div_le_one (by exact_mod_cast hQ)]
    calc ‖∑ c ∈ range Q, A c‖ ≤ ∑ c ∈ range Q, ‖A c‖ := norm_sum_le _ _
      _ = Q := by simp [hAnorm]
  have hχ : ∀ c ∈ range Q, ‖χ c‖ ≤ 1 := by
    intro c _
    rw [hχdef]
    simp only [norm_div, Complex.norm_ofNat]
    have := norm_sub_le (A c) μ
    rw [hAnorm c] at this
    rw [div_le_one (by norm_num)]
    linarith
  have hχ0 : ∑ c ∈ range Q, χ c = 0 := by
    have hsum : ∑ c ∈ range Q, A c = (Q : ℂ) * μ := by
      rw [hμ, periodMean, mul_div_cancel₀ _ hQc]
    rw [hχdef]
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      hsum]
    simp
  -- the correlation, evaluated
  have hcorr : (∑ c ∈ range Q, χ c * progMean B Q R c) / Q
      = (fullMean f (Q * R) - μ * fullMean B (Q * R)) / 2 := by
    have hterm : ∀ c ∈ range Q, χ c * progMean B Q R c
        = (progMean f Q R c - μ * progMean B Q R c) / 2 := by
      intro c _
      rw [hχdef, hB, hQdef, progMean_pairRemainder b P p q t R c, ← hQdef]
      have hAinv : A c * phase (-(t * truncPairTail b P p q c)) = 1 := by
        rw [hA, ← phase_add, add_neg_cancel]
        simp [phase]
      show (A c - μ) / 2 * (phase (-(t * truncPairTail b P p q c)) * progMean f Q R c)
        = (progMean f Q R c - μ * (phase (-(t * truncPairTail b P p q c)) * progMean f Q R c)) / 2
      field_simp
      ring_nf
      rw [show A c * phase (-(t * truncPairTail b P p q c)) * progMean f Q R c
          = (A c * phase (-(t * truncPairTail b P p q c))) * progMean f Q R c from by ring,
        hAinv, one_mul]
      ring
    have h1 : ∑ c ∈ range Q, χ c * progMean B Q R c
        = ((∑ c ∈ range Q, progMean f Q R c) - μ * ∑ c ∈ range Q, progMean B Q R c) / 2 := by
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h2 : fullMean f (Q * R) = (∑ c ∈ range Q, progMean f Q R c) / Q := by
      rw [fullMean_eq_periodMean_progMean f Q R hQ hR, periodMean]
    have h3 : fullMean B (Q * R) = (∑ c ∈ range Q, progMean B Q R c) / Q := by
      rw [fullMean_eq_periodMean_progMean B Q R hQ hR, periodMean]
    rw [h1, h2, h3]
    field_simp
  -- assemble
  have hcert := norm_test_le_pairDefect b P p q t R χ (by rw [← hQdef]; exact hχ) (by
    rw [← hQdef]; exact hχ0)
  rw [← hB, ← hQdef] at hcert
  rw [hcorr] at hcert
  have hBfull : ‖fullMean B (Q * R)‖ ≤ 1 :=
    norm_fullMean_le_one B _ (fun m => le_of_eq (norm_phase _))
  have h2 : ‖fullMean f (Q * R) - μ * fullMean B (Q * R)‖ ≤ 2 * pairDefect b P p q t R := by
    have : ‖(fullMean f (Q * R) - μ * fullMean B (Q * R)) / 2‖ ≤ pairDefect b P p q t R := hcert
    rw [norm_div] at this
    simp only [Complex.norm_ofNat] at this
    linarith
  have h3 : ‖μ * fullMean B (Q * R)‖ ≤ ‖μ‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg μ, norm_nonneg (fullMean B (Q * R))]
  calc ‖fullMean f (Q * R)‖
      ≤ ‖fullMean f (Q * R) - μ * fullMean B (Q * R)‖ + ‖μ * fullMean B (Q * R)‖ := by
        simpa using norm_add_le (fullMean f (Q * R) - μ * fullMean B (Q * R))
          (μ * fullMean B (Q * R))
    _ ≤ 2 * pairDefect b P p q t R + ‖μ‖ := by linarith
    _ = 2 * pairDefect b P p q t R + ‖∏ r ∈ primesLe P, pairLocalFactor b t r p q‖ := by
        rw [hμmodel]

/-! ### The refuter's entry point -/

/-- **Refutation criterion.**  If the pair correlation of `(p, q)` stays `≥ δ > 0` along
arbitrarily long stretches of every primorial modulus, then `PairDecouple b p q t` is FALSE.
The proof picks the cut `P` from the proved model decay `prod_pairLocalFactor_tendsto_zero`, so
no hypothesis on `P` is needed. -/
theorem not_pairDecouple_of_pairCorr_ge (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (ht : t ≠ 0)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ P R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 0 < R ∧
      δ ≤ ‖fullMean (fun n => phase (t * pairTail b p q n)) (primorialLe P * R)‖) :
    ¬ PairDecouple b p q t := by
  intro hdec
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.mp
    ((NormedAddGroup.tendsto_nhds_zero.mp
      (prod_pairLocalFactor_tendsto_zero b hb t ht p q hp hq hpq)) (δ / 2) (by linarith))
  have hmodel : ‖∏ r ∈ primesLe P, pairLocalFactor b t r p q‖ < δ / 2 := by
    have := hP P le_rfl
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using this
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp
    ((NormedAddGroup.tendsto_nhds_zero.mp (hdec P)) (δ / 4) (by linarith))
  obtain ⟨R, hRge, hRpos, hRlow⟩ := h P R₀
  have hdefsmall : pairDefect b P p q t R < δ / 4 := by
    have := hR₀ R hRge
    simpa [Real.norm_eq_abs, abs_of_nonneg (pairDefect_nonnegR b P p q t R)] using this
  have := norm_fullMean_pairTail_le b P p q t R hRpos
  linarith

/-! ### Degenerate cut: `P < 2` -/

lemma primesLe_eq_empty_of_lt_two {P : ℕ} (hP : P < 2) : primesLe P = ∅ := by
  interval_cases P <;> decide

lemma primorialLe_eq_one_of_lt_two {P : ℕ} (hP : P < 2) : primorialLe P = 1 := by
  rw [primorialLe, primesLe_eq_empty_of_lt_two hP, Finset.prod_empty]

/-- With modulus `1` there is only one class and the defect vanishes identically. -/
lemma pairDefect_eq_zero_of_primorialLe_eq_one (b P p q : ℕ) (t : ℝ) (R : ℕ)
    (hP : primorialLe P = 1) : pairDefect b P p q t R = 0 := by
  rw [pairDefect, hP]
  simp [progMean, fullMean]

/-- **Any counterexample to `PairDecouple` needs a cut `P ≥ 2`.** -/
theorem pairDefect_tendsto_zero_of_lt_two (b p q : ℕ) (t : ℝ) {P : ℕ} (hP : P < 2) :
    Tendsto (fun R => pairDefect b P p q t R) atTop (𝓝 0) := by
  have : (fun R => pairDefect b P p q t R) = fun _ => (0 : ℝ) := by
    funext R
    exact pairDefect_eq_zero_of_primorialLe_eq_one b P p q t R
      (primorialLe_eq_one_of_lt_two hP)
  rw [this]
  exact tendsto_const_nhds

/-! ### Degenerate pairs: `p ≡ q` modulo the small primes -/

lemma primePeriodicTerm_mul_congr (b r p q n : ℕ) (h : p ≡ q [MOD r]) :
    primePeriodicTerm b r (p * n) = primePeriodicTerm b r (q * n) := by
  have hmod : (p * n) % r = (q * n) % r := h.mul_right n
  rw [primePeriodicTerm, primePeriodicTerm, hmod]

/-- **The local factor is exactly `1` at every prime `r ∣ p − q`.**  Hence the separation bound
`norm_pairLocalFactor_le` genuinely needs its `∀ᶠ r`: there is no gain at those finitely many
primes. -/
theorem pairLocalFactor_eq_one_of_congr (b : ℕ) (t : ℝ) (r p q : ℕ) (hr : 0 < r)
    (h : p ≡ q [MOD r]) : pairLocalFactor b t r p q = 1 := by
  have hterm : ∀ s ∈ range r,
      phase (t * (primePeriodicTerm b r (p * s) - primePeriodicTerm b r (q * s))) = 1 := by
    intro s _
    rw [primePeriodicTerm_mul_congr b r p q s h, sub_self, mul_zero]
    simp [phase]
  rw [pairLocalFactor, Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, div_self (Nat.cast_ne_zero.mpr (by omega : r ≠ 0))]

theorem prod_pairLocalFactor_eq_one_of_congr (b : ℕ) (t : ℝ) (P p q : ℕ)
    (h : ∀ r ∈ primesLe P, p ≡ q [MOD r]) :
    ∏ r ∈ primesLe P, pairLocalFactor b t r p q = 1 :=
  Finset.prod_eq_one fun r hr =>
    pairLocalFactor_eq_one_of_congr b t r p q (prime_of_mem_primesLe hr).pos (h r hr)

lemma truncPairTail_eq_zero_of_congr (b P p q n : ℕ)
    (h : ∀ r ∈ primesLe P, p ≡ q [MOD r]) : truncPairTail b P p q n = 0 := by
  rw [truncPairTail]
  exact Finset.sum_eq_zero fun r hr => by
    rw [primePeriodicTerm_mul_congr b r p q n (h r hr), sub_self]

/-- **The model/decoupling split is VACUOUS at cut `P` for `p ≡ q (mod primorialLe P)`.**  The
model term is exactly `1` and the defect is the raw class deviation of the pair correlation
itself.  So these pairs are where a counterexample would have to live. -/
theorem pairDefect_eq_classDev_of_congr (b P p q : ℕ) (t : ℝ) (R : ℕ)
    (h : ∀ r ∈ primesLe P, p ≡ q [MOD r]) :
    pairDefect b P p q t R
      = (∑ c ∈ range (primorialLe P),
          ‖progMean (fun n => phase (t * pairTail b p q n)) (primorialLe P) R c
            - fullMean (fun n => phase (t * pairTail b p q n)) (primorialLe P * R)‖)
        / primorialLe P := by
  have hr : ∀ n, pairRemainder b P p q n = pairTail b p q n := fun n => by
    rw [pairRemainder, truncPairTail_eq_zero_of_congr b P p q n h, sub_zero]
  rw [pairDefect]
  simp only [hr]

/-! ### The smallest nontrivial instance -/

lemma primesLe_two : primesLe 2 = {2} := by decide

lemma primorialLe_two : primorialLe 2 = 2 := by
  rw [primorialLe, primesLe_two, Finset.prod_singleton]

/-- **`PairDecouple` at `P = 2` for odd `p, q` is exactly "even and odd `n` agree".** -/
theorem pairDefect_two_of_odd (b p q : ℕ) (t : ℝ) (R : ℕ) (hR : 0 < R)
    (hp : Odd p) (hq : Odd q) :
    pairDefect b 2 p q t R
      = ‖progMean (fun n => phase (t * pairTail b p q n)) 2 R 0
          - progMean (fun n => phase (t * pairTail b p q n)) 2 R 1‖ / 2 := by
  set f : ℕ → ℂ := fun n => phase (t * pairTail b p q n) with hf
  have hcong : ∀ r ∈ primesLe 2, p ≡ q [MOD r] := by
    intro r hr
    rw [primesLe_two, Finset.mem_singleton] at hr
    subst hr
    show p % 2 = q % 2
    rw [Nat.odd_iff.mp hp, Nat.odd_iff.mp hq]
  rw [pairDefect_eq_classDev_of_congr b 2 p q t R hcong, primorialLe_two]
  have hfull : fullMean f (2 * R) = (progMean f 2 R 0 + progMean f 2 R 1) / 2 := by
    rw [fullMean_eq_periodMean_progMean f 2 R (by norm_num) hR, periodMean]
    norm_num [Finset.sum_range_succ]
  rw [hfull, Finset.sum_range_succ, Finset.sum_range_one]
  set g₀ := progMean f 2 R 0
  set g₁ := progMean f 2 R 1
  have e₀ : g₀ - (g₀ + g₁) / 2 = (g₀ - g₁) / 2 := by ring
  have e₁ : g₁ - (g₀ + g₁) / 2 = -((g₀ - g₁) / 2) := by ring
  rw [e₀, e₁, norm_neg, norm_div]
  simp only [Complex.norm_ofNat]
  ring

/-! ### Concrete degenerate pairs (the sharpest places to look) -/

/-- Audit anchor: at `r = 2` the local factor of the pair `(3, 5)` is exactly `1`. -/
example (b : ℕ) (t : ℝ) : pairLocalFactor b t 2 3 5 = 1 :=
  pairLocalFactor_eq_one_of_congr b t 2 3 5 (by norm_num) (by decide)

/-- `p = 5, q = 11` with `11 − 5 = 6 = primorialLe 3`: the split is vacuous at `P = 3`. -/
example (b : ℕ) (t : ℝ) : ∏ r ∈ primesLe 3, pairLocalFactor b t r 5 11 = 1 :=
  prod_pairLocalFactor_eq_one_of_congr b t 3 5 11 (by decide)

/-- `p = 7, q = 37` with `37 − 7 = 30 = primorialLe 5`: the split is vacuous at `P = 5`. -/
example (b : ℕ) (t : ℝ) : ∏ r ∈ primesLe 5, pairLocalFactor b t r 7 37 = 1 :=
  prod_pairLocalFactor_eq_one_of_congr b t 5 7 37 (by decide)

/-- `p = 11, q = 431` with `431 − 11 = 420 = 2·primorialLe 7`: vacuous at `P = 7`. -/
example (b : ℕ) (t : ℝ) : ∏ r ∈ primesLe 7, pairLocalFactor b t r 11 431 = 1 :=
  prod_pairLocalFactor_eq_one_of_congr b t 7 11 431 (by decide)

end NormalNumbers.CastingOut
