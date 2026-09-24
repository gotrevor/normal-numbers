import NormalNumbers.PairDecoupleSplit

/-!
# Van der Corput: the crux as a shifted correlation of the large-prime phase

Laps 1–4 pushed the C1 swing's open input through a chain of reformulations and refuted both
`L¹` routes (the mass route and the iterated split; see `PENDING_WORK.md`).  The `L²` route of
lap 4 landed on `TopCorrSmall`, a correlation statement — but one whose shifts are multiples of
the middle-prime modulus `M`, and whose sums have length only `M`.

Van der Corput does better, and removes the second cut `y` entirely.  For ANY bounded `u` and
ANY scale `K`,

`‖mean_{i<R} u‖ ≤ √(1/K + offDiagShift(u,R,K)/(K²R)) + 2K/R`,

where `offDiagShift` collects the correlations `Σ_{i<R} u(i+j)·conj u(i+j')`, `j ≠ j' < K`.
The shifts are now SMALL and FREE, and the correlation sums have the FULL length `R`.  So the
only remaining input is:

**`ShiftCorrSmall`** — along each progression to the small-prime modulus, the large-prime phase
`e(t·pairRemainder_P)` decorrelates from its own shift by a fixed amount.

That is verbatim the hypothesis format of the Daboussi–Kátai / Bourgain–Sarnak–Ziegler
criterion which this development already carries as a named known theorem
(`KataiOrthogonality`, `SwingC1Katai.lean`).
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- A shifted correlation sum. -/
noncomputable def shiftCorr (u : ℕ → ℂ) (R j j' : ℕ) : ℝ :=
  ‖∑ i ∈ range R, u (i + j) * (starRingEnd ℂ) (u (i + j'))‖

/-- The off-diagonal shifted correlations at scale `K`. -/
noncomputable def offDiagShift (u : ℕ → ℂ) (R K : ℕ) : ℝ :=
  ∑ j ∈ range K, ∑ j' ∈ range K, if j = j' then 0 else shiftCorr u R j j'

lemma offDiagShift_nonneg (u : ℕ → ℂ) (R K : ℕ) : 0 ≤ offDiagShift u R K := by
  rw [offDiagShift]
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun j' _ => ?_
  by_cases h : j = j' <;> simp [h, shiftCorr]

lemma norm_sum_shift_sub (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) (R j : ℕ) :
    ‖(∑ i ∈ range R, u i) - ∑ i ∈ range R, u (i + j)‖ ≤ 2 * j := by
  have hshift : ∑ i ∈ range R, u (i + j) = ∑ i ∈ Finset.Ico j (R + j), u i := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]
  have e1 : (∑ i ∈ Finset.Ico 0 j, u i) + ∑ i ∈ Finset.Ico j (R + j), u i
      = ∑ i ∈ Finset.Ico 0 (R + j), u i :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le j) (by omega)
  have e2 : (∑ i ∈ Finset.Ico 0 R, u i) + ∑ i ∈ Finset.Ico R (R + j), u i
      = ∑ i ∈ Finset.Ico 0 (R + j), u i :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le R) (by omega)
  have hb : ∀ a b : ℕ, ‖∑ i ∈ Finset.Ico a b, u i‖ ≤ ((b - a : ℕ) : ℝ) := by
    intro a b
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.Ico a b, ‖u i‖ ≤ ∑ _i ∈ Finset.Ico a b, (1:ℝ) :=
          Finset.sum_le_sum fun i _ => hu i
      _ = ((b - a : ℕ) : ℝ) := by simp
  have key := e2.trans e1.symm
  have hid : (∑ i ∈ range R, u i) - ∑ i ∈ range R, u (i + j)
      = (∑ i ∈ Finset.Ico 0 j, u i) - ∑ i ∈ Finset.Ico R (R + j), u i := by
    rw [hshift, Finset.range_eq_Ico]
    linear_combination key
  rw [hid]
  have h1 : ‖∑ i ∈ Finset.Ico 0 j, u i‖ ≤ (j:ℝ) := by simpa using hb 0 j
  have h2 := hb R (R + j)
  have h2' : ‖∑ i ∈ Finset.Ico R (R + j), u i‖ ≤ (j : ℝ) := by
    have : R + j - R = j := by omega
    rw [this] at h2; exact h2
  calc ‖(∑ i ∈ Finset.Ico 0 j, u i) - ∑ i ∈ Finset.Ico R (R + j), u i‖
      ≤ ‖∑ i ∈ Finset.Ico 0 j, u i‖ + ‖∑ i ∈ Finset.Ico R (R + j), u i‖ := norm_sub_le _ _
    _ ≤ 2 * j := by linarith


set_option maxHeartbeats 1000000 in
/-- **Van der Corput.**  A mean is controlled by its own shifted correlations at any scale `K`.
The diagonal costs `1/K` — free, since `K` is at the caller's disposal — and everything else is
the off-diagonal correlation, normalised by `K²R`. -/
theorem norm_mean_le_vdC (u : ℕ → ℂ) (R K : ℕ) (hR : 0 < R) (hK : 0 < K)
    (hu : ∀ n, ‖u n‖ ≤ 1) :
    ‖(∑ i ∈ range R, u i) / (R : ℂ)‖
      ≤ Real.sqrt (1 / K + offDiagShift u R K / ((K : ℝ) ^ 2 * R)) + 2 * (K : ℝ) / R := by
  classical
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  set D : ℝ := offDiagShift u R K with hD
  have hDnn : 0 ≤ D := offDiagShift_nonneg u R K
  set V : ℕ → ℂ := fun i => ∑ j ∈ range K, u (i + j) with hV
  set X : ℂ := ∑ i ∈ range R, u i with hX
  -- (A) shifting costs at most `2K²`
  have hA : ‖(K : ℂ) * X - ∑ i ∈ range R, V i‖ ≤ 2 * (K : ℝ) ^ 2 := by
    have hswap : ∑ i ∈ range R, V i = ∑ j ∈ range K, ∑ i ∈ range R, u (i + j) :=
      Finset.sum_comm
    have hconst : (K : ℂ) * X = ∑ _j ∈ range K, X := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hconst, hswap, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ range K, ‖X - ∑ i ∈ range R, u (i + j)‖
        ≤ ∑ j ∈ range K, (2 * (K : ℝ)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have h1 := norm_sum_shift_sub u hu R j
          have h2 : (j : ℝ) ≤ K := by
            have := Finset.mem_range.mp hj
            exact_mod_cast this.le
          rw [hX]; linarith
      _ = 2 * (K : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  -- (B) the mean square of `V`
  have hVsq : ∑ i ∈ range R, ‖V i‖ ^ 2 ≤ (K : ℝ) * R + D := by
    have hexp : ∀ i, ‖V i‖ ^ 2
        = ∑ j ∈ range K, ∑ j' ∈ range K,
            (u (i + j) * (starRingEnd ℂ) (u (i + j'))).re := by
      intro i
      rw [show ‖V i‖^2 = (V i * (starRingEnd ℂ) (V i)).re by
            rw [Complex.sq_norm, Complex.mul_conj]; simp, hV]
      simp only [map_sum]
      rw [Finset.sum_mul_sum, Complex.re_sum]
      exact Finset.sum_congr rfl fun j _ => Complex.re_sum _ _
    have hsum : ∑ i ∈ range R, ‖V i‖ ^ 2
        = ∑ j ∈ range K, ∑ j' ∈ range K,
            (∑ i ∈ range R, u (i + j) * (starRingEnd ℂ) (u (i + j'))).re := by
      rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j' _ => (Complex.re_sum _ _).symm
    have hC : ∀ j j', ‖∑ i ∈ range R, u (i + j) * (starRingEnd ℂ) (u (i + j'))‖ ≤ (R : ℝ) := by
      intro j j'
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i ∈ range R, ‖u (i + j) * (starRingEnd ℂ) (u (i + j'))‖
          ≤ ∑ _i ∈ range R, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_mul, RCLike.norm_conj]
            nlinarith [hu (i + j), hu (i + j'), norm_nonneg (u (i + j)), norm_nonneg (u (i + j'))]
        _ = R := by simp
    have hbd : ∀ j ∈ range K, ∀ j' ∈ range K,
        (∑ i ∈ range R, u (i + j) * (starRingEnd ℂ) (u (i + j'))).re
          ≤ (if j = j' then (R : ℝ) else 0) + (if j = j' then 0 else shiftCorr u R j j') := by
      intro j _ j' _
      by_cases h : j = j'
      · simp only [if_pos h, add_zero]
        exact le_trans (Complex.re_le_norm _) (hC j j')
      · simp only [if_neg h, zero_add]
        exact Complex.re_le_norm _
    rw [hsum]
    calc ∑ j ∈ range K, ∑ j' ∈ range K,
          (∑ i ∈ range R, u (i + j) * (starRingEnd ℂ) (u (i + j'))).re
        ≤ ∑ j ∈ range K, ∑ j' ∈ range K,
            ((if j = j' then (R : ℝ) else 0) + (if j = j' then 0 else shiftCorr u R j j')) :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun j' hj' => hbd j hj j' hj'
      _ = (K : ℝ) * R + D := by
          simp only [Finset.sum_add_distrib]
          have hd : ∑ j ∈ range K, ∑ j' ∈ range K, (if j = j' then (R : ℝ) else 0)
              = (K : ℝ) * R := by
            rw [Finset.sum_congr rfl
              (fun j _ => Finset.sum_ite_eq (range K) j (fun _ => (R : ℝ)))]
            rw [Finset.sum_congr rfl (fun x hx => if_pos hx)]
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [hd, hD, offDiagShift]
  -- (C) Cauchy–Schwarz
  have hCS : ‖∑ i ∈ range R, V i‖ ≤ Real.sqrt ((R : ℝ) * ((K : ℝ) * R + D)) := by
    have h1 : ‖∑ i ∈ range R, V i‖ ≤ ∑ i ∈ range R, ‖V i‖ := norm_sum_le _ _
    have h2 := sq_sum_le_card_mul_sum_sq (s := range R) (f := fun i => ‖V i‖)
    rw [Finset.card_range] at h2
    have h3 : (∑ i ∈ range R, ‖V i‖) ^ 2 ≤ (R : ℝ) * ((K : ℝ) * R + D) := by
      refine le_trans h2 ?_
      have : (0:ℝ) ≤ (R:ℝ) := hRR.le
      nlinarith [hVsq]
    have h4 : 0 ≤ ∑ i ∈ range R, ‖V i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    calc ‖∑ i ∈ range R, V i‖ ≤ ∑ i ∈ range R, ‖V i‖ := h1
      _ = Real.sqrt ((∑ i ∈ range R, ‖V i‖) ^ 2) := (Real.sqrt_sq h4).symm
      _ ≤ _ := Real.sqrt_le_sqrt h3
  -- (D) assemble
  have hXb : (K : ℝ) * ‖X‖ ≤ Real.sqrt ((R : ℝ) * ((K : ℝ) * R + D)) + 2 * (K : ℝ) ^ 2 := by
    have h0 : ‖(K : ℂ) * X‖ = (K : ℝ) * ‖X‖ := by
      rw [norm_mul, Complex.norm_natCast]
    have h1 : ‖(K : ℂ) * X‖ ≤ ‖∑ i ∈ range R, V i‖ + 2 * (K : ℝ) ^ 2 := by
      have h2 : ‖(K : ℂ) * X‖ ≤ ‖(K : ℂ) * X - ∑ i ∈ range R, V i‖ + ‖∑ i ∈ range R, V i‖ := by
        simpa using norm_add_le ((K : ℂ) * X - ∑ i ∈ range R, V i) (∑ i ∈ range R, V i)
      linarith [hA]
    rw [h0] at h1
    linarith [hCS]
  have hsq : Real.sqrt ((R : ℝ) * ((K : ℝ) * R + D))
      = Real.sqrt (1 / K + D / ((K : ℝ) ^ 2 * R)) * ((K : ℝ) * R) := by
    have h0 : (0 : ℝ) ≤ 1 / K + D / ((K : ℝ) ^ 2 * R) := by positivity
    rw [show (R : ℝ) * ((K : ℝ) * R + D)
        = (1 / K + D / ((K : ℝ) ^ 2 * R)) * ((K : ℝ) * R) ^ 2 by field_simp,
      Real.sqrt_mul h0, Real.sqrt_sq (by positivity)]
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hRR]
  rw [hsq] at hXb
  have hfin : (Real.sqrt (1 / K + D / ((K : ℝ) ^ 2 * R)) + 2 * (K : ℝ) / R) * R
      = Real.sqrt (1 / K + D / ((K : ℝ) ^ 2 * R)) * R + 2 * K := by field_simp
  rw [hfin]
  nlinarith [hXb, hKR, hRR, norm_nonneg X]


/-! ### The crux, final form -/

/-- The large-prime phase along the progression `c mod Q`. -/
noncomputable def largeProg (b P p q : ℕ) (t : ℝ) (c : ℕ) : ℕ → ℂ :=
  fun i => phase (t * pairRemainder b P p q (c + i * primorialLe P))

/-- **LEAF: shifted decorrelation.**  Along every progression to the small-prime modulus, the
large-prime phase decorrelates from its own shift by any fixed nonzero amount. -/
def ShiftCorrSmall (b p q : ℕ) (t : ℝ) : Prop :=
  ∀ P c j j' : ℕ, j ≠ j' →
    Tendsto (fun R => shiftCorr (largeProg b P p q t c) R j j' / R) atTop (𝓝 0)

/-- **The van der Corput criterion.**  A bounded sequence whose shifted correlations are all
`o(R)` has mean tending to `0`.  This is the abstract form of everything in this file. -/
theorem tendsto_mean_of_shiftCorr (u : ℕ → ℂ) (hunorm : ∀ n, ‖u n‖ ≤ 1)
    (h : ∀ j j' : ℕ, j ≠ j' → Tendsto (fun R => shiftCorr u R j j' / R) atTop (𝓝 0)) :
    Tendsto (fun R => (∑ i ∈ range R, u i) / (R : ℂ)) atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨K, hK8⟩ := exists_nat_gt (8 / ε ^ 2)
  have hKpos : 0 < K := by
    by_contra hc
    have : K = 0 := by omega
    rw [this] at hK8
    have : (0:ℝ) < 8 / ε ^ 2 := by positivity
    simp at hK8; linarith
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hdiag : 1 / (K : ℝ) < ε ^ 2 / 8 := by
    have h1 : 8 / ε ^ 2 < (K : ℝ) := hK8
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < ε ^ 2)] at h1
    rw [div_lt_div_iff₀ hKR (by norm_num : (0:ℝ) < 8)]
    linarith
  -- the off-diagonal tends to zero
  have hoff : Tendsto (fun R => offDiagShift u R K / ((K : ℝ) ^ 2 * R)) atTop (𝓝 0) := by
    have hterm : ∀ j ∈ range K, Tendsto
        (fun R => ∑ j' ∈ range K, (if j = j' then 0 else shiftCorr u R j j' / R))
        atTop (𝓝 0) := by
      intro j _
      have := tendsto_finsetSum (range K) (fun j' (_ : j' ∈ range K) =>
        show Tendsto (fun R => if j = j' then (0:ℝ) else shiftCorr u R j j' / R) atTop (𝓝 0) by
          by_cases hjj : j = j'
          · simpa [hjj] using tendsto_const_nhds (x := (0:ℝ)) (f := atTop (α := ℕ))
          · simpa [hjj] using h j j' hjj)
      simpa using this
    have hs := tendsto_finsetSum (range K) hterm
    simp only [Finset.sum_const_zero] at hs
    have hres := hs.div_const ((K : ℝ) ^ 2)
    simp only [zero_div] at hres
    refine hres.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    have hRR : (0:ℝ) < R := by exact_mod_cast hR
    have hrw : offDiagShift u R K / ((K:ℝ) ^ 2 * R)
        = (∑ j ∈ range K, ∑ j' ∈ range K,
            (if j = j' then 0 else shiftCorr u R j j' / R)) / (K:ℝ) ^ 2 := by
      rw [offDiagShift, mul_comm ((K:ℝ) ^ 2) (R:ℝ), ← div_div]
      congr 1
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j' _ => ?_
      by_cases hjj : j = j' <;> simp [hjj]
    exact hrw.symm
  -- assemble
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp
    ((NormedAddGroup.tendsto_nhds_zero.mp hoff) (ε ^ 2 / 8) (by positivity))
  obtain ⟨R₁, hR₁⟩ := exists_nat_gt (4 * (K : ℝ) / ε)
  refine Filter.eventually_atTop.mpr ⟨max (max R₀ (R₁ + 1)) 1, fun R hR => ?_⟩
  have hRpos : 0 < R := le_trans (le_max_right _ _) hR
  have hRR : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hoffR : offDiagShift u R K / ((K : ℝ) ^ 2 * R) < ε ^ 2 / 8 := by
    have h0 := hR₀ R (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR)
    rw [Real.norm_eq_abs] at h0
    exact lt_of_abs_lt h0
  have h2K : 2 * (K : ℝ) / R < ε / 2 := by
    have hRgt : (R₁ : ℝ) < (R : ℝ) := by
      have := le_trans (le_trans (le_max_right R₀ (R₁ + 1)) (le_max_left _ _)) hR
      exact_mod_cast (by omega : R₁ < R)
    have hlt : 4 * (K : ℝ) / ε < (R : ℝ) := lt_trans hR₁ hRgt
    rw [div_lt_iff₀ hε] at hlt
    rw [div_lt_iff₀ hRR]
    linarith
  have hmain := norm_mean_le_vdC u R K hRpos hKpos hunorm
  have hsq : Real.sqrt (1 / K + offDiagShift u R K / ((K : ℝ) ^ 2 * R)) < ε / 2 := by
    have hlt : 1 / (K : ℝ) + offDiagShift u R K / ((K : ℝ) ^ 2 * R) < (ε / 2) ^ 2 := by
      have : (ε / 2) ^ 2 = ε ^ 2 / 8 + ε ^ 2 / 8 := by ring
      rw [this]; linarith
    have hnn : 0 ≤ 1 / (K : ℝ) + offDiagShift u R K / ((K : ℝ) ^ 2 * R) := by
      have := offDiagShift_nonneg u R K
      positivity
    have := Real.sqrt_lt_sqrt hnn hlt
    rwa [Real.sqrt_sq (by positivity)] at this
  linarith



theorem largeDecay_of_shiftCorr (b p q : ℕ) (t : ℝ) (h : ShiftCorrSmall b p q t) :
    LargeDecay b p q t := by
  intro P c
  exact tendsto_mean_of_shiftCorr (largeProg b P p q t c)
    (fun n => le_of_eq (norm_phase _)) (fun j j' hjj => h P c j j' hjj)

/-- **`PairDecorr` directly, with no prime cut at all.**  Van der Corput applies to the pair
phase itself: if `e(t·pairTail)` decorrelates from its own shifts, the swing's leaf (D) is
discharged without `PairDecouple`, without the cut `P`, and without the periodic model. -/
def PairShiftCorr (b p q : ℕ) (t : ℝ) : Prop :=
  ∀ j j' : ℕ, j ≠ j' →
    Tendsto (fun R => shiftCorr (fun i => phase (t * pairTail b p q i)) R j j' / R) atTop (𝓝 0)

theorem pairDecorr_of_pairShiftCorr (b : ℕ) (t : ℝ)
    (h : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairShiftCorr b p q t) :
    PairDecorr b t := by
  intro p q hp hq hpq
  have := tendsto_mean_of_shiftCorr (fun i => phase (t * pairTail b p q i))
    (fun n => le_of_eq (norm_phase _)) (h p q hp hq hpq)
  exact this

/-! ### The correlation is itself a phase sum of a prime-periodic difference

`shiftCorr` is bilinear in `u`, but for a unimodular phase `u = e(t·X)` the product
`u(i+j)·conj u(i+j')` collapses to the single phase `e(t·(X(…+jQ) − X(…+j'Q)))`.  So the crux is
again an exponential sum of a function of `n` which is a sum of `r`-periodic terms — the
`SwingC1Pair` machinery applies verbatim, with `pairLocalFactor` replaced by a SHIFTED local
factor. -/

lemma phase_mul_conj_phase (x y : ℝ) :
    phase x * (starRingEnd ℂ) (phase y) = phase (x - y) := by
  rw [conj_phase, ← phase_add]
  congr 1

/-- The shifted difference of the large-prime part. -/
noncomputable def shiftPairDiff (b P p q : ℕ) (c j j' i : ℕ) : ℝ :=
  pairRemainder b P p q (c + (i + j) * primorialLe P)
    - pairRemainder b P p q (c + (i + j') * primorialLe P)

/-- **The crux as a single exponential sum.** -/
theorem shiftCorr_largeProg (b P p q : ℕ) (t : ℝ) (c R j j' : ℕ) :
    shiftCorr (largeProg b P p q t c) R j j'
      = ‖∑ i ∈ range R, phase (t * shiftPairDiff b P p q c j j' i)‖ := by
  rw [shiftCorr]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  show phase (t * pairRemainder b P p q (c + (i + j) * primorialLe P))
      * (starRingEnd ℂ) (phase (t * pairRemainder b P p q (c + (i + j') * primorialLe P)))
      = phase (t * shiftPairDiff b P p q c j j' i)
  rw [phase_mul_conj_phase, shiftPairDiff, mul_sub]

/-- `shiftPairDiff` is the pair difference of the large-prime tail at a FIXED shift: with
`H = (j − j')·Q` it is `X(n) − X(n + H)` up to relabelling, and each prime `r > P` contributes
an `r`-periodic term.  Restated for the record: only finitely many primes divide `H`, so the
Mertens divergence that drives every model term in this development survives the shift. -/
theorem shiftPairDiff_eq (b P p q : ℕ) (c j j' i : ℕ) :
    shiftPairDiff b P p q c j j' i
      = pairTail b p q (c + (i + j) * primorialLe P)
        - truncPairTail b P p q (c + (i + j) * primorialLe P)
        - (pairTail b p q (c + (i + j') * primorialLe P)
          - truncPairTail b P p q (c + (i + j') * primorialLe P)) := by
  rw [shiftPairDiff, pairRemainder, pairRemainder]


end NormalNumbers.CastingOut
