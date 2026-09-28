import NormalNumbers.TwoPointKataiSharp

/-!
# The gap, quantitatively: `π(w) / L(w)² → ∞`

Lap 4 showed the honest Kátai/BSZ inequality consumes `pairSum ≪ L(w)²`, while the `AvgShape`
quantifier order (`KataiOrthogonalityAvg`, `PairMeanAvgZero`) controls only `pairSum / π(w)²`,
and produced `hubTable`: an `AvgShape` table whose pair sum tends to infinity.

To turn that into a refutation one needs `π(w) ≫ L(w)²`, i.e. that the hub witness's pair sum
`≍ 2π(w)` really does swamp the `L(w)²` budget.  That is a Chebyshev-flavoured statement, but it
has a fully elementary proof, given here: for every `K ≥ 1`,

    L(w) = Σ_{p ≤ w} 1/p  ≤  (K + 1)  +  √( π(w) / K ),

by splitting at `K` and applying Cauchy–Schwarz to the tail against `Σ_{n > K} 1/n² ≤ 1/K`.
Hence `L(w)²/π(w) ≤ 2(K+1)²/π(w) + 2/K` for every `K`, and letting `w → ∞` then `K → ∞` gives
`L(w)²/π(w) → 0`.  No prime number theorem, no Mertens.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-! ### The tail of `Σ 1/n²` -/

lemma sum_inv_sq_Ioc_le (K : ℕ) (hK : 1 ≤ K) :
    ∀ w : ℕ, K ≤ w → ∑ n ∈ Finset.Ioc K w, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / K - 1 / w := by
  refine Nat.le_induction ?_ ?_
  · simp
  · intro w hw ih
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hw0 : (0 : ℝ) < w := by exact_mod_cast Nat.lt_of_lt_of_le hK hw
    have hw1 : (0 : ℝ) < (w : ℝ) + 1 := by linarith
    have hstep : (1 : ℝ) / ((w : ℝ) + 1) ^ 2 ≤ 1 / (w : ℝ) - 1 / ((w : ℝ) + 1) := by
      rw [div_sub_div _ _ (ne_of_gt hw0) (ne_of_gt hw1)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      ring_nf
      nlinarith [hw0]
    have hcast : ((w + 1 : ℕ) : ℝ) = (w : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [ih]

lemma sum_inv_sq_primes_tail_le (K w : ℕ) (hK : 1 ≤ K) :
    ∑ p ∈ (primesLe w).filter (fun p => K < p), (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / K := by
  classical
  by_cases hw : K ≤ w
  · have hsub : (primesLe w).filter (fun p => K < p) ⊆ Finset.Ioc K w := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Ioc.mpr ⟨hp2, by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hp1).1
        have hprime := (Finset.mem_filter.mp hp1).2
        rcases Nat.lt_or_ge p (w + 1) with h | h
        · omega
        · omega⟩
    have h1 : ∑ p ∈ (primesLe w).filter (fun p => K < p), (1 : ℝ) / (p : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Ioc K w, (1 : ℝ) / (n : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    have h2 := sum_inv_sq_Ioc_le K hK w hw
    have : (0 : ℝ) ≤ 1 / (w : ℝ) := by positivity
    linarith
  · have hempty : (primesLe w).filter (fun p => K < p) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun p hp => ?_
      have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
      omega
    rw [hempty]
    simp

/-! ### The elementary bound on `L(w)` -/

lemma kataiPrimeRecip_le (K w : ℕ) (hK : 1 ≤ K) :
    kataiPrimeRecip w ≤ ((K : ℝ) + 1) + Real.sqrt (((primesLe w).card : ℝ) / K) := by
  classical
  set A := primesLe w with hA
  have hsplit : kataiPrimeRecip w
      = (∑ p ∈ A.filter (fun p => ¬ K < p), (1 : ℝ) / p)
        + ∑ p ∈ A.filter (fun p => K < p), (1 : ℝ) / p := by
    rw [kataiPrimeRecip, ← hA, ← Finset.sum_filter_add_sum_filter_not A (fun p => ¬ K < p)]
    simp
  -- the small primes: at most `K + 1` of them, each contributing at most `1`
  have hsmall : (∑ p ∈ A.filter (fun p => ¬ K < p), (1 : ℝ) / p) ≤ (K : ℝ) + 1 := by
    have hcard : (A.filter (fun p => ¬ K < p)).card ≤ K + 1 := by
      refine le_trans (Finset.card_le_card (fun p hp => ?_)) (by simp : (Finset.range (K+1)).card ≤ K + 1)
      obtain ⟨_, hp2⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_range.mpr (by omega)
    calc (∑ p ∈ A.filter (fun p => ¬ K < p), (1 : ℝ) / p)
        ≤ ∑ _p ∈ A.filter (fun p => ¬ K < p), (1 : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp2 : 2 ≤ p := (prime_of_mem_primesLe (Finset.mem_filter.mp hp).1).two_le
          have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
          rw [div_le_one (by linarith)]; linarith
      _ = ((A.filter (fun p => ¬ K < p)).card : ℝ) := by simp
      _ ≤ (K : ℝ) + 1 := by exact_mod_cast hcard
  -- the large primes: Cauchy–Schwarz against the tail of `Σ 1/n²`
  have hlarge : (∑ p ∈ A.filter (fun p => K < p), (1 : ℝ) / p)
      ≤ Real.sqrt ((A.card : ℝ) / K) := by
    have hcs : (∑ p ∈ A.filter (fun p => K < p), (1 : ℝ) / p) ^ 2
        ≤ ((A.filter (fun p => K < p)).card : ℝ)
          * ∑ p ∈ A.filter (fun p => K < p), ((1 : ℝ) / p) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have htail : ∑ p ∈ A.filter (fun p => K < p), ((1 : ℝ) / p) ^ 2 ≤ 1 / K := by
      have := sum_inv_sq_primes_tail_le K w hK
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) this
      rw [div_pow, one_pow]
    have hcard : ((A.filter (fun p => K < p)).card : ℝ) ≤ (A.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    have hnn : (0 : ℝ) ≤ ∑ p ∈ A.filter (fun p => K < p), (1 : ℝ) / p :=
      Finset.sum_nonneg fun p _ => by positivity
    have hbound : (∑ p ∈ A.filter (fun p => K < p), (1 : ℝ) / p) ^ 2 ≤ (A.card : ℝ) / K := by
      have hsq : (0:ℝ) ≤ ∑ p ∈ A.filter (fun p => K < p), ((1 : ℝ) / p) ^ 2 :=
        Finset.sum_nonneg fun p _ => by positivity
      calc (∑ p ∈ A.filter (fun p => K < p), (1 : ℝ) / p) ^ 2
          ≤ ((A.filter (fun p => K < p)).card : ℝ)
            * ∑ p ∈ A.filter (fun p => K < p), ((1 : ℝ) / p) ^ 2 := hcs
        _ ≤ (A.card : ℝ) * (1 / K) := by
            refine mul_le_mul hcard htail hsq (by positivity)
        _ = (A.card : ℝ) / K := by ring
    calc (∑ p ∈ A.filter (fun p => K < p), (1 : ℝ) / p)
        = Real.sqrt ((∑ p ∈ A.filter (fun p => K < p), (1 : ℝ) / p) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((A.card : ℝ) / K) := Real.sqrt_le_sqrt hbound
  rw [hsplit]
  linarith

/-! ### The conclusion -/

/-- **`L(w)² = o(π(w))`.**  Elementary: split at `K`, Cauchy–Schwarz the tail. -/
theorem tendsto_kataiPrimeRecip_sq_div_card :
    Tendsto (fun w => (kataiPrimeRecip w) ^ 2 / ((primesLe w).card : ℝ)) atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨K, hK0, hKε⟩ : ∃ K : ℕ, 1 ≤ K ∧ (2 : ℝ) / K < ε / 2 := by
    obtain ⟨K0, hK0⟩ := exists_nat_gt (4 / ε)
    refine ⟨K0 + 1, by omega, ?_⟩
    have hKp : (0:ℝ) < (K0 : ℝ) + 1 := by positivity
    have hK : (4:ℝ)/ε < (K0:ℝ) := hK0
    rw [div_lt_iff₀ hε] at hK
    rw [show ((K0 + 1 : ℕ) : ℝ) = (K0 : ℝ) + 1 by push_cast; ring, div_lt_iff₀ hKp]
    nlinarith
  have hbig : Tendsto (fun w => ((primesLe w).card : ℝ)) atTop atTop := tendsto_card_primesLe
  have hev : ∀ᶠ w : ℕ in atTop, 2 * ((K : ℝ) + 1) ^ 2 / (ε / 2) < ((primesLe w).card : ℝ) :=
    hbig.eventually_gt_atTop _
  filter_upwards [hev, Filter.eventually_ge_atTop 2] with w hw hw2
  have hcpos : (0 : ℝ) < ((primesLe w).card : ℝ) := by exact_mod_cast card_primesLe_pos hw2
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hLnn : 0 ≤ kataiPrimeRecip w :=
    Finset.sum_nonneg fun p _ => by positivity
  have hle := kataiPrimeRecip_le K w hK0
  have hsqrt : Real.sqrt (((primesLe w).card : ℝ) / K) ^ 2 = ((primesLe w).card : ℝ) / K :=
    Real.sq_sqrt (by positivity)
  have hsq : (kataiPrimeRecip w) ^ 2
      ≤ 2 * ((K : ℝ) + 1) ^ 2 + 2 * (((primesLe w).card : ℝ) / K) := by
    have hnn : (0:ℝ) ≤ Real.sqrt (((primesLe w).card : ℝ) / K) := Real.sqrt_nonneg _
    nlinarith [hle, hLnn, hsqrt, hnn, sq_nonneg (((K : ℝ) + 1) - Real.sqrt (((primesLe w).card : ℝ) / K))]
  have hdiv : (kataiPrimeRecip w) ^ 2 / ((primesLe w).card : ℝ)
      ≤ 2 * ((K : ℝ) + 1) ^ 2 / ((primesLe w).card : ℝ) + 2 / K := by
    rw [div_le_iff₀ hcpos]
    have : (2 * ((K : ℝ) + 1) ^ 2 / ((primesLe w).card : ℝ) + 2 / K) * ((primesLe w).card : ℝ)
        = 2 * ((K : ℝ) + 1) ^ 2 + 2 * (((primesLe w).card : ℝ) / K) := by
      field_simp
    rw [this]; exact hsq
  have hA : 2 * ((K : ℝ) + 1) ^ 2 / ((primesLe w).card : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hcpos]
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < ε/2)] at hw
    linarith
  have hB : (2 : ℝ) / K < ε / 2 := hKε
  have hnn0 : 0 ≤ (kataiPrimeRecip w) ^ 2 / ((primesLe w).card : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn0]
  linarith

/-- **`π(w)/L(w)² → ∞`:** the hub witness's pair sum really does swamp the Kátai budget. -/
theorem tendsto_card_div_kataiPrimeRecip_sq :
    Tendsto (fun w => ((primesLe w).card : ℝ) / (kataiPrimeRecip w) ^ 2) atTop atTop := by
  have h := tendsto_kataiPrimeRecip_sq_div_card
  have hpos : ∀ᶠ w : ℕ in atTop,
      (kataiPrimeRecip w) ^ 2 / ((primesLe w).card : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with w hw
    have hcpos : (0 : ℝ) < ((primesLe w).card : ℝ) := by exact_mod_cast card_primesLe_pos hw
    have h2 : (2 : ℕ) ∈ primesLe w :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
    have hL : 0 < kataiPrimeRecip w := by
      refine Finset.sum_pos' (fun p _ => by positivity) ⟨2, h2, by norm_num⟩
    exact Set.mem_Ioi.mpr (by positivity)
  have hnhds : Tendsto (fun w => (kataiPrimeRecip w) ^ 2 / ((primesLe w).card : ℝ)) atTop
      (𝓝[>] 0) := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h hpos
  refine (hnhds.inv_tendsto_nhdsGT_zero).congr fun w => ?_
  simp [inv_div]


/-! ### The refutation, assembled -/

/-- The pair SUM of an abstract table (what `avgTable` divides by `π(w)²`). -/
noncomputable def sumTable (G : ℕ → ℕ → ℕ → ℝ) (w N : ℕ) : ℝ :=
  ∑ p ∈ primesLe w, ∑ q ∈ primesLe w, if p = q then 0 else G p q N

lemma avgTable_eq_sumTable_div (G : ℕ → ℕ → ℕ → ℝ) (w N : ℕ) :
    avgTable G w N = sumTable G w N / ((primesLe w).card : ℝ) ^ 2 := rfl

lemma pairSum_eq_sumTable (a : ℕ → ℂ) (w N : ℕ) :
    pairSum a w N =
      sumTable (fun p q N => ‖fullMean (fun n => a (p * n) * (starRingEnd ℂ) (a (q * n))) N‖)
        w N := rfl

/-- The hub witness blows the Kátai budget: its pair sum is `≫ L(w)²`. -/
theorem hubTable_sumTable_div_sq_atTop (N : ℕ) :
    Tendsto (fun w => sumTable hubTable w N / (kataiPrimeRecip w) ^ 2) atTop atTop := by
  refine tendsto_atTop_mono' atTop
    (f₁ := fun w => (((primesLe w).card : ℝ) / (kataiPrimeRecip w) ^ 2) / 2) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 2,
      tendsto_card_primesLe.eventually_ge_atTop 2] with w hw hcard
    have hcpos : (0 : ℝ) < ((primesLe w).card : ℝ) := by exact_mod_cast card_primesLe_pos hw
    have h2 : (2 : ℕ) ∈ primesLe w :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
    have hL : 0 < kataiPrimeRecip w :=
      Finset.sum_pos' (fun p _ => by positivity) ⟨2, h2, by norm_num⟩
    have hge : ((primesLe w).card : ℝ) - 1 ≤ sumTable hubTable w N := sum_hubTable_ge w N hw
    have hhalf : ((primesLe w).card : ℝ) / 2 ≤ ((primesLe w).card : ℝ) - 1 := by linarith
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hge, hhalf, hL, sq_nonneg (kataiPrimeRecip w)]
  · exact tendsto_card_div_kataiPrimeRecip_sq.atTop_div_const (by norm_num)

/-- **THE REFUTATION.**  There is a `[0,1]`-valued correlation table satisfying the `AvgShape`
quantifier order — exactly the hypothesis `KataiOrthogonalityAvg` / `PairMeanAvgZero` impose —
whose pair SUM, the quantity the honest Kátai/BSZ inequality measures against `L(w)²`, is not
merely unbounded but `≫ L(w)²`.  So the averaged criterion, with `ε` quantified before `w`,
does not supply the input the Cauchy–Schwarz consumes, and its citation as a theorem of
Bourgain–Sarnak–Ziegler / Kátai is not supported by their proof. -/
theorem avgShape_not_imply_kataiBudget :
    ∃ G : ℕ → ℕ → ℕ → ℝ,
      (∀ p q N, 0 ≤ G p q N ∧ G p q N ≤ 1) ∧ AvgShape G ∧
      (∀ N : ℕ, Tendsto (fun w => sumTable G w N / (kataiPrimeRecip w) ^ 2) atTop atTop) :=
  ⟨hubTable, fun p q N => ⟨hubTable_nonneg p q N, hubTable_le_one p q N⟩,
    avgShape_hubTable, hubTable_sumTable_div_sq_atTop⟩

end NormalNumbers.CastingOut
