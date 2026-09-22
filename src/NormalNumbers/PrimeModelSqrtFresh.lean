import NormalNumbers.PrimeModelFamilyConsumer

/-!
# The square-root fresh-mass criterion

`papers/ROUND2-multicutoff-astra.md` §11 (and Fable §9).  The hypothesis

    SqrtFreshMassZero P  :  S_P(⌊√N⌋, N) → 0

replaces the schedule-dependent `FreshMassZero` of `PrimeModelFamilyConsumer`.  This file is
lap 0 of `KICKOFF-2026-09-22-multicutoff-lean.md`: the definition, the **exact finite root-chain
estimate** (Astra 11.3) and the two implications that make the new hypothesis weaker than the
old ones.

Main results:

* `recipSumIoc_le_rootChain` — if `r_P(q) = S_P(⌊√q⌋, q) ≤ ρ` for every `q ≥ Z` and `Z ≤ y < M`,
  then `S_P(y, M) ≤ ρ ⌈log(log M / log y)/log 2⌉`.  The chain `M_{l+1} = ⌊√M_l⌋` telescopes
  exactly; rounding the roots down only helps.
* `sqrtFreshMassZero_of_freshMassZero` — the old cutoff `yI N` is `≤ ⌊√N⌋` eventually.
* `sqrtFreshMassZero_of_relDensityZero` — relative density zero gives it by dominated Abel on
  the single window `(⌊√N⌋, N]`, where the Mertens ratio is bounded by an absolute constant.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.SqrtFresh

open NormalNumbers.G4Sparse NormalNumbers.PrimeModel.DensityMass
open NormalNumbers.PrimeModel.Params NormalNumbers.PrimeModel.FamilyIter

variable (P : ℕ → Prop) [DecidablePred P]

/-- **Square-root fresh reciprocal mass** of `P` vanishes (Astra 11.1). -/
def SqrtFreshMassZero : Prop :=
  Tendsto (fun N : ℕ => recipSumIoc P (Nat.sqrt N) N) atTop (𝓝 0)

/-! ### Elementary monotonicity and splitting of `recipSumIoc` -/

/-- Raising the lower cutoff only removes terms. -/
theorem recipSumIoc_mono_left {y y' x : ℕ} (h : y ≤ y') :
    recipSumIoc P y' x ≤ recipSumIoc P y x := by
  unfold recipSumIoc
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left h)) ?_
  intro p _ _
  positivity

/-- Subadditivity across an arbitrary intermediate point (no ordering assumed). -/
theorem recipSumIoc_split_le (y m x : ℕ) :
    recipSumIoc P y x ≤ recipSumIoc P y m + recipSumIoc P m x := by
  classical
  unfold recipSumIoc
  have hsub : (Finset.Ioc y x).filter (fun p => p.Prime ∧ P p) ⊆
      ((Finset.Ioc y m).filter (fun p => p.Prime ∧ P p)) ∪
        ((Finset.Ioc m x).filter (fun p => p.Prime ∧ P p)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    by_cases hpm : p ≤ m
    · exact Finset.mem_union_left _ (by
        simp only [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨hp.1.1, hpm⟩, hp.2⟩)
    · exact Finset.mem_union_right _ (by
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)) ?_
  have := Finset.sum_union_inter (s₁ := (Finset.Ioc y m).filter (fun p => p.Prime ∧ P p))
    (s₂ := (Finset.Ioc m x).filter (fun p => p.Prime ∧ P p)) (f := fun p => (1:ℝ) / p)
  have hnn : (0:ℝ) ≤ ∑ p ∈ ((Finset.Ioc y m).filter (fun p => p.Prime ∧ P p)) ∩
      ((Finset.Ioc m x).filter (fun p => p.Prime ∧ P p)), (1:ℝ) / p := by
    refine Finset.sum_nonneg fun p _ => by positivity
  linarith

/-- `recipSumIoc P y x = 0` once `x ≤ y`. -/
theorem recipSumIoc_of_le {y x : ℕ} (h : x ≤ y) : recipSumIoc P y x = 0 := by
  unfold recipSumIoc
  rw [Finset.Ioc_eq_empty (by omega)]
  simp

/-! ### The exact finite root-chain estimate (Astra 11.1) -/

/-- Integer form of the root chain: if the square-root window mass above `Z` is `≤ ρ` and
`M ≤ y ^ (2 ^ K)`, then `S_P(y, M) ≤ ρ K`. -/
theorem recipSumIoc_le_rootChain_pow {ρ : ℝ} (hρ : 0 ≤ ρ) {Z y : ℕ} (hZ : Z ≤ y)
    (hr : ∀ q, Z ≤ q → recipSumIoc P (Nat.sqrt q) q ≤ ρ) :
    ∀ K M : ℕ, M ≤ y ^ (2 ^ K) → recipSumIoc P y M ≤ ρ * K := by
  intro K
  induction K with
  | zero =>
      intro M hM
      simp only [pow_zero, pow_one] at hM
      rw [recipSumIoc_of_le P hM]
      simp
  | succ K ih =>
      intro M hM
      by_cases hMy : M ≤ y
      · rw [recipSumIoc_of_le P hMy]
        positivity
      · push_neg at hMy
        have hZM : Z ≤ M := le_trans hZ hMy.le
        have hhead : recipSumIoc P (Nat.sqrt M) M ≤ ρ := hr M hZM
        have hsq : Nat.sqrt M ≤ y ^ (2 ^ K) := by
          have h1 : M ≤ (y ^ (2 ^ K)) * (y ^ (2 ^ K)) := by
            calc M ≤ y ^ (2 ^ (K + 1)) := hM
              _ = (y ^ (2 ^ K)) * (y ^ (2 ^ K)) := by
                  rw [← pow_add]; congr 1; ring
          have h2 : Nat.sqrt (y ^ (2 ^ K) * y ^ (2 ^ K)) = y ^ (2 ^ K) := (by rw [← pow_two]; exact Nat.sqrt_eq' _)
          exact (Nat.sqrt_le_sqrt h1).trans (le_of_eq h2)
        have htail : recipSumIoc P y (Nat.sqrt M) ≤ ρ * K := ih _ hsq
        have := recipSumIoc_split_le P y (Nat.sqrt M) M
        push_cast
        linarith
  
/-- **Astra 11.3**: the exact finite root-chain estimate. -/
theorem recipSumIoc_le_rootChain {ρ : ℝ} (hρ : 0 ≤ ρ) {Z y M : ℕ} (hy : 2 ≤ y) (hZ : Z ≤ y)
    (hM : y < M) (hr : ∀ q, Z ≤ q → recipSumIoc P (Nat.sqrt q) q ≤ ρ) :
    recipSumIoc P y M ≤ ρ * ⌈Real.log (Real.log M / Real.log y) / Real.log 2⌉₊ := by
  set K : ℕ := ⌈Real.log (Real.log M / Real.log y) / Real.log 2⌉₊ with hK
  refine recipSumIoc_le_rootChain_pow P hρ hZ hr K M ?_
  -- `M ≤ y ^ (2 ^ K)` by taking logarithms
  have hy2 : (2:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy
  have hylog : 0 < Real.log y := Real.log_pos (by linarith)
  have hMy : (y:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hMpos : (0:ℝ) < (M:ℝ) := by linarith
  have hMlog : 0 < Real.log M := Real.log_pos (by linarith)
  set t : ℝ := Real.log M / Real.log y with ht
  have htpos : 0 < t := by positivity
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hylog, one_mul]
    exact Real.log_le_log (by linarith) hMy.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKge : Real.log t / Real.log 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hlogt : Real.log t ≤ (K : ℝ) * Real.log 2 := by
    rw [div_le_iff₀ hlog2] at hKge; exact hKge
  have ht2K : t ≤ (2:ℝ) ^ K := by
    have hpow : Real.log ((2:ℝ) ^ K) = (K : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    have := Real.exp_le_exp.2 hlogt
    rw [Real.exp_log htpos] at this
    calc t ≤ Real.exp ((K:ℝ) * Real.log 2) := this
      _ = (2:ℝ) ^ K := by rw [← hpow, Real.exp_log (by positivity)]
  have hlogM : Real.log M ≤ ((2:ℝ) ^ K) * Real.log y := by
    have : t * Real.log y ≤ ((2:ℝ) ^ K) * Real.log y :=
      mul_le_mul_of_nonneg_right ht2K hylog.le
    rwa [ht, div_mul_cancel₀ _ (ne_of_gt hylog)] at this
  have hfin : (M:ℝ) ≤ ((y:ℝ)) ^ (2 ^ K : ℕ) := by
    have hpos : (0:ℝ) < ((y:ℝ)) ^ (2 ^ K : ℕ) := by positivity
    rw [← Real.log_le_log_iff hMpos hpos, Real.log_pow]
    push_cast
    exact hlogM
  exact_mod_cast hfin

/-! ### The old cutoff is below the square root -/

theorem sqrtFreshMassZero_of_freshMassZero (hF : FreshMassZero P) : SqrtFreshMassZero P := by
  have hy : ∀ᶠ N : ℕ in atTop, yI N ≤ Nat.sqrt N := by
    filter_upwards [epsI_facts, eventually_ge_atTop 1] with N hN hN1
    have heps : epsI N < 1 / 2 := hN.2.2.2.1
    have h1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    have hmono : (N:ℝ) ^ epsI N ≤ (N:ℝ) ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow_of_exponent_le h1 heps.le
    have hsq : (N:ℝ) ^ ((1:ℝ)/2) = Real.sqrt N := (Real.sqrt_eq_rpow _).symm
    rw [hsq] at hmono
    calc yI N = ⌊(N:ℝ) ^ epsI N⌋₊ := rfl
      _ ≤ ⌊Real.sqrt N⌋₊ := Nat.floor_le_floor hmono
      _ = Nat.sqrt N := Real.nat_floor_real_sqrt_eq_nat_sqrt
  refine squeeze_zero' (Eventually.of_forall fun N => recipSumIoc_nonneg P _ _) ?_ hF
  filter_upwards [hy] with N hN
  exact (recipSumIoc_mono_left P hN).trans (recipSumIoc_mono_right P (by omega))

/-! ### Relative density zero -/

theorem sqrtFreshMassZero_of_relDensityZero
    (h : Tendsto (fun t : ℕ => (piP P t : ℝ) / (t.primesBelow.card : ℝ)) atTop (𝓝 0)) :
    SqrtFreshMassZero P := by
  have hlog3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set C : ℝ := 9 + 12 * Real.log 3 with hC
  have hCpos : 0 < C := by rw [hC]; linarith
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · exact Eventually.of_forall fun N => lt_of_lt_of_le ha (recipSumIoc_nonneg P _ _)
  · set δ : ℝ := a / (2 * C) with hδ
    have hδpos : 0 < δ := by rw [hδ]; positivity
    obtain ⟨T, hT⟩ := eventually_atTop.1 ((tendsto_order.1 h).2 δ hδpos)
    filter_upwards [eventually_ge_atTop ((T + 3) ^ 2)] with N hN
    have hs : T + 3 ≤ Nat.sqrt N := by
      have h1 : Nat.sqrt ((T + 3) ^ 2) ≤ Nat.sqrt N := Nat.sqrt_le_sqrt hN
      rwa [Nat.sqrt_eq'] at h1
    set s : ℕ := Nat.sqrt N with hsdef
    have hs2 : 2 ≤ s := by omega
    have hsN : s ≤ N := Nat.sqrt_le_self N
    have hdom : ∀ t, s < t → t ≤ N + 1 → (piP P t : ℝ) ≤ δ * (t.primesBelow.card : ℝ) := by
      intro t hts _
      have hTt : T ≤ t := by omega
      have hpi : (0:ℝ) < (t.primesBelow.card : ℝ) := by
        have hmem : 2 ∈ Nat.primesBelow t := by
          rw [Nat.mem_primesBelow]
          exact ⟨by omega, Nat.prime_two⟩
        exact_mod_cast Finset.card_pos.2 ⟨2, hmem⟩
      have hlt := hT t hTt
      rw [div_lt_iff₀ hpi] at hlt
      exact hlt.le
    have key := recipSumIoc_le_of_dominated' P hδpos.le hs2 hsN hdom
    -- the Mertens ratio on `(⌊√N⌋, N]` is at most `3`
    have hcube : N ≤ s ^ 3 := by
      have hlt : N < (s + 1) ^ 2 := Nat.lt_succ_sqrt' N
      nlinarith [hs2, hlt]
    have hsr : (2:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs2
    have hslog : 0 < Real.log s := Real.log_pos (by linarith)
    have hNr : (4:ℝ) ≤ (N:ℝ) := by
      have : (4:ℕ) ≤ N := by nlinarith [hs2, hsN, Nat.sqrt_le' N]
      exact_mod_cast this
    have hNlog : 0 < Real.log N := Real.log_pos (by linarith)
    have hcube' : (N:ℝ) ≤ (s:ℝ) ^ 3 := by exact_mod_cast hcube
    have hlogN : Real.log N ≤ 3 * Real.log s := by
      have h1 : Real.log N ≤ Real.log ((s:ℝ) ^ 3) :=
        Real.log_le_log (by linarith) hcube'
      rwa [Real.log_pow] at h1
      
    have hratio : Real.log N / Real.log s ≤ 3 := by
      rw [div_le_iff₀ hslog]; linarith
    have hratiopos : 0 < Real.log N / Real.log s := by positivity
    have hlogratio : Real.log (Real.log N / Real.log s) ≤ Real.log 3 :=
      Real.log_le_log hratiopos hratio
    have hfinal : δ * (9 + 12 * Real.log (Real.log N / Real.log s)) ≤ δ * C := by
      refine mul_le_mul_of_nonneg_left ?_ hδpos.le
      rw [hC]; linarith
    have hhalf : δ * C = a / 2 := by rw [hδ]; field_simp
    have : recipSumIoc P s N ≤ a / 2 := by rw [← hhalf]; exact key.trans hfinal
    linarith

end NormalNumbers.PrimeModel.SqrtFresh

#print axioms NormalNumbers.PrimeModel.SqrtFresh.recipSumIoc_le_rootChain
#print axioms NormalNumbers.PrimeModel.SqrtFresh.sqrtFreshMassZero_of_freshMassZero
#print axioms NormalNumbers.PrimeModel.SqrtFresh.sqrtFreshMassZero_of_relDensityZero
