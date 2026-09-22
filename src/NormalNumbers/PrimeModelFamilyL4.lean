import NormalNumbers.PrimeModelKMTFixedH
import NormalNumbers.PrimeModelFamilyIterPow

/-!
# Family theorem under `(π_P(x)/π(x)) · log log log log x → 0`

With the phase-weighted transfer term (`window_bound_regime_h`), the fresh mass enters the
window bound with the `h`-dependent coefficient `4π|h|/3` and **no factor of the window length**.
Along the Part IV schedule (`J₁ = ⌊L₃N⌋₊`, `ε = J₁^{-4}`, `y = ⌊N^ε⌋₊`, `J = min(J₁, ⌊S_P(y)/8⌋₊)`)
the Abel log-ratio is `≤ 1 + 4 L₄N`, so `recipSumIoc P y N ≤ δ · (21 + 48 L₄N)` whenever the
relative density on `(y, N+1]` is `≤ δ`.  Since `L₄t ≥ L₄N/2` there, the hypothesis

    SparseL4o P := (π_P(x)/π(x)) · L₄x → 0

gives, for every `η > 0`, `δ = 2η/L₄N` eventually and hence `recipSumIoc P y N ≤ 2η(21/L₄N + 48)
→ O(η)`; `η` arbitrary gives `recipSumIoc P y N → 0` and `recipSumIoc P y (2N) ≤ 1` eventually.
Everything else is reused from Parts IV–V (`term_two_iter3`, `term_three_iter3`, `regime_iter3`,
the tail argument).

Main theorem: `isNormal_subsetLambert_of_sparseL4o : SparseL4o P → DivergentRecip P →
IsNormal 4 (subsetLambert P 4)`.  Covers every `π_P ≤ π/(L₃)^β` (`β > 0`) and every
`π_P ≤ π/(L₄)^γ` (`γ > 1`); density `≍ 1/L₄` is the barrier of this route.  (Astra, mails
20260922T190221Z and 20260922T190418Z.)
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.FamilyIter

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel.DensityMass NormalNumbers.PrimeModel.Params
open NormalNumbers.PrimeModel.KMT NormalNumbers.PrimeModel.PhaseAlgebra
open NormalNumbers.PrimeModel.Family NormalNumbers.PrimeModel.FamilySharp

variable (P : ℕ → Prop) [DecidablePred P]

/-- The little-o density hypothesis: `(π_P(x)/π(x)) · log log log log x → 0`. -/
def SparseL4o : Prop :=
  Tendsto (fun x : ℕ => (piP P x : ℝ) / (x.primesBelow.card : ℝ) * L4 x) atTop (𝓝 0)

/-- `π_P(x) (L₃x)^β ≤ π(x)` eventually, for some `β > 0`, implies `SparseL4o`
(`L₄x = log L₃x ≤ (L₃x)^β / β`... any `L₄ ≪ L₃^β` bound suffices). -/
theorem sparseL4o_of_sparseIterPow {β : ℝ} (hβ : 0 < β) (hS : SparseIterPow P β) :
    SparseL4o P := by
  have hG : Tendsto (fun N : ℕ => L4 N / (L3 N) ^ β) atTop (𝓝 0) := by
    have h := (tendsto_log_div_rpow (r := β) hβ).comp L3_tendsto
    simpa [Function.comp_def, L4] using h
  refine squeeze_zero' ?_ ?_ hG
  · filter_upwards [L3_tendsto.eventually_ge_atTop (1 : ℝ)] with x hx
    have h1 : (0 : ℝ) ≤ L4 x := Real.log_nonneg hx
    have h2 : (0 : ℝ) ≤ (piP P x : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ (x.primesBelow.card : ℝ) := Nat.cast_nonneg _
    exact mul_nonneg (div_nonneg h2 h3) h1
  · filter_upwards [hS, eventually_ge_atTop 3,
      L3_tendsto.eventually_ge_atTop (1 : ℝ)] with x hx hx3 hL3
    have hcard : 0 < x.primesBelow.card :=
      Finset.card_pos.mpr ⟨2, by rw [Nat.mem_primesBelow]; exact ⟨by omega, Nat.prime_two⟩⟩
    have hpi : (0 : ℝ) < (x.primesBelow.card : ℝ) := by exact_mod_cast hcard
    have hu0 : (0 : ℝ) < L3 x := by linarith
    have hupos : (0 : ℝ) < (L3 x) ^ β := Real.rpow_pos_of_pos hu0 β
    have h4 : (0 : ℝ) ≤ L4 x := Real.log_nonneg hL3
    have hratio : (piP P x : ℝ) / (x.primesBelow.card : ℝ) ≤ 1 / (L3 x) ^ β := by
      rw [div_le_div_iff₀ hpi hupos]
      linarith
    calc (piP P x : ℝ) / (x.primesBelow.card : ℝ) * L4 x
        ≤ (1 / (L3 x) ^ β) * L4 x := mul_le_mul_of_nonneg_right hratio h4
      _ = L4 x / (L3 x) ^ β := by ring

/-- `L₄t ≥ L₄N/2` for `t > y_N`, eventually (from `L₃t ≥ L₃N − log 2` and `L₃N ≥ 2`,
`log(L₃N − 1) ≥ L₄N − 1 ≥ L₄N/2` once `L₄N ≥ 2`). -/
theorem L4_half_le : ∀ᶠ N : ℕ in atTop, ∀ t : ℕ, yI N < t → L4 N / 2 ≤ L4 t := by
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 2, L4_tendsto.eventually_ge_atTop 2,
    yI_facts] with N hN hL hL3 hL4 hyI t ht
  obtain ⟨-, h2y, -, hloglogy, hlogypos, -⟩ := hyI
  have hpos : 0 < L2 N := by linarith
  have hu0 : (0 : ℝ) < L3 N := by linarith
  have hyr : (2 : ℝ) ≤ ((yI N : ℕ) : ℝ) := by exact_mod_cast h2y
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hty : ((yI N : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht.le
  have hlt : Real.log (yI N) ≤ Real.log t := Real.log_le_log (by linarith) hty
  have hllt : Real.log (Real.log (yI N)) ≤ Real.log (Real.log t) :=
    Real.log_le_log hlogypos hlt
  have hbig : L2 N / 2 ≤ Real.log (Real.log t) := le_trans hloglogy hllt
  have hL3t : L3 N - Real.log 2 ≤ L3 t := by
    have h1 : Real.log (L2 N / 2) ≤ Real.log (Real.log (Real.log t)) :=
      Real.log_le_log (by linarith) hbig
    rw [Real.log_div (ne_of_gt hpos) (by norm_num), ← L3_eq] at h1
    exact h1
  have hstep : L3 N - 1 ≤ L3 t := by linarith
  have hlog : Real.log (L3 N - 1) ≤ Real.log (L3 t) :=
    Real.log_le_log (by linarith) hstep
  have hsub : Real.log (L3 N) - 1 ≤ Real.log (L3 N - 1) := by
    have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h1 : L3 N ≤ Real.exp 1 * (L3 N - 1) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp 1 - 2.7)
        (by linarith : (0 : ℝ) ≤ L3 N - 1)]
    have h2 : Real.log (L3 N) ≤ Real.log (Real.exp 1 * (L3 N - 1)) :=
      Real.log_le_log hu0 h1
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (by linarith), Real.log_exp] at h2
    linarith
  have hv : L4 N = Real.log (L3 N) := rfl
  have hvt : L4 t = Real.log (L3 t) := rfl
  rw [hv, hvt]
  linarith

/-- For every `η > 0`, eventually `recipSumIoc P y_N M ≤ (2η/L₄N)(9 + 12 log(log M/log y_N))`
for all `M ≥ y_N`. -/
theorem fresh_bound_L4o (hS : SparseL4o P) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, yI N ≤ M →
    recipSumIoc P (yI N) M
      ≤ (2 * η / L4 N) * (9 + 12 * Real.log (Real.log M / Real.log (yI N))) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.1 hS).2 η hη)
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 2, L4_tendsto.eventually_ge_atTop 2,
    yI_facts, L4_half_le, yI_tendsto.eventually_ge_atTop x₀,
    yI_tendsto.eventually_ge_atTop 3] with
    N hN hL hL3 hL4 hyI hhalf hy0 hy3 M hM
  obtain ⟨-, h2y, -, -, hlogypos, -⟩ := hyI
  have hv0 : (0 : ℝ) < L4 N := by linarith
  have hδ : (0 : ℝ) ≤ 2 * η / L4 N := by positivity
  have hdom : ∀ t : ℕ, yI N < t → t ≤ M + 1 →
      (piP P t : ℝ) ≤ (2 * η / L4 N) * (t.primesBelow.card : ℝ) := by
    intro t ht _
    have ht3 : 3 ≤ t := by omega
    have ht0 : x₀ ≤ t := by omega
    have hsp := hx₀ t ht0
    have hcard : 0 < t.primesBelow.card :=
      Finset.card_pos.mpr ⟨2, by rw [Nat.mem_primesBelow]; exact ⟨by omega, Nat.prime_two⟩⟩
    have hpi : (0 : ℝ) < (t.primesBelow.card : ℝ) := by exact_mod_cast hcard
    have hvt : L4 N / 2 ≤ L4 t := hhalf t ht
    have hpnn : (0 : ℝ) ≤ (piP P t : ℝ) := Nat.cast_nonneg _
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpi] at hsp
    have h2 : (piP P t : ℝ) * (L4 N / 2) ≤ η * (t.primesBelow.card : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hvt hpnn]
    rw [div_mul_eq_mul_div, le_div_iff₀ hv0]
    linarith
  exact recipSumIoc_le_of_dominated' P hδ h2y hM hdom

/-- Fresh mass between `y_N` and `N` tends to `0`. -/
theorem fresh_mass_L4o (hS : SparseL4o P) :
    Tendsto (fun N : ℕ => recipSumIoc P (yI N) N) atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hη : (0 : ℝ) < ε / 200 := by linarith
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 2, L4_tendsto.eventually_ge_atTop 1,
    yI_facts, J1_facts, fresh_bound_L4o P hS hη] with N hN _hL hL3 hv1 hyI hJ hfb
  obtain ⟨-, -, hyN, -, hlogypos, hratio⟩ := hyI
  obtain ⟨-, -, hj1, hjlog⟩ := hJ
  have hu0 : (0 : ℝ) < L3 N := by linarith
  have hj0 : (0 : ℝ) < ((J1 N : ℕ) : ℝ) := by linarith
  have hv0 : (0 : ℝ) < L4 N := by linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hratiopos : 0 < Real.log N / Real.log (yI N) := div_pos (by linarith) hlogypos
  have hlr : Real.log (Real.log N / Real.log (yI N)) ≤ Real.log (2 * ((J1 N : ℕ) : ℝ) ^ 4) :=
    Real.log_le_log hratiopos hratio
  have hexp : Real.log (2 * ((J1 N : ℕ) : ℝ) ^ 4)
      = Real.log 2 + 4 * Real.log (J1 N) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb := hfb N hyN
  have hstep : (9 : ℝ) + 12 * Real.log (Real.log N / Real.log (yI N)) ≤ 21 + 48 * L4 N := by
    rw [hexp] at hlr; linarith
  have hδ0 : (0 : ℝ) ≤ 2 * (ε / 200) / L4 N := by positivity
  have h2 : recipSumIoc P (yI N) N ≤ (2 * (ε / 200) / L4 N) * (21 + 48 * L4 N) :=
    le_trans hb (mul_le_mul_of_nonneg_left hstep hδ0)
  have hfin : (2 * (ε / 200) / L4 N) * (21 + 48 * L4 N) < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hv0]
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hv1)]
  have hnn := recipSumIoc_nonneg P (yI N) N
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  linarith

/-- Fresh mass between `y_N` and `2N` is eventually `≤ 1`. -/
theorem fresh_mass_two_L4o (hS : SparseL4o P) : ∀ᶠ N : ℕ in atTop,
    recipSumIoc P (yI N) (2 * N) ≤ 1 := by
  have hη : (0 : ℝ) < 1 / 400 := by norm_num
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
    L3_tendsto.eventually_ge_atTop 2, L4_tendsto.eventually_ge_atTop 1,
    yI_facts, J1_facts, fresh_bound_L4o P hS hη] with N hN hL hL3 hv1 hyI hJ hfb
  obtain ⟨-, -, hyN, -, hlogypos, hratio⟩ := hyI
  obtain ⟨-, -, hj1, hjlog⟩ := hJ
  have hu0 : (0 : ℝ) < L3 N := by linarith
  have hj0 : (0 : ℝ) < ((J1 N : ℕ) : ℝ) := by linarith
  have hv0 : (0 : ℝ) < L4 N := by linarith
  have hlogN : 1 < Real.log N := logN_gt_one hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hlog2N : Real.log ((2 * N : ℕ) : ℝ) ≤ 2 * Real.log N := by
    rw [hcast, Real.log_mul (by norm_num) (ne_of_gt hNpos)]; linarith
  have hlog2Npos : 0 < Real.log ((2 * N : ℕ) : ℝ) := by
    rw [hcast, Real.log_mul (by norm_num) (ne_of_gt hNpos)]; linarith
  have hratio2 : Real.log ((2 * N : ℕ) : ℝ) / Real.log (yI N) ≤ 4 * ((J1 N : ℕ) : ℝ) ^ 4 := by
    rw [div_le_iff₀ hlogypos]
    rw [div_le_iff₀ hlogypos] at hratio
    linarith
  have hlr : Real.log (Real.log ((2 * N : ℕ) : ℝ) / Real.log (yI N))
      ≤ Real.log (4 * ((J1 N : ℕ) : ℝ) ^ 4) :=
    Real.log_le_log (div_pos hlog2Npos hlogypos) hratio2
  have hexp : Real.log (4 * ((J1 N : ℕ) : ℝ) ^ 4)
      = Real.log 4 + 4 * Real.log (J1 N) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hb := hfb (2 * N) (le_trans hyN (by omega))
  have hδ0 : (0 : ℝ) ≤ 2 * (1 / 400 : ℝ) / L4 N := by positivity
  have hstep : recipSumIoc P (yI N) (2 * N)
      ≤ (2 * (1 / 400 : ℝ) / L4 N) * (9 + 12 * (2 + 4 * L4 N)) := by
    refine le_trans hb ?_
    have h9 : (9 : ℝ) + 12 * Real.log (Real.log ((2 * N : ℕ) : ℝ) / Real.log (yI N))
        ≤ 9 + 12 * (2 + 4 * L4 N) := by
      rw [hexp] at hlr; linarith
    exact mul_le_mul_of_nonneg_left h9 hδ0
  have hfin : (2 * (1 / 400 : ℝ) / L4 N) * (9 + 12 * (2 + 4 * L4 N)) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hv0]
    linarith
  linarith

/-- Term 1 (phase-weighted transfer) at fixed `h`: `(4π|h|/3)(2R + J/N) → 0`. -/
theorem term_one_L4o (hS : SparseL4o P) (h : ℤ) :
    Tendsto (fun N : ℕ => (4 * Real.pi * |(h : ℝ)| / 3) *
      (2 * recipSumIoc P (yI N) N + (JI P N : ℝ) / N)) atTop (𝓝 0) := by
  have hR := fresh_mass_L4o P hS
  have hlogdiv : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) atTop (𝓝 0) := by
    have h1 := (tendsto_log_div_rpow (r := (1 : ℝ)) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, Real.rpow_one] using h1
  have hJN : Tendsto (fun N : ℕ => (JI P N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hlogdiv
    · filter_upwards [eventually_ge_atTop 1] with N hN
      positivity
    · filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500,
        JI_le_L3 P] with N hN hL hJ
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have hlogN : 1 < Real.log N := logN_gt_one hN
      have hL2 : L2 N ≤ Real.log N := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.log N by linarith)
        have he : L2 N = Real.log (Real.log N) := rfl
        rw [he]; linarith
      have hL3le : L3 N ≤ L2 N := by
        have hpos : (0 : ℝ) < L2 N := by linarith
        have h := Real.log_le_sub_one_of_pos hpos
        have he : L3 N = Real.log (L2 N) := rfl
        rw [he]; linarith
      exact div_le_div_of_nonneg_right (by linarith) hNpos.le
  have hsum := ((hR.const_mul (2 : ℝ)).add hJN).const_mul (4 * Real.pi * |(h : ℝ)| / 3)
  simpa using hsum

/-- The L¹ tail; identical to `tail_iter3` with `fresh_mass_two_L4o`. -/
theorem tail_L4o (hS : SparseL4o P) (hP : DivergentRecip P) :
    Tendsto (fun N : ℕ => (recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12) / (4 : ℝ) ^ JI P N)
      atTop (𝓝 0) := by
  set ρ : ℝ := Real.log 4 - 1 with hρdef
  have hlog4 : 1 < Real.log 4 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hf : Tendsto (fun N : ℕ => (13 * (JI P N : ℝ) + 21) / (4 : ℝ) ^ (JI P N))
      atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 4)
    have hsum : Tendsto
        (fun n : ℕ => 13 * ((n : ℝ) ^ 1 / (4 : ℝ) ^ n) + 21 * ((n : ℝ) ^ 0 / (4 : ℝ) ^ n))
        atTop (𝓝 0) := by
      simpa using (h1.const_mul (13 : ℝ)).add (h0.const_mul (21 : ℝ))
    refine Tendsto.congr (fun N => ?_) (hsum.comp (JI_tendsto P hP))
    simp only [Function.comp_apply, pow_one, pow_zero]
    ring
  have hgt : Tendsto (fun N : ℕ => 120 * (L2 N) ^ (-ρ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (L2 N) ^ (-ρ)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop hρ0).comp L2_tendsto
      simpa [Function.comp_def] using this
    simpa using h1.const_mul (120 : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ (by simpa using hf.add hgt)
  · have := recipSumLe_nonneg P (2 * N)
    positivity
  filter_upwards [eventually_ge_atTop 3, L2_tendsto.eventually_ge_atTop 2500, JI_le_L3 P,
    fresh_mass_two_L4o P hS, yI_facts] with N hN hL hJle hfm2 hyf
  obtain ⟨hu1, hu2, -⟩ := L3_bounds hL
  obtain ⟨-, -, hyN, -⟩ := hyf
  have ht0 : 0 < L2 N := by linarith
  have hulog : L3 N = Real.log (L2 N) := L3_eq N
  have hrp : (0 : ℝ) < (L2 N) ^ (-ρ) := Real.rpow_pos_of_pos ht0 _
  have hpow0 : (0 : ℝ) < (4 : ℝ) ^ (JI P N) := by positivity
  have hfnn : (0 : ℝ) ≤ (13 * (JI P N : ℝ) + 21) / (4 : ℝ) ^ (JI P N) := by positivity
  have hgnn : (0 : ℝ) ≤ 120 * (L2 N) ^ (-ρ) := by positivity
  rcases le_total (J1 N) (⌊recipSumLe P (yI N) / 8⌋₊) with hcase | hcase
  · have hJlow : L3 N - 1 ≤ (JI P N : ℝ) := JI_lower P hcase (by linarith)
    have hpow : (L2 N) ^ Real.log 4 / 4 ≤ (4 : ℝ) ^ (JI P N) := by
      have h1 : (4 : ℝ) ^ (JI P N) = (4 : ℝ) ^ ((JI P N : ℕ) : ℝ) := (Real.rpow_natCast 4 _).symm
      have h2 : (4 : ℝ) ^ (L3 N - 1) ≤ (4 : ℝ) ^ ((JI P N : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h3 : (4 : ℝ) ^ (L3 N - 1) = (L2 N) ^ Real.log 4 / 4 := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one]
        congr 1
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 4), Real.rpow_def_of_pos ht0, hulog]
        congr 1
        ring
      rw [h1, ← h3]; exact h2
    have hL2two : L2 (2 * N) ≤ L2 N + 1 := by
      have hlogN : 1 < Real.log N := logN_gt_one hN
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
      have hNne : ((N : ℝ)) ≠ 0 := by
        have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        exact ne_of_gt (by linarith)
      have hlog2N : Real.log ((2 * N : ℕ) : ℝ) = Real.log 2 + Real.log N := by
        rw [hcast, Real.log_mul (by norm_num) hNne]
      have hlog2Npos : 0 < Real.log ((2 * N : ℕ) : ℝ) := by rw [hlog2N]; linarith
      have h1 : Real.log ((2 * N : ℕ) : ℝ) ≤ 2 * Real.log N := by rw [hlog2N]; linarith
      have h2 : L2 (2 * N) ≤ Real.log (2 * Real.log N) := Real.log_le_log hlog2Npos h1
      rw [Real.log_mul (by norm_num) (by linarith)] at h2
      have h4 : Real.log (Real.log N) = L2 N := rfl
      linarith [h2, h4.le, h4.ge]
    have hcrude : recipSumLe P (2 * N) ≤ 12 * L2 (2 * N) + 21 :=
      recipSumLe_le_crude P (by omega)
    have hnum : recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12 ≤ 30 * L2 N := by
      have h5 : (JI P N : ℝ) ≤ L3 N := hJle
      linarith
    have h30 : (0 : ℝ) ≤ 30 * L2 N := by linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12) / (4 : ℝ) ^ (JI P N)
        ≤ (30 * L2 N) / ((L2 N) ^ Real.log 4 / 4) :=
      div_le_div₀ h30 hnum (by positivity) hpow
    have hfin : (30 * L2 N) / ((L2 N) ^ Real.log 4 / 4) = 120 * (L2 N) ^ (-ρ) := by
      rw [hρdef, show -(Real.log 4 - 1) = 1 - Real.log 4 by ring, Real.rpow_sub ht0,
        Real.rpow_one]
      field_simp
      norm_num
    linarith [hstep, hfin.le, hfin.ge, hfnn]
  · have hJeq : JI P N = ⌊recipSumLe P (yI N) / 8⌋₊ := min_eq_right hcase
    have hSlt : recipSumLe P (yI N) < 8 * (JI P N : ℝ) + 8 := by
      have := Nat.lt_floor_add_one (recipSumLe P (yI N) / 8)
      rw [← hJeq] at this
      linarith
    have hsplit : recipSumLe P (2 * N)
        = recipSumLe P (yI N) + recipSumIoc P (yI N) (2 * N) :=
      recipSumLe_add_recipSumIoc P (le_trans hyN (by omega))
    have hnum : recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12 ≤ 13 * (JI P N : ℝ) + 21 := by
      rw [hsplit]; linarith
    have hstep : (recipSumLe P (2 * N) + 5 * (JI P N : ℝ) + 12) / (4 : ℝ) ^ (JI P N)
        ≤ (13 * (JI P N : ℝ) + 21) / (4 : ℝ) ^ (JI P N) :=
      div_le_div_of_nonneg_right hnum hpow0.le
    linarith [hstep, hgnn]

theorem tailOK_L4o (hS : SparseL4o P) (hP : DivergentRecip P) : TailOK P (JI P) := by
  rw [TailOK]
  refine squeeze_zero' (Eventually.of_forall (fun N => ?_)) ?_ (tail_L4o P hS hP)
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact tail_error_L1 P (JI P N) N hN

/-- `KMT_along P (JI P)` from `window_bound_regime_h`, `term_one_L4o`, `term_two_iter3`,
`term_three_iter3`, `regime_iter3`. -/
theorem kmt_along_L4o (hS : SparseL4o P) (hP : DivergentRecip P) : KMT_along P (JI P) := by
  intro h hh
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have hsum : Tendsto (fun N : ℕ =>
      (4 * Real.pi * |(h : ℝ)| / 3) * (2 * recipSumIoc P (yI N) N + (JI P N : ℝ) / N)
        + Real.exp (3 * (JI P N : ℝ)) * Real.exp (- recipSumLe P (yI N))
        + (2 * (JI P N : ℝ) ^ 2 + 2 * (JI P N : ℝ) * Real.exp 20 + 4 + 2 * (4 : ℝ) ^ (JI P N))
            * Real.exp (-1 / (8 * (JI P N : ℝ) ^ 2 * epsI N))) atTop (𝓝 0) := by
    have := ((term_one_L4o P hS h).add (term_two_iter3 P hP)).add (term_three_iter3 P hP)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hsum
  filter_upwards [regime_iter3 P hP,
    (JI_tendsto P hP).eventually_ge_atTop (h.natAbs + 1)] with N hR hJ
  have hntw : NontrivialWindow (JI P N) h := ⟨h.natAbs + 1, by omega, hJ, nontrivial_site hh⟩
  have hb := window_bound_regime_h P h hntw hR
  have hy : yOf N (epsI N) = yI N := rfl
  rw [hy] at hb
  linarith [hb]

/-- **Family theorem, little-o form.**  Every prime set with `(π_P(x)/π(x)) log log log log x → 0`
and divergent reciprocal sum has a normal base-4 Lambert constant. -/
theorem isNormal_subsetLambert_of_sparseL4o (hS : SparseL4o P) (hP : DivergentRecip P) :
    IsNormal 4 (subsetLambert P 4) :=
  isNormal_subsetLambert_of_KMT_along P (JI P) (tailOK_L4o P hS hP) (kmt_along_L4o P hS hP)

end NormalNumbers.PrimeModel.FamilyIter
