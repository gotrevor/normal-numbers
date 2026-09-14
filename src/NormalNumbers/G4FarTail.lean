/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4MediumPrimes

/-!
# G4 disjunctivity, §4D: the infinite far tail — the progression mean of `ω`

Brief §4D, far tail.  `farAvg` is the sample mean of `|farPart|`, the layers `j > J`.  Each
layer is a shifted `ω`, and the only input needed is the **mean of `ω` over the AP sample**,
which we take entirely elementary — no Mertens, no Hardy–Ramanujan:

* `two_pow_omega_le_card_divisors` — `2^{ω(m)} ≤ d(m)`;
* `sum_card_divisors_le` — `∑_{m<N} d(m) ≤ N (log N + 1)` (the classical `∑_k ⌊N/k⌋`);
* `sum_log_le_card_mul_log_avg` — Jensen for `log` by hand, from `log x ≤ log c + x/c − 1`;
* **`sum_omegaR_add_le`** — the assembly: on any `P ⊆ range X`,
  `∑_{n∈P} ω(n+ρ) ≤ |P| · log( (X+ρ)(log(X+ρ)+1)/|P| ) / log 2`.

Growth in the shift `ρ` is only logarithmic, so summing against `4^{−j}` over `j > J` needs no
remote cutoff.
-/

open Finset Real
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert

/-! ### `2^ω ≤ d` -/

theorem two_pow_omega_le_card_divisors {m : ℕ} (hm : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ m.divisors.card := by
  rw [Nat.card_divisors hm, ← Finset.prod_const]
  refine Finset.prod_le_prod' fun p hp => ?_
  have := Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hm
    (Nat.dvd_of_mem_primeFactors hp)
  omega

lemma omegaR_mul_log_two_le {m : ℕ} (hm : m ≠ 0) :
    omegaR m * Real.log 2 ≤ Real.log (m.divisors.card : ℝ) := by
  rw [omegaR_eq, ← Real.log_pow]
  refine Real.log_le_log (by positivity) ?_
  exact_mod_cast two_pow_omega_le_card_divisors hm

/-! ### `∑_{m<N} d(m) ≤ N (log N + 1)` -/

lemma card_divisors_eq_sum_ico {m N : ℕ} (hm : m ≠ 0) (hmN : m < N) :
    m.divisors.card = ∑ k ∈ Finset.Ico 1 N, if k ∣ m then 1 else 0 := by
  rw [Finset.sum_boole]
  congr 1
  ext k
  rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨hk, -⟩
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hk
    have := Nat.pos_of_dvd_of_pos hk (Nat.pos_of_ne_zero hm)
    exact ⟨⟨by omega, by omega⟩, hk⟩
  · rintro ⟨-, hk⟩; exact ⟨hk, hm⟩

lemma card_multiples_Ico_le (N k : ℕ) (hk : 0 < k) :
    (((Finset.Ico 1 N).filter (fun m => k ∣ m)).card : ℝ) ≤ (N : ℝ) / k := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have h := Nat.card_multiples' N' k
  have heq : (Finset.Ico 1 (N' + 1)).filter (fun m => k ∣ m)
      = (Finset.range N'.succ).filter (fun m => m ≠ 0 ∧ k ∣ m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range, Nat.succ_eq_add_one]
    omega
  rw [heq, h]
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  calc ((N' / k : ℕ) : ℝ) ≤ (N' : ℝ) / k := Nat.cast_div_le
    _ ≤ ((N' + 1 : ℕ) : ℝ) / k := by gcongr; exact_mod_cast Nat.le_succ N'

/-- `∑_{m<N} d(m) ≤ N (log N + 1)`. -/
theorem sum_card_divisors_le (N : ℕ) :
    ∑ m ∈ Finset.range N, (m.divisors.card : ℝ) ≤ N * (Real.log N + 1) := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N <;> simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 : ∑ m ∈ Finset.range N, (m.divisors.card : ℝ)
      = ∑ m ∈ Finset.Ico 1 N, ∑ k ∈ Finset.Ico 1 N, (if k ∣ m then (1 : ℝ) else 0) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ N),
      ← Finset.range_eq_Ico, Finset.sum_range_one]
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero, zero_add]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Ico] at hm
    rw [card_divisors_eq_sum_ico (by omega) hm.2]
    push_cast
    rfl
  rw [h1, Finset.sum_comm]
  have h2 : ∀ k ∈ Finset.Ico 1 N,
      ∑ m ∈ Finset.Ico 1 N, (if k ∣ m then (1 : ℝ) else 0) ≤ (N : ℝ) / k := by
    intro k hk
    rw [Finset.sum_boole]
    exact card_multiples_Ico_le N k (Finset.mem_Ico.1 hk).1
  calc ∑ k ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, (if k ∣ m then (1 : ℝ) else 0)
      ≤ ∑ k ∈ Finset.Ico 1 N, (N : ℝ) / k := Finset.sum_le_sum h2
    _ = N * ∑ k ∈ Finset.Icc 1 (N - 1), (k : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        have : Finset.Ico 1 N = Finset.Icc 1 (N - 1) := by
          ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
        rw [this]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [div_eq_mul_inv]
    _ ≤ N * (1 + Real.log ((N - 1 : ℕ) : ℝ) - Real.log ((1 : ℕ) : ℝ)) := by
        gcongr
        exact sum_Icc_inv_le le_rfl (by omega)
    _ ≤ N * (Real.log N + 1) := by
        gcongr
        rw [Nat.cast_one, Real.log_one, sub_zero]
        have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
        have := Real.log_le_log (by exact_mod_cast (show 0 < N - 1 by omega)) this
        linarith

/-! ### Jensen for `log`, by hand -/

/-- `∑ log x_i ≤ |s| · log(mean x)` for positive `x_i`. -/
theorem sum_log_le_card_mul_log_avg {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, Real.log (x i) ≤ s.card * Real.log ((∑ i ∈ s, x i) / s.card) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  set c := (∑ i ∈ s, x i) / s.card with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact div_pos (Finset.sum_pos hx hs) hc
  have hstep : ∀ i ∈ s, Real.log (x i) ≤ Real.log c + x i / c - 1 := by
    intro i hi
    have := Real.log_le_sub_one_of_pos (div_pos (hx i hi) hcpos)
    rw [Real.log_div (hx i hi).ne' hcpos.ne'] at this
    linarith
  calc ∑ i ∈ s, Real.log (x i)
      ≤ ∑ i ∈ s, (Real.log c + x i / c - 1) := Finset.sum_le_sum hstep
    _ = s.card * Real.log c + (∑ i ∈ s, x i) / c - s.card := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
          nsmul_eq_mul, nsmul_eq_mul, Finset.sum_div]
        ring
    _ = s.card * Real.log c := by
        have hsum : 0 < ∑ i ∈ s, x i := Finset.sum_pos hx hs
        have : (∑ i ∈ s, x i) / c = s.card := by
          rw [hcdef, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hsum.ne', mul_one]
        rw [this]; ring

/-! ### The progression mean of `ω` -/

/-- **The AP-mean of `ω`**: for `P ⊆ range X` nonempty and any shift `ρ ≥ 1`,
`∑_{n∈P} ω(n+ρ) ≤ |P| · log((X+ρ)(log(X+ρ)+1)/|P|) / log 2`. -/
theorem sum_omegaR_add_le {X : ℕ} (P : Finset ℕ) (hP : P ⊆ Finset.range X) (hne : P.Nonempty)
    {ρ : ℕ} (hρ : 1 ≤ ρ) :
    ∑ n ∈ P, omegaR (n + ρ)
      ≤ P.card * Real.log (((X + ρ : ℕ) : ℝ) * (Real.log ((X + ρ : ℕ) : ℝ) + 1) / P.card)
          / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  rw [le_div_iff₀ hlog2, Finset.sum_mul]
  have hd : ∀ n ∈ P, 0 < ((n + ρ).divisors.card : ℝ) := fun n _ => by
    exact_mod_cast Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 (by omega)⟩
  calc ∑ n ∈ P, omegaR (n + ρ) * Real.log 2
      ≤ ∑ n ∈ P, Real.log ((n + ρ).divisors.card : ℝ) :=
        Finset.sum_le_sum fun n _ => omegaR_mul_log_two_le (by omega)
    _ ≤ P.card * Real.log ((∑ n ∈ P, ((n + ρ).divisors.card : ℝ)) / P.card) :=
        sum_log_le_card_mul_log_avg P hne _ hd
    _ ≤ P.card * Real.log (((X + ρ : ℕ) : ℝ) * (Real.log ((X + ρ : ℕ) : ℝ) + 1) / P.card) := by
        gcongr
        · exact div_pos (Finset.sum_pos hd hne) hc
        · calc ∑ n ∈ P, ((n + ρ).divisors.card : ℝ)
              = ∑ m ∈ P.image (· + ρ), (m.divisors.card : ℝ) := by
                rw [Finset.sum_image (fun a _ b _ h => by omega)]
            _ ≤ ∑ m ∈ Finset.range (X + ρ), (m.divisors.card : ℝ) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => by positivity
                intro m hm
                obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
                have := Finset.mem_range.1 (hP hn)
                exact Finset.mem_range.2 (by omega)
            _ ≤ _ := sum_card_divisors_le (X + ρ)

/-! ### The far tail on the grid -/

/-- The far layers `j = J + i + 1` of one atom, on a sample point, are summable. -/
lemma summable_far (G : GridParams) {X n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀) (α : G.Atom) :
    Summable (fun i : ℕ => omegaR (n + shiftG G.B G.Q G.D₀ α (G.K + G.N + i + 1))
      / (4 : ℝ) ^ (G.K + G.N + i + 1)) := by
  obtain ⟨k, hk1, -⟩ := G.exists_mult_mul hn α
  have hsum : Summable
      (fun j : ℕ => omegaR (n + shiftG G.B G.Q G.D₀ α (j + 1)) / (4 : ℝ) ^ (j + 1)) := by
    refine (summable_dilatedTailB (b := 4) (by norm_num) (G.d α) k (G.d_pos α).ne').congr
      (fun j => ?_)
    rw [hk1]
    show omegaR (G.d α * (k + j + 1)) / (4 : ℝ) ^ (j + 1)
      = omegaR (offset G.B G.Q α + mult G.B G.Q G.D₀ α * k
          + shiftG G.B G.Q G.D₀ α (j + 1)) / (4 : ℝ) ^ (j + 1)
    rw [add_shiftG_eq G.B G.Q G.D₀ α (G.hD α) (by omega)]
    show omegaR (G.d α * (k + j + 1)) / (4 : ℝ) ^ (j + 1)
      = omegaR (G.d α * (k + (j + 1))) / (4 : ℝ) ^ (j + 1)
    rw [show k + j + 1 = k + (j + 1) by omega]
  refine ((summable_nat_add_iff (G.K + G.N)).2 hsum).congr (fun i => ?_)
  rw [show i + (G.K + G.N) + 1 = G.K + G.N + i + 1 by omega]

/-- The far-tail constant `C₀ = log((X+Dm)/|P|) + log(log(X+Dm)+1)`, where `Dm` bounds every
`d_α`.  Under §5 this is `O(log P₀ + L)`. -/
noncomputable def farC (G : GridParams) (X Dm : ℕ) : ℝ :=
  Real.log (((X + Dm : ℕ) : ℝ) / (apSample X G.P₀ G.b₀).card)
    + Real.log (Real.log ((X + Dm : ℕ) : ℝ) + 1)

/-- **The AP-mean of `ω` at layer `j`**: `∑_{n∈P} ω(n + ρ_{α,j}) ≤ |P| (C₀ + 2j)/log 2`. -/
theorem sum_omegaR_shiftG_le (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (α : G.Atom) {j : ℕ} (hj : 1 ≤ j) :
    ∑ n ∈ apSample X G.P₀ G.b₀, omegaR (n + shiftG G.B G.Q G.D₀ α j)
      ≤ (apSample X G.P₀ G.b₀).card * ((farC G X Dm + 2 * j) / Real.log 2) := by
  set P := apSample X G.P₀ G.b₀ with hP
  set ρ := shiftG G.B G.Q G.D₀ α j with hρ
  have hρ1 : 1 ≤ ρ := shiftG_pos G α hj
  have hρle : ρ ≤ j * Dm := by
    rw [hρ]; unfold shiftG
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_left j (hDm α))
  have hPsub : P ⊆ Finset.range X := Finset.filter_subset _ _
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := ((X + Dm : ℕ) : ℝ) with hA
  have hDm0 : (0 : ℝ) ≤ Dm := by positivity
  have hX1 : (1 : ℝ) ≤ X := by
    have h1 := hne.card_pos
    have h2 := Finset.card_le_card hPsub
    rw [Finset.card_range] at h2
    exact_mod_cast (show 1 ≤ X by omega)
  have hA1 : 1 ≤ A := by rw [hA]; push_cast; linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hjr : (0 : ℝ) ≤ j := by positivity
  have hlogj : Real.log ((j : ℝ) + 1) ≤ j := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < j + 1); linarith
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h1 : ((X + ρ : ℕ) : ℝ) ≤ A * (j + 1) := by
    rw [hA]; push_cast
    have : (ρ : ℝ) ≤ j * Dm := by exact_mod_cast hρle
    nlinarith
  have hXρpos : (0 : ℝ) < ((X + ρ : ℕ) : ℝ) := by positivity
  have hXρ1 : (1 : ℝ) ≤ ((X + ρ : ℕ) : ℝ) := by push_cast; linarith
  have h2 : Real.log ((X + ρ : ℕ) : ℝ) ≤ Real.log A + j := by
    calc Real.log ((X + ρ : ℕ) : ℝ) ≤ Real.log (A * (j + 1)) := Real.log_le_log hXρpos h1
      _ = Real.log A + Real.log ((j : ℝ) + 1) := Real.log_mul (by linarith) hj1.ne'
      _ ≤ Real.log A + j := by linarith
  have hlogXρ : 0 ≤ Real.log ((X + ρ : ℕ) : ℝ) := Real.log_nonneg hXρ1
  have h3 : Real.log ((X + ρ : ℕ) : ℝ) + 1 ≤ (Real.log A + 1) * (j + 1) := by nlinarith
  have hq : ((X + ρ : ℕ) : ℝ) * (Real.log ((X + ρ : ℕ) : ℝ) + 1) / P.card
      ≤ (A / P.card) * ((Real.log A + 1) * (((j : ℝ) + 1) * ((j : ℝ) + 1))) := by
    have := mul_le_mul h1 h3 (by linarith) (by positivity)
    calc ((X + ρ : ℕ) : ℝ) * (Real.log ((X + ρ : ℕ) : ℝ) + 1) / P.card
        ≤ (A * (j + 1)) * ((Real.log A + 1) * (j + 1)) / P.card :=
          div_le_div_of_nonneg_right this hc.le
      _ = _ := by ring
  have hqpos : 0 < ((X + ρ : ℕ) : ℝ) * (Real.log ((X + ρ : ℕ) : ℝ) + 1) / P.card := by
    positivity
  have hlogq : Real.log (((X + ρ : ℕ) : ℝ) * (Real.log ((X + ρ : ℕ) : ℝ) + 1) / P.card)
      ≤ farC G X Dm + 2 * j := by
    calc Real.log (((X + ρ : ℕ) : ℝ) * (Real.log ((X + ρ : ℕ) : ℝ) + 1) / P.card)
        ≤ Real.log ((A / P.card) * ((Real.log A + 1) * (((j : ℝ) + 1) * ((j : ℝ) + 1)))) :=
          Real.log_le_log hqpos hq
      _ = Real.log (A / P.card) + (Real.log (Real.log A + 1)
            + (Real.log ((j : ℝ) + 1) + Real.log ((j : ℝ) + 1))) := by
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity),
            Real.log_mul hj1.ne' hj1.ne']
      _ ≤ farC G X Dm + 2 * j := by
          unfold farC
          rw [← hA, ← hP]
          linarith
  have hmain := sum_omegaR_add_le P hPsub hne hρ1
  refine hmain.trans ?_
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlogq hlog2.le) hc.le

/-- The far bound series `(C + 2(J+i+1)) · 4^{−(J+i+1)}`, summed explicitly. -/
lemma hasSum_farBound (C : ℝ) (J : ℕ) :
    HasSum (fun i : ℕ => (C + 2 * ((J : ℝ) + i + 1)) * (1 / 4 : ℝ) ^ (J + i + 1))
      ((1 / 4 : ℝ) ^ J * ((C + 2 * J + 2) / 3 + 2 / 9)) := by
  have h1 := hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have h2 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := (1 / 4 : ℝ))
    (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)
  have h := ((h1.mul_left ((C + 2 * J + 2) * (1 / 4 : ℝ))).add
    (h2.mul_left (2 * (1 / 4 : ℝ)))).mul_left ((1 / 4 : ℝ) ^ J)
  have hfun : (fun i : ℕ => (C + 2 * ((J : ℝ) + i + 1)) * (1 / 4 : ℝ) ^ (J + i + 1))
      = fun i : ℕ => (1 / 4 : ℝ) ^ J * ((C + 2 * J + 2) * (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ i
          + 2 * (1 / 4 : ℝ) * ((i : ℝ) * (1 / 4 : ℝ) ^ i)) := by
    funext i; ring
  rw [hfun, show (1 / 4 : ℝ) ^ J * ((C + 2 * J + 2) / 3 + 2 / 9)
      = (1 / 4 : ℝ) ^ J * ((C + 2 * J + 2) * (1 / 4 : ℝ) * (1 - 1 / 4 : ℝ)⁻¹
          + 2 * (1 / 4 : ℝ) * ((1 / 4 : ℝ) / (1 - 1 / 4) ^ 2)) by norm_num; ring]
  exact h

/-- **The far tail of one row, summed over the sample.** -/
theorem sum_abs_farPart_le (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (a : Fin G.K → Fin G.s) :
    ∑ n ∈ apSample X G.P₀ G.b₀, |farPart G n a|
      ≤ (apSample X G.P₀ G.b₀).card * ((2 : ℝ) ^ G.K / Real.log 2
          * ((1 / 4 : ℝ) ^ (G.K + G.N) * ((farC G X Dm + 2 * (G.K + G.N : ℕ) + 2) / 3 + 2 / 9))) := by
  set P := apSample X G.P₀ G.b₀ with hP
  set J := G.K + G.N with hJ
  set C := farC G X Dm with hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set f : G.Atom → ℕ → ℕ → ℝ := fun α n i =>
    omegaR (n + shiftG G.B G.Q G.D₀ α (J + i + 1)) / (4 : ℝ) ^ (J + i + 1) with hf
  have hf0 : ∀ α n i, 0 ≤ f α n i := fun α n i => by
    simp only [hf]; exact div_nonneg (omegaR_nonneg _) (by positivity)
  have hfs : ∀ α, ∀ n ∈ P, Summable (f α n) := fun α n hn => summable_far G hn α
  -- pointwise: `|farPart n a| ≤ ∑_α |A_{aα}| ∑'_i f α n i`
  have hpt : ∀ n ∈ P, |farPart G n a|
      ≤ ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * ∑' i, f α n i := by
    intro n _
    unfold farPart
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    rw [abs_mul, abs_of_nonneg (tsum_nonneg fun i => hf0 α n i)]
  -- the layer bound
  have hlayer : ∀ α i, ∑ n ∈ P, f α n i
      ≤ P.card * ((C + 2 * ((J : ℝ) + i + 1)) * (1 / 4 : ℝ) ^ (J + i + 1)) / Real.log 2 := by
    intro α i
    simp only [hf]
    rw [← Finset.sum_div]
    have := sum_omegaR_shiftG_le G X hne hDm α (j := J + i + 1) (by omega)
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ (J + i + 1))]
    refine this.trans (le_of_eq ?_)
    rw [one_div_pow, ← hP, ← hC]
    field_simp
    push_cast
    ring
  have hbound := hasSum_farBound C J
  have hbound_sum : HasSum (fun i : ℕ => P.card * ((C + 2 * ((J : ℝ) + i + 1))
      * (1 / 4 : ℝ) ^ (J + i + 1)) / Real.log 2)
      (P.card * ((1 / 4 : ℝ) ^ J * ((C + 2 * J + 2) / 3 + 2 / 9)) / Real.log 2) := by
    have := (hbound.mul_left (P.card : ℝ)).div_const (Real.log 2)
    exact this
  calc ∑ n ∈ P, |farPart G n a|
      ≤ ∑ n ∈ P, ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * ∑' i, f α n i :=
        Finset.sum_le_sum hpt
    _ = ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * ∑' i, ∑ n ∈ P, f α n i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← Finset.mul_sum, Summable.tsum_finsetSum (hfs α)]
    _ ≤ ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)|
          * (P.card * ((1 / 4 : ℝ) ^ J * ((C + 2 * J + 2) / 3 + 2 / 9)) / Real.log 2) := by
        refine Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [← hbound_sum.tsum_eq]
        refine Summable.tsum_le_tsum (hlayer α) ?_ hbound_sum.summable
        exact summable_sum fun n hn => hfs α n hn
    _ = _ := by
        rw [← Finset.sum_mul, sum_abs_kronPow_diffZ]
        ring

lemma farC_nonneg (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (Dm : ℕ) :
    0 ≤ farC G X Dm := by
  unfold farC
  have hc : (0 : ℝ) < (apSample X G.P₀ G.b₀).card := by exact_mod_cast hne.card_pos
  have hcX : ((apSample X G.P₀ G.b₀).card : ℝ) ≤ ((X + Dm : ℕ) : ℝ) := by
    have := Finset.card_le_card (Finset.filter_subset _ _ : apSample X G.P₀ G.b₀ ⊆ Finset.range X)
    rw [Finset.card_range] at this
    exact_mod_cast this.trans (Nat.le_add_right X Dm)
  have h1 : 0 ≤ Real.log (((X + Dm : ℕ) : ℝ) / (apSample X G.P₀ G.b₀).card) :=
    Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith)
  have h2 : 0 ≤ Real.log ((X + Dm : ℕ) : ℝ) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ (apSample X G.P₀ G.b₀).card := by exact_mod_cast hne.card_pos
    linarith)
  have h3 : 0 ≤ Real.log (Real.log ((X + Dm : ℕ) : ℝ) + 1) := Real.log_nonneg (by linarith)
  linarith

/-- **`farAvg`, in closed form (brief §4D, the infinite far tail).**  With `Dm ≥ every d_α`
and `C₀ = farC G X Dm = log((X+Dm)/|P|) + log(log(X+Dm)+1)`,

  `farAvg ≤ 2^K · 4^{−J} · ((C₀ + 2J + 2)/3 + 2/9) / log 2`,   `J = K + N`.

Under §5 this is `O(2^K L^{−6} (L + log P₀))`, which is `o(η)`. -/
theorem farAvg_le (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) :
    farAvg G X ≤ (2 : ℝ) ^ G.K / Real.log 2
      * ((1 / 4 : ℝ) ^ (G.K + G.N) * ((farC G X Dm + 2 * (G.K + G.N : ℕ) + 2) / 3 + 2 / 9)) := by
  set P := apSample X G.P₀ G.b₀ with hP
  set Bd : ℝ := (2 : ℝ) ^ G.K / Real.log 2
      * ((1 / 4 : ℝ) ^ (G.K + G.N) * ((farC G X Dm + 2 * (G.K + G.N : ℕ) + 2) / 3 + 2 / 9))
    with hBd
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC := farC_nonneg G X hne Dm
  have hBd0 : 0 ≤ Bd := by
    rw [hBd]
    have h1 : 0 ≤ (2 : ℝ) ^ G.K / Real.log 2 := by positivity
    have h2 : 0 ≤ (1 / 4 : ℝ) ^ (G.K + G.N) := by positivity
    have h3 : 0 ≤ (farC G X Dm + 2 * (G.K + G.N : ℕ) + 2) / 3 + 2 / 9 := by positivity
    positivity
  have hrow : ∀ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P, |farPart G n (G.rowEquiv.symm ν)| ≤ Bd := by
    intro ν
    have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
    have := sum_abs_farPart_le G X hne hDm (G.rowEquiv.symm ν)
    rw [← hP] at this
    calc (P.card : ℝ)⁻¹ * ∑ n ∈ P, |farPart G n (G.rowEquiv.symm ν)|
        ≤ (P.card : ℝ)⁻¹ * (P.card * Bd) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = Bd := by field_simp
  unfold farAvg
  rw [← hP]
  have hswap : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |farPart G n (G.rowEquiv.symm ν)|
      = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
        |farPart G n (G.rowEquiv.symm ν)| := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hswap]
  have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
  rw [← hr]
  exact avg_le_of_forall_le _ _ hBd0 fun ν _ => hrow ν

/-! ### `PropD` from the two closed forms -/

/-- **`PropD` from the two closed-form remainder bounds.**  §4D is now reduced to two real
inequalities in the parameters alone: the medium/very-large bound `bigAvg_le'` and the far-tail
bound `farAvg_le`, each at most its share of `ε η`. -/
theorem gridFrame_propD_of_bounds (G : GridParams) (X R Y : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (hK : 0 < G.K) (hR : 2 ≤ R) (hRY : R ≤ Y)
    {Mx : ℝ} (hMx1 : 1 ≤ Mx)
    (hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
      ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) {δbig δfar : ℝ}
    (hbig : Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R))
            * ((1 / 8 : ℝ) ^ G.K / 15)
          + 2 * (Y : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ G.K / 3) ^ 2 / (apSample X G.P₀ G.b₀).card)
        + (Real.log Mx / Real.log Y) * (1 / 2 : ℝ) ^ G.K / 3 ≤ δbig * (ε * η))
    (hfar : (2 : ℝ) ^ G.K / Real.log 2
      * ((1 / 4 : ℝ) ^ (G.K + G.N) * ((farC G X Dm + 2 * (G.K + G.N : ℕ) + 2) / 3 + 2 / 9))
        ≤ δfar * (ε * η)) :
    (gridFrame G X hne (smallPrimes R G.P₀) (frozenGamma G) hη hε D).PropD (δbig + δfar) :=
  gridFrame_propD G X hne R hη hε D
    ((bigAvg_le' G X R Y hne hK hR hRY hMx1 hMx).trans hbig)
    ((farAvg_le G X hne hDm).trans hfar)

end NormalNumbers.G4
