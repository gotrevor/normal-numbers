/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4CRTInput

/-!
# G4 §4C assembled: uniform small-prime Fourier control, abstractly

`ee(q·S(n)) = ∏_{p ≤ R} ee(θ_p(n))` with `θ_p(n)` depending only on `n mod p`, equal to a phase
`x_{p,b}` when `n ≡ b` for one of the `k_p ≤ p/2` active roots `b`, and `0` otherwise.  This
file assembles C1–C3 into one theorem about such products, with every constant explicit:

* `LocalPhase p` — the local data: active roots `⊆ range p`, phases, `2k ≤ p`.
* `resMean_ee_theta` — `μ_p = p⁻¹((p−k) + ∑_{roots} ee x_b)`, so C2 applies;
  `norm_resMean_ee_theta_sub_one_le` — `‖μ_p − 1‖ ≤ 2k/p`;
  `resMean_indicator` — the active indicator has mean `k/p`.
* `crt_input_two` — `crt_input` for functions bounded by `2` (the fluctuations `ee θ − 1`).
* **`norm_sampleAvg_prod_ee_le`** — the assembled bound

      ‖avg_n ∏_{p∈s} ee(θ_p n)‖ ≤ exp(−∑_p 4θ_p/p) + N_M·ε + λ'^{−M}∏(1+2λ'k_p/p)
                                  + 2(2e/λ)^M ∏(1+e^λ k_p/p) + 2(2e/M)^M|s|^M ε'

  with `ε = 2^{M+1}R^M/|P|`, `ε' = 2R^M/|P|`, for any `θ_p ≤ ∑_{roots} dist(x_{p,b},ℤ)²`.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### `crt_input` for functions bounded by two -/

/-- `crt_input` with `‖h_i‖ ≤ 2`: the error picks up `2^{|T|}`. -/
theorem crt_input_two {ι : Type*} [DecidableEq ι] (X P₀ a : ℕ) (hP₀ : 0 < P₀) (ha : a < P₀)
    (hne : (apSample X P₀ a).Nonempty)
    (T : Finset ι) (p : ι → ℕ) (hp : ∀ i ∈ T, 0 < p i)
    (hcop : (T : Set ι).Pairwise (fun i j => (p i).Coprime (p j)))
    (hcopP : ∀ i ∈ T, (p i).Coprime P₀)
    (h : ι → ℕ → ℂ) (hper : ∀ i ∈ T, PeriodicMod (h i) (p i))
    (hb : ∀ i ∈ T, ∀ n, ‖h i n‖ ≤ 2) :
    ‖sampleAvg (apSample X P₀ a) id (fun n => ∏ i ∈ T, h i n) - ∏ i ∈ T, resMean (h i) (p i)‖
      ≤ 2 ^ T.card * (2 * (∏ i ∈ T, (p i : ℝ)) / (apSample X P₀ a).card) := by
  have hper' : ∀ i ∈ T, PeriodicMod (fun n => h i n / 2) (p i) := fun i hi n => by
    simp only; rw [hper i hi n]
  have hb' : ∀ i ∈ T, ∀ n, ‖h i n / 2‖ ≤ 1 := fun i hi n => by
    rw [norm_div, Complex.norm_ofNat]; linarith [hb i hi n]
  have key := crt_input X P₀ a hP₀ ha hne T p hp hcop hcopP (fun i n => h i n / 2) hper' hb'
  have hsplit : ∀ n, ∏ i ∈ T, h i n = (2 : ℂ) ^ T.card * ∏ i ∈ T, (h i n / 2) := fun n => by
    rw [Finset.prod_div_distrib, Finset.prod_const]
    field_simp
  have hmean : ∀ i, resMean (h i) (p i) = 2 * resMean (fun n => h i n / 2) (p i) := fun i => by
    unfold resMean
    simp only
    rw [← Finset.sum_div, mul_div_assoc']
    field_simp
  have hL : sampleAvg (apSample X P₀ a) id (fun n => ∏ i ∈ T, h i n)
      = (2 : ℂ) ^ T.card * sampleAvg (apSample X P₀ a) id (fun n => ∏ i ∈ T, (h i n / 2)) := by
    unfold sampleAvg
    simp only [id_eq]
    rw [Finset.smul_sum, Finset.smul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hsplit n, mul_smul_comm]
  have hR : ∏ i ∈ T, resMean (h i) (p i)
      = (2 : ℂ) ^ T.card * ∏ i ∈ T, resMean (fun n => h i n / 2) (p i) := by
    rw [Finset.prod_congr rfl fun i _ => hmean i, Finset.prod_mul_distrib, Finset.prod_const]
  rw [hL, hR, ← mul_sub, norm_mul, norm_pow, Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left key (by positivity)

/-! ### Local phase data -/

/-- Local data at the prime `p`: the active residues, their phases, and the good-prime condition
`2k ≤ p` (a default class of probability at least one half). -/
structure LocalPhase (p : ℕ) where
  /-- the active residues -/
  roots : Finset ℕ
  hroots : roots ⊆ range p
  /-- the phase at an active residue -/
  x : ℕ → ℝ
  hk : 2 * roots.card ≤ p

namespace LocalPhase

variable {p : ℕ} (L : LocalPhase p)

/-- The local phase `θ_p(n)`. -/
noncomputable def θ (n : ℕ) : ℝ := if n % p ∈ L.roots then L.x (n % p) else 0

/-- `n` is active at `p`. -/
abbrev Active (n : ℕ) : Prop := n % p ∈ L.roots

lemma θ_eq_zero_of_not_active {n : ℕ} (h : ¬ L.Active n) : L.θ n = 0 := by
  unfold Active at h; unfold θ; rw [if_neg h]

lemma periodicMod_ee_theta (hp : 0 < p) : PeriodicMod (fun n => ee (L.θ n)) p := by
  intro n
  simp only [θ, Nat.mod_mod_of_dvd n (dvd_refl p), Nat.mod_mod]

lemma periodicMod_indicator (hp : 0 < p) :
    PeriodicMod (fun n => if L.Active n then (1 : ℂ) else 0) p := by
  intro n
  simp only [Active, Nat.mod_mod]

@[simp] lemma ee_zero : ee 0 = 1 := by
  simp [ee]

lemma ee_theta_eq_one_of_not_active {n : ℕ} (h : ¬ L.Active n) : ee (L.θ n) = 1 := by
  rw [L.θ_eq_zero_of_not_active h, ee_zero]

/-- The residue mean of `ee ∘ θ` is the local character average of C2. -/
lemma resMean_ee_theta (hp : 0 < p) :
    resMean (fun n => ee (L.θ n)) p
      = (p : ℂ)⁻¹ * (((p - L.roots.card : ℕ) : ℂ) + ∑ b ∈ L.roots, ee (L.x b)) := by
  unfold resMean
  congr 1
  have h1 : (range p).filter (fun b => b ∈ L.roots) = L.roots := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.1 (L.hroots h), h⟩⟩
  have hsplit : ∑ b ∈ range p, ee (L.θ b)
      = ∑ b ∈ (range p).filter (fun b => b ∈ L.roots), ee (L.θ b)
        + ∑ b ∈ (range p).filter (fun b => ¬ b ∈ L.roots), ee (L.θ b) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hcard : ((range p).filter (fun b => ¬ b ∈ L.roots)).card = p - L.roots.card := by
    rw [Finset.filter_not, h1, Finset.card_sdiff_of_subset L.hroots, Finset.card_range]
  have h2 : ∑ b ∈ (range p).filter (fun b => ¬ b ∈ L.roots), ee (L.θ b)
      = ((p - L.roots.card : ℕ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun b hb => L.ee_theta_eq_one_of_not_active ?_), Finset.sum_const,
      nsmul_eq_mul, mul_one, hcard]
    have hb' := Finset.mem_filter.1 hb
    unfold Active
    rw [Nat.mod_eq_of_lt (Finset.mem_range.1 hb'.1)]
    exact hb'.2
  rw [hsplit, h1, h2, add_comm]
  refine congrArg _ (Finset.sum_congr rfl fun b hb => ?_)
  simp only [θ]
  rw [Nat.mod_eq_of_lt (Finset.mem_range.1 (L.hroots hb)), if_pos hb]

/-- **C2 for the residue mean**: `‖μ_p‖ ≤ 1 − 4θ/p` whenever `θ ≤ ∑_{roots} dist(x_b,ℤ)²`. -/
lemma norm_resMean_ee_theta_le (hp : 0 < p) {θ₀ : ℝ}
    (hθ : θ₀ ≤ ∑ b ∈ L.roots, distZ (L.x b) ^ 2) :
    ‖resMean (fun n => ee (L.θ n)) p‖ ≤ 1 - 4 * θ₀ / p := by
  rw [L.resMean_ee_theta hp]
  have h := norm_localAvg_le_of_sum_sq (ι := {b // b ∈ L.roots}) hp
    (by rw [Fintype.card_coe]; exact L.hk)
    (fun b => L.x b) (θ := θ₀)
    (by rw [Finset.sum_coe_sort L.roots (fun b => distZ (L.x b) ^ 2)]; exact hθ)
  rwa [Fintype.card_coe, Finset.sum_coe_sort L.roots (fun b => ee (L.x b))] at h

/-- `‖μ_p − 1‖ ≤ 2k/p`. -/
lemma norm_resMean_ee_theta_sub_one_le (hp : 0 < p) :
    ‖resMean (fun n => ee (L.θ n)) p - 1‖ ≤ 2 * L.roots.card / p := by
  rw [L.resMean_ee_theta hp]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hkp : L.roots.card ≤ p := by linarith [L.hk]
  have hid : (p : ℂ)⁻¹ * (((p - L.roots.card : ℕ) : ℂ) + ∑ b ∈ L.roots, ee (L.x b)) - 1
      = (p : ℂ)⁻¹ * ∑ b ∈ L.roots, (ee (L.x b) - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_sub hkp]
    field_simp
    ring
  rw [hid, norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hpr.le)
  calc ‖∑ b ∈ L.roots, (ee (L.x b) - 1)‖ ≤ ∑ b ∈ L.roots, ‖ee (L.x b) - 1‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ L.roots, (2 : ℝ) := by
        refine Finset.sum_le_sum fun b _ => ?_
        calc ‖ee (L.x b) - 1‖ ≤ ‖ee (L.x b)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_ee, norm_one]; norm_num
    _ = 2 * L.roots.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The active indicator has residue mean `k/p`. -/
lemma resMean_indicator (hp : 0 < p) :
    resMean (fun n => if L.Active n then (1 : ℂ) else 0) p = (L.roots.card : ℂ) / p := by
  unfold resMean
  have : ∑ b ∈ range p, (if L.Active b then (1 : ℂ) else 0)
      = ∑ b ∈ range p, (if b ∈ L.roots then (1 : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun b hb => ?_
    unfold Active
    rw [Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
  rw [this, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 L.hroots]
  ring

end LocalPhase

/-! ### The assembly -/

/-- **§4C assembled.**  For a set `s` of good primes (each with local phase data, each coprime
to the progression modulus `P₀`, each `≤ R`) and lower bounds `θ_p ≤ ∑_{roots} dist(x_{p,b},ℤ)²`,
the sample average of `∏_p ee(θ_p(n))` over `{n < X : n ≡ a (P₀)}` is at most the
independent-model contraction `exp(−∑_p 4θ_p/p)` plus four explicit errors: two CRT errors of size
`R^M/|sample|` and two model tails `exp(−Θ(M))`. -/
theorem norm_sampleAvg_prod_ee_le (X P₀ a : ℕ) (hP₀ : 0 < P₀) (ha : a < P₀)
    (hne : (apSample X P₀ a).Nonempty)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hsP : ∀ p ∈ s, p.Coprime P₀)
    {R : ℕ} (hR1 : 1 ≤ R) (hR : ∀ p ∈ s, p ≤ R)
    (L : ∀ p, LocalPhase p) (θ : ℕ → ℝ) (hθ0 : ∀ p ∈ s, 0 ≤ θ p)
    (hθ : ∀ p ∈ s, θ p ≤ ∑ b ∈ (L p).roots, distZ ((L p).x b) ^ 2)
    {M : ℕ} (hM : 1 ≤ M) {lam' lam : ℝ} (hlam' : 1 ≤ lam') (hlam : 0 < lam) :
    ‖sampleAvg (apSample X P₀ a) id (fun n => ∏ p ∈ s, ee ((L p).θ n))‖
      ≤ Real.exp (-∑ p ∈ s, 4 * θ p / p)
        + ((s.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ M)).card
            * (2 ^ M * (2 * (R : ℝ) ^ M / (apSample X P₀ a).card))
          + (∏ p ∈ s, (1 + lam' * (2 * (L p).roots.card / p))) / lam' ^ M
          + 2 * (2 * Real.exp 1 / lam) ^ M
              * ∏ p ∈ s, (1 + Real.exp lam * ((L p).roots.card / p))
          + 2 * (2 * Real.exp 1 / M) ^ M * (s.card : ℝ) ^ M
              * (2 * (R : ℝ) ^ M / (apSample X P₀ a).card)) := by
  classical
  set P := apSample X P₀ a with hPdef
  have hPc : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.2 hne
  have hpos : ∀ p ∈ s, 0 < p := fun p hp => (hs p hp).pos
  have hcop : (s : Set ℕ).Pairwise (fun i j => i.Coprime j) := fun i hi j hj hij =>
    (Nat.coprime_primes (hs i hi) (hs j hj)).2 hij
  -- the objects of the skeleton
  set g : ℕ → ℕ → ℂ := fun p n => ee ((L p).θ n) with hg
  set Act : ℕ → Finset ℕ := fun n => s.filter (fun p => (L p).Active n) with hAct
  set μ : ℕ → ℂ := fun p => resMean (fun n => ee ((L p).θ n)) p with hμ
  set c : ℕ → ℝ := fun p => 2 * (L p).roots.card / p with hc
  set π : ℕ → ℝ := fun p => (L p).roots.card / p with hπ
  set ε : ℝ := 2 ^ M * (2 * (R : ℝ) ^ M / P.card) with hε
  set ε' : ℝ := 2 * (R : ℝ) ^ M / P.card with hε'
  have hε0 : 0 ≤ ε := by positivity
  have hε'0 : 0 ≤ ε' := by positivity
  -- `∏_{p∈T} p ≤ R^M` for `T ⊆ s`, `|T| ≤ M`
  have hprodR : ∀ T ∈ s.powerset, T.card ≤ M → (∏ p ∈ T, (p : ℝ)) ≤ (R : ℝ) ^ M := by
    intro T hT hTM
    have hTs : T ⊆ s := Finset.mem_powerset.1 hT
    have hR1' : (1 : ℝ) ≤ R := by exact_mod_cast hR1
    calc (∏ p ∈ T, (p : ℝ)) ≤ ∏ _p ∈ T, (R : ℝ) :=
          Finset.prod_le_prod (fun p _ => Nat.cast_nonneg _)
            (fun p hp => by exact_mod_cast hR p (hTs hp))
      _ = (R : ℝ) ^ T.card := Finset.prod_const _
      _ ≤ (R : ℝ) ^ M := pow_le_pow_right₀ hR1' hTM
  have hpC : ∀ p ∈ s, (p : ℂ) ≠ 0 := fun p hp => by exact_mod_cast (hpos p hp).ne'
  -- (i) the fluctuation input, from `crt_input_two`
  have hsmall : ∀ T ∈ s.powerset, T.Nonempty → T.card ≤ M →
      ‖sampleAvg P id (fun n => ∏ p ∈ T, (g p n - 1)) - ∏ p ∈ T, (μ p - 1)‖ ≤ ε := by
    intro T hT _ hTM
    have hTs : T ⊆ s := Finset.mem_powerset.1 hT
    have key := crt_input_two X P₀ a hP₀ ha hne T (fun p => p) (fun p hp => hpos p (hTs hp))
      (hcop.mono (Finset.coe_subset.2 hTs)) (fun p hp => hsP p (hTs hp)) (fun p n => g p n - 1)
      (fun p hp n => by
        simp only [hg]
        have := (L p).periodicMod_ee_theta (hpos p (hTs hp)) n
        simp only at this
        rw [this])
      (fun p _ n => by
        simp only [hg]
        calc ‖ee ((L p).θ n) - 1‖ ≤ ‖ee ((L p).θ n)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_ee, norm_one]; norm_num)
    have hmean : ∀ p ∈ T, resMean (fun n => g p n - 1) p = μ p - 1 := fun p hp => by
      simp only [resMean, hg, hμ]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
        mul_sub, inv_mul_cancel₀ (hpC p (hTs hp))]
    rw [Finset.prod_congr rfl hmean] at key
    refine key.trans ?_
    rw [hε]
    have h2 : (2 : ℝ) ^ T.card ≤ 2 ^ M := pow_le_pow_right₀ one_le_two hTM
    have h3 := hprodR T hT hTM
    have h4 : (0 : ℝ) ≤ 2 * ∏ p ∈ T, (p : ℝ) / P.card := by positivity
    calc (2 : ℝ) ^ T.card * (2 * (∏ p ∈ T, (p : ℝ)) / P.card)
        ≤ 2 ^ M * (2 * (∏ p ∈ T, (p : ℝ)) / P.card) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ 2 ^ M * (2 * (R : ℝ) ^ M / P.card) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right (by linarith) hPc.le
  -- (ii) the indicator input, from `crt_input`
  have hcrt : ∀ D ∈ s.powerset, D.Nonempty → D.card ≤ M →
      sampleAvg P id (fun n => if D ⊆ Act n then (1 : ℝ) else 0) ≤ ∏ p ∈ D, π p + ε' := by
    intro D hD _ hDM
    have hDs : D ⊆ s := Finset.mem_powerset.1 hD
    have key := crt_input X P₀ a hP₀ ha hne D (fun p => p) (fun p hp => hpos p (hDs hp))
      (hcop.mono (Finset.coe_subset.2 hDs)) (fun p hp => hsP p (hDs hp))
      (fun p n => if (L p).Active n then (1 : ℂ) else 0)
      (fun p hp => (L p).periodicMod_indicator (hpos p (hDs hp)))
      (fun p _ n => by split_ifs <;> simp)
    have hprod : ∀ n, ∏ p ∈ D, (if (L p).Active n then (1 : ℂ) else 0)
        = if D ⊆ Act n then 1 else 0 := fun n => by
      rw [Finset.prod_boole]
      congr 1
      apply propext
      constructor
      · intro h q hq; exact Finset.mem_filter.2 ⟨hDs hq, h q hq⟩
      · intro h q hq; exact (Finset.mem_filter.1 (h hq)).2
    have hmeans : ∏ p ∈ D, resMean (fun n => if (L p).Active n then (1 : ℂ) else 0) p
        = ((∏ p ∈ D, π p : ℝ) : ℂ) := by
      rw [Finset.prod_congr rfl (fun p hp => (L p).resMean_indicator (hpos p (hDs hp)))]
      simp only [hπ]
      push_cast
      rfl
    have hcast : sampleAvg P id (fun n => if D ⊆ Act n then (1 : ℂ) else 0)
        = ((sampleAvg P id (fun n => if D ⊆ Act n then (1 : ℝ) else 0) : ℝ) : ℂ) := by
      simp only [sampleAvg, id_eq, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul,
        Complex.ofReal_sum, Complex.ofReal_inv, Complex.ofReal_natCast]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> simp
    simp only [hprod] at key
    rw [hmeans, hcast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at key
    have := (le_abs_self _).trans key
    have hbound : 2 * (∏ p ∈ D, (p : ℝ)) / P.card ≤ ε' := by
      rw [hε']
      exact div_le_div_of_nonneg_right (by linarith [hprodR D hD hDM]) hPc.le
    linarith
  -- the per-prime facts
  have hAct : ∀ n, Act n ⊆ s := fun n => Finset.filter_subset _ _
  have hg1 : ∀ p ∈ s, ∀ n, ‖g p n‖ ≤ 1 := fun p _ n => by simp [hg]
  have hgoff : ∀ p ∈ s, ∀ n, p ∉ Act n → g p n = 1 := fun p hp n hpn => by
    simp only [hg]
    refine (L p).ee_theta_eq_one_of_not_active fun hA => hpn ?_
    exact Finset.mem_filter.2 ⟨hp, hA⟩
  have hc0 : ∀ p ∈ s, 0 ≤ c p := fun p _ => by simp only [hc]; positivity
  have hμc : ∀ p ∈ s, ‖μ p - 1‖ ≤ c p := fun p hp =>
    (L p).norm_resMean_ee_theta_sub_one_le (hpos p hp)
  have hπ0 : ∀ p ∈ s, 0 ≤ π p := fun p _ => by simp only [hπ]; positivity
  have skel := norm_sampleAvg_prod_sub_prod_le' P hne s g Act hAct hg1 hgoff μ c hc0 hμc π hπ0
    hM hlam' hlam hε0 hε'0 hsmall hcrt
  -- the independent-model contraction
  have hmain : ‖∏ p ∈ s, μ p‖ ≤ Real.exp (-∑ p ∈ s, 4 * θ p / p) := by
    rw [norm_prod]
    have hμle : ∀ p ∈ s, ‖μ p‖ ≤ 1 - 4 * θ p / p := fun p hp =>
      (L p).norm_resMean_ee_theta_le (hpos p hp) (hθ p hp)
    calc ∏ p ∈ s, ‖μ p‖ ≤ ∏ p ∈ s, (1 - 4 * θ p / p) :=
          Finset.prod_le_prod (fun p _ => norm_nonneg _) hμle
      _ ≤ Real.exp (-∑ p ∈ s, 4 * θ p / p) := by
          refine prod_one_sub_le_exp_neg_sum s _ (fun p hp => ?_) (fun p hp => ?_)
          · have : (0 : ℝ) < p := by exact_mod_cast hpos p hp
            have := hθ0 p hp
            positivity
          · linarith [hμle p hp, norm_nonneg (μ p)]
  have hfun : (fun n => ∏ p ∈ s, ee ((L p).θ n)) = fun n => ∏ p ∈ s, g p n := rfl
  rw [hfun]
  have htri : ‖sampleAvg P id (fun n => ∏ p ∈ s, g p n)‖
      ≤ ‖∏ p ∈ s, μ p‖ + ‖sampleAvg P id (fun n => ∏ p ∈ s, g p n) - ∏ p ∈ s, μ p‖ := by
    have := norm_add_le (∏ p ∈ s, μ p) (sampleAvg P id (fun n => ∏ p ∈ s, g p n) - ∏ p ∈ s, μ p)
    rwa [add_sub_cancel] at this
  simp only [hc, hπ] at skel
  linarith [htri, skel, hmain]

end NormalNumbers.G4
