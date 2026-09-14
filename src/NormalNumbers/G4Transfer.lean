/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4LocalContraction
import NormalNumbers.G4SeparatingTest

/-!
# G4 §4C, C3: the transfer skeleton from the independent model to the sample

The brief's warning is explicit:

> The transfer from the independent residue model to the actual progression is not automatic
> independence.  Expand moments to even degree `M`, count residue classes by CRT, and sum the
> finite-sample errors, bounded schematically by `P R^(2m)/X` for `m ≤ M`.

This file proves the **skeleton** of that argument in full, unconditionally, and thereby
reduces C3 to exactly two named inputs.  Write `f p n = g p n - μ p` for the fluctuation of the
local factor `g p` about its independent-model mean `μ p`.

* `prod_sub_expansion` — `∏_{p ∈ s} g p n = ∑_{T ⊆ s} (∏_{p∈T} f p n)(∏_{p ∈ s∖T} μ p)`
  (`Finset.prod_add`).  The `T = ∅` term is the model value `∏ μ p`.
* `mul_pow_sum_powerset_card_gt_le` — the **Chernoff subset tail**: for `1 ≤ lam` and
  nonnegative `c`,  `lam^M · ∑_{|T| > M} ∏_{p∈T} c p ≤ ∏_{p∈s}(1 + lam · c p)`.
  This is what makes the `2^{|s|}` subsets summable: the tail is paid for by a single
  exponential moment, not termwise.
* **`norm_sampleAvg_prod_sub_prod_le`** — the skeleton:

      ‖avg_n ∏_{p∈s} g p n  −  ∏_{p∈s} μ p‖  ≤  N_M · ε  +  B / lam^M

  where `N_M` counts the nonempty subsets of size `≤ M`, given
  (i)  `‖avg_n ∏_{p∈T} f p n‖ ≤ ε` for every nonempty `T ⊆ s` with `|T| ≤ M`  — **C3a**, the
       CRT/equidistribution input: `∏_{p∈T} p ≤ R^M` is below the sample length, so this is
       elementary counting, with `ε` of size `P R^M / X`;
  (ii) `avg_n ∏_{p∈s}(1 + lam‖f p n‖) ≤ B`  — **C3core**, the exponential-moment input.

  `N_M ≤ (|s|+1)^M`, so the first term is the brief's `P R^{2m}/X`: `(|s|+1)^M ≤ R^M` times
  `P R^M / X`.

**What is still open is only (ii)**, and only (ii).  In the G4 application `f p n` is tiny
(`O(k/p)`) unless `n` lies in one of the `k = H(J−K)` active residue classes mod `p`, so
`∏_p(1 + lam‖f p n‖) ≤ (1+2lam)^{V(n)}·exp(2 lam k ∑_p p⁻¹)` with `V(n)` the number of active
primes; `𝔼 V ≍ k L`, and the brief's `M ≍ C k L` is exactly calibrated to beat it.  Bounding
`𝔼 (1+2lam)^{V(n)}` over the progression is a Shiu-type exponential moment for `ω` — a proven,
project-scale theorem, **not** an open conjecture.  That is the honest status of C3: a named
analytic prerequisite, not a gap in the argument's logic.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

section Transfer

variable {ι : Type*} [DecidableEq ι]

/-- Subset expansion of a product of `mean + fluctuation`. -/
lemma prod_sub_expansion (s : Finset ι) (g μ : ι → ℂ) :
    ∏ p ∈ s, g p = ∑ T ∈ s.powerset, (∏ p ∈ T, (g p - μ p)) * ∏ p ∈ s \ T, μ p := by
  have h : ∀ p, g p = (g p - μ p) + μ p := fun p => by ring
  calc ∏ p ∈ s, g p = ∏ p ∈ s, ((g p - μ p) + μ p) := by
        exact Finset.prod_congr rfl fun p _ => h p
    _ = _ := Finset.prod_add _ _ _

/-- **The Chernoff subset tail.**  For `lam ≥ 1` and nonnegative weights, the subsets of size
greater than `M` contribute at most `lam^{-M} ∏ (1 + lam c)`. -/
lemma mul_pow_sum_powerset_card_gt_le {s : Finset ι} (c : ι → ℝ) (hc : ∀ p ∈ s, 0 ≤ c p)
    (M : ℕ) {lam : ℝ} (hlam : 1 ≤ lam) :
    lam ^ M * ∑ T ∈ s.powerset.filter (fun T => M < T.card), ∏ p ∈ T, c p
      ≤ ∏ p ∈ s, (1 + lam * c p) := by
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  have hnn : ∀ T ∈ s.powerset, (0 : ℝ) ≤ ∏ p ∈ T, (lam * c p) := by
    intro T hT
    exact Finset.prod_nonneg fun p hp =>
      mul_nonneg hlam0 (hc p (Finset.mem_powerset.1 hT hp))
  calc lam ^ M * ∑ T ∈ s.powerset.filter (fun T => M < T.card), ∏ p ∈ T, c p
      = ∑ T ∈ s.powerset.filter (fun T => M < T.card), lam ^ M * ∏ p ∈ T, c p := by
        rw [Finset.mul_sum]
    _ ≤ ∑ T ∈ s.powerset.filter (fun T => M < T.card), ∏ p ∈ T, (lam * c p) := by
        refine Finset.sum_le_sum fun T hT => ?_
        have hTs : T ⊆ s := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
        have hcard : M ≤ T.card := le_of_lt (Finset.mem_filter.1 hT).2
        have hprod : ∏ p ∈ T, (lam * c p) = lam ^ T.card * ∏ p ∈ T, c p := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
        rw [hprod]
        refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlam hcard) ?_
        exact Finset.prod_nonneg fun p hp => hc p (hTs hp)
    _ ≤ ∑ T ∈ s.powerset, ∏ p ∈ T, (lam * c p) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun T hT _ => hnn T hT)
    _ = ∏ p ∈ s, (lam * c p + 1) := by
        rw [Finset.prod_add (fun p => lam * c p) (fun _ => (1 : ℝ)) s]
        exact Finset.sum_congr rfl fun T _ => by rw [Finset.prod_const_one, mul_one]
    _ = ∏ p ∈ s, (1 + lam * c p) := by
        exact Finset.prod_congr rfl fun p _ => by ring

/-! ### Sample averages -/

lemma sampleAvg_id_sum {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Finset ℕ)
    {κ : Type*} (𝒯 : Finset κ) (F : κ → ℕ → E) :
    sampleAvg P id (fun n => ∑ T ∈ 𝒯, F T n) = ∑ T ∈ 𝒯, sampleAvg P id (F T) := by
  unfold sampleAvg
  simp only [id_eq]
  rw [Finset.sum_comm, Finset.smul_sum]

lemma sampleAvg_id_const_mul (P : Finset ℕ) (c : ℂ) (h : ℕ → ℂ) :
    sampleAvg P id (fun n => h n * c) = sampleAvg P id h * c := by
  unfold sampleAvg
  simp only [id_eq, ← Finset.sum_mul, smul_mul_assoc]

lemma norm_sampleAvg_id_le_avg_norm (P : Finset ℕ) (h : ℕ → ℂ) :
    ‖sampleAvg P id h‖ ≤ sampleAvg P id (fun n => ‖h n‖) := by
  have hnn : (0 : ℝ) ≤ ((P.card : ℝ))⁻¹ := by positivity
  unfold sampleAvg
  simp only [id_eq]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hnn

lemma sampleAvg_id_mono (P : Finset ℕ) {u v : ℕ → ℝ} (h : ∀ n ∈ P, u n ≤ v n) :
    sampleAvg P id u ≤ sampleAvg P id v := by
  unfold sampleAvg
  simp only [id_eq, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (inv_nonneg.2 (Nat.cast_nonneg P.card))

lemma sampleAvg_id_const_smul (P : Finset ℕ) (c : ℝ) (u : ℕ → ℝ) :
    sampleAvg P id (fun n => c * u n) = c * sampleAvg P id u := by
  unfold sampleAvg
  simp only [id_eq, smul_eq_mul, ← Finset.mul_sum]
  ring

/-! ### The skeleton -/

/-- **The C3 skeleton.**  With `ε` controlling every CRT-reachable subset (size `≤ M`) and `B`
an exponential moment of the fluctuations, the sample average of the product is within
`N_M ε + B/lam^M` of the independent-model product. -/
theorem norm_sampleAvg_prod_sub_prod_le (P : Finset ℕ) (hP : P.Nonempty) (s : Finset ι)
    (g : ι → ℕ → ℂ) (μ : ι → ℂ) (hμ : ∀ p ∈ s, ‖μ p‖ ≤ 1)
    (M : ℕ) {lam ε B : ℝ} (hlam : 1 ≤ lam) (hε : 0 ≤ ε)
    (hsmall : ∀ T ∈ s.powerset, T.Nonempty → T.card ≤ M →
        ‖sampleAvg P id (fun n => ∏ p ∈ T, (g p n - μ p))‖ ≤ ε)
    (hbig : sampleAvg P id (fun n => ∏ p ∈ s, (1 + lam * ‖g p n - μ p‖)) ≤ B) :
    ‖sampleAvg P id (fun n => ∏ p ∈ s, g p n) - ∏ p ∈ s, μ p‖
      ≤ (s.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ M)).card * ε + B / lam ^ M := by
  classical
  have hlamM : (0 : ℝ) < lam ^ M := by positivity
  have hcard : (P.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hP.choose_spec)
  set A : Finset ι → ℂ :=
    fun T => sampleAvg P id (fun n => ∏ p ∈ T, (g p n - μ p)) * ∏ p ∈ s \ T, μ p with hA
  -- the average of the product expands over subsets
  have hexp : sampleAvg P id (fun n => ∏ p ∈ s, g p n) = ∑ T ∈ s.powerset, A T := by
    have h1 : (fun n => ∏ p ∈ s, g p n)
        = fun n => ∑ T ∈ s.powerset, (∏ p ∈ T, (g p n - μ p)) * ∏ p ∈ s \ T, μ p := by
      funext n; exact prod_sub_expansion s (fun p => g p n) μ
    rw [h1, sampleAvg_id_sum]
    exact Finset.sum_congr rfl fun T _ => sampleAvg_id_const_mul P _ _
  -- the empty subset is the independent-model value
  have hempty : A ∅ = ∏ p ∈ s, μ p := by
    have : sampleAvg P id (fun _ : ℕ => (1 : ℂ)) = 1 := by
      unfold sampleAvg
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Complex.real_smul,
        Complex.ofReal_inv, Complex.ofReal_natCast]
      exact inv_mul_cancel₀ (by exact_mod_cast hcard)
    simp [hA, this]
  -- the norm of a `μ`-cofactor is at most one
  have hcof : ∀ T : Finset ι, T ⊆ s → ‖∏ p ∈ s \ T, μ p‖ ≤ 1 := by
    intro T _
    rw [norm_prod]
    exact Finset.prod_le_one (fun p _ => norm_nonneg _)
      (fun p hp => hμ p (Finset.mem_sdiff.1 hp).1)
  -- pointwise Chernoff bound on the large subsets
  have hchern : ∀ n : ℕ,
      ∑ T ∈ s.powerset.filter (fun T => M < T.card), ∏ p ∈ T, ‖g p n - μ p‖
        ≤ (∏ p ∈ s, (1 + lam * ‖g p n - μ p‖)) / lam ^ M := by
    intro n
    rw [le_div_iff₀ hlamM, mul_comm]
    exact mul_pow_sum_powerset_card_gt_le (fun p => ‖g p n - μ p‖)
      (fun p _ => norm_nonneg _) M hlam
  -- split the nonempty subsets
  set E : Finset (Finset ι) := s.powerset.erase ∅ with hE
  have hsplit : ∑ T ∈ s.powerset, A T = A ∅ + ∑ T ∈ E, A T :=
    (Finset.add_sum_erase _ _ (Finset.empty_mem_powerset s)).symm
  rw [hexp, hsplit, hempty, add_sub_cancel_left,
    ← Finset.sum_filter_add_sum_filter_not E (fun T => T.card ≤ M)]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- CRT-reachable subsets
    calc ‖∑ T ∈ E.filter (fun T => T.card ≤ M), A T‖
        ≤ ∑ T ∈ E.filter (fun T => T.card ≤ M), ‖A T‖ := norm_sum_le _ _
      _ ≤ ∑ _T ∈ E.filter (fun T => T.card ≤ M), ε := by
          refine Finset.sum_le_sum fun T hT => ?_
          obtain ⟨hTE, hTM⟩ := Finset.mem_filter.1 hT
          have hTne : T ≠ ∅ := (Finset.mem_erase.1 (hE ▸ hTE)).1
          have hTs : T ∈ s.powerset := (Finset.mem_erase.1 (hE ▸ hTE)).2
          rw [hA]
          simp only [norm_mul]
          calc ‖sampleAvg P id (fun n => ∏ p ∈ T, (g p n - μ p))‖ * ‖∏ p ∈ s \ T, μ p‖
              ≤ ε * 1 := by
                refine mul_le_mul (hsmall T hTs (Finset.nonempty_iff_ne_empty.2 hTne) hTM)
                  (hcof T (Finset.mem_powerset.1 hTs)) (norm_nonneg _) hε
            _ = ε := mul_one ε
      _ = (E.filter (fun T => T.card ≤ M)).card * ε := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ M)).card * ε := by
          refine mul_le_mul_of_nonneg_right ?_ hε
          refine Nat.cast_le.2 (Finset.card_le_card fun T hT => ?_)
          obtain ⟨hTE, hTM⟩ := Finset.mem_filter.1 hT
          have hTne : T ≠ ∅ := (Finset.mem_erase.1 (hE ▸ hTE)).1
          have hTs : T ∈ s.powerset := (Finset.mem_erase.1 (hE ▸ hTE)).2
          exact Finset.mem_filter.2 ⟨hTs, Finset.nonempty_iff_ne_empty.2 hTne, hTM⟩
  · -- the Chernoff tail
    calc ‖∑ T ∈ E.filter (fun T => ¬ T.card ≤ M), A T‖
        ≤ ∑ T ∈ E.filter (fun T => ¬ T.card ≤ M), ‖A T‖ := norm_sum_le _ _
      _ ≤ ∑ T ∈ E.filter (fun T => ¬ T.card ≤ M),
            sampleAvg P id (fun n => ∏ p ∈ T, ‖g p n - μ p‖) := by
          refine Finset.sum_le_sum fun T hT => ?_
          obtain ⟨hTE, _⟩ := Finset.mem_filter.1 hT
          have hTs : T ∈ s.powerset := (Finset.mem_erase.1 (hE ▸ hTE)).2
          rw [hA]
          simp only [norm_mul]
          calc ‖sampleAvg P id (fun n => ∏ p ∈ T, (g p n - μ p))‖ * ‖∏ p ∈ s \ T, μ p‖
              ≤ ‖sampleAvg P id (fun n => ∏ p ∈ T, (g p n - μ p))‖ * 1 :=
                mul_le_mul_of_nonneg_left (hcof T (Finset.mem_powerset.1 hTs)) (norm_nonneg _)
            _ = ‖sampleAvg P id (fun n => ∏ p ∈ T, (g p n - μ p))‖ := mul_one _
            _ ≤ sampleAvg P id (fun n => ‖∏ p ∈ T, (g p n - μ p)‖) :=
                norm_sampleAvg_id_le_avg_norm P _
            _ = sampleAvg P id (fun n => ∏ p ∈ T, ‖g p n - μ p‖) := by
                unfold sampleAvg
                simp only [id_eq, norm_prod]
      _ = sampleAvg P id (fun n =>
            ∑ T ∈ E.filter (fun T => ¬ T.card ≤ M), ∏ p ∈ T, ‖g p n - μ p‖) :=
          (sampleAvg_id_sum P _ _).symm
      _ ≤ sampleAvg P id (fun n => (lam ^ M)⁻¹ * ∏ p ∈ s, (1 + lam * ‖g p n - μ p‖)) := by
          refine sampleAvg_id_mono P fun n _ => ?_
          have hsub : E.filter (fun T => ¬ T.card ≤ M)
              ⊆ s.powerset.filter (fun T => M < T.card) := by
            intro T hT
            obtain ⟨hTE, hTM⟩ := Finset.mem_filter.1 hT
            have hTs : T ∈ s.powerset := (Finset.mem_erase.1 (hE ▸ hTE)).2
            exact Finset.mem_filter.2 ⟨hTs, by omega⟩
          calc ∑ T ∈ E.filter (fun T => ¬ T.card ≤ M), ∏ p ∈ T, ‖g p n - μ p‖
              ≤ ∑ T ∈ s.powerset.filter (fun T => M < T.card), ∏ p ∈ T, ‖g p n - μ p‖ :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub
                  (fun T _ _ => Finset.prod_nonneg fun p _ => norm_nonneg _)
            _ ≤ (lam ^ M)⁻¹ * ∏ p ∈ s, (1 + lam * ‖g p n - μ p‖) := by
                rw [inv_mul_eq_div]
                exact hchern n
      _ = (lam ^ M)⁻¹ * sampleAvg P id (fun n => ∏ p ∈ s, (1 + lam * ‖g p n - μ p‖)) :=
          sampleAvg_id_const_smul P _ _
      _ ≤ (lam ^ M)⁻¹ * B := by
          exact mul_le_mul_of_nonneg_left hbig (by positivity)
      _ = B / lam ^ M := by rw [inv_mul_eq_div]


/-- **§4C assembled, modulo the two named inputs.**  The per-prime contraction of
`G4LocalContraction` (through `‖μ p‖ ≤ 1 - c / w p`, with `c = 4·4^{-4}·8^{-K}` from
`G4FreqSep.sum_sq_distZ_freqDepth_ge` and `w p = p`) together with the transfer skeleton gives

    ‖avg_n ∏_{p∈s} g p n‖ ≤ exp(-c ∑_{p∈s} w p⁻¹) + N_M ε + B / lam^M .

With `s` the good primes up to `R` and `∑_{p≤R} p⁻¹ = L - o(L)`, the first term is the brief's
`exp(-c L 8^{-K})`.  This is the shape `PropC δ₃` needs; only `ε` (C3a, CRT counting) and
`B` (C3core, the exponential moment) remain to be supplied. -/
theorem norm_sampleAvg_prod_le_exp (P : Finset ℕ) (hP : P.Nonempty) (s : Finset ι)
    (g : ι → ℕ → ℂ) (μ : ι → ℂ) (w : ι → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hw : ∀ p ∈ s, 0 < w p) (hcw : ∀ p ∈ s, c ≤ w p)
    (hcontract : ∀ p ∈ s, ‖μ p‖ ≤ 1 - c / w p)
    (M : ℕ) {lam ε B : ℝ} (hlam : 1 ≤ lam) (hε : 0 ≤ ε)
    (hsmall : ∀ T ∈ s.powerset, T.Nonempty → T.card ≤ M →
        ‖sampleAvg P id (fun n => ∏ p ∈ T, (g p n - μ p))‖ ≤ ε)
    (hbig : sampleAvg P id (fun n => ∏ p ∈ s, (1 + lam * ‖g p n - μ p‖)) ≤ B) :
    ‖sampleAvg P id (fun n => ∏ p ∈ s, g p n)‖
      ≤ Real.exp (-∑ p ∈ s, c / w p)
        + ((s.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ M)).card * ε + B / lam ^ M) := by
  have hμ1 : ∀ p ∈ s, ‖μ p‖ ≤ 1 := by
    intro p hp
    have h1 := hcontract p hp
    have h2 : (0 : ℝ) ≤ c / w p := div_nonneg hc (hw p hp).le
    linarith
  have hskel := norm_sampleAvg_prod_sub_prod_le P hP s g μ hμ1 M hlam hε hsmall hbig
  have hprod : ‖∏ p ∈ s, μ p‖ ≤ Real.exp (-∑ p ∈ s, c / w p) := by
    rw [norm_prod]
    exact le_trans (Finset.prod_le_prod (fun p _ => norm_nonneg _) hcontract)
      (prod_contraction_le_exp s w c hc hw hcw)
  calc ‖sampleAvg P id (fun n => ∏ p ∈ s, g p n)‖
      ≤ ‖∏ p ∈ s, μ p‖ + ‖sampleAvg P id (fun n => ∏ p ∈ s, g p n) - ∏ p ∈ s, μ p‖ := by
        simpa using
          norm_add_le (∏ p ∈ s, μ p)
            (sampleAvg P id (fun n => ∏ p ∈ s, g p n) - ∏ p ∈ s, μ p)
    _ ≤ _ := add_le_add hprod hskel

end Transfer

end NormalNumbers.G4
