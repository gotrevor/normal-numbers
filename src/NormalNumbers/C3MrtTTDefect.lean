/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtUnifK
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The TT interface defects, machine-checked — and the faithful restatement

Astro's cross-branch fidelity audit (2026-09-25,
`~/src/normal-numbers/docs/REVIEW-2026-09-25-normal-numbers.md` lines 66-70) found three
definitional defects in the formal Tao–Teräväinen interface.  This file turns each of them
into a **theorem**, then restates the two damaged `Prop`s faithfully and proves a
**non-vacuity guard** for each restatement.

## §1-§3, the defects as theorems

* `ttNonPretentious_trivial` — `TTNonPretentious g X L` holds for **every** 1-bounded `g`,
  `g = 1` included, as soon as `0 < L`.  The witness is `A = 1/L`: every summand of
  `ttPretentiousSum` is `≥ 0`, so `exp` of it is `≥ 1`, and `A` is chosen *after* `X, L`.
  TT (3.3) has an implied constant that is absolute — outside `X` and `L`.
* `not_kPointNoExcWith_const_one` — consequently `KPointNoExcWith cK CstK 2` is **false**
  whenever `0 < cK 2`: take `g 0 = g 1 = 1`, `W = 1`, shifts `1, 2`, `X = exp L`,
  `N = ⌈√X⌉`.  The progression-restricted mean is exactly `1`, while the claimed bound
  `CstK 2 · L^{-cK 2}` is `< 1` once `L` is large.
* `twoPointNaturalCorrelation_trivially_true` — `TwoPointNaturalCorrelation` is **true**,
  for the wrong reason: its exceptional set `E ⊆ ℝ` is charged by the Lebesgue integral
  `∫_E t⁻¹`, so `E = ℕ ∩ [√X, X]` is free and excludes every scale `N : ℕ` the conclusion
  quantifies over.

Together these say: the old interface assumes nothing (§1), the consumers of the K-point form
have a hypothesis that is never satisfiable (§2), and the two-point form has no content (§3).

## §4-§5, the faithful restatement

* `ttPretentiousSumChar` / `TTNonPretentiousAt A g X L` — TT's `M(g; X², Q)` with the
  infimum over **Dirichlet characters** of conductor `q ≤ Q = (log X)^{1/125}` as well as the
  twists, and the twist range TT's `|t| ≤ X²`, not `|t| ≤ Q`.  The implied constant `A` is a
  **parameter**, so it is outside `X` and `L`.
* `TTNonPretentiousUnif g` — `∃ A > 0` outside the `∀ X L`, the form TT's `≫` means.
  Guard: `not_ttNonPretentiousUnif_one` — `g = 1` does **not** satisfy it.  So unlike §1 the
  restatement is not trivially true.
* `TwoPointDyadicCorrelation` — the exceptional set is a `Finset` of **dyadic scales** and its
  cost is a *fraction* `≤ Cst · L^{-c}` of all the scales in `[√X, X]`, a counting/log-density
  cost, not a Lebesgue one.  Guards: `full_exceptional_set_not_admissible` (the §3 trick is
  now forbidden: the all-scales set fails the cost bound once `Cst L^{-c} < 1`, and
  `exists_L_cost_lt_one` says such an `L` exists) together with
  `not_ttNonPretentiousAt_one` (the §2 refutation no longer applies: the constant-one family
  fails the faithful hypothesis in exactly the large-`L` regime the refutation needs).
* `ttNonPretentious_of_At` — the restatement is a genuine strengthening: the faithful
  hypothesis implies the old one, so nothing that consumed the old one gets weaker.
-/

open Finset MeasureTheory

namespace NormalNumbers

namespace CastingOut

/-! ## §1 `TTNonPretentious` is vacuous -/

/-- Each summand of `ttPretentiousSum` is nonnegative for a 1-bounded `g`. -/
theorem ttPretentiousSum_nonneg {g : ℕ → ℂ} (hg : ∀ n, ‖g n‖ ≤ 1) (X t : ℝ) :
    0 ≤ ttPretentiousSum g X t := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hnorm : ‖g p * Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_exp]
    have : (-(t : ℂ) * Complex.I * (Real.log p : ℂ)).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [this, Real.exp_zero, mul_one]
    exact hg p
  have hre : (g p * Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))).re ≤ 1 :=
    le_trans (Complex.re_le_norm _) hnorm
  exact div_nonneg (by linarith) hp0.le

/-- **Defect 1 (Astro 2026-09-25).**  `TTNonPretentious` holds for *every* 1-bounded `g`,
including `g = 1`: the constant `A` is existentially quantified after `X` and `L`, so `A = 1/L`
always works.  TT (3.3) has an absolute implied constant; see `TTNonPretentiousAt`. -/
theorem ttNonPretentious_trivial {g : ℕ → ℂ} (hg : ∀ n, ‖g n‖ ≤ 1) {X L : ℝ} (hL : 0 < L) :
    TTNonPretentious g X L := by
  refine ⟨1 / L, by positivity, fun t _ => ?_⟩
  have h1 : (1 / L) * L = 1 := by field_simp
  rw [h1]
  exact Real.one_le_exp (ttPretentiousSum_nonneg hg X t)

/-- In particular the constant function `1` — the most pretentious function there is — is
"non-pretentious" in the old sense. -/
theorem ttNonPretentious_one {X L : ℝ} (hL : 0 < L) :
    TTNonPretentious (fun _ => (1 : ℂ)) X L :=
  ttNonPretentious_trivial (fun _ => by simp) hL


/-! ## §2 the K-point input is FALSE at the constant function -/

/-- A scale at which the `L^c` saving has already beaten a prescribed size. -/
theorem exists_rpow_ge {c : ℝ} (hc : 0 < c) (M : ℝ) : ∃ L : ℝ, 2 ≤ L ∧ M ≤ L ^ c := by
  set M' : ℝ := max 2 M with hM'
  have hM'0 : (0 : ℝ) < M' := lt_of_lt_of_le two_pos (le_max_left _ _)
  refine ⟨max 2 (M' ^ c⁻¹), le_max_left _ _, ?_⟩
  have h2 : (M' ^ c⁻¹) ^ c ≤ (max 2 (M' ^ c⁻¹)) ^ c :=
    Real.rpow_le_rpow (Real.rpow_nonneg hM'0.le _) (le_max_right _ _) hc.le
  rw [Real.rpow_inv_rpow hM'0.le hc.ne'] at h2
  exact le_trans (le_max_right _ _) h2

/-- **Defect 2 (Astro 2026-09-25).**  `KPointNoExcWith cK CstK 2` is **false** whenever
`0 < cK 2` — not merely hard.  Take both factors to be the constant `1`, `W = 1`, shifts
`1, 2`, `X = exp L`, `N = ⌈√X⌉`: the hypothesis `∃ i, TTNonPretentious (g i) X L` is free by
§1, the progression-restricted mean is exactly `1`, and `CstK 2 · L^{-cK 2} < 1` for large `L`.

Hence every theorem taking `KPointNoExcWith`, `KPointNoExcRoots`, `KPointNoExcDepth` or
`KPointNoExcAllWith` as a hypothesis is vacuous as those `Prop`s stand. -/
theorem not_kPointNoExcWith_const_one {cK CstK : ℕ → ℝ} (hc : 0 < cK 2) :
    ¬ KPointNoExcWith cK CstK 2 := by
  intro h
  obtain ⟨L, hL2, hLbig⟩ := exists_rpow_ge hc (max 2 (CstK 2 + 2))
  have hLc2 : (2 : ℝ) ≤ L ^ cK 2 := le_trans (le_max_left _ _) hLbig
  have hLcC : CstK 2 + 2 ≤ L ^ cK 2 := le_trans (le_max_right _ _) hLbig
  set X : ℝ := Real.exp L with hX
  have hlogX : Real.log X = L := Real.log_exp L
  have hX4 : (4 : ℝ) ≤ X := by
    have h1 : Real.exp 2 ≤ X := Real.exp_le_exp.mpr hL2
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hX2 : (2 : ℝ) ≤ X := by linarith
  -- the scale
  set N : ℕ := ⌈Real.sqrt X⌉₊ with hN
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hsqX : Real.sqrt X ≤ (N : ℝ) := Nat.le_ceil _
  have hsq2 : (2 : ℝ) ≤ Real.sqrt X := by
    have := Real.sqrt_le_sqrt hX4
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have hNX : (N : ℝ) ≤ X := by
    have h1 : (N : ℝ) ≤ Real.sqrt X + 1 := le_of_lt (Nat.ceil_lt_add_one hsqrt0)
    have hs : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by linarith)
    nlinarith
  have hNpos : 0 < N := by
    have : (0 : ℝ) < (N : ℝ) := by linarith
    exact_mod_cast this
  -- the constant-one family
  set g : Fin 2 → ℕ → ℂ := fun _ _ => 1 with hg
  have hmult : ∀ i, IsCoprimeMultiplicativeNat (g i) := fun i => ⟨rfl, by simp [hg]⟩
  have hbd : ∀ i n, ‖g i n‖ ≤ 1 := fun i n => by simp [hg]
  have hnp : ∃ i, TTNonPretentious (g i) X L := ⟨0, ttNonPretentious_trivial (hbd 0) (by linarith)⟩
  have hshinj : Function.Injective (![1, 2] : Fin 2 → ℕ) := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  have hshle : ∀ i, ((![1, 2] : Fin 2 → ℕ) i : ℝ) ≤ L ^ cK 2 := by
    intro i; fin_cases i
    · simpa using le_trans (by norm_num) hLc2
    · simpa using hLc2
  have key := h g hmult hbd X L hX2 (by linarith) (by rw [hlogX]) hnp N hsqX hNX 1 0 ![1, 2]
    one_pos (by simpa using le_trans (by norm_num) hLc2) hshle hshinj
  -- the left-hand side is exactly 1
  have hfilter : (Finset.Ioc N (2 * N)).filter (fun n => n % 1 = 0 % 1)
      = Finset.Ioc N (2 * N) := Finset.filter_true_of_mem (fun x _ => by omega)
  have hcard : (Finset.Ioc N (2 * N)).card = N := by simp [Nat.card_Ioc, two_mul]
  have hlhs : ‖((1 : ℝ) / (N : ℝ) : ℝ) •
      ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % 1 = 0 % 1),
        ∏ i : Fin 2, g i (n + (![1, 2] : Fin 2 → ℕ) i)‖ = 1 := by
    rw [hfilter]
    have hsum : ∑ n ∈ Finset.Ioc N (2 * N), ∏ i : Fin 2, g i (n + (![1, 2] : Fin 2 → ℕ) i)
        = (N : ℂ) := by
      simp [hg, hcard]
    rw [hsum]
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    rw [norm_smul]
    simp [hN0]
  simp only [Nat.cast_one] at key
  rw [hlhs] at key
  -- but the right-hand side is < 1
  have hLc0 : (0 : ℝ) < L ^ cK 2 := by linarith
  have hneg : L ^ (-(cK 2)) = (L ^ cK 2)⁻¹ := by
    rw [Real.rpow_neg (by linarith)]
  rw [hneg] at key
  have : CstK 2 * (L ^ cK 2)⁻¹ < 1 := by
    rw [mul_inv_lt_iff₀ hLc0]
    nlinarith
  linarith


/-! ### §2b the same refutation reaches the two named open problems

`KPointNaturalCorrelationNoExc 2` and `TwoPointNaturalCorrelationNoExc` — the `Prop`s the
`D = 2` natural-density rung and the whole `C3MrtNoExc` chain are stated over — are refuted by
the same constant-one witness.  So the ledger's "named open problem" was not open: it was
false.  Both are repaired by swapping in `TTNonPretentiousAt`. -/

theorem not_kPointNaturalCorrelationNoExc : ¬ KPointNaturalCorrelationNoExc 2 := by
  intro h
  obtain ⟨c, Cst, hc, _, hw⟩ := exists_with_of_kPointNoExc h
  exact not_kPointNoExcWith_const_one (cK := fun _ => c) (CstK := fun _ => Cst) hc hw

/-- The two-point form *is* the `K = 2` form: the missing direction of
`twoPointNoExc_of_kPointNoExc`, available precisely because §1 makes the non-pretentiousness
hypothesis free. -/
theorem kPointNoExcWith_of_twoPointNoExc (h : TwoPointNaturalCorrelationNoExc) :
    ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧ KPointNoExcWith (fun _ => c) (fun _ => Cst) 2 := by
  obtain ⟨c, Cst, hc, hCst, hmain⟩ := h
  refine ⟨c, Cst, hc, hCst, ?_⟩
  intro g hmult hbd X L hX hL1 hLX _ N hN1 hN2 W b hsh hW hWL hshL hshinj
  have hne : hsh 0 ≠ hsh 1 := fun hEq => by simpa using hshinj hEq
  have hspec := hmain (g 0) (g 1) (hmult 0) (hmult 1) (hbd 0) (hbd 1) X L hX hL1 hLX
    (ttNonPretentious_trivial (hbd 0) (by linarith)) N hN1 hN2 W b (hsh 0) (hsh 1) hW hWL
    (hshL 0) (hshL 1) hne
  refine le_trans (le_of_eq ?_) hspec
  congr 2
  exact Finset.sum_congr rfl fun n _ => Fin.prod_univ_two _

theorem not_twoPointNaturalCorrelationNoExc : ¬ TwoPointNaturalCorrelationNoExc := by
  intro h
  obtain ⟨c, Cst, hc, _, hw⟩ := kPointNoExcWith_of_twoPointNoExc h
  exact not_kPointNoExcWith_const_one (cK := fun _ => c) (CstK := fun _ => Cst) hc hw

/-! ## §3 the exceptional set is free if it is the integers -/

/-- **Defect 3 (Astro 2026-09-25).**  `TwoPointNaturalCorrelation` is **true**, and for the
wrong reason: its exceptional set is an arbitrary measurable `E ⊆ ℝ` charged by the Lebesgue
integral `∫_E t⁻¹`, while the conclusion is only ever asked at *integer* scales `N`.  Taking
`E` to be the integers in `[√X, X]` costs nothing and excludes every `N`.

So this `Prop` supplies no near-all-scale information whatsoever, and neither does anything
derived from it alone.  TT's exceptional set is a set of scales measured by the logarithmic
density of the integer/dyadic scales; see `TwoPointDyadicCorrelation`. -/
theorem twoPointNaturalCorrelation_trivially_true : TwoPointNaturalCorrelation := by
  refine ⟨1, 1, one_pos, one_pos, fun g₁ g₂ _ _ _ _ X L hX hL1 hLX _ => ?_⟩
  refine ⟨Set.range (fun n : ℕ => (n : ℝ)) ∩ Set.Icc (Real.sqrt X) X, ?_, Set.inter_subset_right,
    ?_, ?_⟩
  · exact ((Set.countable_range _).mono Set.inter_subset_left).measurableSet
  · have hzero : volume (Set.range (fun n : ℕ => (n : ℝ)) ∩ Set.Icc (Real.sqrt X) X) = 0 :=
      ((Set.countable_range _).mono Set.inter_subset_left).measure_zero volume
    rw [MeasureTheory.setIntegral_measure_zero _ hzero]
    have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    have : (0 : ℝ) ≤ L ^ (-(1 : ℝ)) := Real.rpow_nonneg (by linarith) _
    positivity
  · intro N hN1 hN2 hNE
    exact absurd (Set.mem_inter (Set.mem_range_self (f := fun n : ℕ => (n : ℝ)) N)
      (Set.mem_Icc.mpr ⟨hN1, hN2⟩)) hNE


/-! ## §4 the faithful non-pretentiousness hypothesis -/

/-- The inner sum of TT's `M(g; X², Q)` at the Dirichlet character `χ` and the twist `t`:
`∑_{p ≤ X²} (1 − Re(g(p) conj(χ(p)) p^{-it}))/p` — TT's `D(g, n ↦ χ(n)n^{it}; X²)²`, whose
summand is `1 − Re(g(p) conj(χ(p)p^{it}))` (paper (1.17)-(1.18), lines 557-576).  `ttPretentiousSum` is the `q = 1` case
(`ttPretentiousSumChar_one`), which is exactly what the old interface omitted. -/
noncomputable def ttPretentiousSumChar (g : ℕ → ℂ) (X : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌈X ^ 2⌉₊ + 1)).filter Nat.Prime,
    (1 - (g p * (starRingEnd ℂ) (χ (p : ZMod q)) *
      Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))).re) / (p : ℝ)

theorem ttPretentiousSumChar_one (g : ℕ → ℂ) (X t : ℝ) :
    ttPretentiousSumChar g X (1 : DirichletCharacter ℂ 1) t = ttPretentiousSum g X t := by
  unfold ttPretentiousSumChar ttPretentiousSum
  refine Finset.sum_congr rfl fun p _ => ?_
  have : (starRingEnd ℂ) ((1 : DirichletCharacter ℂ 1) ((p : ℕ) : ZMod 1)) = 1 := by
    rw [Subsingleton.elim ((p : ℕ) : ZMod 1) 1, map_one, map_one]
  rw [this, mul_one]

/-- **TT (3.3), faithfully** — `exp(M(g; X², (log X)^{1/125})) ≥ A · L` with the implied
constant `A` a **parameter**, so it lives outside `X` and `L`, and with the infimum taken over
Dirichlet characters of modulus `q ≤ (log X)^{1/125}` (TT: conductor `q ≤ Q`; quantifying over
all characters of every modulus `≤ Q` is the same class) as well as over the twists
`|t| ≤ X²` (TT's twist range, not `Q`).

Both repairs make the hypothesis *harder* to satisfy, i.e. this `Prop` implies the old
`TTNonPretentious` (`ttNonPretentious_of_At`), so no consumer is weakened by the swap. -/
def TTNonPretentiousAt (A : ℝ) (g : ℕ → ℂ) (X L : ℝ) : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) →
    ∀ t : ℝ, |t| ≤ X ^ 2 → A * L ≤ Real.exp (ttPretentiousSumChar g X χ t)

/-- **The repaired `TTNonPretentious`.**  `∃ A > 0` is *outside* the `∀ X L`, which is what
TT's `≫` means; §1's `A = 1/L` witness is therefore unavailable. -/
def TTNonPretentiousUnif (g : ℕ → ℂ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X → TTNonPretentiousAt A g X L

theorem one_le_log_of_exp_le {X : ℝ} (hX : Real.exp 1 ≤ X) : 1 ≤ Real.log X := by
  have := Real.log_le_log (Real.exp_pos 1) hX
  rwa [Real.log_exp] at this

/-- The faithful hypothesis implies the old one: the `q = 1`, `|t| ≤ (log X)^{1/125}` corner. -/
theorem ttNonPretentious_of_At {A : ℝ} {g : ℕ → ℂ} {X L : ℝ} (hA : 0 < A)
    (hX : Real.exp 1 ≤ X) (h : TTNonPretentiousAt A g X L) : TTNonPretentious g X L := by
  have hlog1 : 1 ≤ Real.log X := one_le_log_of_exp_le hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (by nlinarith [Real.add_one_le_exp (1:ℝ)]) hX
  refine ⟨A, hA, fun t ht => ?_⟩
  have hQ : (1 : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) :=
    Real.one_le_rpow hlog1 (by norm_num)
  have htX : |t| ≤ X ^ 2 := by
    have h1 : Real.log X ^ ((1 : ℝ) / 125) ≤ Real.log X ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
    rw [Real.rpow_one] at h1
    have h2 : Real.log X ≤ X - 1 := Real.log_le_sub_one_of_pos (by linarith)
    nlinarith
  have := h 1 (1 : DirichletCharacter ℂ 1) (by simpa using hQ) t htX
  rwa [ttPretentiousSumChar_one] at this

/-! ### Guard: the restatement is *not* trivially true -/

theorem ttPretentiousSumChar_one_const_one (X t : ℝ) (ht : t = 0) :
    ttPretentiousSumChar (fun _ => (1 : ℂ)) X (1 : DirichletCharacter ℂ 1) t = 0 := by
  rw [ttPretentiousSumChar_one]
  unfold ttPretentiousSum
  refine Finset.sum_eq_zero fun p _ => ?_
  subst ht
  simp

/-- **Guard for `TTNonPretentiousAt`** (against §1): the constant function `1` fails it at
every `L > 1/A`.  This is also why §2's refutation of `KPointNoExcWith` does **not** transfer
to the `At` form: the refutation needs `L` large, and there the hypothesis is false. -/
theorem not_ttNonPretentiousAt_one {A X L : ℝ} (hX : Real.exp 1 ≤ X) (hAL : 1 < A * L) :
    ¬ TTNonPretentiousAt A (fun _ => (1 : ℂ)) X L := by
  intro h
  have hlog1 : 1 ≤ Real.log X := one_le_log_of_exp_le hX
  have hQ : (1 : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) := Real.one_le_rpow hlog1 (by norm_num)
  have hX1 : (1 : ℝ) ≤ X := le_trans (by nlinarith [Real.add_one_le_exp (1:ℝ)]) hX
  have := h 1 (1 : DirichletCharacter ℂ 1) (by simpa using hQ) 0 (by
    simp only [abs_zero]; nlinarith)
  rw [ttPretentiousSumChar_one_const_one X 0 rfl, Real.exp_zero] at this
  linarith

/-- **Guard for `TTNonPretentiousUnif`** (the headline non-vacuity check): unlike
`TTNonPretentious` (§1), the repaired hypothesis is **false** for `g = 1`.  So it is not
trivially true, and the `g = 1` family can no longer be fed to any consumer. -/
theorem not_ttNonPretentiousUnif_one : ¬ TTNonPretentiousUnif (fun _ => (1 : ℂ)) := by
  rintro ⟨A, hA, h⟩
  set L : ℝ := max 1 (2 / A) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hAL : 1 < A * L := by
    have h2 : 2 / A ≤ L := le_max_right _ _
    have : 2 ≤ A * L :=
      calc (2 : ℝ) = A * (2 / A) := by field_simp
        _ ≤ A * L := mul_le_mul_of_nonneg_left h2 hA.le
    linarith
  have hXe : Real.exp 1 ≤ Real.exp L := Real.exp_le_exp.mpr hL1
  have hX2 : (2 : ℝ) ≤ Real.exp L := by
    nlinarith [Real.exp_one_gt_d9, hXe]
  exact not_ttNonPretentiousAt_one hXe hAL
    (h (Real.exp L) L hX2 hL1 (by rw [Real.log_exp]))


/-! ## §5 the faithful exceptional set: integer (dyadic) scales, counted -/

/-- The dyadic scales inside `[√X, X]`: the exponents `j` with `√X ≤ 2^j` and `2^{j+1} ≤ X`.
A `Finset`, so that an exceptional subset of it can be **counted** — the log-density cost TT
actually pay, and the thing `E ⊆ ℝ` charged by `∫_E t⁻¹` could not see (§3). -/
noncomputable def dyadicScales (X : ℝ) : Finset ℕ :=
  (Finset.range (⌈Real.logb 2 X⌉₊ + 1)).filter
    (fun j => Real.sqrt X ≤ 2 ^ j ∧ (2 : ℝ) ^ (j + 1) ≤ X)

/-- **Theorem 3.1(ii), faithfully.**  The exceptional set is a set of **dyadic scales**, and
its cost is a *fraction* `≤ Cst · L^{-c}` of all the scales in `[√X, X]` — a counting /
log-density cost.  The non-pretentiousness hypothesis is the faithful `TTNonPretentiousAt A`,
whose implied constant `A` is outside `X, L`; the conclusion's constants `c, Cst` may depend on
`A` (TT's `c` is absolute *given* the implied constant in `≫`) but on nothing else.

Guards: `full_exceptional_set_not_admissible` + `exists_L_cost_lt_one` (the §3 free-set trick
is forbidden) and `not_ttNonPretentiousAt_one` (the §2 constant-one refutation does not
apply). -/
def TwoPointDyadicCorrelation (A : ℝ) : Prop :=
  ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧
    ∀ g₁ g₂ : ℕ → ℂ, IsCoprimeMultiplicativeNat g₁ → IsCoprimeMultiplicativeNat g₂ →
      (∀ n, ‖g₁ n‖ ≤ 1) → (∀ n, ‖g₂ n‖ ≤ 1) →
      ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X →
        TTNonPretentiousAt A g₁ X L →
        ∃ E : Finset ℕ, E ⊆ dyadicScales X ∧
          (E.card : ℝ) ≤ Cst * L ^ (-c) * ((dyadicScales X).card : ℝ) ∧
          ∀ j ∈ dyadicScales X, j ∉ E →
            ∀ N : ℕ, (2 : ℝ) ^ j ≤ (N : ℝ) → (N : ℝ) < 2 ^ (j + 1) →
              ∀ W b h₁ h₂ : ℕ, 0 < W → (W : ℝ) ≤ L ^ c →
                (h₁ : ℝ) ≤ L ^ c → (h₂ : ℝ) ≤ L ^ c → h₁ ≠ h₂ →
                ‖((W : ℝ) / (N : ℝ) : ℝ) •
                    ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = b % W),
                      g₁ (n + h₁) * g₂ (n + h₂)‖
                  ≤ Cst * L ^ (-c)

/-- **Guard for `TwoPointDyadicCorrelation`, part 1.**  The §3 trick — declare *every* scale
exceptional — is now forbidden: at any `L` with `Cst L^{-c} < 1` the all-scales set breaks the
counting cost, as soon as there is a scale at all. -/
theorem full_exceptional_set_not_admissible {c Cst L : ℝ}
    (h : Cst * L ^ (-c) < 1) {X : ℝ} (hne : (dyadicScales X).Nonempty) :
    ¬ (((dyadicScales X).card : ℝ) ≤ Cst * L ^ (-c) * ((dyadicScales X).card : ℝ)) := by
  intro hle
  have hpos : (0 : ℝ) < ((dyadicScales X).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  nlinarith

/-- …and such an `L` exists, in the very regime the conclusion is interesting in
(`L → ∞` with `L ≤ log X`). -/
theorem exists_L_cost_lt_one {c Cst : ℝ} (hc : 0 < c) (_hCst : 0 < Cst) :
    ∃ L : ℝ, 2 ≤ L ∧ Cst * L ^ (-c) < 1 := by
  obtain ⟨L, hL2, hLbig⟩ := exists_rpow_ge hc (Cst + 1)
  have hL0 : (0 : ℝ) < L := by linarith
  have hLc0 : (0 : ℝ) < L ^ c := by positivity
  refine ⟨L, hL2, ?_⟩
  rw [Real.rpow_neg hL0.le, mul_inv_lt_iff₀ hLc0]
  linarith

/-! ### The faithful `K`-point input -/

/-- `KPointNoExcWith` with the faithful non-pretentiousness hypothesis `TTNonPretentiousAt A`
in place of the vacuous `TTNonPretentious`.  Everything downstream of `KPointNoExcWith`
should be rethreaded onto this (see the SURVIVORS table in the handoff). -/
def KPointNoExcAtWith (A : ℝ) (cK CstK : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ g : Fin K → ℕ → ℂ, (∀ i, IsCoprimeMultiplicativeNat (g i)) →
    (∀ i n, ‖g i n‖ ≤ 1) →
    ∀ X L : ℝ, Real.exp 1 ≤ X → 1 ≤ L → L ≤ Real.log X →
      (∃ i, TTNonPretentiousAt A (g i) X L) →
        ∀ N : ℕ, Real.sqrt X ≤ (N : ℝ) → (N : ℝ) ≤ X →
          ∀ (W b : ℕ) (hsh : Fin K → ℕ), 0 < W → (W : ℝ) ≤ L ^ cK K →
            (∀ i, (hsh i : ℝ) ≤ L ^ cK K) → Function.Injective hsh →
            ‖((W : ℝ) / (N : ℝ) : ℝ) •
                ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = b % W),
                  ∏ i : Fin K, g i (n + hsh i)‖
              ≤ CstK K * L ^ (-(cK K))

/-- The faithful input asks for **less** than the old one: the old `Prop` implies it.  (The old
one is false, §2; this is only here to certify that the swap weakens no consumer.) -/
theorem kPointNoExcAtWith_of_with {A : ℝ} (hA : 0 < A) {cK CstK : ℕ → ℝ} {K : ℕ}
    (h : KPointNoExcWith cK CstK K) : KPointNoExcAtWith A cK CstK K := by
  intro g hmult hbd X L hX hL1 hLX hnp
  have hX1 : (1 : ℝ) ≤ X := le_trans (by nlinarith [Real.add_one_le_exp (1:ℝ)]) hX
  have hX2 : (2 : ℝ) ≤ X := by nlinarith [Real.exp_one_gt_d9, hX]
  obtain ⟨i, hi⟩ := hnp
  exact h g hmult hbd X L hX2 hL1 hLX ⟨i, ttNonPretentious_of_At hA hX hi⟩

/-- **Guard for `KPointNoExcAtWith`.**  §2's refutation is blocked: the constant-one family
does not satisfy the faithful hypothesis once `L > 1/A`, which is exactly the range in which
the conclusion `≤ CstK K · L^{-cK K}` has any bite.  (At `L ≤ 1/A` the conclusion is not
contradicted, since `CstK K · L^{-cK K}` need not be `< 1` there.) -/
theorem const_one_not_faithful {A : ℝ} {K : ℕ} {X L : ℝ} (hX : Real.exp 1 ≤ X)
    (hAL : 1 < A * L) :
    ¬ (∃ _i : Fin K, TTNonPretentiousAt A (fun _ => (1 : ℂ)) X L) := by
  rintro ⟨_, h⟩
  exact not_ttNonPretentiousAt_one hX hAL h

#print axioms ttNonPretentious_trivial
#print axioms not_kPointNoExcWith_const_one
#print axioms not_kPointNaturalCorrelationNoExc
#print axioms not_twoPointNaturalCorrelationNoExc
#print axioms twoPointNaturalCorrelation_trivially_true
#print axioms not_ttNonPretentiousUnif_one
#print axioms ttNonPretentious_of_At
#print axioms full_exceptional_set_not_admissible
#print axioms kPointNoExcAtWith_of_with

end CastingOut

end NormalNumbers
