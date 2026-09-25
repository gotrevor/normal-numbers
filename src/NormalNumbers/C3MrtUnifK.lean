/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtQuantKPoint
import NormalNumbers.C3MrtBudget

/-!
# The diagonal, and why only uniformity in `K` can reach it

`weylLambertTwist_of_depthElliottLL` (`C3MrtSchedule`) consumes exactly one thing: the
**diagonal** limit

    ‖depthAvg b P Q j h (depthLL b N) N‖ → 0 ,

the point count growing with `N` like `log_b log log N`.  Two layers were built towards it and
neither can reach it; this file says why, in Lean, and puts the correct shape in place.

## The budget layer is vacuous (`quantDepthElliottGen_forces_diagonal`)

`QuantDepthElliottGen b` asks for `C η` with `‖depthAvg b P Q j h D N‖ ≤ C D · η N` for **all**
`D`, plus `C(depthLL b N)·η(N) → 0`.  Instantiating the first at `D = depthLL b N` gives

    C(depthLL b N)·η(N)  ≥  ‖depthAvg b P Q j h (depthLL b N) N‖ ,

so *every* budget — `b^{κD}`, `A_D e^{D²}`, anything at all — already forces the diagonal.
Freeing the constant buys nothing: a budget cannot manufacture uniformity it is not given, and
`budget_absorb` / `pow_self_sq_le_exp_cube` / a `sup_D` assembly are bookkeeping around a `Prop`
that is no weaker than the target.

## The fixed-`K` layer is the end of its line

`depthAvg_K_tendsto_of_noExc` (`C3MrtKPointNoExc`) gives, for each fixed `K`, a limit.  A family
of sequences each tending to `0` has no diagonal limit along a growing index without uniformity,
and `KPointNaturalCorrelationNoExc K` hides its two constants behind a per-`K` `∃ c Cst` with no
control whatever on how they degrade in `K`.

## What this file puts in place

* `KPointNoExcWith cK CstK K` — the same input with the constants as explicit functions of `K`,
  and `kPointNoExc_of_with`, so nothing is weakened and every lap-85 consumer survives.
* `norm_progression_sum_le_class_sum` and `progression_avg_le_of_window` — the quantitative twin
  of `progression_avg_tendsto_of_window`: head, the two boundary points and the halving stack,
  as one explicit inequality in `(J, k₀)` rather than a limit.
-/

open Filter Finset Topology

namespace NormalNumbers

namespace CastingOut

/-! ### The budget layer, retired -/

/-- **The budget buys nothing.**  `QuantDepthElliottGen b` — for any budget `C` whatsoever —
already implies the diagonal limit that `weylLambertTwist_of_depthElliottLL` consumes.

So the remaining obligation is not "find a budget the assembly fits in"; it is the diagonal
itself, and that needs the `K`-point input's constants to be uniform in `K`. -/
theorem quantDepthElliottGen_forces_diagonal {b : ℕ} (H : QuantDepthElliottGen b)
    (P Q j : ℕ) (h : ℤ) (hQ : 0 < Q) (hj0 : 0 < j) (hjQ : j < Q) :
    Tendsto (fun N : ℕ => depthAvg b P Q j h (PairDecouple.depthLL b N) N) atTop (𝓝 0) := by
  obtain ⟨C, η, _, hbd, hlim⟩ := H P Q j h hQ hj0 hjQ
  exact squeeze_zero_norm (fun N => hbd _ N) hlim

/-- The diagonal is *equivalent* to the crux's hypothesis as stated: `DepthDiagonal b` is what
`weylLambertTwist_of_depthElliottLL` takes, and `quantDepthElliottGen_forces_diagonal` says
`QuantDepthElliottGen b → DepthDiagonal b`. -/
def DepthDiagonal (b : ℕ) : Prop :=
  ∀ (P Q j : ℕ) (h : ℤ), 0 < Q → 0 < j → j < Q →
    Tendsto (fun N : ℕ => depthAvg b P Q j h (PairDecouple.depthLL b N) N) atTop (𝓝 0)

/-- The crux from the diagonal — a named wrapper for `weylLambertTwist_of_depthElliottLL`. -/
theorem weylLambertTwist_of_depthDiagonal {b : ℕ} (hb : 3 ≤ b) (H : DepthDiagonal b) :
    WeylLambertTwist b :=
  weylLambertTwist_of_depthElliottLL hb H

/-- `QuantDepthElliottGen` is (at least) as strong as the diagonal. -/
theorem depthDiagonal_of_quantDepthElliottGen {b : ℕ} (H : QuantDepthElliottGen b) :
    DepthDiagonal b :=
  fun P Q j h hQ hj0 hjQ => quantDepthElliottGen_forces_diagonal H P Q j h hQ hj0 hjQ

/-! ### The `K`-point input with its constants named -/

/-- **The `K`-point input, constants explicit.**  `KPointNaturalCorrelationNoExc K` with the
exponent `cK K` and the constant `CstK K` given as functions of the point count, instead of
hidden behind a per-`K` existential.

This is *not* a strengthening at any fixed `K` (`kPointNoExc_of_with`); the point is that the
diagonal `K = depthLL b N` needs to know how `cK` and `CstK` degrade, and the existential form
provably cannot say. -/
def KPointNoExcWith (cK CstK : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ g : Fin K → ℕ → ℂ, (∀ i, IsCoprimeMultiplicativeNat (g i)) →
    (∀ i n, ‖g i n‖ ≤ 1) →
    ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X →
      (∃ i, TTNonPretentious (g i) X L) →
        ∀ N : ℕ, Real.sqrt X ≤ (N : ℝ) → (N : ℝ) ≤ X →
          ∀ (W b : ℕ) (hsh : Fin K → ℕ), 0 < W → (W : ℝ) ≤ L ^ cK K →
            (∀ i, (hsh i : ℝ) ≤ L ^ cK K) → Function.Injective hsh →
            ‖((W : ℝ) / (N : ℝ) : ℝ) •
                ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = b % W),
                  ∏ i : Fin K, g i (n + hsh i)‖
              ≤ CstK K * L ^ (-(cK K))

/-- Nothing is weakened: naming the constants gives back the existential form. -/
theorem kPointNoExc_of_with {cK CstK : ℕ → ℝ} {K : ℕ} (hc : 0 < cK K) (hC : 0 < CstK K)
    (h : KPointNoExcWith cK CstK K) : KPointNaturalCorrelationNoExc K :=
  ⟨cK K, CstK K, hc, hC, h⟩

/-- …and conversely, at any fixed `K` the existential form *is* the named form for some choice
of the two constants.  So the two `Prop`s differ only in what they let a `K`-indexed family
say. -/
theorem exists_with_of_kPointNoExc {K : ℕ} (h : KPointNaturalCorrelationNoExc K) :
    ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧ KPointNoExcWith (fun _ => c) (fun _ => Cst) K := by
  obtain ⟨c, Cst, hc, hCst, hmain⟩ := h
  exact ⟨c, Cst, hc, hCst, hmain⟩

/-! ### The quantitative progression average -/

open scoped Classical in
/-- **Head and the two boundary points, as an inequality.**  The `J`-term progression sum is the
class sum below `Y = M·J + r`, up to a head of at most `r` terms and the two endpoints `0`, `Y`
by which `range Y` and `Ioc 0 Y` differ.  This is the first half of
`progression_avg_tendsto_of_window`, extracted so a *rate* can use it. -/
theorem norm_progression_sum_le_class_sum {g : ℕ → ℂ} (hg : ∀ n, ‖g n‖ ≤ 1)
    {M : ℕ} (hM : 0 < M) (r J : ℕ) (hJ : 1 ≤ J) :
    ‖∑ m ∈ range J, g (M * m + r)‖
      ≤ ((r : ℝ) + 2)
        + ‖∑ n ∈ (Finset.Ioc 0 (M * J + r)).filter (fun n => n % M = r % M), g n‖ := by
  classical
  set Y : ℕ := M * J + r with hY
  have hsplit := class_sum_split hM r J g
  have hhead : ‖∑ n ∈ (range r).filter (fun n => n % M = r % M), g n‖ ≤ (r : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∑ n ∈ (range r).filter (fun n => n % M = r % M), ‖g n‖
        ≤ ∑ _n ∈ (range r).filter (fun n => n % M = r % M), (1 : ℝ) :=
      Finset.sum_le_sum fun n _ => hg n
    refine le_trans h1 ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have := Finset.card_filter_le (range r) (fun n => n % M = r % M)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hrange : ∑ n ∈ (range Y).filter (fun n => n % M = r % M), g n
      = (∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M), g n)
        + ((if (0 : ℕ) % M = r % M then g 0 else 0)
           - (if Y % M = r % M then g Y else 0)) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    have hMJ : 0 < M * J := Nat.mul_pos hM hJ
    have hY0 : 0 < Y := by omega
    have h1 : ∑ n ∈ range Y, (if n % M = r % M then g n else 0)
        = (if (0 : ℕ) % M = r % M then g 0 else 0)
          + ∑ n ∈ Finset.Ico 1 Y, (if n % M = r % M then g n else 0) := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hY0]
    have h2 : ∑ n ∈ Finset.Ioc 0 Y, (if n % M = r % M then g n else 0)
        = (∑ n ∈ Finset.Ico 1 Y, (if n % M = r % M then g n else 0))
          + (if Y % M = r % M then g Y else 0) := by
      rw [show Finset.Ioc 0 Y = Finset.Ico 1 Y ∪ {Y} by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_union, Finset.mem_Ico,
          Finset.mem_singleton]; omega]
      rw [Finset.sum_union (by
        refine Finset.disjoint_left.2 fun n hn hn' => ?_
        rw [Finset.mem_Ico] at hn
        rw [Finset.mem_singleton] at hn'
        omega)]
      simp
    rw [h1, h2]
    ring
  have heq : ∑ m ∈ range J, g (M * m + r)
      = (∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M), g n)
        + ((if (0 : ℕ) % M = r % M then g 0 else 0)
           - (if Y % M = r % M then g Y else 0))
        - ∑ n ∈ (range r).filter (fun n => n % M = r % M), g n := by
    rw [← hrange, hY, hsplit]
    ring
  rw [heq]
  have hb1 : ‖(if (0 : ℕ) % M = r % M then g 0 else 0)‖ ≤ 1 := by
    split
    · exact hg 0
    · simp
  have hb2 : ‖(if Y % M = r % M then g Y else 0)‖ ≤ 1 := by
    split
    · exact hg Y
    · simp
  have hs := norm_sub_le
    ((∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M), g n)
      + ((if (0 : ℕ) % M = r % M then g 0 else 0) - (if Y % M = r % M then g Y else 0)))
    (∑ n ∈ (range r).filter (fun n => n % M = r % M), g n)
  have h3 := norm_add_le
    (∑ n ∈ (Finset.Ioc 0 Y).filter (fun n => n % M = r % M), g n)
    ((if (0 : ℕ) % M = r % M then g 0 else 0) - (if Y % M = r % M then g Y else 0))
  have h4 := norm_sub_le
    ((if (0 : ℕ) % M = r % M then g 0 else 0)) ((if Y % M = r % M then g Y else 0))
  linarith [hhead, hb1, hb2, hs, h3, h4]

open scoped Classical in
/-- **The progression average, quantitatively.**  The twin of
`progression_avg_tendsto_of_window` with the limit replaced by the inequality it came from:
for every `J ≥ 1` and every cut level `k₀`,

    ‖(1/J) ∑_{m<J} g(Mm+r)‖  ≤  [ r + 2 + (log₂ Y + 1) + (Φ(Y/2^{k₀}) + 2^{-k₀})·Y ] / J ,
    Y = M·J + r .

This is what a *rate* needs, and hence what the diagonal needs. -/
theorem progression_avg_le_of_window {g : ℕ → ℂ} (hg : ∀ n, ‖g n‖ ≤ 1) {Φ : ℕ → ℝ}
    (h0 : ∀ a, 0 ≤ Φ a) (h1 : ∀ a, Φ a ≤ 1) (hanti : ∀ {a b : ℕ}, a ≤ b → Φ b ≤ Φ a)
    {M : ℕ} (hM : 0 < M) (r : ℕ)
    (hB : ∀ a : ℕ, ‖∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M), g n‖
        ≤ Φ a * (a : ℝ))
    (J k₀ : ℕ) (hJ : 1 ≤ J) :
    ‖(∑ m ∈ range J, g (M * m + r)) / (J : ℂ)‖
      ≤ ((r : ℝ) + 2 + ((Nat.log 2 (M * J + r) + 1 : ℕ) : ℝ)
          + (Φ ((M * J + r) / 2 ^ k₀) + (1 / 2) ^ k₀) * ((M * J + r : ℕ) : ℝ)) / (J : ℝ) := by
  classical
  have hJR : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  rw [norm_div, Complex.norm_natCast]
  refine div_le_div_of_nonneg_right ?_ hJR.le
  have hhead := norm_progression_sum_le_class_sum hg hM r J hJ
  have hstack := class_sum_le_of_window hg h0 h1 hanti (M := M) r hB (M * J + r) k₀
  linarith

/-! ### The dyadic window bound with an explicit threshold -/

/-- **The `K`-point dyadic window bound, constants and threshold explicit.**
`dyadic_window_bound_K` packages its scale threshold as an unnamed `∃ N₀`; along the diagonal
`K = depthLL b N` that is useless, because `N₀` moves with `K`.  Here the threshold is the
hypothesis `hthr`, which is a condition on `(K, N)` that can be checked along a schedule.

At `X = N²`, `L = (2 log N)^κ`, shifts `h i = i+1`. -/
theorem dyadic_window_bound_with {K : ℕ} (hK : 0 < K) {cK CstK : ℕ → ℝ}
    (h : KPointNoExcWith cK CstK K)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (z 0)) X L)
    {N : ℕ} (hN2 : 2 ≤ N)
    (hthr : max 2 ((K : ℝ) + 1) ≤ (2 * Real.log N) ^ (κ * cK K))
    {M : ℕ} (hM : 0 < M) (r : ℕ) (hML : (M : ℝ) ≤ (2 * Real.log N) ^ (κ * cK K)) :
    ‖∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
        ∏ i : Fin K, z i ^ omegaNat (n + (i : ℕ) + 1)‖
      ≤ CstK K * (2 * Real.log N) ^ (-(κ * cK K)) * (N : ℝ) / (M : ℝ) := by
  have h2L : (2 : ℝ) ≤ (2 * Real.log N) ^ (κ * cK K) := le_trans (le_max_left _ _) hthr
  have hKL : (K : ℝ) + 1 ≤ (2 * Real.log N) ^ (κ * cK K) := le_trans (le_max_right _ _) hthr
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  set X : ℝ := (N : ℝ) ^ 2 with hX
  have hlogX : Real.log X = 2 * Real.log N := by rw [hX, Real.log_pow]; push_cast; ring
  have hX3 : 3 ≤ X := by rw [hX]; nlinarith
  have hbase : (1 : ℝ) ≤ 2 * Real.log N := by linarith
  have hbase0 : (0 : ℝ) ≤ 2 * Real.log N := by linarith
  set L : ℝ := (2 * Real.log N) ^ κ with hLdef
  have hpow : ∀ s : ℝ, L ^ s = (2 * Real.log N) ^ (κ * s) := by
    intro s; rw [hLdef, ← Real.rpow_mul hbase0]
  have hL1 : (1 : ℝ) ≤ L := Real.one_le_rpow hbase hκ.le
  have hLlog : L ≤ Real.log X := by
    rw [hlogX, hLdef]
    calc (2 * Real.log N) ^ κ ≤ (2 * Real.log N) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase hκ1
      _ = 2 * Real.log N := Real.rpow_one _
  have hLκ : L ≤ Real.log X ^ κ := by rw [hlogX]
  have hsqrt : Real.sqrt X = (N : ℝ) := by rw [hX, Real.sqrt_sq hNpos.le]
  have hNX : (N : ℝ) ≤ X := by rw [hX]; nlinarith
  have hshift : ∀ i : Fin K, (((i : ℕ) + 1 : ℕ) : ℝ) ≤ L ^ cK K := by
    intro i
    rw [hpow]
    have : ((i : ℕ) : ℝ) + 1 ≤ (K : ℝ) + 1 := by
      have : ((i : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_of_lt i.isLt)
      linarith
    push_cast
    linarith
  have hspec := h (fun i => zOmegaNat (z i))
    (fun i => isCoprimeMultiplicativeNat_zOmegaNat _)
    (fun i n => norm_zOmegaNat_le_one (hz i) n) X L (by linarith) hL1 hLlog
    ⟨⟨0, hK⟩, hnp X L hX3 hL1 hLκ⟩
    N (by rw [hsqrt]) hNX M r (fun i => (i : ℕ) + 1) hM (by rw [hpow]; exact hML) hshift
    (by
      intro i j hij
      have h' : (i : ℕ) + 1 = (j : ℕ) + 1 := hij
      exact Fin.ext (by omega))
  rw [hpow, mul_neg] at hspec
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hspec
  set S : ℂ := ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
      ∏ i : Fin K, zOmegaNat (z i) (n + ((i : ℕ) + 1)) with hS
  have hSrw : (∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % M = r % M),
      ∏ i : Fin K, z i ^ omegaNat (n + (i : ℕ) + 1)) = S := by
    rw [hS]
    refine Finset.sum_congr rfl fun n _ => Finset.prod_congr rfl fun i _ => ?_
    simp [zOmegaNat, ← add_assoc]
  rw [hSrw]
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [div_mul_eq_mul_div, div_le_iff₀ hNpos] at hspec
  rw [le_div_iff₀ hMpos]
  nlinarith [hspec, norm_nonneg S, hNpos.le, hMpos.le]

/-! ### The explicit per-scale window profile -/

/-- **The per-scale window profile.**  Below the threshold scale `A` the trivial bound `1` is
used — `‖∑_{Ioc a (2a)}‖ ≤ a` holds for every 1-bounded summand — and at or above `A` the
analytic bound of `dyadic_window_bound_with`, capped at `1`.

The cap and the threshold are what make the profile `≤ 1` and **antitone everywhere**, which is
exactly what `class_sum_le_of_window` / `progression_avg_le_of_window` demand.  `A` is a free
parameter: the caller picks it so that `dyadic_window_bound_with`'s hypotheses hold from `A` on,
and along the diagonal `A` is allowed to move with `K`. -/
noncomputable def windowPhi (cK CstK : ℕ → ℝ) (κ : ℝ) (K M A : ℕ) (a : ℕ) : ℝ :=
  if a < A then 1 else min 1 (CstK K * (2 * Real.log a) ^ (-(κ * cK K)) / (M : ℝ))

theorem windowPhi_le_one (cK CstK : ℕ → ℝ) (κ : ℝ) (K M A a : ℕ) :
    windowPhi cK CstK κ K M A a ≤ 1 := by
  unfold windowPhi
  split
  · exact le_refl 1
  · exact min_le_left _ _

theorem windowPhi_nonneg {cK CstK : ℕ → ℝ} {κ : ℝ} {K M A : ℕ} (hA : 2 ≤ A)
    (hC : 0 ≤ CstK K) (a : ℕ) : 0 ≤ windowPhi cK CstK κ K M A a := by
  unfold windowPhi
  split
  · norm_num
  · rename_i hnot
    have ha : A ≤ a := Nat.not_lt.1 hnot
    have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast le_trans hA ha
    have hlog : 0 < Real.log a := Real.log_pos (by linarith)
    have hb : (0 : ℝ) < 2 * Real.log a := by linarith
    have hrp : (0 : ℝ) < (2 * Real.log a) ^ (-(κ * cK K)) := Real.rpow_pos_of_pos hb _
    exact le_min (by norm_num)
      (div_nonneg (mul_nonneg hC hrp.le) (Nat.cast_nonneg _))

/-- **The profile is antitone.**  Below `A` it is constantly `1`; above, the base `2 log a`
increases and the exponent `-(κ·cK K)` is `≤ 0`. -/
theorem windowPhi_antitone {cK CstK : ℕ → ℝ} {κ : ℝ} {K M A : ℕ} (hA : 2 ≤ A)
    (hC : 0 ≤ CstK K) (hz : 0 ≤ κ * cK K) {a b : ℕ} (hab : a ≤ b) :
    windowPhi cK CstK κ K M A b ≤ windowPhi cK CstK κ K M A a := by
  unfold windowPhi
  by_cases ha : a < A
  · rw [if_pos ha]
    split
    · exact le_refl 1
    · exact min_le_left _ _
  · have hbA : ¬ b < A := by omega
    rw [if_neg ha, if_neg hbA]
    refine min_le_min (le_refl 1) ?_
    have haA : A ≤ a := Nat.not_lt.1 ha
    have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast le_trans hA haA
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hloga : 0 < Real.log a := Real.log_pos (by linarith)
    have hlogab : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab'
    have hbase : (0 : ℝ) < 2 * Real.log a := by linarith
    have hstep : (2 * Real.log b) ^ (-(κ * cK K)) ≤ (2 * Real.log a) ^ (-(κ * cK K)) :=
      Real.rpow_le_rpow_of_nonpos hbase (by linarith) (by linarith)
    have := mul_le_mul_of_nonneg_left hstep hC
    exact div_le_div_of_nonneg_right this (Nat.cast_nonneg _)

open scoped Classical in
/-- **The profile supplies the `hB` hypothesis.**  Below `A` by the trivial count of the dyadic
window; at or above `A` by the analytic bound, capped. -/
theorem windowPhi_window_bound {cK CstK : ℕ → ℝ} {κ : ℝ} {K M A : ℕ} {f : ℕ → ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) {r : ℕ}
    (hwin : ∀ a : ℕ, A ≤ a →
      ‖∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M), f n‖
        ≤ CstK K * (2 * Real.log a) ^ (-(κ * cK K)) * (a : ℝ) / (M : ℝ))
    (a : ℕ) :
    ‖∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M), f n‖
      ≤ windowPhi cK CstK κ K M A a * (a : ℝ) := by
  classical
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have htriv : ‖∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M), f n‖
      ≤ (a : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M), ‖f n‖
        ≤ ∑ _n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M), (1 : ℝ) :=
      Finset.sum_le_sum fun n _ => hf n
    refine le_trans h1 ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc := Finset.card_filter_le (Finset.Ioc a (2 * a)) (fun n => n % M = r % M)
    rw [Nat.card_Ioc, show 2 * a - a = a by omega] at hc
    exact_mod_cast hc
  unfold windowPhi
  split
  · simpa using htriv
  · rename_i hnot
    have haA : A ≤ a := Nat.not_lt.1 hnot
    rcases le_total (1 : ℝ) (CstK K * (2 * Real.log a) ^ (-(κ * cK K)) / (M : ℝ)) with hcase | hcase
    · rw [min_eq_left hcase]
      simpa using htriv
    · rw [min_eq_right hcase]
      have := hwin a haA
      calc ‖∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M), f n‖
          ≤ CstK K * (2 * Real.log a) ^ (-(κ * cK K)) * (a : ℝ) / (M : ℝ) := this
        _ = CstK K * (2 * Real.log a) ^ (-(κ * cK K)) / (M : ℝ) * (a : ℝ) := by ring

#print axioms NormalNumbers.CastingOut.quantDepthElliottGen_forces_diagonal
#print axioms NormalNumbers.CastingOut.weylLambertTwist_of_depthDiagonal
#print axioms NormalNumbers.CastingOut.kPointNoExc_of_with
#print axioms NormalNumbers.CastingOut.norm_progression_sum_le_class_sum
#print axioms NormalNumbers.CastingOut.progression_avg_le_of_window
#print axioms NormalNumbers.CastingOut.dyadic_window_bound_with
#print axioms NormalNumbers.CastingOut.windowPhi_antitone
#print axioms NormalNumbers.CastingOut.windowPhi_window_bound

end CastingOut

end NormalNumbers
