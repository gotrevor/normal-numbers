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

/-! ### From the window profile to an explicit `depthAvg` majorant -/

/-- The number of terms of the progression `M·m + r` that lie below `N`. -/
def progCount (M r N : ℕ) : ℕ := (N - 1 - r) / M + 1

theorem progCount_pos (M r N : ℕ) : 0 < progCount M r N := Nat.succ_pos _

/-- The progression's top term straddles `N`: `N ≤ M·progCount + r ≤ N + M`. -/
theorem progCount_bounds {M : ℕ} (hM : 0 < M) {r N : ℕ} (hr : r < N) :
    N ≤ M * progCount M r N + r ∧ M * progCount M r N + r ≤ N + M := by
  have h1 := Nat.div_add_mod (N - 1 - r) M
  have h2 := Nat.mod_lt (N - 1 - r) hM
  have h3 : M * progCount M r N = M * ((N - 1 - r) / M) + M := by
    unfold progCount; ring
  rw [h3]
  generalize M * ((N - 1 - r) / M) = X at h1 ⊢
  generalize (N - 1 - r) % M = Y at h1 h2
  omega

open scoped Classical in
/-- **One residue class, quantitatively.**  The progression sum below `N` — which is what
`norm_depthAvg_le_omega_progressions` produces — bounded by the halving stack evaluated at the
scale `N` itself, with the `Y = M·progCount + r` straddle absorbed into the `+ M`. -/
theorem norm_progression_below_le {g : ℕ → ℂ} (hg : ∀ n, ‖g n‖ ≤ 1) {Φ : ℕ → ℝ}
    (h0 : ∀ a, 0 ≤ Φ a) (h1 : ∀ a, Φ a ≤ 1) (hanti : ∀ {a b : ℕ}, a ≤ b → Φ b ≤ Φ a)
    {M : ℕ} (hM : 0 < M)
    (hB : ∀ r a : ℕ, ‖∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M), g n‖
        ≤ Φ a * (a : ℝ))
    {r N : ℕ} (hr : r < N) (k₀ : ℕ) :
    ‖∑ m ∈ (range N).filter (fun m => M * m + r < N), g (M * m + r)‖
      ≤ ((r : ℝ) + 2) + ((Nat.log 2 (N + M) + 1 : ℕ) : ℝ)
        + (Φ (N / 2 ^ k₀) + (1 / 2) ^ k₀) * ((N : ℝ) + (M : ℝ)) := by
  classical
  obtain ⟨hlow, hhigh⟩ := progCount_bounds hM hr
  rw [filter_linear_lt_eq_range hM hr, show (N - 1 - r) / M + 1 = progCount M r N from rfl]
  have hstep1 := norm_progression_sum_le_class_sum hg hM r (progCount M r N)
    (progCount_pos M r N)
  have hstep2 := class_sum_le_of_window hg h0 h1 hanti (M := M) r (hB r)
    (M * progCount M r N + r) k₀
  have hΦ : Φ ((M * progCount M r N + r) / 2 ^ k₀) ≤ Φ (N / 2 ^ k₀) :=
    hanti (Nat.div_le_div_right hlow)
  have hlen : ((M * progCount M r N + r : ℕ) : ℝ) ≤ (N : ℝ) + (M : ℝ) := by
    have hc : ((M * progCount M r N + r : ℕ) : ℝ) ≤ ((N + M : ℕ) : ℝ) := by exact_mod_cast hhigh
    push_cast at hc ⊢; linarith
  have hlogm : ((Nat.log 2 (M * progCount M r N + r) + 1 : ℕ) : ℝ)
      ≤ ((Nat.log 2 (N + M) + 1 : ℕ) : ℝ) := by
    have := Nat.log_mono_right (b := 2) hhigh
    exact_mod_cast Nat.succ_le_succ this
  have hhalf : (0 : ℝ) < (1 / 2 : ℝ) ^ k₀ := by positivity
  have hnnN : (0 : ℝ) ≤ Φ (N / 2 ^ k₀) + (1 / 2) ^ k₀ := by
    have := h0 (N / 2 ^ k₀); linarith
  have hkey : (Φ ((M * progCount M r N + r) / 2 ^ k₀) + (1 / 2) ^ k₀)
        * ((M * progCount M r N + r : ℕ) : ℝ)
      ≤ (Φ (N / 2 ^ k₀) + (1 / 2) ^ k₀) * ((N : ℝ) + (M : ℝ)) :=
    mul_le_mul (by linarith) hlen (by positivity) hnnN
  linarith

open scoped Classical in
/-- **The explicit `depthAvg` majorant.**  Everything downstream of the window profile, as one
inequality: the `M₀ = Q·primorial P` residue classes, the head of each, the halving stack cut at
`k₀`, and the `1/N` normalisation.  `M₀` is fixed before `N`, so the `M₀²` head term is `O(1/N)`
and the rate is carried entirely by `Φ (N / 2 ^ k₀) + 2^{-k₀}`. -/
theorem depthAvg_le_of_window {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ) {D : ℕ}
    {Φ : ℕ → ℝ} (h0 : ∀ a, 0 ≤ Φ a) (h1 : ∀ a, Φ a ≤ 1)
    (hanti : ∀ {a b : ℕ}, a ≤ b → Φ b ≤ Φ a)
    (hB : ∀ r a : ℕ, ‖∑ n ∈ (Finset.Ioc a (2 * a)).filter
          (fun n => n % (Q * primorial P) = r % (Q * primorial P)),
            ∏ i ∈ range D, depthRoot b hh i ^ omegaNat (n + i + 1)‖ ≤ Φ a * (a : ℝ))
    {N : ℕ} (hN : Q * primorial P < N) (k₀ : ℕ) :
    ‖depthAvg b P Q j hh D N‖
      ≤ ((Q * primorial P : ℕ) : ℝ)
          * ((((Q * primorial P : ℕ) : ℝ) + 2) + ((Nat.log 2 (N + Q * primorial P) + 1 : ℕ) : ℝ)
            + (Φ (N / 2 ^ k₀) + (1 / 2) ^ k₀) * ((N : ℝ) + ((Q * primorial P : ℕ) : ℝ)))
        / (N : ℝ) := by
  classical
  set M : ℕ := Q * primorial P with hMdef
  have hM0 : 0 < M := Nat.mul_pos hQ (primorial_pos P)
  set g : ℕ → ℂ := fun n => ∏ i ∈ range D, depthRoot b hh i ^ omegaNat (n + i + 1) with hgdef
  have hg : ∀ n, ‖g n‖ ≤ 1 := by
    intro n
    simp only [hgdef, norm_prod, norm_pow]
    have : ∀ i ∈ range D, ‖depthRoot b hh i‖ ^ omegaNat (n + i + 1) = 1 := by
      intro i _
      rw [show ‖depthRoot b hh i‖ = 1 from by rw [depthRoot]; exact norm_ee_real _, one_pow]
    rw [Finset.prod_congr rfl this, Finset.prod_const_one]
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  refine le_trans (norm_depthAvg_le_omega_progressions hQ b P j hh D N) ?_
  refine div_le_div_of_nonneg_right ?_ hN0.le
  have hterm : ∀ r ∈ range M,
      ‖∑ m ∈ (range N).filter (fun m => M * m + r < N),
          ∏ i ∈ range D, depthRoot b hh i ^ omegaNat (M * m + r + i + 1)‖
        ≤ ((M : ℝ) + 2) + ((Nat.log 2 (N + M) + 1 : ℕ) : ℝ)
          + (Φ (N / 2 ^ k₀) + (1 / 2) ^ k₀) * ((N : ℝ) + (M : ℝ)) := by
    intro r hrm
    have hrM : r < M := Finset.mem_range.1 hrm
    have hrN : r < N := by omega
    have := norm_progression_below_le hg h0 h1 hanti hM0 hB hrN k₀
    have hrR : (r : ℝ) ≤ (M : ℝ) := by exact_mod_cast hrM.le
    refine le_trans (le_of_eq ?_) (le_trans this (by linarith))
    rfl
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### The splice: the named input supplies the profile -/

open scoped Classical in
/-- **`dyadic_window_bound_with` supplies `windowPhi`'s analytic branch.**  One threshold
condition at the single scale `A` propagates to every `a ≥ A`, because `a ↦ (2 log a)^(κ·cK K)`
is increasing.  `A` may — and along the diagonal must — depend on `K`. -/
theorem windowPhi_hwin {K : ℕ} (hK : 0 < K) {cK CstK : ℕ → ℝ} (hc : 0 < cK K)
    (h : KPointNoExcWith cK CstK K)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (z 0)) X L)
    {M A : ℕ} (hM : 0 < M) (hA2 : 2 ≤ A)
    (hAthr : max (max 2 ((K : ℝ) + 1)) (M : ℝ) ≤ (2 * Real.log A) ^ (κ * cK K))
    (r : ℕ) {a : ℕ} (haA : A ≤ a) :
    ‖∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M),
        ∏ i ∈ range K, z i ^ omegaNat (n + i + 1)‖
      ≤ CstK K * (2 * Real.log a) ^ (-(κ * cK K)) * (a : ℝ) / (M : ℝ) := by
  classical
  have ha2 : 2 ≤ a := le_trans hA2 haA
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA2
  have hAa : (A : ℝ) ≤ (a : ℝ) := by exact_mod_cast haA
  have hlogA : Real.log 2 ≤ Real.log A := Real.log_le_log (by norm_num) hAR
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogAa : Real.log A ≤ Real.log a := Real.log_le_log (by linarith) hAa
  have hmono : (2 * Real.log A) ^ (κ * cK K) ≤ (2 * Real.log a) ^ (κ * cK K) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (mul_pos hκ hc).le
  have hthr : max 2 ((K : ℝ) + 1) ≤ (2 * Real.log a) ^ (κ * cK K) :=
    le_trans (le_trans (le_max_left _ _) hAthr) hmono
  have hML : (M : ℝ) ≤ (2 * Real.log a) ^ (κ * cK K) :=
    le_trans (le_trans (le_max_right _ _) hAthr) hmono
  have hrw : ∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M),
        ∏ i ∈ range K, z i ^ omegaNat (n + i + 1)
      = ∑ n ∈ (Finset.Ioc a (2 * a)).filter (fun n => n % M = r % M),
        ∏ i : Fin K, z i ^ omegaNat (n + (i : ℕ) + 1) :=
    Finset.sum_congr rfl fun n _ =>
      (Fin.prod_univ_eq_prod_range (fun i => z i ^ omegaNat (n + i + 1)) K).symm
  rw [hrw]
  exact dyadic_window_bound_with hK h z hz hκ hκ1 hnp ha2 hthr hM r hML

open scoped Classical in
/-- **The explicit `depthAvg` majorant from the named input, constants and all.**
Everything of laps 84–87 in one statement: the `K`-point input with named constants, the
archimedean certificate, the window profile, the halving stack cut at `k₀`, the `M₀` residue
classes and the `1/N`.  Only three quantities move with `K`: `cK K`, `CstK K` and the threshold
scale `A`.  That is exactly the data the diagonal `K = depthLL b N` needs. -/
theorem depthAvg_le_with {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ) {K : ℕ} (hK : 0 < K)
    {cK CstK : ℕ → ℝ} (hc : 0 < cK K) (hC : 0 < CstK K)
    (hin : KPointNoExcWith cK CstK K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b hh 0)) X L)
    {A : ℕ} (hA2 : 2 ≤ A)
    (hAthr : max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log A) ^ (κ * cK K))
    {N : ℕ} (hN : Q * primorial P < N) (k₀ : ℕ) :
    ‖depthAvg b P Q j hh K N‖
      ≤ ((Q * primorial P : ℕ) : ℝ)
          * ((((Q * primorial P : ℕ) : ℝ) + 2)
              + ((Nat.log 2 (N + Q * primorial P) + 1 : ℕ) : ℝ)
            + (windowPhi cK CstK κ K (Q * primorial P) A (N / 2 ^ k₀) + (1 / 2) ^ k₀)
                * ((N : ℝ) + ((Q * primorial P : ℕ) : ℝ)))
        / (N : ℝ) := by
  classical
  have hM0 : 0 < Q * primorial P := Nat.mul_pos hQ (primorial_pos P)
  have hz : ∀ i, ‖depthRoot b hh i‖ = 1 := fun i => by rw [depthRoot]; exact norm_ee_real _
  have hf : ∀ n : ℕ, ‖∏ i ∈ range K, depthRoot b hh i ^ omegaNat (n + i + 1)‖ ≤ 1 := by
    intro n
    simp only [norm_prod, norm_pow]
    have hone : ∀ i ∈ range K, ‖depthRoot b hh i‖ ^ omegaNat (n + i + 1) = 1 := by
      intro i _
      rw [hz i, one_pow]
    rw [Finset.prod_congr rfl hone, Finset.prod_const_one]
  refine depthAvg_le_of_window hQ P j hh
    (windowPhi_nonneg hA2 hC.le)
    (fun a => windowPhi_le_one cK CstK κ K (Q * primorial P) A a)
    (fun {x y} hxy => windowPhi_antitone hA2 hC.le (mul_pos hκ hc).le hxy)
    (fun r a => windowPhi_window_bound hf
      (fun a' ha' => windowPhi_hwin hK hc hin (fun i => depthRoot b hh i) hz hκ hκ1 hnp
        hM0 hA2 hAthr r ha') a)
    hN k₀

/-! ### The diagonal -/

theorem depthLL_pos (b N : ℕ) : 0 < PairDecouple.depthLL b N := by
  rw [PairDecouple.depthLL]; exact Nat.succ_pos _

/-- `(log₂ Y + 1)/Y → 0` — the halving stack's own head cost is negligible. -/
theorem tendsto_natLog_succ_div :
    Tendsto (fun Y : ℕ => ((Nat.log 2 Y + 1 : ℕ) : ℝ) / (Y : ℝ)) atTop (𝓝 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogdiv : Tendsto (fun Y : ℕ => (Real.log Y / Real.log 2 + 1) / (Y : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h2 : Tendsto (fun Y : ℕ => Real.log Y / (Y : ℝ)) atTop (𝓝 0) :=
      h1.comp tendsto_natCast_atTop_atTop
    have h3 : Tendsto (fun Y : ℕ => (1 : ℝ) / (Y : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h4 := (h2.div_const (Real.log 2)).add h3
    simp only [zero_div, zero_add] at h4
    refine h4.congr fun Y => ?_
    field_simp
  refine squeeze_zero' (Filter.Eventually.of_forall fun Y => by positivity)
    (Filter.eventually_atTop.2 ⟨1, fun Y hY => ?_⟩) hlogdiv
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hYpos : (0 : ℝ) < (Y : ℝ) := by linarith
  refine div_le_div_of_nonneg_right ?_ hYpos.le
  have hpow : (2 : ℕ) ^ Nat.log 2 Y ≤ Y := Nat.pow_log_le_self 2 (by omega)
  have hpowR : ((2 : ℝ)) ^ (Nat.log 2 Y) ≤ (Y : ℝ) := by exact_mod_cast hpow
  have hle : (Nat.log 2 Y : ℝ) * Real.log 2 ≤ Real.log Y := by
    have := Real.log_le_log (by positivity) hpowR
    rwa [Real.log_pow] at this
  push_cast
  rw [div_add' _ _ _ (ne_of_gt hlog2), le_div_iff₀ hlog2]
  nlinarith [hle, hlog2]

/-- `(log₂(N+c) + 1)/N → 0` for any fixed shift `c`. -/
theorem tendsto_natLog_shift_div (c : ℕ) :
    Tendsto (fun N : ℕ => ((Nat.log 2 (N + c) + 1 : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun N : ℕ => N + c) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_add_right N c) tendsto_id
  have hcomp : Tendsto (fun N : ℕ => ((Nat.log 2 (N + c) + 1 : ℕ) : ℝ) / ((N + c : ℕ) : ℝ))
      atTop (𝓝 0) := tendsto_natLog_succ_div.comp hshift
  have hmul := hcomp.const_mul (2 : ℝ)
  rw [mul_zero] at hmul
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => by positivity)
    (Filter.eventually_atTop.2 ⟨c + 1, fun N hN => ?_⟩) hmul
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hNc : ((N + c : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    have : (N + c : ℕ) ≤ 2 * N := by omega
    exact_mod_cast this
  have hNcpos : (0 : ℝ) < ((N + c : ℕ) : ℝ) := by
    have : 0 < N + c := by omega
    exact_mod_cast this
  have hnum : (0 : ℝ) ≤ ((Nat.log 2 (N + c) + 1 : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ hN0]
  have hkey : ((Nat.log 2 (N + c) + 1 : ℕ) : ℝ) / ((N + c : ℕ) : ℝ) * (2 * (N : ℝ))
      ≥ ((Nat.log 2 (N + c) + 1 : ℕ) : ℝ) / ((N + c : ℕ) : ℝ) * ((N + c : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hNc (by positivity)
  rw [div_mul_cancel₀ _ (ne_of_gt hNcpos)] at hkey
  linarith

open scoped Classical in
/-- **THE DIAGONAL, from a `K`-uniform input.**  `depthAvg_le_with` instantiated at
`K = depthLL b N`.  Everything but one hypothesis is bookkeeping that dies under `1/N`:
the `M₀²` head, the `log₂` head, and the `(N+M₀)/N → 1` rescaling.  The single surviving
hypothesis is `hsched`, the *schedule compatibility* of the profile —

    windowPhi cK CstK κ (depthLL b N) M₀ (Athr (depthLL b N)) (N / 2^{k₀ N}) + 2^{-k₀ N} → 0 ,

which is precisely the uniformity the per-`K` existential could not express (lap 87 F2). -/
theorem depthAvg_diag_tendsto_of_unif {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    {cK CstK : ℕ → ℝ} (hc : ∀ K, 0 < cK K) (hC : ∀ K, 0 < CstK K)
    (hin : ∀ K, KPointNoExcWith cK CstK K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b hh 0)) X L)
    (Athr : ℕ → ℕ) (hA2 : ∀ K, 2 ≤ Athr K)
    (hAthr : ∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * cK K))
    (k₀ : ℕ → ℕ)
    (hsched : Tendsto (fun N : ℕ =>
        windowPhi cK CstK κ (PairDecouple.depthLL b N) (Q * primorial P)
            (Athr (PairDecouple.depthLL b N)) (N / 2 ^ k₀ N)
          + (1 / 2 : ℝ) ^ k₀ N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh (PairDecouple.depthLL b N) N) atTop (𝓝 0) := by
  classical
  have hM0 : 0 < Q * primorial P := Nat.mul_pos hQ (primorial_pos P)
  set M₀ : ℕ := Q * primorial P with hM₀def
  set Ψ : ℕ → ℝ := fun N =>
    windowPhi cK CstK κ (PairDecouple.depthLL b N) M₀ (Athr (PairDecouple.depthLL b N))
        (N / 2 ^ k₀ N)
      + (1 / 2 : ℝ) ^ k₀ N with hΨdef
  -- the three pieces of the majorant
  have hT1 : Tendsto (fun N : ℕ => (M₀ : ℝ) * (((M₀ : ℝ) + 2)) / (N : ℝ)) atTop (𝓝 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul ((M₀ : ℝ) * ((M₀ : ℝ) + 2))
    rw [mul_zero] at this
    exact this.congr fun N => by ring
  have hT2 : Tendsto
      (fun N : ℕ => (M₀ : ℝ) * (((Nat.log 2 (N + M₀) + 1 : ℕ) : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
    have := (tendsto_natLog_shift_div M₀).const_mul ((M₀ : ℝ))
    rwa [mul_zero] at this
  have hone : Tendsto (fun N : ℕ => 1 + (M₀ : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul ((M₀ : ℝ))
    rw [mul_zero] at this
    have h2 : Tendsto (fun N : ℕ => (M₀ : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      this.congr fun N => by ring
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add h2
  have hT3 : Tendsto (fun N : ℕ => (M₀ : ℝ) * Ψ N * (1 + (M₀ : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
    have hΨ0 : Tendsto Ψ atTop (𝓝 0) := hsched
    have := ((hΨ0.const_mul ((M₀ : ℝ))).mul hone)
    simpa using this
  have hmaj : Tendsto (fun N : ℕ =>
      (M₀ : ℝ) * (((M₀ : ℝ) + 2)) / (N : ℝ)
        + (M₀ : ℝ) * (((Nat.log 2 (N + M₀) + 1 : ℕ) : ℝ) / (N : ℝ))
        + (M₀ : ℝ) * Ψ N * (1 + (M₀ : ℝ) / (N : ℝ))) atTop (𝓝 0) := by
    simpa using (hT1.add hT2).add hT3
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [Filter.eventually_ge_atTop (M₀ + 1)] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hstep := depthAvg_le_with hQ P j hh (depthLL_pos b N) (hc _) (hC _) (hin _)
    hκ hκ1 hnp (hA2 _) (hAthr _) (show M₀ < N by omega) (k₀ N)
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  ring

theorem depthAvg_gen_tendsto_of_unif {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    {cK CstK : ℕ → ℝ} (hc : ∀ K, 0 < cK K) (hC : ∀ K, 0 < CstK K)
    (KN : ℕ → ℕ) (hKN : ∀ N, 0 < KN N)
    (hin : ∀ K, KPointNoExcWith cK CstK K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b hh 0)) X L)
    (Athr : ℕ → ℕ) (hA2 : ∀ K, 2 ≤ Athr K)
    (hAthr : ∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * cK K))
    (k₀ : ℕ → ℕ)
    (hsched : Tendsto (fun N : ℕ =>
        windowPhi cK CstK κ (KN N) (Q * primorial P)
            (Athr (KN N)) (N / 2 ^ k₀ N)
          + (1 / 2 : ℝ) ^ k₀ N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh (KN N) N) atTop (𝓝 0) := by
  classical
  have hM0 : 0 < Q * primorial P := Nat.mul_pos hQ (primorial_pos P)
  set M₀ : ℕ := Q * primorial P with hM₀def
  set Ψ : ℕ → ℝ := fun N =>
    windowPhi cK CstK κ (KN N) M₀ (Athr (KN N))
        (N / 2 ^ k₀ N)
      + (1 / 2 : ℝ) ^ k₀ N with hΨdef
  -- the three pieces of the majorant
  have hT1 : Tendsto (fun N : ℕ => (M₀ : ℝ) * (((M₀ : ℝ) + 2)) / (N : ℝ)) atTop (𝓝 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul ((M₀ : ℝ) * ((M₀ : ℝ) + 2))
    rw [mul_zero] at this
    exact this.congr fun N => by ring
  have hT2 : Tendsto
      (fun N : ℕ => (M₀ : ℝ) * (((Nat.log 2 (N + M₀) + 1 : ℕ) : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
    have := (tendsto_natLog_shift_div M₀).const_mul ((M₀ : ℝ))
    rwa [mul_zero] at this
  have hone : Tendsto (fun N : ℕ => 1 + (M₀ : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul ((M₀ : ℝ))
    rw [mul_zero] at this
    have h2 : Tendsto (fun N : ℕ => (M₀ : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      this.congr fun N => by ring
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add h2
  have hT3 : Tendsto (fun N : ℕ => (M₀ : ℝ) * Ψ N * (1 + (M₀ : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
    have hΨ0 : Tendsto Ψ atTop (𝓝 0) := hsched
    have := ((hΨ0.const_mul ((M₀ : ℝ))).mul hone)
    simpa using this
  have hmaj : Tendsto (fun N : ℕ =>
      (M₀ : ℝ) * (((M₀ : ℝ) + 2)) / (N : ℝ)
        + (M₀ : ℝ) * (((Nat.log 2 (N + M₀) + 1 : ℕ) : ℝ) / (N : ℝ))
        + (M₀ : ℝ) * Ψ N * (1 + (M₀ : ℝ) / (N : ℝ))) atTop (𝓝 0) := by
    simpa using (hT1.add hT2).add hT3
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [Filter.eventually_ge_atTop (M₀ + 1)] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hstep := depthAvg_le_with hQ P j hh (hKN N) (hc _) (hC _) (hin _)
    hκ hκ1 hnp (hA2 _) (hAthr _) (show M₀ < N by omega) (k₀ N)
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  ring


/-! ### Making the schedule hypothesis checkable -/

/-- **Step 1: the profile's limit is a scalar rate.**  Once the scale `aN N` has passed the
threshold `AN N`, the `min` and the `if` are inert and `windowPhi` is just its analytic branch. -/
theorem windowPhi_diag_tendsto {cK CstK : ℕ → ℝ} {κ : ℝ} {M₀ : ℕ}
    (KN AN aN : ℕ → ℕ) (hA2 : ∀ N, 2 ≤ AN N) (hC : ∀ K, 0 ≤ CstK K)
    (hA : ∀ᶠ N : ℕ in atTop, AN N ≤ aN N)
    (hrate : Tendsto (fun N : ℕ =>
        CstK (KN N) * (2 * Real.log (aN N)) ^ (-(κ * cK (KN N))) / (M₀ : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => windowPhi cK CstK κ (KN N) M₀ (AN N) (aN N)) atTop (𝓝 0) := by
  refine squeeze_zero' (Filter.Eventually.of_forall
    fun N => windowPhi_nonneg (hA2 N) (hC (KN N)) (aN N)) ?_ hrate
  filter_upwards [hA] with N hN
  unfold windowPhi
  rw [if_neg (by omega)]
  exact min_le_right _ _

/-- **Step 2: the scalar rate is an exponent going to `-∞`.**  `Cst·x^{-e} = exp(log Cst − e log x)`,
so the whole question is whether the constant's logarithm is beaten by the saving. -/
theorem rate_tendsto_of_exponent {cK CstK : ℕ → ℝ} (hC : ∀ K, 0 < CstK K) {κ : ℝ} {M₀ : ℕ}
    (KN aN : ℕ → ℕ)
    (hbase : ∀ᶠ N : ℕ in atTop, 0 < 2 * Real.log (aN N))
    (hexp : Tendsto (fun N : ℕ =>
        Real.log (CstK (KN N)) - κ * cK (KN N) * Real.log (2 * Real.log (aN N)))
      atTop atBot) :
    Tendsto (fun N : ℕ =>
        CstK (KN N) * (2 * Real.log (aN N)) ^ (-(κ * cK (KN N))) / (M₀ : ℝ)) atTop (𝓝 0) := by
  have hexp0 : Tendsto (fun N : ℕ => Real.exp
      (Real.log (CstK (KN N)) - κ * cK (KN N) * Real.log (2 * Real.log (aN N))))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hexp
  have hdiv := hexp0.div_const ((M₀ : ℝ))
  rw [zero_div] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [hbase] with N hN
  rw [Real.exp_sub, Real.exp_log (hC (KN N)), Real.rpow_def_of_pos hN,
    show Real.log (2 * Real.log (aN N)) * -(κ * cK (KN N))
      = -(κ * cK (KN N) * Real.log (2 * Real.log (aN N))) from by ring, Real.exp_neg]
  ring

/-- **Step 3, the concrete profile: a `K`-UNIFORM input closes the crux.**  With the exponent and
the constant independent of `K`, the exponent of Step 2 is `log Cst₀ − κc₀ log(2 log a) → −∞`
outright: no arithmetic about the schedule is needed at all. -/
theorem exponent_tendsto_atBot_of_uniform {c₀ Cst₀ : ℝ} (hc₀ : 0 < c₀) {κ : ℝ} (hκ : 0 < κ)
    (KN aN : ℕ → ℕ) (haN : Tendsto aN atTop atTop) :
    Tendsto (fun N : ℕ =>
        Real.log ((fun _ : ℕ => Cst₀) (KN N))
          - κ * (fun _ : ℕ => c₀) (KN N) * Real.log (2 * Real.log (aN N)))
      atTop atBot := by
  have h1 : Tendsto (fun N : ℕ => ((aN N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp haN
  have h2 : Tendsto (fun N : ℕ => Real.log (aN N)) atTop atTop :=
    Real.tendsto_log_atTop.comp h1
  have h3 : Tendsto (fun N : ℕ => 2 * Real.log (aN N)) atTop atTop :=
    h2.const_mul_atTop (by norm_num)
  have h4 : Tendsto (fun N : ℕ => Real.log (2 * Real.log (aN N))) atTop atTop :=
    Real.tendsto_log_atTop.comp h3
  have h5 : Tendsto (fun N : ℕ => κ * c₀ * Real.log (2 * Real.log (aN N))) atTop atTop :=
    h4.const_mul_atTop (by positivity)
  have h6 : Tendsto (fun N : ℕ => -(κ * c₀ * Real.log (2 * Real.log (aN N)))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h5
  have h7 := Filter.tendsto_atBot_add_const_left atTop (Real.log Cst₀) h6
  exact h7.congr fun N => by simp [sub_eq_add_neg]

/-- **The crux from a `K`-UNIFORM input, assembled.**  `KPointNoExcWith` with constants that do
not degrade in `K` at all — the strongest shape of the named open problem — gives the diagonal
for free, with no schedule arithmetic: the only remaining hypotheses are that the cut level and
the cut scale both grow, and that the (fixed) threshold sequence is eventually passed. -/
theorem depthAvg_diag_tendsto_of_uniform {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    {c₀ Cst₀ : ℝ} (hc₀ : 0 < c₀) (hCst₀ : 0 < Cst₀)
    (hin : ∀ K, KPointNoExcWith (fun _ => c₀) (fun _ => Cst₀) K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b hh 0)) X L)
    (Athr : ℕ → ℕ) (hA2 : ∀ K, 2 ≤ Athr K)
    (hAthr : ∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * c₀))
    (k₀ : ℕ → ℕ) (hk₀ : Tendsto k₀ atTop atTop)
    (hscale : Tendsto (fun N : ℕ => N / 2 ^ k₀ N) atTop atTop)
    (hAle : ∀ᶠ N : ℕ in atTop, Athr (PairDecouple.depthLL b N) ≤ N / 2 ^ k₀ N) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh (PairDecouple.depthLL b N) N) atTop (𝓝 0) := by
  have hbase : ∀ᶠ N : ℕ in atTop, 0 < 2 * Real.log ((N / 2 ^ k₀ N : ℕ) : ℝ) := by
    filter_upwards [hscale.eventually_ge_atTop 2] with N hN
    have h2 : (2 : ℝ) ≤ ((N / 2 ^ k₀ N : ℕ) : ℝ) := by exact_mod_cast hN
    have hlog : 0 < Real.log ((N / 2 ^ k₀ N : ℕ) : ℝ) := Real.log_pos (by linarith)
    linarith
  have hrate := rate_tendsto_of_exponent (cK := fun _ => c₀) (CstK := fun _ => Cst₀)
    (fun _ => hCst₀) (κ := κ) (M₀ := Q * primorial P)
    (fun N => PairDecouple.depthLL b N) (fun N => N / 2 ^ k₀ N) hbase
    (exponent_tendsto_atBot_of_uniform hc₀ hκ (fun N => PairDecouple.depthLL b N)
      (fun N => N / 2 ^ k₀ N) hscale)
  have hΦ := windowPhi_diag_tendsto (cK := fun _ => c₀) (CstK := fun _ => Cst₀) (κ := κ)
    (M₀ := Q * primorial P) (fun N => PairDecouple.depthLL b N)
    (fun N => Athr (PairDecouple.depthLL b N)) (fun N => N / 2 ^ k₀ N)
    (fun N => hA2 _) (fun _ => hCst₀.le) hAle hrate
  have hhalf : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ k₀ N) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hk₀
  refine depthAvg_diag_tendsto_of_unif hQ P j hh (fun _ => hc₀) (fun _ => hCst₀) hin
    hκ hκ1 hnp Athr hA2 hAthr k₀ ?_
  simpa using hΦ.add hhalf

/-! ### The DEGRADING profile — the realistic shape of the input

The `K`-uniform input of `depthAvg_diag_tendsto_of_uniform` is the strongest conceivable form of
`KPointNoExcWith`; nothing in TT's proof gives it.  The honest shape lets both constants degrade
polynomially in `K`:

    cK   K = c₀ / (K+1)^m      (the saving exponent shrinks)
    CstK K = exp ((K+1)^m)     (the constant blows up)

and the diagonal still closes, because along the schedule `K = depthLL b N` the level is only
`O(log log log N)` while the base `2 log a_N` is `≍ log N`.  Quantitatively the *whole* question
becomes one comparison, `hgrow` below: the double logarithm of the cut scale must beat
`(K+1)^{2m}` — the square appears because the constant costs `(K+1)^m` and the saving is divided
by `(K+1)^m`. -/

/-- The degrading saving exponent, `c₀/(K+1)^m`. -/
noncomputable def cKdeg (c₀ : ℝ) (m K : ℕ) : ℝ := c₀ / ((K : ℝ) + 1) ^ m

/-- The degrading constant, `exp ((K+1)^m)`. -/
noncomputable def CstKdeg (m K : ℕ) : ℝ := Real.exp (((K : ℝ) + 1) ^ m)

theorem cKdeg_pos {c₀ : ℝ} (hc₀ : 0 < c₀) (m K : ℕ) : 0 < cKdeg c₀ m K := by
  unfold cKdeg; positivity

theorem CstKdeg_pos (m K : ℕ) : 0 < CstKdeg m K := Real.exp_pos _

/-- **The degrading profile still drives the exponent to `-∞`.**  Writing `P = (K+1)^m ≥ 1`, the
exponent is `P - κ c₀ L / P = P (1 - κ c₀ · L/P²)`; once `L/P² ≥ 1/(κc₀)` the bracket is `≤ 0`
and `P ≥ 1` only helps, so the exponent is `≤ 1 - κ c₀ · L/P² → -∞`. -/
theorem exponent_tendsto_atBot_of_degrading {c₀ : ℝ} (hc₀ : 0 < c₀) {κ : ℝ} (hκ : 0 < κ)
    (m : ℕ) (KN aN : ℕ → ℕ)
    (hgrow : Tendsto (fun N : ℕ =>
        Real.log (2 * Real.log (aN N)) / ((KN N : ℝ) + 1) ^ (2 * m)) atTop atTop) :
    Tendsto (fun N : ℕ =>
        Real.log (CstKdeg m (KN N))
          - κ * cKdeg c₀ m (KN N) * Real.log (2 * Real.log (aN N))) atTop atBot := by
  have hκc : 0 < κ * c₀ := by positivity
  -- the majorant `1 - κ c₀ · L/P²`
  have hmaj : Tendsto (fun N : ℕ => 1 - κ * c₀ *
      (Real.log (2 * Real.log (aN N)) / ((KN N : ℝ) + 1) ^ (2 * m))) atTop atBot := by
    have h1 := hgrow.const_mul_atTop hκc
    have h2 := tendsto_neg_atTop_atBot.comp h1
    have h3 := Filter.tendsto_atBot_add_const_left atTop (1 : ℝ) h2
    exact h3.congr fun N => by simp [sub_eq_add_neg]
  refine tendsto_atBot_mono' atTop ?_ hmaj
  filter_upwards [hgrow.eventually_ge_atTop (1 / (κ * c₀))] with N hN
  set P : ℝ := ((KN N : ℝ) + 1) ^ m with hP
  set L : ℝ := Real.log (2 * Real.log (aN N)) with hL
  have hP1 : 1 ≤ P := one_le_pow₀ (by have h : (0:ℝ) ≤ (KN N : ℝ) := Nat.cast_nonneg _; linarith)
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hsq : ((KN N : ℝ) + 1) ^ (2 * m) = P ^ 2 := by
    rw [hP, ← pow_mul, mul_comm m 2]
  rw [hsq] at hN ⊢
  have hR : 1 / (κ * c₀) ≤ L / P ^ 2 := hN
  have hbr : κ * c₀ * (L / P ^ 2) ≥ 1 := by
    rw [ge_iff_le, ← div_le_iff₀' hκc] at *
    exact hR
  have hlog : Real.log (CstKdeg m (KN N)) = P := by
    unfold CstKdeg; rw [Real.log_exp]
  have hc : cKdeg c₀ m (KN N) = c₀ / P := by unfold cKdeg; rfl
  rw [hlog, hc]
  have hPsq : (0 : ℝ) < P ^ 2 := by positivity
  have key : P - κ * (c₀ / P) * L = P * (1 - κ * c₀ * (L / P ^ 2)) := by
    field_simp
  rw [key]
  nlinarith [hbr, hP1]

/-- **The crux from the DEGRADING input, assembled.**  Same shape as
`depthAvg_diag_tendsto_of_uniform`, but with constants that degrade polynomially in `K`; the extra
price is the single comparison `hgrow`. -/
theorem depthAvg_diag_tendsto_of_degrading {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (m : ℕ)
    (hin : ∀ K, KPointNoExcWith (cKdeg c₀ m) (CstKdeg m) K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b hh 0)) X L)
    (Athr : ℕ → ℕ) (hA2 : ∀ K, 2 ≤ Athr K)
    (hAthr : ∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * cKdeg c₀ m K))
    (k₀ : ℕ → ℕ) (hk₀ : Tendsto k₀ atTop atTop)
    (hscale : Tendsto (fun N : ℕ => N / 2 ^ k₀ N) atTop atTop)
    (hAle : ∀ᶠ N : ℕ in atTop, Athr (PairDecouple.depthLL b N) ≤ N / 2 ^ k₀ N)
    (hgrow : Tendsto (fun N : ℕ =>
        Real.log (2 * Real.log ((N / 2 ^ k₀ N : ℕ) : ℝ))
          / ((PairDecouple.depthLL b N : ℝ) + 1) ^ (2 * m)) atTop atTop) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh (PairDecouple.depthLL b N) N) atTop (𝓝 0) := by
  have hrate := rate_tendsto_of_exponent (cK := cKdeg c₀ m) (CstK := CstKdeg m)
    (fun K => CstKdeg_pos m K) (κ := κ) (M₀ := Q * primorial P)
    (fun N => PairDecouple.depthLL b N) (fun N => N / 2 ^ k₀ N) ?_
    (exponent_tendsto_atBot_of_degrading hc₀ hκ m (fun N => PairDecouple.depthLL b N)
      (fun N => N / 2 ^ k₀ N) hgrow)
  · have hΦ := windowPhi_diag_tendsto (cK := cKdeg c₀ m) (CstK := CstKdeg m) (κ := κ)
      (M₀ := Q * primorial P) (fun N => PairDecouple.depthLL b N)
      (fun N => Athr (PairDecouple.depthLL b N)) (fun N => N / 2 ^ k₀ N)
      (fun N => hA2 _) (fun K => (CstKdeg_pos m K).le) hAle hrate
    have hhalf : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ k₀ N) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hk₀
    refine depthAvg_diag_tendsto_of_unif hQ P j hh (fun K => cKdeg_pos hc₀ m K)
      (fun K => CstKdeg_pos m K) hin hκ hκ1 hnp Athr hA2 hAthr k₀ ?_
    simpa using hΦ.add hhalf
  · -- the base `2 log a_N` is eventually positive, since the cut scale grows
    filter_upwards [hscale.eventually_ge_atTop 2] with N hN
    have h2 : (2 : ℝ) ≤ ((N / 2 ^ k₀ N : ℕ) : ℝ) := by exact_mod_cast hN
    have hlog : 0 < Real.log ((N / 2 ^ k₀ N : ℕ) : ℝ) := Real.log_pos (by linarith)
    linarith

theorem depthAvg_gen_tendsto_of_degrading {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (m : ℕ)
    (KN : ℕ → ℕ) (hKN : ∀ N, 0 < KN N)
    (hin : ∀ K, KPointNoExcWith (cKdeg c₀ m) (CstKdeg m) K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b hh 0)) X L)
    (Athr : ℕ → ℕ) (hA2 : ∀ K, 2 ≤ Athr K)
    (hAthr : ∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * cKdeg c₀ m K))
    (k₀ : ℕ → ℕ) (hk₀ : Tendsto k₀ atTop atTop)
    (hscale : Tendsto (fun N : ℕ => N / 2 ^ k₀ N) atTop atTop)
    (hAle : ∀ᶠ N : ℕ in atTop, Athr (KN N) ≤ N / 2 ^ k₀ N)
    (hgrow : Tendsto (fun N : ℕ =>
        Real.log (2 * Real.log ((N / 2 ^ k₀ N : ℕ) : ℝ))
          / ((KN N : ℝ) + 1) ^ (2 * m)) atTop atTop) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh (KN N) N) atTop (𝓝 0) := by
  have hrate := rate_tendsto_of_exponent (cK := cKdeg c₀ m) (CstK := CstKdeg m)
    (fun K => CstKdeg_pos m K) (κ := κ) (M₀ := Q * primorial P)
    KN (fun N => N / 2 ^ k₀ N) ?_
    (exponent_tendsto_atBot_of_degrading hc₀ hκ m KN
      (fun N => N / 2 ^ k₀ N) hgrow)
  · have hΦ := windowPhi_diag_tendsto (cK := cKdeg c₀ m) (CstK := CstKdeg m) (κ := κ)
      (M₀ := Q * primorial P) KN
      (fun N => Athr (KN N)) (fun N => N / 2 ^ k₀ N)
      (fun N => hA2 _) (fun K => (CstKdeg_pos m K).le) hAle hrate
    have hhalf : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ k₀ N) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hk₀
    refine depthAvg_gen_tendsto_of_unif hQ P j hh (fun K => cKdeg_pos hc₀ m K)
      (fun K => CstKdeg_pos m K) KN hKN hin hκ hκ1 hnp Athr hA2 hAthr k₀ ?_
    simpa using hΦ.add hhalf
  · -- the base `2 log a_N` is eventually positive, since the cut scale grows
    filter_upwards [hscale.eventually_ge_atTop 2] with N hN
    have h2 : (2 : ℝ) ≤ ((N / 2 ^ k₀ N : ℕ) : ℝ) := by exact_mod_cast hN
    have hlog : 0 < Real.log ((N / 2 ^ k₀ N : ℕ) : ℝ) := Real.log_pos (by linarith)
    linarith


/-! ### Discharging `hgrow` for the concrete schedule

`hgrow` is the only price of the degrading profile.  With the cut level
`k₀ N = log₂ log₂ N =: u_N` it is a theorem, not a hypothesis, and the reason is a clean
separation of scales:

* the numerator is `log (2 log a_N) ≥ log log N ≥ (u_N - 2) log 2` — *linear* in `u_N`, because
  `2^{u_N} ≤ log₂ N`;
* the denominator is `(D_N+1)^{2m} ≤ (2 + 3 log (u_N+1))^{2m}` — a *power of the logarithm* of
  `u_N`, because `b^{D_N} ≤ b (u_N+1)²`.

So the ratio is `≍ u / (log u)^{2m} → ∞`, which is the exponential beating a power after the
substitution `u + 1 = exp t`. -/

/-- `k^3 ≤ 2^k` for `k ≥ 10`. -/
theorem cube_le_two_pow : ∀ k : ℕ, 10 ≤ k → k ^ 3 ≤ 2 ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 10 with hn | hn
    · have hn9 : n = 9 := by omega
      subst hn9; norm_num
    · have h := ih (by omega)
      have h1 : 10 * n ^ 2 ≤ n ^ 3 := by
        calc 10 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ hn
          _ = n ^ 3 := by ring
      have h2 : 10 * n ≤ n ^ 2 := by
        calc 10 * n ≤ n * n := Nat.mul_le_mul_right _ hn
          _ = n ^ 2 := by ring
      have hn3 : (n + 1) ^ 3 ≤ 2 * n ^ 3 := by nlinarith
      calc (n + 1) ^ 3 ≤ 2 * n ^ 3 := hn3
        _ ≤ 2 * 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by ring

/-- The exponential beats a power of its argument's logarithm, in the shape the schedule needs. -/
theorem tendsto_expRatio_atTop (p : ℕ) :
    Tendsto (fun t : ℝ => (Real.exp t - 3) * Real.log 2 / (2 + 3 * t) ^ p) atTop atTop := by
  have hmin : Tendsto (fun t : ℝ => Real.log 2 / (2 * 5 ^ p) * (Real.exp t / t ^ p))
      atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop p).const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hmin
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hex : (6 : ℝ) ≤ Real.exp t := by
    have h1 : Real.exp 2 ≤ Real.exp t := Real.exp_le_exp.2 ht
    have h2 : (6 : ℝ) ≤ Real.exp 2 := by
      have h3 := Real.exp_one_gt_d9
      have h4 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 : ℝ)]
    linarith
  have hnum : Real.exp t / 2 ≤ Real.exp t - 3 := by linarith
  have hden : (2 + 3 * t) ^ p ≤ (5 * t) ^ p := by
    exact pow_le_pow_left₀ (by linarith) (by linarith) p
  have hdenpos : (0 : ℝ) < (2 + 3 * t) ^ p := by positivity
  have hkey : Real.log 2 / (2 * 5 ^ p) * (Real.exp t / t ^ p)
      ≤ (Real.exp t / 2) * Real.log 2 / (5 * t) ^ p := by
    rw [mul_pow]
    have h5 : (0 : ℝ) < (5 : ℝ) ^ p := by positivity
    have h6 : (0 : ℝ) < t ^ p := pow_pos ht0 p
    field_simp
    norm_num
  refine hkey.trans ?_
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have h1 : (Real.exp t / 2) * Real.log 2 ≤ (Real.exp t - 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hnum hlog2
  have h2 : (Real.exp t - 3) * Real.log 2 / (5 * t) ^ p
      ≤ (Real.exp t - 3) * Real.log 2 / (2 + 3 * t) ^ p :=
    div_le_div_of_nonneg_left (by nlinarith) hdenpos hden
  exact le_trans (div_le_div_of_nonneg_right h1 (by positivity)) h2

/-- The minorant of `hgrow`, as a function of the double-log level `u`. -/
noncomputable def degMinorant (m u : ℕ) : ℝ :=
  ((u : ℝ) - 2) * Real.log 2 / (2 + 3 * Real.log ((u : ℝ) + 1)) ^ (2 * m)

/-- **The minorant diverges.**  `u + 1 = exp (log (u+1))` turns this into
`tendsto_expRatio_atTop`, with no inversion of the logarithm anywhere. -/
theorem tendsto_degMinorant (m : ℕ) : Tendsto (fun u : ℕ => degMinorant m u) atTop atTop := by
  have ht : Tendsto (fun u : ℕ => Real.log ((u : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hcomp := (tendsto_expRatio_atTop (2 * m)).comp ht
  refine hcomp.congr fun u => ?_
  have hpos : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  simp only [Function.comp_apply, degMinorant, Real.exp_log hpos]
  ring_nf

/-- **The denominator: the depth level is a LOGARITHM of the double-log level.**
`b^{D_N} ≤ b·(u_N+1)²` (`pow_depthLL_le`), so `D_N + 1 ≤ 2 + 3 log (u_N+1)`. -/
theorem depthLL_succ_le_log {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    ((PairDecouple.depthLL b N : ℝ) + 1) ≤ 2 + 3 * Real.log (llProxy N) := by
  have hb1 : (1 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hbpos : (0 : ℝ) < b := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hp1 : (1 : ℝ) ≤ llProxy N := one_le_llProxy N
  have hlp : 0 ≤ Real.log (llProxy N) := Real.log_nonneg hp1
  have hpow := pow_depthLL_le hb N
  have hlog : (PairDecouple.depthLL b N : ℝ) * Real.log b
      ≤ Real.log b + 2 * Real.log (llProxy N) := by
    have hL : Real.log ((b : ℝ) ^ PairDecouple.depthLL b N)
        ≤ Real.log ((b : ℝ) * llProxy N ^ 2) :=
      Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_mul (ne_of_gt hbpos) (by positivity),
      Real.log_pow] at hL
    push_cast at hL
    linarith
  -- `log b ≥ log 2 > 0.69`, so `2 / log b ≤ 3`
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hb2 : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) (by exact_mod_cast hb)
  have hkey : (PairDecouple.depthLL b N : ℝ) ≤ 1 + 3 * Real.log (llProxy N) := by
    have h3 : (2 : ℝ) ≤ 3 * Real.log b := by nlinarith [hb2, hlog2]
    nlinarith [hlog, hlp, hlogb, h3, mul_nonneg hlp hlogb.le]
  linarith

/-! The numerator: the cut scale `a_N = N / 2^{u_N}` satisfies `a_N² ≥ N`, so
`2 log a_N ≥ log N`, and `log N ≥ 2^{u_N} log 2` makes `log log N` LINEAR in `u_N`. -/

/-- The cut divisor is at most `log₂ N`. -/
theorem two_pow_llLevel_le {N : ℕ} (hN : 2 ≤ N) :
    2 ^ (Nat.log 2 (Nat.log 2 N)) ≤ Nat.log 2 N := by
  have h0 : Nat.log 2 N ≠ 0 := by
    have : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
    omega
  exact Nat.pow_log_le_self 2 h0

/-- **The cut scale is at least `√N`.**  `a_N = N / 2^{u_N} ≥ N / log₂ N ≥ √N`, because
`(log₂ N)³ ≤ 2^{log₂ N} ≤ N`. -/
theorem le_sq_cut (N : ℕ) (hN : 1024 ≤ N) :
    N ≤ (N / 2 ^ (Nat.log 2 (Nat.log 2 N))) ^ 2 := by
  set L2 : ℕ := Nat.log 2 N with hL2
  have hN2 : 2 ≤ N := by omega
  have h1024 : 2 ^ 10 ≤ N := le_trans (by norm_num) hN
  have hL10 : 10 ≤ L2 := Nat.le_log_of_pow_le (by norm_num) h1024
  have hL0 : 0 < L2 := by omega
  have hd := two_pow_llLevel_le hN2
  have hdpos : 0 < 2 ^ (Nat.log 2 (Nat.log 2 N)) := pow_pos (by norm_num) _
  have hqa : N / L2 ≤ N / 2 ^ (Nat.log 2 (Nat.log 2 N)) := Nat.div_le_div_left hd hdpos
  -- `L2³ ≤ 2^{L2} ≤ N`
  have hcube : L2 ^ 3 ≤ N := le_trans (cube_le_two_pow L2 hL10)
    (Nat.pow_log_le_self 2 (by omega))
  set q : ℕ := N / L2 with hq
  have hmod : L2 * q + N % L2 = N := Nat.div_add_mod N L2
  have hlt : N % L2 < L2 := Nat.mod_lt _ hL0
  have hq1 : 1 ≤ q := by
    rw [hq]
    refine Nat.one_le_div_iff hL0 |>.2 ?_
    exact Nat.log_le_self 2 N
  have h2q : N ≤ 2 * (L2 * q) := by nlinarith
  have h4 : 4 * L2 ^ 2 ≤ N := by nlinarith
  have hqsq : N ≤ q ^ 2 := by nlinarith
  exact le_trans hqsq (Nat.pow_le_pow_left hqa 2)

/-- **The numerator is linear in the double-log level.**  `log (2 log a_N) ≥ (u_N - 2) log 2`. -/
theorem log_two_log_cut_ge (N : ℕ) (hN : 1024 ≤ N) :
    ((Nat.log 2 (Nat.log 2 N) : ℝ) - 2) * Real.log 2
      ≤ Real.log (2 * Real.log ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ)) := by
  set u : ℕ := Nat.log 2 (Nat.log 2 N) with hu
  set a : ℕ := N / 2 ^ u with ha
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hN2 : 2 ≤ N := by omega
  -- `log N ≥ (log₂ N) log 2 ≥ 2^u log 2`
  have hpowN : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hlogN : ((Nat.log 2 N : ℝ)) * Real.log 2 ≤ Real.log N := by
    have h1 : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log N := by
      refine Real.log_le_log (by positivity) ?_
      exact_mod_cast hpowN
    rwa [Real.log_pow] at h1
  have hu2 : ((2 : ℝ) ^ u) ≤ (Nat.log 2 N : ℝ) := by
    have := two_pow_llLevel_le hN2
    calc ((2 : ℝ) ^ u) = ((2 ^ u : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Nat.log 2 N : ℝ) := by exact_mod_cast this
  have hlogNge : (2 : ℝ) ^ u * Real.log 2 ≤ Real.log N := by
    have := mul_le_mul_of_nonneg_right hu2 (le_of_lt (by linarith : (0:ℝ) < Real.log 2))
    linarith
  -- `2 log a ≥ log N`
  have hsq : N ≤ a ^ 2 := le_sq_cut N hN
  have hapos : (1 : ℝ) ≤ (a : ℝ) := by
    have h1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · exfalso
        rw [h0] at hsq
        have h2 : N ≤ 0 := by simpa using hsq
        omega
      · exact h0
    exact_mod_cast h1
  have h2a : Real.log N ≤ 2 * Real.log (a : ℝ) := by
    have h1 : Real.log (N : ℝ) ≤ Real.log (((a ^ 2 : ℕ) : ℝ)) := by
      refine Real.log_le_log ?_ (by exact_mod_cast hsq)
      have : (0 : ℝ) < (N : ℝ) := by positivity
      linarith [this]
    have h2 : Real.log (((a ^ 2 : ℕ) : ℝ)) = 2 * Real.log (a : ℝ) := by
      push_cast; rw [Real.log_pow]; push_cast; ring
    linarith [h1, h2.le, h2.ge]
  -- put it together
  have hNpos : (0 : ℝ) < Real.log N := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    exact Real.log_pos (by linarith)
  have hstep : Real.log (2 ^ u * Real.log 2) ≤ Real.log (2 * Real.log (a : ℝ)) := by
    refine Real.log_le_log (by positivity) ?_
    linarith
  have hexpand : Real.log ((2 : ℝ) ^ u * Real.log 2)
      = (u : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
    rw [Real.log_mul (by positivity) (by
      have : (0 : ℝ) < Real.log 2 := by linarith
      exact ne_of_gt this), Real.log_pow]
  have hll : (-1 : ℝ) ≤ Real.log (Real.log 2) := by
    have h1 : Real.log (Real.log 2) ≥ Real.log (0.6931471803 : ℝ) :=
      Real.log_le_log (by norm_num) hlog2.le
    have h2 : Real.log (0.6931471803 : ℝ) ≥ -1 := by
      have : Real.exp (-1 : ℝ) ≤ (0.6931471803 : ℝ) := by
        have h3 : Real.exp (-1 : ℝ) = 1 / Real.exp 1 := by
          rw [Real.exp_neg]; ring
        rw [h3]
        rw [div_le_iff₀ (Real.exp_pos 1)]
        nlinarith [Real.exp_one_gt_d9]
      have h4 := Real.log_le_log (Real.exp_pos (-1)) this
      rwa [Real.log_exp] at h4
    linarith
  have : ((u : ℝ) - 2) * Real.log 2 ≤ (u : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
    nlinarith [hll, hlog2]
  linarith [hstep, hexpand.le, hexpand.ge]

/-- **`hgrow` IS A THEOREM for the concrete cut `k₀ N = u_N = log₂ log₂ N`.**  The numerator is
linear in `u_N`, the denominator a fixed power of `log u_N`; `tendsto_degMinorant` does the rest.
This is the last hypothesis of `depthAvg_diag_tendsto_of_degrading` that was not free. -/
theorem hgrow_of_schedule {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    Tendsto (fun N : ℕ =>
        Real.log (2 * Real.log ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ))
          / ((PairDecouple.depthLL b N : ℝ) + 1) ^ (2 * m)) atTop atTop := by
  have hu : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop :=
    (PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
      (PairDecouple.tendsto_natLog_atTop 2 le_rfl)
  have hmin := (tendsto_degMinorant m).comp hu
  refine tendsto_atTop_mono' atTop ?_ hmin
  filter_upwards [Filter.eventually_ge_atTop 1024, hu.eventually_ge_atTop 2] with N hN hu2
  set u : ℕ := Nat.log 2 (Nat.log 2 N) with hudef
  have hnum := log_two_log_cut_ge N hN
  have hden := depthLL_succ_le_log hb N
  have hllp : llProxy N = (u : ℝ) + 1 := by rw [llProxy]
  rw [hllp] at hden
  have hA0 : (0 : ℝ) ≤ ((u : ℝ) - 2) * Real.log 2 := by
    have h1 : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu2
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hBpos : (0 : ℝ) < ((PairDecouple.depthLL b N : ℝ) + 1) ^ (2 * m) := by positivity
  have hB'pos : (0 : ℝ) < (2 + 3 * Real.log ((u : ℝ) + 1)) ^ (2 * m) := by
    have h1 : (1 : ℝ) ≤ (u : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg _
      linarith
    have h0 : 0 ≤ Real.log ((u : ℝ) + 1) := Real.log_nonneg h1
    positivity
  have hBB : ((PairDecouple.depthLL b N : ℝ) + 1) ^ (2 * m)
      ≤ (2 + 3 * Real.log ((u : ℝ) + 1)) ^ (2 * m) :=
    pow_le_pow_left₀ (by positivity) hden _
  have hC0 : (0 : ℝ) ≤ Real.log (2 * Real.log ((N / 2 ^ u : ℕ) : ℝ)) := le_trans hA0 hnum
  have hfirst : ((fun u : ℕ => degMinorant m u) ∘ fun N : ℕ => Nat.log 2 (Nat.log 2 N)) N
      = ((u : ℝ) - 2) * Real.log 2 / (2 + 3 * Real.log ((u : ℝ) + 1)) ^ (2 * m) := rfl
  rw [hfirst]
  calc ((u : ℝ) - 2) * Real.log 2 / (2 + 3 * Real.log ((u : ℝ) + 1)) ^ (2 * m)
      ≤ Real.log (2 * Real.log ((N / 2 ^ u : ℕ) : ℝ))
          / (2 + 3 * Real.log ((u : ℝ) + 1)) ^ (2 * m) :=
        div_le_div_of_nonneg_right hnum hB'pos.le
    _ ≤ Real.log (2 * Real.log ((N / 2 ^ u : ℕ) : ℝ))
          / ((PairDecouple.depthLL b N : ℝ) + 1) ^ (2 * m) :=
        div_le_div_of_nonneg_left hC0 hBpos hBB

theorem hgrow_of_schedule_le {b : ℕ} (hb : 2 ≤ b) (m : ℕ) (KN : ℕ → ℕ)
    (hKle : ∀ᶠ N : ℕ in atTop, KN N ≤ PairDecouple.depthLL b N) :
    Tendsto (fun N : ℕ =>
        Real.log (2 * Real.log ((N / 2 ^ (Nat.log 2 (Nat.log 2 N)) : ℕ) : ℝ))
          / ((KN N : ℝ) + 1) ^ (2 * m)) atTop atTop := by
  have hu : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop :=
    (PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
      (PairDecouple.tendsto_natLog_atTop 2 le_rfl)
  have hmin := (tendsto_degMinorant m).comp hu
  refine tendsto_atTop_mono' atTop ?_ hmin
  filter_upwards [Filter.eventually_ge_atTop 1024, hu.eventually_ge_atTop 2, hKle]
    with N hN hu2 hKN
  set u : ℕ := Nat.log 2 (Nat.log 2 N) with hudef
  have hnum := log_two_log_cut_ge N hN
  have hdenLL := depthLL_succ_le_log hb N
  have hKR : ((KN N : ℝ) + 1) ≤ ((PairDecouple.depthLL b N : ℝ) + 1) := by
    have : ((KN N : ℝ)) ≤ ((PairDecouple.depthLL b N : ℝ)) := by exact_mod_cast hKN
    linarith
  have hden : ((KN N : ℝ) + 1) ≤ 2 + 3 * Real.log (llProxy N) := le_trans hKR hdenLL
  have hllp : llProxy N = (u : ℝ) + 1 := by rw [llProxy]
  rw [hllp] at hden
  have hA0 : (0 : ℝ) ≤ ((u : ℝ) - 2) * Real.log 2 := by
    have h1 : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu2
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hBpos : (0 : ℝ) < ((KN N : ℝ) + 1) ^ (2 * m) := by positivity
  have hB'pos : (0 : ℝ) < (2 + 3 * Real.log ((u : ℝ) + 1)) ^ (2 * m) := by
    have h1 : (1 : ℝ) ≤ (u : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg _
      linarith
    have h0 : 0 ≤ Real.log ((u : ℝ) + 1) := Real.log_nonneg h1
    positivity
  have hBB : ((KN N : ℝ) + 1) ^ (2 * m)
      ≤ (2 + 3 * Real.log ((u : ℝ) + 1)) ^ (2 * m) :=
    pow_le_pow_left₀ (by positivity) hden _
  have hC0 : (0 : ℝ) ≤ Real.log (2 * Real.log ((N / 2 ^ u : ℕ) : ℝ)) := le_trans hA0 hnum
  have hfirst : ((fun u : ℕ => degMinorant m u) ∘ fun N : ℕ => Nat.log 2 (Nat.log 2 N)) N
      = ((u : ℝ) - 2) * Real.log 2 / (2 + 3 * Real.log ((u : ℝ) + 1)) ^ (2 * m) := rfl
  rw [hfirst]
  calc ((u : ℝ) - 2) * Real.log 2 / (2 + 3 * Real.log ((u : ℝ) + 1)) ^ (2 * m)
      ≤ Real.log (2 * Real.log ((N / 2 ^ u : ℕ) : ℝ))
          / (2 + 3 * Real.log ((u : ℝ) + 1)) ^ (2 * m) :=
        div_le_div_of_nonneg_right hnum hB'pos.le
    _ ≤ Real.log (2 * Real.log ((N / 2 ^ u : ℕ) : ℝ))
          / ((KN N : ℝ) + 1) ^ (2 * m) :=
        div_le_div_of_nonneg_left hC0 hBpos hBB


/-- **The cut scale grows.**  `a_N ≥ √N`. -/
theorem tendsto_cut_atTop :
    Tendsto (fun N : ℕ => N / 2 ^ (Nat.log 2 (Nat.log 2 N))) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun M => ⟨max 1024 (M * M), fun N hN => ?_⟩
  have h1 : 1024 ≤ N := le_trans (le_max_left _ _) hN
  have h2 : M * M ≤ N := le_trans (le_max_right _ _) hN
  have h3 := le_sq_cut N h1
  by_contra hcon
  push_neg at hcon
  have h4 : (N / 2 ^ Nat.log 2 (Nat.log 2 N)) ^ 2 < M ^ 2 :=
    Nat.pow_lt_pow_left hcon (by norm_num)
  have h5 : M ^ 2 ≤ N := by rw [pow_two]; exact h2
  linarith

/-- **THE DIAGONAL FROM THE DEGRADING INPUT, NO SCHEDULE HYPOTHESIS.**  With the cut level
`k₀ N = log₂ log₂ N` the comparison `hgrow` is discharged (`hgrow_of_schedule`), so the diagonal
— and hence the C3 crux, via `weylLambertTwist_of_depthDiagonal` — follows from
`KPointNoExcWith (cKdeg c₀ m) (CstKdeg m)`: the `K`-point correlation input with a saving
exponent decaying like `K^{-m}` and a constant blowing up like `exp (K^m)`.

The only hypotheses left are about the *threshold* sequence `Athr` of the input, which is where
TT Thm 3.1's `X ≥ X₀(K)` lives; they say the threshold is eventually below `√N`, which is what a
threshold depending on `K = O(log log log N)` always satisfies. -/
theorem depthAvg_diag_tendsto_of_degrading_sched {b Q : ℕ} (hb : 2 ≤ b) (hQ : 0 < Q)
    (P j : ℕ) (hh : ℤ) {c₀ : ℝ} (hc₀ : 0 < c₀) (m : ℕ)
    (hin : ∀ K, KPointNoExcWith (cKdeg c₀ m) (CstKdeg m) K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b hh 0)) X L)
    (Athr : ℕ → ℕ) (hA2 : ∀ K, 2 ≤ Athr K)
    (hAthr : ∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * cKdeg c₀ m K))
    (hAle : ∀ᶠ N : ℕ in atTop,
        Athr (PairDecouple.depthLL b N) ≤ N / 2 ^ (Nat.log 2 (Nat.log 2 N))) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh (PairDecouple.depthLL b N) N) atTop (𝓝 0) :=
  depthAvg_diag_tendsto_of_degrading hQ P j hh hc₀ m hin hκ hκ1 hnp Athr hA2 hAthr
    (fun N => Nat.log 2 (Nat.log 2 N))
    ((PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
      (PairDecouple.tendsto_natLog_atTop 2 le_rfl))
    tendsto_cut_atTop hAle (hgrow_of_schedule hb m)

/-! ### The degenerate twist levels of `DepthDiagonal`

`DepthDiagonal b` quantifies over ALL `hh : ℤ`, while the chain needs `depthRoot b hh 0 ≠ 1`
(i.e. `b ∤ hh`) to get `κ > 0`.  Two levels are degenerate, and both are elementary.

* `hh = 0`: the depth phase is identically `1` and `depthAvg` is the bare twist average
  `(1/N) ∑_{n<N} e(jn/Q)`, a geometric sum with `0 < j < Q`, hence `O(1/N)`.
* `b ∣ hh`, `hh ≠ 0`: the first `v = v_b(hh)` roots are trivial and the correlation is the same
  shape re-indexed from depth `v` — handled by `depthAvg_eq_shift` below. -/

/-- **The bare twist average vanishes.**  `0 < j < Q` makes `e(j/Q) ≠ 1`, so the geometric sum is
bounded and the average is `O(1/N)`. -/
theorem twistAvg_tendsto {Q j : ℕ} (hj0 : 0 < j) (hjQ : j < Q) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ) : ℂ))) / N)
      atTop (𝓝 0) := by
  have hQ0 : 0 < Q := lt_of_le_of_lt (Nat.zero_le j) hjQ
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  set ζ : ℂ := ee ((((j : ℝ) / Q : ℝ) : ℂ)) with hζdef
  -- `ζ ≠ 1`: `j/Q` is not an integer
  have hζ : ζ ≠ 1 := by
    rw [hζdef]
    intro hone
    obtain ⟨M, hM⟩ := ee_eq_one_iff_int.1 hone
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj0
    have hjQR : (j : ℝ) < (Q : ℝ) := by exact_mod_cast hjQ
    have h0 : (0 : ℝ) < (M : ℝ) := by rw [← hM]; positivity
    have h1 : (M : ℝ) < 1 := by
      rw [← hM, div_lt_one hQR]; exact hjQR
    have h2 : (0 : ℤ) < M := by exact_mod_cast h0
    have h3 : (M : ℤ) < 1 := by exact_mod_cast h1
    omega
  -- the sum is geometric
  have hgeom : ∀ N : ℕ, (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ) : ℂ)))
      = ∑ n ∈ range N, ζ ^ n := by
    intro N
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hζdef, ← ee_nat_mul]
    congr 1
    push_cast
    ring
  have hbd : ∀ N : ℕ, ‖(∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ) : ℂ))) / N‖
      ≤ (2 / ‖ζ - 1‖) * (1 / N) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hζ1 : ζ - 1 ≠ 0 := sub_ne_zero_of_ne hζ
    have hnormζ : ‖ζ‖ = 1 := norm_ee_real _
    have hsum : (∑ n ∈ range N, ζ ^ n) = (ζ ^ N - 1) / (ζ - 1) :=
      geom_sum_eq hζ N
    rw [hgeom, hsum, norm_div, norm_div, Complex.norm_natCast]
    have hnum : ‖ζ ^ N - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, hnormζ, one_pow, norm_one]
      norm_num
    have hden : (0 : ℝ) < ‖ζ - 1‖ := norm_pos_iff.2 hζ1
    rw [div_div, div_le_iff₀ (by positivity : (0 : ℝ) < ‖ζ - 1‖ * N)]
    have hid : 2 / ‖ζ - 1‖ * (1 / (N : ℝ)) * (‖ζ - 1‖ * N) = 2 := by
      field_simp
    rw [hid]
    exact hnum
  refine squeeze_zero_norm hbd ?_
  have := tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 / ‖ζ - 1‖)
  rwa [mul_zero] at this

/-- **`DepthDiagonal` at the trivial twist level.**  `hh = 0`. -/
theorem depthAvg_zero_tendsto (b P Q j : ℕ) {D : ℕ → ℕ} (hj0 : 0 < j) (hjQ : j < Q) :
    Tendsto (fun N : ℕ => depthAvg b P Q j 0 (D N) N) atTop (𝓝 0) := by
  have hcongr : ∀ N : ℕ, depthAvg b P Q j 0 (D N) N
      = (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ) : ℂ))) / N := by
    intro N
    rw [depthAvg]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    norm_num [ee_zero]
  exact (twistAvg_tendsto hj0 hjQ).congr fun N => (hcongr N).symm

/-- `e(m) = 1` at an integer. -/
theorem ee_intCast_eq_one (m : ℤ) : ee (((m : ℝ) : ℂ)) = 1 :=
  ee_eq_one_iff_int.2 ⟨m, rfl⟩

/-- **The first `v` roots of a `b^v`-divisible twist are trivial.** -/
theorem depthRoot_eq_one_of_dvd {b : ℕ} (hb : 0 < b) (h' : ℤ) {v i : ℕ} (hi : i < v) :
    depthRoot b ((b : ℤ) ^ v * h') i = 1 := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hkey : (((b : ℤ) ^ v * h' : ℤ) : ℝ) / (b : ℝ) ^ (i + 1)
      = ((h' * (b : ℤ) ^ (v - (i + 1)) : ℤ) : ℝ) := by
    have hexp : v = (i + 1) + (v - (i + 1)) := by omega
    push_cast
    rw [show ((b : ℝ)) ^ v = (b : ℝ) ^ (i + 1) * (b : ℝ) ^ (v - (i + 1)) by
      rw [← pow_add, ← hexp]]
    field_simp
  rw [depthRoot, hkey]
  exact ee_intCast_eq_one _

/-- **Beyond depth `v` the twist is the shifted one.** -/
theorem depthRoot_shift {b : ℕ} (hb : 0 < b) (h' : ℤ) (v i : ℕ) :
    depthRoot b ((b : ℤ) ^ v * h') (v + i) = depthRoot b h' i := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hkey : ((((b : ℤ) ^ v * h' : ℤ)) : ℝ) / (b : ℝ) ^ (v + i + 1)
      = ((h' : ℝ)) / (b : ℝ) ^ (i + 1) := by
    rw [show v + i + 1 = v + (i + 1) by omega, pow_add]
    push_cast
    field_simp
  rw [depthRoot, depthRoot, hkey]

/-- **The depth phase of a `b^v`-divisible twist is the phase of the reduced twist, re-indexed.**
`ee (b^v h' · tailDepth D n) = ee (h' · tailDepth (D-v) (n+v))`: the first `v` digit slots
contribute integer phases. -/
theorem ee_tailDepth_dvd {b : ℕ} (hb : 0 < b) (P : ℕ) (h' : ℤ) {v D : ℕ} (hvD : v ≤ D) (n : ℕ) :
    ee (((((((b : ℤ) ^ v * h' : ℤ)) : ℝ) * tailDepth P b D n : ℝ) : ℂ))
      = ee ((((h' : ℝ) * tailDepth P b (D - v) (n + v) : ℝ) : ℂ)) := by
  rw [ee_tailDepth_eq_prod, ee_tailDepth_eq_prod]
  have hD : D = v + (D - v) := by omega
  conv_lhs => rw [hD]
  rw [Finset.prod_range_add]
  have hfirst : (∏ i ∈ range v, depthRoot b ((b : ℤ) ^ v * h') i ^ omegaLarge P (n + i + 1))
      = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    rw [depthRoot_eq_one_of_dvd hb h' (Finset.mem_range.1 hi), one_pow]
  rw [hfirst, one_mul]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [depthRoot_shift hb h' v i]
  congr 2
  omega

/-- **The `b ∣ hh` level of `DepthDiagonal`, reduced.**  Writing `hh = b^v h'`, the depth-`D`
average at `hh` is the depth-`(D-v)` average at `h'`, up to a shift of `n` by `v` — and that shift
costs at most `2v/N`.  So the diagonal at a `b`-divisible twist level follows from the diagonal at
the reduced level with the depth schedule lowered by the constant `v`. -/
theorem norm_depthAvg_dvd_le {b : ℕ} (hb : 0 < b) (P Q j : ℕ) (h' : ℤ) {v D : ℕ} (hvD : v ≤ D)
    (N : ℕ) :
    ‖depthAvg b P Q j ((b : ℤ) ^ v * h') D N‖
      ≤ ‖depthAvg b P Q j h' (D - v) N‖ + 2 * v / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [depthAvg]
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set T : ℕ → ℂ := fun m => ee ((((j : ℝ) * m / Q : ℝ) : ℂ)) with hT
  set F : ℕ → ℂ := fun m => ee ((((h' : ℝ) * tailDepth P b (D - v) m : ℝ) : ℂ)) with hF
  set g : ℕ → ℂ := fun m => T m * F m with hg
  have hTnorm : ∀ m, ‖T m‖ = 1 := fun m => norm_ee_real _
  have hFnorm : ∀ m, ‖F m‖ = 1 := fun m => norm_ee_real _
  have hgnorm : ∀ m, ‖g m‖ = 1 := fun m => by rw [hg]; simp [norm_mul, hTnorm, hFnorm]
  -- the shift on the twist
  have hTadd : ∀ n : ℕ, T (n + v) = T n * T v := by
    intro n
    rw [hT]
    simp only
    rw [← ee_add]
    congr 1
    push_cast
    rcases Nat.eq_zero_or_pos Q with rfl | hQ
    · simp
    have hQR : (Q : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
      exact ne_of_gt this
    field_simp
  have hTv : T v ≠ 0 := by
    intro h0
    have := hTnorm v
    rw [h0, norm_zero] at this
    norm_num at this
  -- step 1: the divisible average is the reduced average with `n` shifted
  have hstep1 : depthAvg b P Q j ((b : ℤ) ^ v * h') D N
      = (∑ n ∈ range N, T n * F (n + v)) / N := by
    rw [depthAvg]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hT, hF]
    simp only
    rw [ee_tailDepth_dvd hb P h' hvD n]
  -- step 2: pull the twist shift out
  have hstep2 : (∑ n ∈ range N, T n * F (n + v))
      = (T v)⁻¹ * ∑ n ∈ range N, g (n + v) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hg]
    simp only
    rw [hTadd n]
    field_simp
  -- step 3: the shifted sum differs from the plain one by at most `2v` terms
  have hstep3 : ‖(∑ n ∈ range N, g (n + v)) - ∑ m ∈ range N, g m‖ ≤ 2 * v := by
    have e1 : (∑ m ∈ range (v + N), g m)
        = (∑ i ∈ range v, g i) + ∑ i ∈ range N, g (v + i) := Finset.sum_range_add g v N
    have e2 : (∑ m ∈ range (N + v), g m)
        = (∑ i ∈ range N, g i) + ∑ i ∈ range v, g (N + i) := Finset.sum_range_add g N v
    have e3 : v + N = N + v := by omega
    rw [e3] at e1
    have hshift : ∀ i, g (v + i) = g (i + v) := fun i => by rw [Nat.add_comm]
    have key : (∑ n ∈ range N, g (n + v)) - ∑ m ∈ range N, g m
        = (∑ i ∈ range v, g (N + i)) - ∑ i ∈ range v, g i := by
      have e1' : (∑ m ∈ range (N + v), g m)
          = (∑ i ∈ range v, g i) + ∑ i ∈ range N, g (i + v) := by
        rw [e1]
        congr 1
        exact Finset.sum_congr rfl fun i _ => hshift i
      rw [e1'] at e2
      linear_combination e2
    rw [key]
    refine (norm_sub_le _ _).trans ?_
    have b1 : ‖∑ i ∈ range v, g (N + i)‖ ≤ v := by
      refine (norm_sum_le _ _).trans ?_
      simp [hgnorm]
    have b2 : ‖∑ i ∈ range v, g i‖ ≤ v := by
      refine (norm_sum_le _ _).trans ?_
      simp [hgnorm]
    linarith
  -- assemble
  have hnormTv : ‖(T v)⁻¹‖ = 1 := by
    rw [norm_inv, hTnorm v, inv_one]
  rw [hstep1, hstep2, norm_div, norm_mul, hnormTv, one_mul, Complex.norm_natCast]
  have hplain : depthAvg b P Q j h' (D - v) N = (∑ m ∈ range N, g m) / N := by
    rw [depthAvg, hg]
  rw [hplain, norm_div, Complex.norm_natCast]
  have hsplit : ‖∑ n ∈ range N, g (n + v)‖ ≤ ‖∑ m ∈ range N, g m‖ + 2 * v := by
    have hrev := norm_sub_norm_le (∑ n ∈ range N, g (n + v)) (∑ m ∈ range N, g m)
    linarith [hstep3, hrev]
  calc ‖∑ n ∈ range N, g (n + v)‖ / (N : ℝ)
      ≤ (‖∑ m ∈ range N, g m‖ + 2 * v) / (N : ℝ) :=
        div_le_div_of_nonneg_right hsplit hNR.le
    _ = ‖∑ m ∈ range N, g m‖ / (N : ℝ) + 2 * v / (N : ℝ) := by ring

/-- **THE DIAGONAL AT ANY LEVEL SEQUENCE BELOW THE SCHEDULE, from the degrading input.**  The
general-level twin of `depthAvg_diag_tendsto_of_degrading_sched`: `KN N ≤ depthLL b N` (eventually)
is all the schedule arithmetic needs, so this serves the `b ∣ hh` level too, where the level is
`depthLL b N - v`. -/
theorem depthAvg_gen_tendsto_of_degrading_sched {b Q : ℕ} (hb : 2 ≤ b) (hQ : 0 < Q)
    (P j : ℕ) (hh : ℤ) {c₀ : ℝ} (hc₀ : 0 < c₀) (m : ℕ)
    (KN : ℕ → ℕ) (hKN : ∀ N, 0 < KN N)
    (hKle : ∀ᶠ N : ℕ in atTop, KN N ≤ PairDecouple.depthLL b N)
    (hin : ∀ K, KPointNoExcWith (cKdeg c₀ m) (CstKdeg m) K)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b hh 0)) X L)
    (Athr : ℕ → ℕ) (hA2 : ∀ K, 2 ≤ Athr K)
    (hAthr : ∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * cKdeg c₀ m K))
    (hAle : ∀ᶠ N : ℕ in atTop, Athr (KN N) ≤ N / 2 ^ (Nat.log 2 (Nat.log 2 N))) :
    Tendsto (fun N : ℕ => depthAvg b P Q j hh (KN N) N) atTop (𝓝 0) :=
  depthAvg_gen_tendsto_of_degrading hQ P j hh hc₀ m KN hKN hin hκ hκ1 hnp Athr hA2 hAthr
    (fun N => Nat.log 2 (Nat.log 2 N))
    ((PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
      (PairDecouple.tendsto_natLog_atTop 2 le_rfl))
    tendsto_cut_atTop hAle (hgrow_of_schedule_le hb m KN hKle)

/-- `depthLL b N → ∞`. -/
theorem tendsto_depthLL {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun N : ℕ => PairDecouple.depthLL b N) atTop atTop := by
  have hu : Tendsto (fun N : ℕ => Nat.log 2 (Nat.log 2 N)) atTop atTop :=
    (PairDecouple.tendsto_natLog_atTop 2 le_rfl).comp
      (PairDecouple.tendsto_natLog_atTop 2 le_rfl)
  have hsq : Tendsto (fun N : ℕ => (Nat.log 2 (Nat.log 2 N) + 1) ^ 2) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun M => ?_
    obtain ⟨N₀, hN₀⟩ := tendsto_atTop_atTop.1 hu M
    exact ⟨N₀, fun N hN => le_trans (hN₀ N hN) (by nlinarith [Nat.zero_le (Nat.log 2 (Nat.log 2 N))])⟩
  have := (PairDecouple.tendsto_natLog_atTop b hb).comp hsq
  refine tendsto_atTop_atTop.2 fun M => ?_
  obtain ⟨N₀, hN₀⟩ := tendsto_atTop_atTop.1 this M
  exact ⟨N₀, fun N hN => le_trans (hN₀ N hN) (by simp only [Function.comp_apply, PairDecouple.depthLL]; omega)⟩

/-- **Any nonzero twist level is `b^v` times a primitive one.** -/
theorem exists_pow_mul_not_dvd {b : ℕ} (hb : 2 ≤ b) (hh : ℤ) (hne : hh ≠ 0) :
    ∃ (v : ℕ) (h' : ℤ), hh = (b : ℤ) ^ v * h' ∧ ¬ ((b : ℤ) ∣ h') := by
  suffices H : ∀ n : ℕ, ∀ hh : ℤ, hh.natAbs = n → hh ≠ 0 →
      ∃ (v : ℕ) (h' : ℤ), hh = (b : ℤ) ^ v * h' ∧ ¬ ((b : ℤ) ∣ h') from
    H hh.natAbs hh rfl hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hh hn hne
    by_cases hd : (b : ℤ) ∣ hh
    · obtain ⟨c, hc⟩ := hd
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hc
        exact hne hc
      have hb' : 2 ≤ ((b : ℤ)).natAbs := by simpa using hb
      have hcpos : 0 < c.natAbs := Int.natAbs_pos.2 hc0
      have hlt : c.natAbs < n := by
        subst hn
        rw [hc, Int.natAbs_mul]
        calc c.natAbs < 2 * c.natAbs := by omega
          _ ≤ ((b : ℤ)).natAbs * c.natAbs := Nat.mul_le_mul_right _ hb'
      obtain ⟨v, h', hv, hnd⟩ := ih c.natAbs hlt c rfl hc0
      refine ⟨v + 1, h', ?_, hnd⟩
      rw [hc, hv, pow_succ]
      ring
    · exact ⟨0, hh, by simp, hd⟩

/-- **The diagonal at a `b`-divisible twist level, from the primitive one.**  The shift costs
`2v/N`, which dies; the level drops by the constant `v`, which the general-level machinery
(`depthAvg_gen_tendsto_of_degrading_sched`) absorbs. -/
theorem depthAvg_dvd_tendsto_of_primitive {b : ℕ} (hb : 2 ≤ b) (P Q j : ℕ) (h' : ℤ) (v : ℕ)
    (hprim : Tendsto (fun N : ℕ =>
      depthAvg b P Q j h' (PairDecouple.depthLL b N - v) N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      depthAvg b P Q j ((b : ℤ) ^ v * h') (PairDecouple.depthLL b N) N) atTop (𝓝 0) := by
  have hb0 : 0 < b := by omega
  have hshift : Tendsto (fun N : ℕ => 2 * (v : ℝ) / N) atTop (𝓝 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 * (v : ℝ))
    rw [mul_zero] at this
    exact this.congr fun N => by ring
  have hmaj : Tendsto (fun N : ℕ =>
      ‖depthAvg b P Q j h' (PairDecouple.depthLL b N - v) N‖ + 2 * (v : ℝ) / N)
      atTop (𝓝 0) := by
    simpa using hprim.norm.add hshift
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [(tendsto_depthLL hb).eventually_ge_atTop v] with N hN
  exact norm_depthAvg_dvd_le hb0 P Q j h' hN N

/-- A primitive twist level has a nontrivial leading root. -/
theorem depthRoot_ne_one_of_not_dvd {b : ℕ} (hb : 0 < b) {h' : ℤ} (hnd : ¬ ((b : ℤ) ∣ h')) :
    depthRoot b h' 0 ≠ 1 := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [depthRoot]
  intro hone
  obtain ⟨M, hM⟩ := ee_eq_one_iff_int.1 hone
  have hR : ((h' : ℝ)) = ((M * (b : ℤ) : ℤ) : ℝ) := by
    push_cast
    rw [pow_one] at hM
    field_simp at hM
    linarith [hM]
  have hZ : h' = M * (b : ℤ) := by exact_mod_cast hR
  exact hnd ⟨M, by rw [hZ]; ring⟩

/-- **The threshold data of the `K`-point input, `κ`-uniformly.**  TT Thm 3.1 carries a scale
threshold `X ≥ X₀(K)`; this says a threshold exists for every admissible saving exponent, and that
along the schedule it sits below the cut scale `N/2^{u_N}` for every level at or below
`depthLL b N` (so the constant level drop `v` of a divisible twist is covered too). -/
def KPointThresholdOK (b Q P : ℕ) (c₀ : ℝ) (m : ℕ) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 1 → ∃ Athr : ℕ → ℕ, (∀ K, 2 ≤ Athr K) ∧
    (∀ K : ℕ, max (max 2 ((K : ℝ) + 1)) ((Q * primorial P : ℕ) : ℝ)
        ≤ (2 * Real.log (Athr K)) ^ (κ * cKdeg c₀ m K)) ∧
    (∀ᶠ N : ℕ in atTop, ∀ K : ℕ, K ≤ PairDecouple.depthLL b N →
        Athr K ≤ N / 2 ^ (Nat.log 2 (Nat.log 2 N)))

/-- **`DepthDiagonal b` FROM THE DEGRADING INPUT — all twist levels.**  Both degenerate levels are
discharged inside: `hh = 0` by `depthAvg_zero_tendsto`, and `b ∣ hh` by
`depthAvg_dvd_tendsto_of_primitive` at the level `depthLL b N - v`.  Composed with
`weylLambertTwist_of_depthDiagonal` this makes the C3 crux a theorem on
`KPointNoExcWith (cKdeg c₀ m) (CstKdeg m)` plus the threshold data. -/
theorem depthDiagonal_of_degrading {b : ℕ} (hb : 2 ≤ b) {c₀ : ℝ} (hc₀ : 0 < c₀) (m : ℕ)
    (hin : ∀ K, KPointNoExcWith (cKdeg c₀ m) (CstKdeg m) K)
    (hthr : ∀ P Q : ℕ, 0 < Q → KPointThresholdOK b Q P c₀ m) :
    DepthDiagonal b := by
  intro P Q j hh hQ hj0 hjQ
  have hb0 : 0 < b := by omega
  rcases eq_or_ne hh 0 with rfl | hne
  · exact depthAvg_zero_tendsto b P Q j hj0 hjQ
  obtain ⟨v, h', hfac, hnd⟩ := exists_pow_mul_not_dvd hb hh hne
  subst hfac
  -- the archimedean side, at the primitive level
  set z : ℂ := depthRoot b h' 0 with hzdef
  have hznorm : ‖z‖ = 1 := norm_ee_real _
  have hz1 : z ≠ 1 := depthRoot_ne_one_of_not_dvd hb0 hnd
  set κ : ℝ := ttExponent z with hκdef
  have hκ : 0 < κ := ttExponent_pos hznorm hz1
  have hκ1 : κ ≤ 1 := ttExponent_le_one hznorm
  have hnp : ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat (depthRoot b h' 0)) X L :=
    ttNonPretentious_zOmegaNat hznorm hz1 le_rfl
  obtain ⟨Athr, hA2, hAthr, hAcut⟩ := hthr P Q hQ κ hκ hκ1
  -- the level sequence: the schedule lowered by `v`, kept positive
  set KN : ℕ → ℕ := fun N => max 1 (PairDecouple.depthLL b N - v) with hKNdef
  have hKN : ∀ N, 0 < KN N := fun N => lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hvN := (tendsto_depthLL hb).eventually_ge_atTop (v + 1)
  have hKle : ∀ᶠ N : ℕ in atTop, KN N ≤ PairDecouple.depthLL b N := by
    filter_upwards [hvN] with N hN
    rw [hKNdef]
    simp only
    omega
  have hKeq : ∀ᶠ N : ℕ in atTop, KN N = PairDecouple.depthLL b N - v := by
    filter_upwards [hvN] with N hN
    rw [hKNdef]
    simp only
    omega
  have hAle : ∀ᶠ N : ℕ in atTop,
      Athr (KN N) ≤ N / 2 ^ (Nat.log 2 (Nat.log 2 N)) := by
    filter_upwards [hAcut, hKle] with N hcut hle
    exact hcut _ hle
  have hgen := depthAvg_gen_tendsto_of_degrading_sched hb hQ P j h' hc₀ m KN hKN hKle hin
    hκ hκ1 hnp Athr hA2 hAthr hAle
  have hprim : Tendsto (fun N : ℕ =>
      depthAvg b P Q j h' (PairDecouple.depthLL b N - v) N) atTop (𝓝 0) := by
    refine hgen.congr' ?_
    filter_upwards [hKeq] with N hN
    rw [hN]
  exact depthAvg_dvd_tendsto_of_primitive hb P Q j h' v hprim

/-- **THE C3 CRUX FROM THE DEGRADING `K`-POINT INPUT.**  `WeylLambertTwist b` — hence `ConjC3` —
on `KPointNoExcWith (cKdeg c₀ m) (CstKdeg m)` and the threshold data alone.  Every other
ingredient (the archimedean certificate, the schedule comparison, the two degenerate twist
levels, the budget layer) is now discharged in-kernel. -/
theorem weylLambertTwist_of_degrading {b : ℕ} (hb : 3 ≤ b) {c₀ : ℝ} (hc₀ : 0 < c₀) (m : ℕ)
    (hin : ∀ K, KPointNoExcWith (cKdeg c₀ m) (CstKdeg m) K)
    (hthr : ∀ P Q : ℕ, 0 < Q → KPointThresholdOK b Q P c₀ m) :
    WeylLambertTwist b :=
  weylLambertTwist_of_depthDiagonal hb (depthDiagonal_of_degrading (by omega) hc₀ m hin hthr)

#print axioms NormalNumbers.CastingOut.quantDepthElliottGen_forces_diagonal
#print axioms NormalNumbers.CastingOut.weylLambertTwist_of_depthDiagonal
#print axioms NormalNumbers.CastingOut.kPointNoExc_of_with
#print axioms NormalNumbers.CastingOut.norm_progression_sum_le_class_sum
#print axioms NormalNumbers.CastingOut.progression_avg_le_of_window
#print axioms NormalNumbers.CastingOut.dyadic_window_bound_with
#print axioms NormalNumbers.CastingOut.windowPhi_antitone
#print axioms NormalNumbers.CastingOut.windowPhi_window_bound
#print axioms NormalNumbers.CastingOut.norm_progression_below_le
#print axioms NormalNumbers.CastingOut.depthAvg_le_of_window
#print axioms NormalNumbers.CastingOut.windowPhi_hwin
#print axioms NormalNumbers.CastingOut.depthAvg_le_with
#print axioms NormalNumbers.CastingOut.tendsto_natLog_shift_div
#print axioms NormalNumbers.CastingOut.depthAvg_diag_tendsto_of_unif
#print axioms NormalNumbers.CastingOut.rate_tendsto_of_exponent
#print axioms NormalNumbers.CastingOut.depthAvg_diag_tendsto_of_uniform
#print axioms NormalNumbers.CastingOut.exponent_tendsto_atBot_of_degrading
#print axioms NormalNumbers.CastingOut.depthAvg_diag_tendsto_of_degrading
#print axioms NormalNumbers.CastingOut.tendsto_degMinorant
#print axioms NormalNumbers.CastingOut.depthLL_succ_le_log
#print axioms NormalNumbers.CastingOut.le_sq_cut
#print axioms NormalNumbers.CastingOut.log_two_log_cut_ge
#print axioms NormalNumbers.CastingOut.hgrow_of_schedule
#print axioms NormalNumbers.CastingOut.depthAvg_diag_tendsto_of_degrading_sched
#print axioms NormalNumbers.CastingOut.twistAvg_tendsto
#print axioms NormalNumbers.CastingOut.depthAvg_zero_tendsto
#print axioms NormalNumbers.CastingOut.ee_tailDepth_dvd
#print axioms NormalNumbers.CastingOut.norm_depthAvg_dvd_le
#print axioms NormalNumbers.CastingOut.hgrow_of_schedule_le
#print axioms NormalNumbers.CastingOut.exists_pow_mul_not_dvd
#print axioms NormalNumbers.CastingOut.depthAvg_dvd_tendsto_of_primitive
#print axioms NormalNumbers.CastingOut.depthRoot_ne_one_of_not_dvd
#print axioms NormalNumbers.CastingOut.depthDiagonal_of_degrading
#print axioms NormalNumbers.CastingOut.weylLambertTwist_of_degrading
#print axioms NormalNumbers.CastingOut.depthAvg_gen_tendsto_of_unif
#print axioms NormalNumbers.CastingOut.depthAvg_gen_tendsto_of_degrading_sched

end CastingOut

end NormalNumbers
