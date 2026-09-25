import NormalNumbers.ElliottCaseA
import ErdosProblems.Erdos448.HalberstamComplete448

open NormalNumbers.ElliottMultStatement

/-!
# Hall's inequality for `‖g‖`, and the density mean-value bound

The thin-window regime of Case A needs the *density* form of the mean-value bound — the crude
Euler product over `m ≤ Y` loses the factor `log Y / log W`, which is unbounded when the window is
logarithmically thin.

**The hard core was already formalized.**  `Erdos448.HalberstamComplete448.halberstam_richert_explicit`
is exactly Halberstam–Richert Theorem 01, unconditional and explicit:
for nonnegative multiplicative `h` with `h(p^{j+1}) ≤ λ₁λ₂^j`, `λ₂ < 2`,
`∑_{n ≤ N} h n ≤ (K+1)·(N/log N)·∏_{p ≤ N} ∑'_j h(p^j)/p^j`.
A `1`-bounded `h` is the case `λ₁ = λ₂ = 1`.  (Recorded in `PENDING_WORK.md`: do not re-derive.)

This file instantiates it at `h = ‖g‖` and feeds the Euler product through the same local-factor /
Mertens chain as `NormalNumbers.ElliottEulerBound`, giving

`∑_{n ≤ N} ‖g n‖ ≤ (K+1)·e^{1+B}·N·exp(-Σ_N)`

— note the `log N` cancels exactly against the Euler product's.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottHall

open Erdos67b
open NormalNumbers.ElliottEulerBound
open NormalNumbers.ElliottCaseA

noncomputable section

/-- `n ↦ ‖g n‖`, extended by `0` at `0`. -/
noncomputable def normFun (g : ℤ → ℂ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ‖g (n : ℤ)‖

theorem normFun_apply (g : ℤ → ℂ) {n : ℕ} (hn : 0 < n) : normFun g n = ‖g (n : ℤ)‖ := by
  simp [normFun, hn.ne']

theorem normFun_nonneg (g : ℤ → ℂ) (n : ℕ) : 0 ≤ normFun g n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [normFun, h]
  · rw [normFun_apply g h]; exact norm_nonneg _

theorem normFun_le_one {g : ℤ → ℂ} (hg : ∀ n : ℤ, ‖g n‖ ≤ 1) (n : ℕ) : normFun g n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [normFun, h]
  · rw [normFun_apply g h]; exact hg _

theorem normFun_mul {g : ℤ → ℂ} (hg : IsCoprimeMultOnPosInt g) {m n : ℕ}
    (hmn : m.Coprime n) : normFun g (m * n) = normFun g m * normFun g n := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [normFun, hm]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [normFun, hn]
  rw [normFun_apply g (Nat.mul_pos hm hn), normFun_apply g hm, normFun_apply g hn]
  rw [show ((m * n : ℕ) : ℤ) = ((m * n : ℕ) : ℤ) from rfl, hg.2 m n hm hn hmn, norm_mul]

/-- The `p`-local factor of the Hall Euler product converges and is `≤ 1 + ‖g p‖/p + 1/(p(p-1))`. -/
theorem tsum_local_le {g : ℤ → ℂ} (hm : IsCoprimeMultOnPosInt g)
    (hg : ∀ n : ℤ, ‖g n‖ ≤ 1) {p : ℕ} (hp : p.Prime) :
    ∑' j : ℕ, normFun g (p ^ j) / ((p ^ j : ℕ) : ℝ) ≤
      1 + normFun g p / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < p := by linarith
  set r : ℝ := 1 / (p : ℝ) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hppos]; linarith
  have hterm : ∀ j : ℕ, normFun g (p ^ j) / ((p ^ j : ℕ) : ℝ) ≤ r ^ j := by
    intro j
    have hcast : (((p ^ j : ℕ)) : ℝ) = (p : ℝ) ^ j := by push_cast; ring
    rw [hcast]
    have hpow : (0 : ℝ) < (p : ℝ) ^ j := by positivity
    rw [hr, div_pow, one_pow]
    gcongr
    exact normFun_le_one hg _
  have hnn : ∀ j : ℕ, 0 ≤ normFun g (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
    intro j
    have : (0 : ℝ) ≤ ((p ^ j : ℕ) : ℝ) := by positivity
    exact div_nonneg (normFun_nonneg g _) this
  have hsummable : Summable fun j : ℕ ↦ normFun g (p ^ j) / ((p ^ j : ℕ) : ℝ) :=
    Summable.of_nonneg_of_le hnn hterm (summable_geometric_of_lt_one hr0.le hr1)
  -- split off `j = 0, 1` and bound the rest geometrically
  have hsplit : ∑' j : ℕ, normFun g (p ^ j) / ((p ^ j : ℕ) : ℝ) =
      normFun g 1 / ((1 : ℕ) : ℝ) + normFun g p / ((p : ℕ) : ℝ) +
        ∑' j : ℕ, normFun g (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ) := by
    rw [(hsummable.sum_add_tsum_nat_add 2).symm]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [add_assoc]
  have htail : ∑' j : ℕ, normFun g (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ) ≤
      1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    have hsub : Summable fun j : ℕ ↦ normFun g (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ) :=
      (hsummable.comp_injective (add_left_injective 2))
    have hle : ∀ j : ℕ, normFun g (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ) ≤ r ^ 2 * r ^ j := by
      intro j
      have := hterm (j + 2)
      calc _ ≤ r ^ (j + 2) := this
        _ = r ^ 2 * r ^ j := by ring
    refine (hsub.tsum_le_tsum hle
      ((summable_geometric_of_lt_one hr0.le hr1).mul_left _)).trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1]
    rw [hr, div_pow, one_pow]
    have h1 : (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
    rw [h1]
    field_simp
    ring_nf
    exact le_refl _
  have hone : normFun g 1 = 1 := by
    rw [normFun_apply g Nat.one_pos]
    norm_num [hm.1]
  rw [hsplit, hone, Nat.cast_one, div_one]
  linarith [htail]

/-- The Hall constant for a `1`-bounded multiplicative function (`λ₁ = λ₂ = 1`). -/
noncomputable def hallConst : ℝ := HalberstamScratch.explicitMassConstant 1 1 + 1

theorem hallConst_pos : 0 < hallConst := by
  rw [hallConst, HalberstamScratch.explicitMassConstant]
  have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem defectOf_normFun_eq (g : ℤ → ℂ) (N : ℕ) :
    defectOf (fun n ↦ normFun g n / (n : ℝ)) N = primeDefect (normDivArith g) N := by
  rw [primeDefect, defectOf]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
  rw [normDivArith_apply g hpp.pos, normFun_apply g hpp.pos]

/-- **Hall's inequality for `‖g‖`, in density form.**  For `g` multiplicative and `1`-bounded on
the positive integers,

`∑_{n ≤ N} ‖g n‖ ≤ hallConst · e^{1+B} · N · exp(-Σ_N)`,

`Σ_N = ∑_{p ≤ N} (1/p - ‖g p‖/p)`.  The `log N` of Halberstam–Richert cancels exactly against the
`log N` of the Euler product.

This is the density bound the *thin-window* regime of Case A needs: unlike the crude
`ElliottEulerBound.sum_Icc_le_log_mul_exp_neg_defect`, it has no `log N` left over, so dyadic
partial summation over the window costs only `log W`. -/
theorem sum_Icc_normFun_le {g : ℤ → ℂ} (hm : IsCoprimeMultOnPosInt g)
    (hg : ∀ n : ℤ, ‖g n‖ ≤ 1) {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, normFun g n ≤
      hallConst * Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) * (N : ℝ) *
        Real.exp (-primeDefect (normDivArith g) N) := by
  classical
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set w : ℕ → ℝ := fun n ↦ normFun g n / (n : ℝ) with hw
  -- Halberstam–Richert
  have hone : normFun g 1 = 1 := by
    rw [normFun_apply g Nat.one_pos]; norm_num [hm.1]
  have hall := HalberstamComplete448.halberstam_richert_explicit (normFun g)
    (by simp [normFun]) hone (fun {m n} hmn ↦ normFun_mul hm hmn) (normFun_nonneg g)
    1 1 (by norm_num) (by norm_num) (by norm_num)
    (fun p _ j ↦ by simpa using normFun_le_one hg (p ^ (j + 1))) N hN
  rw [HalberstamScratch.partialSum] at hall
  -- the Euler product
  have hF0 : ∀ p ∈ Nat.primesBelow (N + 1),
      0 ≤ ∑' j : ℕ, normFun g (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
    intro p _
    refine tsum_nonneg fun j ↦ ?_
    have : (0 : ℝ) ≤ ((p ^ j : ℕ) : ℝ) := by positivity
    exact div_nonneg (normFun_nonneg g _) this
  have hFle : ∀ p ∈ Nat.primesBelow (N + 1),
      (∑' j : ℕ, normFun g (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        1 + w p + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    exact tsum_local_le hm hg (Nat.mem_primesBelow.mp hp).2
  have hprod := prod_le_exp_prime_sum (w := w) hF0 hFle
  have hmert := exp_prime_sum_le_log_mul_exp_neg_defect w hN
  have hchain : (∏ p ∈ Nat.primesBelow (N + 1),
      ∑' j : ℕ, normFun g (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) * Real.log (N : ℝ) *
        Real.exp (-primeDefect (normDivArith g) N) := by
    refine hprod.trans ?_
    rw [← defectOf_normFun_eq g N]
    exact hmert
  have hpre : (0 : ℝ) ≤ hallConst * ((N : ℝ) / Real.log (N : ℝ)) := by
    have := hallConst_pos
    positivity
  calc ∑ n ∈ Finset.Icc 1 N, normFun g n
      ≤ hallConst * ((N : ℝ) / Real.log (N : ℝ)) *
          ∏ p ∈ Nat.primesBelow (N + 1), ∑' j : ℕ, normFun g (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
        rw [hallConst]
        convert hall using 2
        ring
    _ ≤ hallConst * ((N : ℝ) / Real.log (N : ℝ)) *
          (Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) * Real.log (N : ℝ) *
            Real.exp (-primeDefect (normDivArith g) N)) :=
        mul_le_mul_of_nonneg_left hchain hpre
    _ = _ := by field_simp


/-! ## Dyadic partial summation: the thin-window logarithmic sum -/

/-- The pretentious defect grows with the scale (each term `1/p - ‖g p‖/p` is nonnegative). -/
theorem primeDefect_mono {g : ℤ → ℂ} (hg : ∀ n : ℤ, ‖g n‖ ≤ 1) {L N : ℕ} (h : L ≤ N) :
    primeDefect (normDivArith g) L ≤ primeDefect (normDivArith g) N := by
  rw [primeDefect, primeDefect]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    obtain ⟨hpL, hpp⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩
  · intro p hp _
    have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    rw [normDivArith_apply g hpp.pos]
    rw [sub_nonneg, div_le_iff₀ hppos]
    rw [inv_mul_cancel₀ (ne_of_gt hppos)]
    exact hg _

/-- One dyadic block contributes at most `2 · hallConst · e^{1+B} · e^{-Σ_L}`. -/
theorem sum_dyadic_block_le {g : ℤ → ℂ} (hm : IsCoprimeMultOnPosInt g)
    (hg : ∀ n : ℤ, ‖g n‖ ≤ 1) {L : ℕ} (hL : 1 ≤ L) (j : ℕ) :
    ∑ m ∈ Finset.Icc (L * 2 ^ j) (L * 2 ^ (j + 1) - 1), normDivArith g m ≤
      2 * hallConst * Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) *
        Real.exp (-primeDefect (normDivArith g) L) := by
  classical
  set N : ℕ := L * 2 ^ (j + 1) with hN
  set T : ℕ := L * 2 ^ j with hT
  have hTpos : 0 < T := by rw [hT]; positivity
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hN2 : 2 ≤ N := by
    rw [hN, pow_succ]
    have : 1 * 2 ≤ L * (2 ^ j * 2) := by
      refine Nat.mul_le_mul hL ?_
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega
    omega
  have hNT : (N : ℝ) = 2 * T := by rw [hN, hT]; push_cast; ring
  -- bound each term by `‖g m‖ / T`
  have hstep : ∑ m ∈ Finset.Icc T (N - 1), normDivArith g m ≤
      (T : ℝ)⁻¹ * ∑ m ∈ Finset.Icc 1 N, normFun g m := by
    have h1 : ∀ m ∈ Finset.Icc T (N - 1), normDivArith g m ≤ (T : ℝ)⁻¹ * normFun g m := by
      intro m hm'
      obtain ⟨hmT, -⟩ := Finset.mem_Icc.mp hm'
      have hmpos : 0 < m := by omega
      have hmr : (0 : ℝ) < m := by exact_mod_cast hmpos
      have hTm : (T : ℝ) ≤ m := by exact_mod_cast hmT
      rw [normDivArith_apply g hmpos, ← normFun_apply g hmpos]
      rw [div_le_iff₀ hmr, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hTr]
      nlinarith [normFun_nonneg g m, hTm, hTr]
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ ↦ normFun_nonneg g i)
    intro m hm'
    obtain ⟨hmT, hmN⟩ := Finset.mem_Icc.mp hm'
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hhall := sum_Icc_normFun_le hm hg hN2
  have hdef : Real.exp (-primeDefect (normDivArith g) N) ≤
      Real.exp (-primeDefect (normDivArith g) L) := by
    apply Real.exp_le_exp.mpr
    have : L ≤ N := by
      rw [hN]
      calc L = L * 1 := by ring
        _ ≤ L * 2 ^ (j + 1) := Nat.mul_le_mul_left L Nat.one_le_two_pow
    linarith [primeDefect_mono hg this]
  calc ∑ m ∈ Finset.Icc T (N - 1), normDivArith g m
      ≤ (T : ℝ)⁻¹ * ∑ m ∈ Finset.Icc 1 N, normFun g m := hstep
    _ ≤ (T : ℝ)⁻¹ * (hallConst * Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) * (N : ℝ) *
          Real.exp (-primeDefect (normDivArith g) N)) :=
        mul_le_mul_of_nonneg_left hhall (by positivity)
    _ ≤ (T : ℝ)⁻¹ * (hallConst * Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) * (N : ℝ) *
          Real.exp (-primeDefect (normDivArith g) L)) := by
        have hpos : (0 : ℝ) ≤ (T : ℝ)⁻¹ *
            (hallConst * Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) * (N : ℝ)) := by
          have := hallConst_pos
          positivity
        nlinarith [hdef, hpos, (Real.exp_pos (-primeDefect (normDivArith g) L)).le]
    _ = _ := by rw [hNT]; field_simp


/-- **The dyadic logarithmic sum.**  Over `L ≤ m ≤ Y` the logarithmic mean of `‖g‖` costs only the
*number of dyadic blocks*, `⌊log₂(Y/L)⌋+1`, times `e^{-Σ_L}` — not `log Y`.

This is what the crude Euler bound cannot give, and it is exactly the thin-window statement:
with `L ≈ Y/W` the block count is `≈ log₂ W`. -/
theorem sum_Icc_dyadic_le {g : ℤ → ℂ} (hm : IsCoprimeMultOnPosInt g)
    (hg : ∀ n : ℤ, ‖g n‖ ≤ 1) {L Y : ℕ} (hL : 1 ≤ L) :
    ∑ m ∈ Finset.Icc L Y, normDivArith g m ≤
      ((Nat.log 2 (Y / L) + 1 : ℕ) : ℝ) *
        (2 * hallConst * Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) *
          Real.exp (-primeDefect (normDivArith g) L)) := by
  classical
  set J : ℕ := Nat.log 2 (Y / L) + 1 with hJ
  set blk : ℕ → Finset ℕ := fun j ↦ Finset.Icc (L * 2 ^ j) (L * 2 ^ (j + 1) - 1) with hblk
  have hsub : Finset.Icc L Y ⊆ (Finset.range J).biUnion blk := by
    intro m hm'
    obtain ⟨hmL, hmY⟩ := Finset.mem_Icc.mp hm'
    have hmpos : 0 < m := by omega
    have hqpos : 0 < m / L := Nat.one_le_div_iff (by omega) |>.mpr hmL
    set j : ℕ := Nat.log 2 (m / L) with hj
    have hlow : 2 ^ j ≤ m / L := Nat.pow_log_le_self 2 (by omega)
    have hhigh : m / L < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr ?_, ?_⟩
    · have : m / L ≤ Y / L := Nat.div_le_div_right hmY
      have := Nat.log_mono_right (b := 2) this
      omega
    · refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · calc L * 2 ^ j ≤ L * (m / L) := Nat.mul_le_mul_left L hlow
          _ ≤ m := Nat.mul_div_le m L
      · have h1 : m < L * (m / L + 1) := by
          have := Nat.div_add_mod m L
          have := Nat.mod_lt m (show 0 < L by omega)
          nlinarith [Nat.div_add_mod m L, Nat.mod_lt m (show 0 < L by omega)]
        have h2 : L * (m / L + 1) ≤ L * 2 ^ (j + 1) := Nat.mul_le_mul_left L (by omega)
        omega
  have hdisj : (↑(Finset.range J) : Set ℕ).PairwiseDisjoint blk := by
    intro i _ k _ hik
    rcases Nat.lt_or_ge i k with h | h
    · refine Finset.disjoint_left.mpr fun m hmi hmk ↦ ?_
      obtain ⟨-, hi2⟩ := Finset.mem_Icc.mp hmi
      obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hmk
      have hpow : L * 2 ^ (i + 1) ≤ L * 2 ^ k :=
        Nat.mul_le_mul_left L (Nat.pow_le_pow_right (by norm_num) (by omega))
      have : 0 < L * 2 ^ (i + 1) := by positivity
      omega
    · have hki : k < i := by omega
      refine Finset.disjoint_left.mpr fun m hmi hmk ↦ ?_
      obtain ⟨hi1, -⟩ := Finset.mem_Icc.mp hmi
      obtain ⟨-, hk2⟩ := Finset.mem_Icc.mp hmk
      have hpow : L * 2 ^ (k + 1) ≤ L * 2 ^ i :=
        Nat.mul_le_mul_left L (Nat.pow_le_pow_right (by norm_num) (by omega))
      have : 0 < L * 2 ^ (k + 1) := by positivity
      omega
  have hexpand : ∑ m ∈ (Finset.range J).biUnion blk, normDivArith g m =
      ∑ j ∈ Finset.range J, ∑ m ∈ blk j, normDivArith g m :=
    Finset.sum_biUnion hdisj
  calc ∑ m ∈ Finset.Icc L Y, normDivArith g m
      ≤ ∑ m ∈ (Finset.range J).biUnion blk, normDivArith g m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ ↦ normDivArith_nonneg g i)
    _ = ∑ j ∈ Finset.range J, ∑ m ∈ blk j, normDivArith g m := hexpand
    _ ≤ ∑ _j ∈ Finset.range J, (2 * hallConst *
          Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) *
          Real.exp (-primeDefect (normDivArith g) L)) :=
        Finset.sum_le_sum fun j _ ↦ sum_dyadic_block_le hm hg hL j
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]


end

end NormalNumbers.ElliottHall

#print axioms NormalNumbers.ElliottHall.sum_Icc_normFun_le
#print axioms NormalNumbers.ElliottHall.sum_Icc_dyadic_le
