import NormalNumbers.PrimeModelKMTFixedH

/-!
# Theorem A, leg E1: the graded (per-site) transfer error

Lap 6a of `KICKOFF-2026-09-22-multicutoff-lean.md`; spec `papers/ROUND2-multicutoff-fable.md` §2
("E1").  The fixed-cutoff transfer error `windowMean_sub_windowMeanLe_le_h` truncates every site
of the window product at the **same** `y`.  Theorem A truncates site `j` at its own cutoff `y_j`:

    ‖W − W_{y⃗}‖ ≤ ∑_j a_j (2 R(y_j, N) + k/N),      a_j = 4π|h| / 4^{j+1}.

Specialising `y_j = y` recovers the old bound (`∑_j a_j ≤ 4π|h|/3`), so nothing is lost; what is
gained is that a site whose cutoff is large pays only its own fresh mass.

The proof is the ungraded one with the index promoted: the sitewise estimate
`‖z_j^{a+c} − z_j^a‖ ≤ c ‖z_j − 1‖ ≤ c a_j` is already per-site, and
`PhaseFactor.sum_omegaGt_shift_le` is already general in `y`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.KMT

open NormalNumbers.PrimeLambert NormalNumbers.G4 NormalNumbers.G4Sparse
open NormalNumbers.PrimeModel NormalNumbers.PrimeModel.PhaseAlgebra
open NormalNumbers.PrimeModel.PhaseFactor

variable (S : ℕ → Prop) [DecidablePred S]

/-- The per-site phase budget `a_j = 4π|h| / 4^{j+1}` (Fable §2). -/
noncomputable def siteBudget (h : ℤ) (j : ℕ) : ℝ :=
  4 * Real.pi * |(h : ℝ)| * ((1 : ℝ) / 4) ^ (j + 1)

theorem siteBudget_nonneg (h : ℤ) (j : ℕ) : 0 ≤ siteBudget h j := by
  unfold siteBudget; positivity

theorem sum_siteBudget_le (h : ℤ) (k : ℕ) :
    ∑ j : Fin k, siteBudget h j.val ≤ 4 * Real.pi * |(h : ℝ)| / 3 := by
  have heq : ∀ m : ℕ, ∑ j ∈ Finset.range m, ((1 : ℝ) / 4) ^ (j + 1)
      = (1 - ((1 : ℝ) / 4) ^ m) / 3 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  have hgeom : ∑ j ∈ Finset.range k, ((1 : ℝ) / 4) ^ (j + 1) ≤ 1 / 3 := by
    rw [heq k]
    have : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ k := by positivity
    linarith
  have h1 : ∑ j : Fin k, siteBudget h j.val = ∑ j ∈ Finset.range k, siteBudget h j :=
    Fin.sum_univ_eq_sum_range (fun j => siteBudget h j) k
  have h2 : ∑ j ∈ Finset.range k, siteBudget h j
      = (4 * Real.pi * |(h : ℝ)|) * ∑ j ∈ Finset.range k, ((1 : ℝ) / 4) ^ (j + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by unfold siteBudget; ring
  rw [h1, h2]
  have hc : (0 : ℝ) ≤ 4 * Real.pi * |(h : ℝ)| := by positivity
  nlinarith [hgeom]

theorem norm_zPhase_sub_one_le' (h : ℤ) (k : ℕ) (j : Fin k) :
    ‖zPhase h k j - 1‖ ≤ siteBudget h j.val := by
  have hz0 : ePhase (0 : ℝ) = 1 := by simp [ePhase]
  have hb := norm_ePhase_sub ((h : ℝ) / (4 : ℝ) ^ (j.val + 1)) 0
  rw [hz0] at hb
  have habs : |(h : ℝ) / (4 : ℝ) ^ (j.val + 1) - 0| = |(h : ℝ)| * ((1 : ℝ) / 4) ^ (j.val + 1) := by
    rw [sub_zero, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ (j.val + 1)),
      div_pow, one_pow]
    ring
  rw [habs] at hb
  have hzeq : zPhase h k j = ePhase ((h : ℝ) / (4 : ℝ) ^ (j.val + 1)) := rfl
  rw [hzeq]
  refine hb.trans (le_of_eq ?_)
  unfold siteBudget; ring

theorem norm_pow_sub_pow_le'' (z : ℂ) (hz : ‖z‖ = 1) (a c : ℕ) {B : ℝ}
    (hB : ‖z - 1‖ ≤ B) : ‖z ^ (a + c) - z ^ a‖ ≤ (c : ℝ) * B := by
  have hrw : z ^ (a + c) - z ^ a = z ^ a * (z ^ c - 1) := by ring
  rw [hrw, norm_mul, norm_pow, hz, one_pow, one_mul]
  refine (norm_pow_sub_one_le z hz c).trans ?_
  exact mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg c)

/-- **The graded truncated window mean**: site `j` keeps only the primes `≤ y j`. -/
noncomputable def windowMeanLeG (k : ℕ) (y : Fin k → ℕ) (h : ℤ) (x : ℕ) : ℂ :=
  prefixMean (fun n => ∏ j : Fin k, zPhase h k j ^ omegaLe S (y j) (n + j.val + 1)) x

theorem windowMeanLeG_const (k y : ℕ) (h : ℤ) (x : ℕ) :
    windowMeanLeG S k (fun _ => y) h x = windowMeanLe S y k h x := rfl

/-- **Theorem A, leg E1 (graded).** -/
theorem windowMean_sub_windowMeanLeG_le (k : ℕ) (y : Fin k → ℕ) (h : ℤ) (x : ℕ) (hx : 1 ≤ x) :
    ‖windowMeanS S k h x - windowMeanLeG S k y h x‖
      ≤ ∑ j : Fin k, siteBudget h j.val * (2 * recipSumIoc S (y j) x + (k : ℝ) / x) := by
  classical
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx0
  have key : ∀ n : ℕ,
      ‖ePhase ((h : ℝ) * truncTailS S k n)
        - ∏ j : Fin k, zPhase h k j ^ omegaLe S (y j) (n + j.val + 1)‖
        ≤ ∑ j : Fin k, siteBudget h j.val * (omegaGt S (y j) (n + j.val + 1) : ℝ) := by
    intro n
    rw [window_term_eq]
    refine le_trans (norm_prod_sub_prod_le Finset.univ _ _ ?_ ?_) ?_
    · intro i _; rw [norm_pow, norm_zPhase, one_pow]
    · intro i _; rw [norm_pow, norm_zPhase, one_pow]
    · refine Finset.sum_le_sum fun i _ => ?_
      rw [omegaSN_eq_omegaLe_add_omegaGt S (y i)]
      refine le_trans (norm_pow_sub_pow_le'' _ (norm_zPhase h k i) _ _
        (norm_zPhase_sub_one_le' h k i)) (le_of_eq ?_)
      ring
  rw [windowMeanS, windowMeanLeG, prefixMean, prefixMean, div_sub_div_same, norm_div,
    Complex.norm_natCast, ← Finset.sum_sub_distrib]
  rw [div_le_iff₀ hx0]
  have hnum : ‖∑ n ∈ Finset.range x,
      (ePhase ((h : ℝ) * truncTailS S k n)
        - ∏ j : Fin k, zPhase h k j ^ omegaLe S (y j) (n + j.val + 1))‖
      ≤ ∑ j : Fin k, siteBudget h j.val * (2 * (x : ℝ) * recipSumIoc S (y j) x + k) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun n _ => key n) ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_omegaGt_shift_le S (y j) k x j.val j.isLt)
      (siteBudget_nonneg h j.val)
  refine hnum.trans (le_of_eq ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

end NormalNumbers.PrimeModel.KMT
