/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorBadNormal

/-!
# Retired off-path nodes of `CantorBadNormal`

Moved verbatim from `CantorBadNormal.lean` (operator rescope 2026-10-06): the two off-path open
nodes `midStages` (the Cassels-rate route for `resLaw`) and
`fourierPairRate_descent_of_deadRateDecay` (the rule-independent `DeadRateDecay` reduction),
together with every declaration that depends on them or is used only by them.  Statements,
docstrings and confidences are unchanged.  After the move, `CantorBadNormal.lean` contains exactly
the headline path, so its `sorry`s are the headline's open obligations.
-/

namespace NormalNumbers.CantorBadNormal

open SchmidtGames MeasureTheory Filter Topology
open CantorLiouville CantorLiouvilleAll DecayAeNormal ExplicitSquare

/-- The coin block at stage `s` is dead (the descent intervenes there). -/
def DeadAt (s : ℕ) (ω : ℕ → Bool) : Prop :=
  ¬ Alive 5 c₀ (build 5 c₀ s ω) (List.ofFn fun i : Fin (2 * 5) => ω (2 * 5 * s + i))

/-- **Open node: Cesàro decay of the dead-stage probability**, at a rate summable along
`sched`.  Believed false (80%): the numerics in `AdversarialReplacement` show a flat rate
`η ≈ 10⁻³`.  Recorded because it is exactly what the rule-independent reduction below needs. -/
def DeadRateDecay : Prop :=
  ∃ W : ℕ → ℝ, Summable (fun j => W (sched j)) ∧ ∀ S : ℕ, 1 ≤ S →
    (∑ s ∈ Finset.range S, (coinMeasure {ω | DeadAt s ω}).toReal) ≤ S * W S

/-- **Rule-independent reduction (believed, 75%): dead-stage decay gives the crux.**

English proof.  Write `ν̂(ξ) = E[Π_s X_s]`, `X_s = e(ξ·3^{−10s}·y_s)` for the block digits `y_s`.
Conditioning on the prefix, `E[X_s | F_{s−1}] = ρ_s(ξ) + ε_s`, `ρ_s` the uniform-block character and
`|ε_s| ≤ 2·(4/1024)·1{DeadAt s}`-mass, with additionally `|ε_s| ≤ 8π|ξ|3^{−10(s+1)}·1{dead}` for blocks
finer than `ξ`.  This holds for EVERY admissible replacement rule (only the dead coin mass moves).
Peeling from the top: `|ν̂(ξ)| ≤ Π|ρ_s| + Σ_S P(DeadAt S)·min(1, |ξ|3^{−10S})·Π_{s>S}|ρ_s|`.  For
`ξ = h(bⁿ−bᵐ)`, `3 ∤ b`, the Cantor products decay on average over `(n,m)` (Cassels/Feldman–Smorodinsky),
so only `O(1)` stages near `S ≈ n log₃ b / 10` survive and the pair sum is `O(N² W(N)) + o(N²)` at a
summable rate.  The step most in doubt: a quantitative pair-average of the partial Cantor products.
Consequence: with `AdversarialReplacement`, the crux is essentially equivalent to `DeadRateDecay`. -/
theorem fourierPairRate_descent_of_deadRateDecay (hD : DeadRateDecay) {b : ℕ} (hb : 2 ≤ b)
    (h3 : ¬ 3 ∣ b) : FourierPairRate descentLaw b := by
  sorry

/-- **Exact unrolled recursion.**  Proved from `prefChar_succ`. -/
theorem prefChar_eq (ξ : ℝ) (S : ℕ) :
    prefChar ξ S = rhoProd ξ 0 S - ∑ S' ∈ Finset.range S, deadChar ξ S' * rhoProd ξ (S' + 1) S := by
  induction S with
  | zero => simp [prefChar_zero, rhoProd]
  | succ S ih =>
    rw [prefChar_succ, ih, Finset.sum_range_succ]
    have h1 : rhoProd ξ 0 (S + 1) = rhoProd ξ 0 S * rhoS ξ (10 * S) := by
      rw [rhoProd, Finset.prod_Ico_succ_top (Nat.zero_le _)]; rfl
    have h2 : ∀ S' ∈ Finset.range S, rhoProd ξ (S' + 1) (S + 1) =
        rhoProd ξ (S' + 1) S * rhoS ξ (10 * S) := by
      intro S' hS'
      rw [Finset.mem_range] at hS'
      rw [rhoProd, Finset.prod_Ico_succ_top (by omega)]; rfl
    have h3 : rhoProd ξ (S + 1) (S + 1) = 1 := by simp [rhoProd]
    have hs : ∑ S' ∈ Finset.range S, deadChar ξ S' * rhoProd ξ (S' + 1) (S + 1) =
        rhoS ξ (10 * S) * ∑ S' ∈ Finset.range S, deadChar ξ S' * rhoProd ξ (S' + 1) S := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S' hS' => ?_
      rw [h2 S' hS']; ring
    rw [h1, h3, hs]
    ring

/-- The second moment is the real part of a signed pair sum of Fourier coefficients.  Proved. -/
theorem secondMoment_le_norm_sum (L : Law) (b : ℕ) (h : ℤ) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (L.φ ω))‖ ^ 2 ∂coinMeasure ≤
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * cpt (L.φ ω)) ∂coinMeasure‖ := by
  have hG : Measurable fun ω => cpt (L.φ ω) := measurable_cpt.comp L.meas
  have hint : ∀ ξ : ℝ, Integrable (fun ω => ee (ξ * cpt (L.φ ω))) coinMeasure := fun ξ =>
    Integrable.of_bound ((measurable_ee.comp (hG.const_mul ξ)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => (norm_ee _).le)
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (L.φ ω))‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * cpt (L.φ ω)) := by
    intro ω
    rw [sq_norm_sum_ee (fun k => h * (b : ℝ) ^ k * cpt (L.φ ω))]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cpt (L.φ ω))‖ ^ 2 ∂coinMeasure : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * cpt (L.φ ω)) ∂coinMeasure := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ fun m _ => hint _]
  have := congrArg Complex.re hI
  rw [Complex.ofReal_re] at this
  rw [this]
  exact Complex.re_le_norm _

/-- **The stage-`S'` dead character is `O(|ξ| 3^{−10S'})`.**  Proved. -/
theorem norm_deadChar_le (ξ : ℝ) (S : ℕ) :
    ‖deadChar ξ S‖ ≤ 1024 * (2 * Real.pi * |ξ| / 3 ^ (10 * S)) := by
  unfold deadChar
  have := norm_integral_le_of_norm_le_const (μ := coinMeasure)
    (f := fun ω => ee (ξ * cylLeft (buildU S ω)) * deadErr ξ (buildU S ω))
    (C := 1024 * (2 * Real.pi * |ξ| / 3 ^ (10 * S))) (Eventually.of_forall fun ω => by
      rw [norm_mul, norm_ee, one_mul, ← length_buildU ω S]; exact norm_deadErr_le _ _)
  simpa using this

theorem nat_tail_ineq {b N k : ℕ} (hb : 2 ≤ b) (hN : 1 ≤ N) :
    3 ^ 10 * k * b ^ N * N ≤ 3 ^ (9 * (N * b + k)) := by
  have h1 : k ≤ 3 ^ k := (Nat.lt_pow_self (by norm_num)).le
  have h2 : b ^ N ≤ 3 ^ (b * N) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_pow_self (by norm_num)).le _
  have h3 : N ≤ 3 ^ (b * N) :=
    (Nat.lt_pow_self (by norm_num)).le.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have h4 : 3 ^ 10 ≤ 3 ^ (5 * (b * N)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc 3 ^ 10 * k * b ^ N * N ≤ 3 ^ (5 * (b * N)) * 3 ^ k * 3 ^ (b * N) * 3 ^ (b * N) := by gcongr
    _ = 3 ^ (7 * (b * N) + k) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- **Stages beyond `S₀ = N b + |h|` are negligible** (locality, from `norm_deadChar_le`).
Proved: the tail of the signed stage sum is at most `1/N` for each pair `(n, m)`. -/
theorem deadChar_tail_le {b : ℕ} (hb : 2 ≤ b) (h : ℤ) {N n m : ℕ} (hN : 1 ≤ N) (hn : n ≤ N)
    (hm : m ≤ N) (S : ℕ) :
    ‖∑ S' ∈ Finset.Ico (N * b + h.natAbs) S, deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
        rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S‖ ≤ 1 / N := by
  set ξ : ℝ := h * ((b : ℝ) ^ n - (b : ℝ) ^ m)
  set S₀ := N * b + h.natAbs
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hξ : |ξ| ≤ 2 * h.natAbs * (b : ℝ) ^ N := by
    have e1 : (b : ℝ) ^ n ≤ (b : ℝ) ^ N := pow_le_pow_right₀ hb1 hn
    have e2 : (b : ℝ) ^ m ≤ (b : ℝ) ^ N := pow_le_pow_right₀ hb1 hm
    have p1 : (0 : ℝ) ≤ (b : ℝ) ^ n := by positivity
    have p2 : (0 : ℝ) ≤ (b : ℝ) ^ m := by positivity
    have hna : ((h.natAbs : ℕ) : ℝ) = |(h : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [abs_mul, hna]
    have : |(b : ℝ) ^ n - (b : ℝ) ^ m| ≤ 2 * (b : ℝ) ^ N := by rw [abs_le]; constructor <;> linarith
    calc |(h : ℝ)| * |(b : ℝ) ^ n - (b : ℝ) ^ m| ≤ |(h : ℝ)| * (2 * (b : ℝ) ^ N) := by gcongr
      _ = _ := by ring
  set Y : ℝ := 1024 * (2 * Real.pi * |ξ|) / 3 ^ (9 * S₀)
  have hterm : ∀ S' ∈ Finset.Ico S₀ S, ‖deadChar ξ S' * rhoProd ξ (S' + 1) S‖ ≤ Y * (1 / 3) ^ S' := by
    intro S' hS'
    rw [Finset.mem_Ico] at hS'
    have hp : (3 : ℝ) ^ (9 * S₀) * 3 ^ S' ≤ 3 ^ (10 * S') := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [norm_mul, norm_rhoProd _ (by omega)]
    calc ‖deadChar ξ S'‖ * tailProd ξ (10 * (S' + 1)) (10 * S) ≤ ‖deadChar ξ S'‖ :=
          mul_le_of_le_one_right (norm_nonneg _) (tailProd_le_one _ _ _)
      _ ≤ 1024 * (2 * Real.pi * |ξ| / 3 ^ (10 * S')) := norm_deadChar_le ξ S'
      _ = 1024 * (2 * Real.pi * |ξ|) / 3 ^ (10 * S') := by ring
      _ ≤ 1024 * (2 * Real.pi * |ξ|) / (3 ^ (9 * S₀) * 3 ^ S') :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hp
      _ = Y * (1 / 3) ^ S' := by simp only [Y]; rw [one_div_pow]; field_simp
  have hgeo : ∑ S' ∈ Finset.Ico S₀ S, (1 / 3 : ℝ) ^ S' ≤ 3 / 2 :=
    (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans (by
      rw [div_le_iff₀ (by norm_num)]
      have : (1 / 3 : ℝ) ^ S₀ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith)
  have hY : 0 ≤ Y := by positivity
  have hfin : Y * (3 / 2) ≤ 1 / N := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have key : ((3 ^ 10 * h.natAbs * b ^ N * N : ℕ) : ℝ) ≤ ((3 ^ (9 * S₀) : ℕ) : ℝ) := by
      exact_mod_cast nat_tail_ineq hb hN
    push_cast at key
    rw [le_div_iff₀ hNpos]
    have hpi := Real.pi_lt_four
    have h1 : 1024 * (2 * Real.pi * |ξ|) * (3 / 2) * N ≤ 3 ^ 10 * h.natAbs * (b : ℝ) ^ N * N := by
      have : 1024 * (2 * Real.pi * |ξ|) * (3 / 2) ≤ 3 ^ 10 * h.natAbs * (b : ℝ) ^ N := by
        have hh0 : (0 : ℝ) ≤ h.natAbs * (b : ℝ) ^ N := by positivity
        nlinarith [abs_nonneg ξ, Real.pi_pos]
      exact mul_le_mul_of_nonneg_right this hNpos.le
    have h3 : (0 : ℝ) < 3 ^ (9 * S₀) := by positivity
    calc Y * (3 / 2) * N = 1024 * (2 * Real.pi * |ξ|) * (3 / 2) * N / 3 ^ (9 * S₀) := by
          simp only [Y]; ring
      _ ≤ 1 := by rw [div_le_one h3]; exact h1.trans (by norm_num at key ⊢; linarith)
  calc _ ≤ ∑ S' ∈ Finset.Ico S₀ S, ‖deadChar ξ S' * rhoProd ξ (S' + 1) S‖ := norm_sum_le _ _
    _ ≤ ∑ S' ∈ Finset.Ico S₀ S, Y * (1 / 3) ^ S' := Finset.sum_le_sum hterm
    _ = Y * ∑ S' ∈ Finset.Ico S₀ S, (1 / 3 : ℝ) ^ S' := by rw [Finset.mul_sum]
    _ ≤ Y * (3 / 2) := mul_le_mul_of_nonneg_left hgeo hY
    _ ≤ _ := hfin

/-- **Hybrid telescope.**  Proved from `prefChar_succ`.  The dead-character stage sum is
`Π_{s<S} ρ_s − T_a · Π_{a≤s<S} ρ_s`, the character of uniform digits minus that of the hybrid law
(`resLaw` for `a` stages, then uniform digits to depth `S`). -/
theorem stage_telescope (ξ : ℝ) {a S : ℕ} (haS : a ≤ S) :
    ∑ S' ∈ Finset.range a, deadChar ξ S' * rhoProd ξ (S' + 1) S =
      rhoProd ξ 0 S - prefChar ξ a * rhoProd ξ a S := by
  induction a with
  | zero => simp [prefChar_zero, rhoProd]
  | succ a ih =>
    rw [Finset.sum_range_succ, ih (by omega), prefChar_succ]
    have : rhoProd ξ a S = rhoS ξ (10 * a) * rhoProd ξ (a + 1) S := by
      rw [rhoProd, rhoProd, Finset.prod_eq_prod_Ico_succ_bot (by omega)]
    rw [this]; ring

/-- `exp(−c ⌊log₃N⌋/2) ≤ e^c N^{−c/(2 log 3)}`.  Proved (from the `cassels_Bf` bookkeeping). -/
theorem exp_neg_log3_le {c : ℝ} (hc : 0 ≤ c) {N : ℕ} (hN : 1 ≤ N) :
    Real.exp (-c * ((Nat.log 3 N / 2 : ℕ) : ℝ)) ≤ Real.exp c * (N : ℝ) ^ (-(c / (2 * Real.log 3))) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set k := Nat.log 3 N
  have hlt : N < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlog : Real.log N < (k + 1) * Real.log 3 := by
    have : (N : ℝ) < (3 : ℝ) ^ (k + 1) := by exact_mod_cast hlt
    have := Real.log_lt_log hN0 this
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
  have hk2 : (k : ℝ) - 1 ≤ 2 * ((k / 2 : ℕ) : ℝ) := by
    have : k ≤ 2 * (k / 2) + 1 := by omega
    have : (k : ℝ) ≤ 2 * ((k / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  rw [Real.rpow_def_of_pos hN0, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have : Real.log N * (1 / Real.log 3) < k + 1 := by
    rw [← div_eq_mul_one_div, div_lt_iff₀ hl3]; linarith
  have hδ : Real.log N * -(c / (2 * Real.log 3)) = -(c / 2) * (Real.log N * (1 / Real.log 3)) := by
    field_simp
  rw [hδ]
  nlinarith

/-- **Cassels for the Cantor digits above position `p₀`** (proved).  If `2p₀ ≤ ⌊log₃N⌋/2`, the
pair sum of the digit products over positions `p₀ ≤ p < ⌊log₃N⌋/2` has a power saving, uniformly
in `p₀`. -/
theorem cassels_tail {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ p₀ : ℕ,
      2 * p₀ ≤ Nat.log 3 N / 2 →
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        tailProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) p₀ (Nat.log 3 N / 2) ≤ C * (N : ℝ) ^ 2 * W N := by
  set e := padicValNat 3 h.natAbs
  set t := CantorLiouvilleAll.tb b
  set c : ℝ := Real.log (3 / 2) / 2
  have hc : 0 < c := by unfold c; have := Real.log_pos (by norm_num : (1:ℝ) < 3 / 2); positivity
  set c' : ℝ := c / 2
  have hc' : 0 < c' := by positivity
  set δ : ℝ := c' / (2 * Real.log 3)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set K : ℝ := 3 * (3 ^ (e + t) + 2 * (3 / 2 : ℝ) ^ t)
  have hK : 0 ≤ K := by positivity
  refine ⟨K * Real.exp c' * Real.exp c' + 1,
    fun N => (N : ℝ) ^ (-(1 / 2 : ℝ)) + (N : ℝ) ^ (-δ),
    (summable_sched_rpow (by norm_num)).add (summable_sched_rpow (by positivity)),
    fun N hN p₀ hp => ?_⟩
  set M := Nat.log 3 N / 2
  set free : ℕ → Bool := fun p => decide (p₀ ≤ p)
  have hB := pairSum_Bf_le_explicit_b free hb h3 h hh N hN
  have hBf : ∀ ξ : ℝ, CantorLiouville.Bf free M ξ = tailProd ξ p₀ M := by
    intro ξ
    unfold CantorLiouville.Bf tailProd
    congr 1
    ext p; simp [free, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => hBf _] at hB
  have hF : (M : ℝ) - 1 ≤ 2 * (CantorLiouville.freeCount free M : ℝ) := by
    have : M - p₀ ≤ CantorLiouville.freeCount free M := by
      unfold CantorLiouville.freeCount
      rw [← Nat.card_Ico]
      refine Finset.card_le_card fun i hi => ?_
      simp only [Finset.mem_Ico] at hi
      simp only [Finset.mem_filter, Finset.mem_range, free]
      exact ⟨hi.2, by simpa using hi.1⟩
    have h2 : M ≤ 2 * CantorLiouville.freeCount free M + 1 := by omega
    have : (M : ℝ) ≤ 2 * (CantorLiouville.freeCount free M : ℝ) + 1 := by exact_mod_cast h2
    linarith
  have hexp : Real.exp (-c * CantorLiouville.freeCount free M) ≤
      Real.exp c' * (Real.exp c' * (N : ℝ) ^ (-δ)) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (exp_neg_log3_le hc'.le hN) (Real.exp_pos _).le)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    simp only [c']; nlinarith
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have hr : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hr2 : (0 : ℝ) ≤ (N : ℝ) ^ (-δ) := by positivity
  have hE2 : 0 ≤ Real.exp c' * Real.exp c' := by positivity
  calc _ ≤ _ := hB
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
          K * (N : ℝ) ^ 2 * (Real.exp c' * (Real.exp c' * (N : ℝ) ^ (-δ))) := by
        have := mul_le_mul_of_nonneg_left hexp (mul_nonneg hK hN2)
        simp only [K, c] at this ⊢
        linarith
    _ ≤ _ := by
        have h1 := mul_nonneg (mul_nonneg hK hE2) (mul_nonneg hN2 hr)
        nlinarith [mul_nonneg hN2 hr, mul_nonneg hN2 hr2, mul_nonneg (mul_nonneg hK hN2) hr]

/-- **The hybrid Cassels bound for few `resLaw` stages** (proved; special case of
`hybridCassels`).  If `20a ≤ ⌊log₃N⌋/2 ≤ 10S`, the hybrid law (`a` stages of `resLaw`, then
uniform digits) has the Cassels power saving, uniformly in `a` and `S`. -/
theorem hybridCassels_low {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ a S : ℕ,
      2 * (10 * a) ≤ Nat.log 3 N / 2 → Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        prefChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) a *
          rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) a S‖ ≤ C * (N : ℝ) ^ 2 * W N := by
  obtain ⟨C, W, hW, hC⟩ := cassels_tail hb h3 h hh
  refine ⟨C, W, hW, fun N hN a S ha hS => ?_⟩
  refine le_trans ?_ (hC N hN (10 * a) ha)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun m _ => ?_))
  set ξ : ℝ := h * ((b : ℝ) ^ n - (b : ℝ) ^ m)
  have haS : a ≤ S := by omega
  have hpc : ‖prefChar ξ a‖ ≤ 1 := by
    unfold prefChar
    refine (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun ω => ?_)).trans
      (by simp)
    rw [norm_ee]
  rw [norm_mul, norm_rhoProd _ haS]
  calc ‖prefChar ξ a‖ * tailProd ξ (10 * a) (10 * S) ≤ 1 * tailProd ξ (10 * a) (10 * S) :=
        mul_le_mul_of_nonneg_right hpc (tailProd_nonneg _ _ _)
    _ = tailProd ξ (10 * a) (Nat.log 3 N / 2) * tailProd ξ (Nat.log 3 N / 2) (10 * S) := by
        rw [one_mul, tailProd_mul ξ (by omega) hS]
    _ ≤ _ := mul_le_of_le_one_right (tailProd_nonneg _ _ _) (tailProd_le_one _ _ _)

/-- **The crux, middle stages only** (open; believed 55%).  The signed dead-character sum over the
stages `a₁ ≤ S' < a`, where `a₁ = min a (⌊log₃N⌋/2/20)` and `a = min S (N b + |h|)`, is
`O(N² W(N))`.  The low stages `S' < a₁` are free (`hybridCassels_low`) and the high ones are
local (`deadChar_tail_le`).  What remains is exactly the stages whose scale `3^{10S'}` lies
between `N^{1/40}` and the frequency scale `b^N`.  This is where the decorrelation of dead events
(rationals near `K`) from the lacunary sums is needed.

Off the headline path since lap 6 (the headline now goes through the local route,
`localDeadBias_resLaw`).  Reason: this is a Cassels *rate* for `resLaw`, and any stage-by-stage
bound of it multiplies each dead correction by `rhoProd ξ (S' + 1) S`, whose modulus lives on the
middle and leading ternary digits of `bⁿ`.  Granting the decorrelation, a rate still needs
quantitative equidistribution of `n log₃ b` (Baker-type input).  The local route needs only its
irrationality. -/
theorem midStages {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ,
      Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑ S' ∈ Finset.Ico (min (min S (N * b + h.natAbs)) (Nat.log 3 N / 2 / 20))
            (min S (N * b + h.natAbs)),
          deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
            rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S‖ ≤ C * (N : ℝ) ^ 2 * W N := by
  sorry

/-- **The hybrid-law Cassels bound.**  Proved from `hybridCassels_low` and `midStages` (open).  The pair sum of
the hybrid characters `T_a(ξ) Π_{a≤s<S} ρ_s(ξ)`, which is `E|S_N|²` under `resLaw` for `a`
stages followed by uniform Cantor digits, is `O(N² W(N))` for `a = min S (N b + |h|)`.  It
implies `deadCharSigned_core`, because the uniform part is
`cassels_Bf`. -/
theorem hybridCassels {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ, Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        prefChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (min S (N * b + h.natAbs)) *
          rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (min S (N * b + h.natAbs)) S‖ ≤
        C * (N : ℝ) ^ 2 * W N := by
  obtain ⟨C₁, W₁, hW₁, h₁⟩ := hybridCassels_low hb h3 h hh
  obtain ⟨C₂, W₂, hW₂, h₂⟩ := midStages hb h3 h hh
  refine ⟨|C₁| + |C₂|, fun N => |W₁ N| + |W₂ N|, hW₁.abs.add hW₂.abs, fun N hN S hS => ?_⟩
  set a := min S (N * b + h.natAbs)
  set a₁ := min a (Nat.log 3 N / 2 / 20)
  set ξ : ℕ → ℕ → ℝ := fun n m => h * ((b : ℝ) ^ n - (b : ℝ) ^ m)
  have haS : a ≤ S := min_le_left _ _
  have ha₁ : a₁ ≤ a := min_le_left _ _
  have hH : ∀ n m, prefChar (ξ n m) a * rhoProd (ξ n m) a S =
      prefChar (ξ n m) a₁ * rhoProd (ξ n m) a₁ S -
        ∑ S' ∈ Finset.Ico a₁ a, deadChar (ξ n m) S' * rhoProd (ξ n m) (S' + 1) S := by
    intro n m
    have e1 := stage_telescope (ξ n m) haS
    have e2 := stage_telescope (ξ n m) (ha₁.trans haS)
    rw [← Finset.sum_range_add_sum_Ico _ ha₁] at e1
    rw [e2] at e1
    linear_combination e1
  have hlow := h₁ N hN a₁ S (by omega) hS
  have hmid := h₂ N hN S hS
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have k : ∀ C W : ℝ, C * (N : ℝ) ^ 2 * W ≤ |C| * (N : ℝ) ^ 2 * |W| := fun C W =>
    (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_of_nonneg hN2])
  calc _ = ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, prefChar (ξ n m) a₁ * rhoProd (ξ n m) a₁ S -
        ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ∑ S' ∈ Finset.Ico a₁ a, deadChar (ξ n m) S' * rhoProd (ξ n m) (S' + 1) S‖ := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun m _ => hH n m
    _ ≤ _ := norm_sub_le _ _
    _ ≤ C₁ * (N : ℝ) ^ 2 * W₁ N + C₂ * (N : ℝ) ^ 2 * W₂ N := add_le_add hlow hmid
    _ ≤ _ := by
        have := k C₁ (W₁ N); have := k C₂ (W₂ N)
        have a1 := abs_nonneg C₁; have a2 := abs_nonneg C₂
        have b1 := abs_nonneg (W₁ N); have b2 := abs_nonneg (W₂ N)
        nlinarith [mul_nonneg (mul_nonneg a1 hN2) b2, mul_nonneg (mul_nonneg a2 hN2) b1]

/-- **The crux, localized to the first `S₀ = N b + |h|` stages.**  Proved from `hybridCassels`
(via `stage_telescope`) and `cassels_Bf`.  The analysis below is of the open input.

This is `deadCharSigned` with the stage sum cut at `S₀(N) = N b + |h|`.  The cut loses
nothing, since later stages contribute `≤ 1/N` per pair (`deadChar_tail_le`).  So only the
`O(N)` stages whose scale `3^{10S'}` is at most about `b^N` remain.

What a proof must supply.  The `S'`-term equals `E_{ν_{S'+1}}|S_N|² − E_{ν_{S'}}|S_N|²` for the
hybrid laws `ν_{S'}` (`resLaw` for `S'` stages, then Cantor coins).  Write
`S_N = A + B`, where `A` holds the terms with `bⁿ < 3^{10S'}` (frozen by the prefix) and `B` the
terms randomized by the Cantor tail.  Changing the stage-`S'` block moves only `O(1)` terms of
`A`, so that stage changes `|A|²` by `O(P(dead at S') · E[|A| | dead at S'])`.

Two routes are recorded as insufficient here.
(1) Cauchy–Schwarz bootstrap (`cs_bootstrap_floor`).  Bounding `E[1_dead |A|] ≤ √(η E|A|²)` gives
`f(N) ≤ f_K(N) + c√(η f(N))` for `f = E|S_N|²/N²`.  That recurrence has the constant solution
`f ≍ η`, so it gives only a floor, never decay.
(2) Large sieve over the obstacle centres `p/q`, `q² ≍ 3^{10S'}`.  This bounds the average of
`|A(p/q)|²` over all Farey fractions by `O(n₀)`.  The centres near `K` are a sparse subset, and
restricting to them loses the factor `(3/2)^{10S'}`.
What is needed is the decorrelation `E_ν[1_{dead at S'} |A|²] ≲ P(dead at S') · n₀^{2−δ}`: the
lacunary sums `Σ_{n<n₀} e(h bⁿ p/q)` are not inflated at the centres `p/q` near `K`.
Heuristically this follows from the equidistribution of rationals near `K` (Khalil–Lüthi;
Bénard–He–Zhang) together with Cassels decay of `μ̂_K` at the reduced frequencies
`h(bⁿ − bᵐ) mod q`.  Guards: it fails for `b = 3` and for dyadic centres
(`perStage_deadCount_not_enough`). -/
theorem deadCharSigned_core {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ, Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑ S' ∈ Finset.range (min S (N * b + h.natAbs)),
          deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
            rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S‖ ≤ C * (N : ℝ) ^ 2 * W N := by
  obtain ⟨C₁, W₁, hW₁, h₁⟩ := cassels_Bf hb h3 h hh
  obtain ⟨C₂, W₂, hW₂, h₂⟩ := hybridCassels hb h3 h hh
  refine ⟨|C₁| + |C₂|, fun N => |W₁ N| + |W₂ N|, hW₁.abs.add hW₂.abs, fun N hN S hS => ?_⟩
  set a := min S (N * b + h.natAbs)
  set ξ : ℕ → ℕ → ℝ := fun n m => h * ((b : ℝ) ^ n - (b : ℝ) ^ m)
  have hA : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖rhoProd (ξ n m) 0 S‖ ≤
      C₁ * (N : ℝ) ^ 2 * W₁ N := by
    refine le_trans (Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => ?_) (h₁ N hN)
    rw [norm_rhoProd _ (Nat.zero_le _), mul_zero, ← tailProd_zero_eq_Bf,
      ← tailProd_mul (ξ n m) (Nat.zero_le _) hS]
    exact mul_le_of_le_one_right (tailProd_nonneg _ _ _) (tailProd_le_one _ _ _)
  have hB := h₂ N hN S hS
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have k : ∀ C W : ℝ, C * (N : ℝ) ^ 2 * W ≤ |C| * (N : ℝ) ^ 2 * |W| := fun C W =>
    (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_of_nonneg hN2])
  calc _ = ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, rhoProd (ξ n m) 0 S -
        ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, prefChar (ξ n m) a * rhoProd (ξ n m) a S‖ := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun m _ => stage_telescope _ (min_le_left _ _)
    _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖rhoProd (ξ n m) 0 S‖ +
        ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, prefChar (ξ n m) a * rhoProd (ξ n m) a S‖ :=
        (norm_sub_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun n _ => norm_sum_le _ _)) le_rfl)
    _ ≤ C₁ * (N : ℝ) ^ 2 * W₁ N + C₂ * (N : ℝ) ^ 2 * W₂ N := add_le_add hA hB
    _ ≤ _ := by
        have := k C₁ (W₁ N); have := k C₂ (W₂ N)
        have a1 := abs_nonneg C₁; have a2 := abs_nonneg C₂
        have b1 := abs_nonneg (W₁ N); have b2 := abs_nonneg (W₂ N)
        nlinarith [mul_nonneg (mul_nonneg a1 hN2) b2, mul_nonneg (mul_nonneg a2 hN2) b1]

/-- **The crux (signed form): cancellation in the dead-children terms.**  Proved from the
localized crux `deadCharSigned_core` (stages `< N b + |h|`, open) and the tail bound
`deadChar_tail_le`.

Uniformly in the depth `S`, `‖Σ_{n,m<N} Σ_{S'<S} deadChar(ξ, S')·Π_{S'<s<S} ρ_s(ξ)‖ = O(N² W(N))`,
`ξ = h(bⁿ − bᵐ)`.  For each `S'` the inner pair sum is `∫ |S_N|² dτ_{S'}` for the signed measure
`τ_{S'}` = (`resLaw` to stage `S'`) ⊗ (dead child minus its share of a uniform child) ⊗ (Cantor
tail): the diagonal `n = m` cancels exactly (equal masses), terms with `bⁿ ≪ 3^{10S'}` change by
`O(1)` in total between the two parts, so heuristically each stage contributes
`O(P(dead at S')·N^{1/2}·N)` and the sum is `O(η N^{3/2})`.  This is weaker than
`DeadCharCancelAbs` (`deadCharSigned_of_abs`), whose triangle inequality over `(n, m)` forfeits
this cancellation and needs Fourier decay at the middle ternary digits of `bⁿ`.

Guards: `b = 3` is false (`cantor_not_normal_three_pow`), and the base-2 dyadic sibling
(`perStage_deadCount_not_enough`) must fail: its dead children sit at `p/2ᵏ`, where
`|S_N|²` is maximal, so `∫ |S_N|² dτ` has a sign and does not cancel. -/
theorem deadCharSigned {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ (C : ℝ) (W : ℕ → ℝ), Summable (fun j => W (sched j)) ∧ ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ, Nat.log 3 N / 2 ≤ 10 * S →
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑ S' ∈ Finset.range S, deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
          rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S‖ ≤ C * (N : ℝ) ^ 2 * W N := by
  obtain ⟨C, W, hW, hC⟩ := deadCharSigned_core hb h3 h hh
  refine ⟨|C| + 1, fun N => |W N| + (N : ℝ) ^ (-(1 / 2 : ℝ)),
    hW.abs.add (summable_sched_rpow (by norm_num)), fun N hN S hS => ?_⟩
  set S₀ := N * b + h.natAbs
  set F : ℕ → ℕ → ℕ → ℂ := fun n m S' => deadChar (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) S' *
    rhoProd (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) (S' + 1) S
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : ∀ n m, ∑ S' ∈ Finset.range S, F n m S' =
      ∑ S' ∈ Finset.range (min S S₀), F n m S' + ∑ S' ∈ Finset.Ico (min S S₀) S, F n m S' :=
    fun n m => (Finset.sum_range_add_sum_Ico _ (min_le_left _ _)).symm
  have htail : ∀ n ∈ Finset.range N, ∀ m ∈ Finset.range N,
      ‖∑ S' ∈ Finset.Ico (min S S₀) S, F n m S'‖ ≤ 1 / N := by
    intro n hn m hm
    rw [Finset.mem_range] at hn hm
    by_cases hS : S₀ ≤ S
    · rw [min_eq_right hS]; exact deadChar_tail_le hb h hN hn.le hm.le S
    · rw [min_eq_left (by omega), Finset.Ico_self, Finset.sum_empty, norm_zero]; positivity
  have hC' := hC N hN S hS
  have hT : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ‖∑ S' ∈ Finset.Ico (min S S₀) S, F n m S'‖ ≤ N := by
    calc _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (1 / N : ℝ) :=
          Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => htail n hn m hm
      _ = N := by simp; field_simp
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have hr : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hrN : (N : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = N * (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (N : ℝ) ^ 2 = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 : ℝ) by
        rw [← Real.rpow_add hNpos]; norm_num, mul_assoc, ← Real.rpow_add hNpos, Real.rpow_one]
      norm_num
    rw [this]
    exact le_mul_of_one_le_right hNpos.le (Real.one_le_rpow (by exact_mod_cast hN) (by norm_num))
  calc ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∑ S' ∈ Finset.range S, F n m S'‖
      ≤ ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∑ S' ∈ Finset.range (min S S₀), F n m S'‖ +
        ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ‖∑ S' ∈ Finset.Ico (min S S₀) S, F n m S'‖ := by
        simp_rw [hsplit, Finset.sum_add_distrib]
        exact (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun n _ => norm_sum_le _ _)))
    _ ≤ C * (N : ℝ) ^ 2 * W N + N := add_le_add hC' hT
    _ ≤ _ := by
        have k : C * (N : ℝ) ^ 2 * W N ≤ |C| * (N : ℝ) ^ 2 * |W N| :=
          (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_of_nonneg hN2])
        have a1 := abs_nonneg C; have b1 := abs_nonneg (W N)
        nlinarith [mul_nonneg (mul_nonneg a1 hN2) hr, mul_nonneg hN2 b1]

/-- **Cassels rate for the resampling law**, from the signed crux.  Proved modulo
`deadCharSigned`. -/
theorem casselsRate_resLaw {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) : CasselsRate resLaw b := by
  intro h hh
  obtain ⟨C₁, W₁, hW₁, h₁⟩ := cassels_Bf hb h3 h hh
  obtain ⟨C₂, W₂, hW₂, h₂⟩ := deadCharSigned hb h3 h hh
  refine ⟨|C₁| + |C₂| + 1, fun N => |W₁ N| + |W₂ N| + (N : ℝ) ^ (-(1 / 2 : ℝ)),
    (hW₁.abs.add hW₂.abs).add (summable_sched_rpow (by norm_num)), fun N hN => ?_⟩
  set ξ : ℕ → ℕ → ℝ := fun n m => h * ((b : ℝ) ^ n - (b : ℝ) ^ m) with hξ
  have h₂' : ∀ N : ℕ, 1 ≤ N → ∀ S : ℕ, Nat.log 3 N / 2 ≤ 10 * S → ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ∑ S' ∈ Finset.range S, deadChar (ξ n m) S' * rhoProd (ξ n m) (S' + 1) S‖ ≤
        C₂ * (N : ℝ) ^ 2 * W₂ N := h₂
  set K : ℝ := ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, 16 * |ξ n m|
  set S : ℕ := ⌈K⌉₊ + Nat.log 3 N
  have hK : K ≤ 3 ^ (10 * S) := by
    have h1 : K ≤ (S : ℝ) := (Nat.le_ceil K).trans (by exact_mod_cast Nat.le_add_right _ _)
    have h2 : S < 3 ^ (10 * S) := (Nat.lt_pow_self (by norm_num)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact h1.trans (by exact_mod_cast h2.le)
  have hM : Nat.log 3 N / 2 ≤ 10 * S := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have hr : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hrN : (1 : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = (N : ℝ) ^ (3 / 2 : ℝ) := by
      rw [show (N : ℝ) ^ 2 = (N : ℝ) ^ (2 : ℝ) by norm_cast, ← Real.rpow_add (by positivity)]
      norm_num
    rw [this]; exact Real.one_le_rpow hN1 (by norm_num)
  have h3S : (0 : ℝ) < 3 ^ (10 * S) := by positivity
  have hA : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖rhoProd (ξ n m) 0 S‖ ≤
      C₁ * (N : ℝ) ^ 2 * W₁ N := by
    refine le_trans (Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => ?_) (h₁ N hN)
    rw [norm_rhoProd _ (Nat.zero_le _), mul_zero, ← tailProd_zero_eq_Bf,
      ← tailProd_mul (ξ n m) (Nat.zero_le _) hM]
    exact mul_le_of_le_one_right (tailProd_nonneg _ _ _) (tailProd_le_one _ _ _)
  have hC : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, 16 * |ξ n m| / 3 ^ (10 * S) ≤
      (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simp only [← Finset.sum_div]
    rw [div_le_iff₀ h3S]
    nlinarith
  have k : ∀ C W : ℝ, C * (N : ℝ) ^ 2 * W ≤ |C| * (N : ℝ) ^ 2 * |W| := fun C W =>
    (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_of_nonneg hN2])
  -- ν̂ = (ν̂ − T_S) + Πρ − Σ deadChar·Πρ
  set ν : ℝ → ℂ := fun x => ∫ ω, ee (x * cpt (resLaw.φ ω)) ∂coinMeasure
  have hsplit : ∀ n m, ν (ξ n m) = (ν (ξ n m) - prefChar (ξ n m) S) + rhoProd (ξ n m) 0 S -
      ∑ S' ∈ Finset.range S, deadChar (ξ n m) S' * rhoProd (ξ n m) (S' + 1) S := by
    intro n m; rw [prefChar_eq]; ring
  have hsum : ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ν (ξ n m)‖ ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, 16 * |ξ n m| / 3 ^ (10 * S) +
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ‖rhoProd (ξ n m) 0 S‖ +
      ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∑ S' ∈ Finset.range S, deadChar (ξ n m) S' * rhoProd (ξ n m) (S' + 1) S‖ := by
    rw [Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => hsplit n m]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) le_rfl)
    · simp only [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun m _ => norm_fourier_sub_prefChar _ _))
    · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => norm_sum_le _ _)
  calc _ ≤ _ := secondMoment_le_norm_sum resLaw b h N
    _ ≤ _ := hsum
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) + C₁ * (N : ℝ) ^ 2 * W₁ N +
          C₂ * (N : ℝ) ^ 2 * W₂ N := add_le_add (add_le_add hC hA) (h₂' N hN S hM)
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) + |C₁| * (N : ℝ) ^ 2 * |W₁ N| +
          |C₂| * (N : ℝ) ^ 2 * |W₂ N| := by linarith [k C₁ (W₁ N), k C₂ (W₂ N)]
    _ ≤ _ := by
        have a1 := abs_nonneg C₁; have a2 := abs_nonneg C₂
        have b1 := abs_nonneg (W₁ N); have b2 := abs_nonneg (W₂ N)
        nlinarith [mul_nonneg (mul_nonneg a1 hN2) b2, mul_nonneg (mul_nonneg a2 hN2) b1,
          mul_nonneg (mul_nonneg a1 hN2) hr, mul_nonneg (mul_nonneg a2 hN2) hr,
          mul_nonneg hN2 b1, mul_nonneg hN2 b2]

end NormalNumbers.CantorBadNormal
