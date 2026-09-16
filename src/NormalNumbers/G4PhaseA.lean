/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SmallPrimeVector

/-!
# G4 §4C for the `a`-weighted small-prime vector

Campaign B's last axis.  Every weight the machine has handled so far kept the *retained*
small-prime vector equal to the **indicator** count `omegaOn sm m = #{p ∈ sm : p ∣ m}`, so §4C —
the near-field Fourier core — was never touched: the campaigns all lived in §4D.  A general
bounded multiplier `a : ℕ → ℕ` changes the retained vector itself, to

  `ω_{sm,a}(m) = ∑_{p ∈ sm, p ∣ m} a_p`     (`omegaOnA`).

This module proves that §4C survives that change, and that it survives it *cheaply*.  Two facts
carry everything:

* **`phaseA_eq_sum_local`** — `Φ_a(n) = ∑_i x_i ω_{sm,a}(n+ρ_i) = ∑_{p ∈ sm} localPhase p ρ (a_p·x) n`.
  The local phase at `p` is the **ordinary** local phase at the *scaled* coefficient vector
  `a_p · x`.  So the only question §4C has to answer is whether the good-prime gain survives a
  rescaling of the coefficients — and a priori it need not, since `dist(a·x, ℤ)` can vanish while
  `dist(x, ℤ) > 0`.

* **`sum_sq_distZ_coeffA_ge_gen`** — it does survive, with the frequency-separation seed
  `freqSeed bb K = bb^{−4}(2/bb²)^K` **unchanged**.  The reason is structural rather than
  numerical: `coeffAL` is *linear in the frequency* (`coeffAL_const_mul`, from
  `vecMul_const_mul`), so scaling the coefficients by `a_p` is the same as scaling `q` by `a_p`;
  and `sum_sq_distZ_freqDepthB_ge` carries **no hypothesis on the Fourier box** — it holds for an
  arbitrary nonzero integer frequency.  The box `D` enters the separation argument only through
  `freqDepthB_le`, the *admissibility* statement that the selected depth `j_α` fits inside the
  layer budget `N`.  Hence the entire cost of a general bounded `a` is the single enlargement

      `N ≥ 1 + ⌈log_bb(2^K·D)⌉`   ⟶   `N ≥ 1 + ⌈log_bb(2^K·Ca·D)⌉`,

  an *additive* `⌈log_bb Ca⌉` on a budget already of size `Θ(K)`.

The four §4C error terms do not move at all: the roots of `LocalPhase.ofShifts` are
`image (root p ρ)` and depend only on the shifts (`shiftPhaseA_roots`), so
`norm_sampleAvg_ee_phaseA_le` has literally the error budget of `norm_sampleAvg_ee_phase_le`.
And no new probabilistic layer is needed, because `norm_sampleAvg_prod_ee_le` already accepts a
*per-prime* `LocalPhase` family together with a *per-prime* seed — here
`if GoodPrime ρ p ∧ 1 ≤ a p then θ₀ else 0`, whose active set is exactly `S = {p : 1 ≤ a_p}`.

`omegaOnA_one` and `omegaOnA_indicator` record that this generalises both earlier retained
vectors: `a = 1` is `omegaOn sm`, and `a = 1_S` is `omegaOn (sm.filter S)` — i.e. the prime-subset
campaign *is* this one at `a = 1_S`.
-/

open Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### The `a`-weighted phase decomposition -/

section PhaseA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `a`-weighted small-prime count `ω_{s,a}(m) = ∑_{p ∈ s, p ∣ m} a_p`. -/
def omegaOnA (a : ℕ → ℕ) (s : Finset ℕ) (m : ℕ) : ℕ := ∑ p ∈ s.filter (fun p => p ∣ m), a p

/-- `a = 1` recovers the indicator count of `G4PhaseDecomp`. -/
@[simp] lemma omegaOnA_one (s : Finset ℕ) (m : ℕ) : omegaOnA (fun _ => 1) s m = omegaOn s m := by
  unfold omegaOnA omegaOn
  rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- `a = 1_S` recovers the *subset* count: the prime-subset campaign is this one at `a = 1_S`. -/
lemma omegaOnA_indicator (S : ℕ → Prop) [DecidablePred S] (s : Finset ℕ) (m : ℕ) :
    omegaOnA (fun p => if S p then 1 else 0) s m = omegaOn (s.filter S) m := by
  classical
  unfold omegaOnA omegaOn
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one,
    mul_zero, add_zero, Finset.filter_filter, Finset.filter_filter]
  congr 1
  exact Finset.filter_congr fun p _ => by tauto

/-- The `a`-weighted total phase `Φ_a(n) = ∑_i x_i ω_{s,a}(n + ρ_i)`. -/
noncomputable def totalPhaseA (a : ℕ → ℕ) (s : Finset ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i, x i * omegaOnA a s (n + ρ i)

omit [DecidableEq ι] in
@[simp] lemma totalPhaseA_one (s : Finset ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (n : ℕ) :
    totalPhaseA (fun _ => 1) s ρ x n = totalPhase s ρ x n := by
  unfold totalPhaseA totalPhase; simp

omit [DecidableEq ι] in
/-- `localPhase` is linear in the coefficient vector. -/
lemma localPhase_const_mul (p : ℕ) (ρ : ι → ℕ) (k : ℝ) (x : ι → ℝ) (n : ℕ) :
    localPhase p ρ (fun i => k * x i) n = k * localPhase p ρ x n := by
  unfold localPhase
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq ι] in
/-- **The `a`-side phase decomposition.**  `Φ_a(n) = ∑_{p ∈ s} localPhase p ρ (a_p · x) n`: the
local phase at `p` is the ordinary local phase at the *scaled* coefficients `a_p · x`. -/
lemma phaseA_eq_sum_local (a : ℕ → ℕ) (s : Finset ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (n : ℕ) :
    totalPhaseA a s ρ x n = ∑ p ∈ s, localPhase p ρ (fun i => (a p : ℝ) * x i) n := by
  unfold totalPhaseA omegaOnA
  simp only [localPhase]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by split_ifs <;> ring

omit [DecidableEq ι] in
lemma ee_phaseA_eq_prod (a : ℕ → ℕ) (s : Finset ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (n : ℕ) :
    ee (totalPhaseA a s ρ x n) = ∏ p ∈ s, ee (localPhase p ρ (fun i => (a p : ℝ) * x i) n) := by
  rw [phaseA_eq_sum_local, ee_sum]

/-- The per-prime local data of the `a`-weighted phase: the ordinary data at `a_p · x`. -/
noncomputable def shiftPhaseA (a : ℕ → ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (p : ℕ) : LocalPhase p :=
  shiftPhase ρ (fun i => (a p : ℝ) * x i) p

omit [DecidableEq ι] in
/-- **The error budget does not move.**  The roots depend only on the shifts, so every §4C error
term for the `a`-weighted phase is the one for the unweighted phase. -/
lemma shiftPhaseA_roots (a : ℕ → ℕ) (ρ : ι → ℕ) (x : ι → ℝ) (p : ℕ) :
    (shiftPhaseA a ρ x p).roots = (shiftPhase ρ x p).roots := by
  unfold shiftPhaseA shiftPhase
  split_ifs with h
  · rfl
  · rfl

open Classical in
/-- **§4C for the `a`-weighted phase sum.**  The contraction runs over the good primes of `s`
that are *active* for `a` (`1 ≤ a_p`); every prime of `s` enters the four error terms, which are
identical to the unweighted ones. -/
theorem norm_sampleAvg_ee_phaseA_le (X P₀ aa : ℕ) (hP₀ : 0 < P₀)
    (ha : aa < P₀) (hne : (apSample X P₀ aa).Nonempty)
    (a : ℕ → ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hsP : ∀ p ∈ s, p.Coprime P₀)
    {R : ℕ} (hR1 : 1 ≤ R) (hR : ∀ p ∈ s, p ≤ R)
    (ρ : ι → ℕ) (x : ι → ℝ) (hk : ∀ p ∈ s, 2 * Fintype.card ι ≤ p)
    {θ₀ : ℝ} (hθ0 : 0 ≤ θ₀)
    (hθ : ∀ p ∈ s, 1 ≤ a p → θ₀ ≤ ∑ i, distZ ((a p : ℝ) * x i) ^ 2)
    {M : ℕ} (hM : 1 ≤ M) {lam' lam : ℝ} (hlam' : 1 ≤ lam') (hlam : 0 < lam) :
    ‖sampleAvg (apSample X P₀ aa) id (fun n => ee (totalPhaseA a s ρ x n))‖
      ≤ Real.exp (-∑ p ∈ s, 4 * (if GoodPrime ρ p ∧ 1 ≤ a p then θ₀ else 0) / p)
        + ((s.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ M)).card
            * (2 ^ M * (2 * (R : ℝ) ^ M / (apSample X P₀ aa).card))
          + (∏ p ∈ s, (1 + lam' * (2 * (shiftPhase ρ x p).roots.card / p))) / lam' ^ M
          + 2 * (2 * Real.exp 1 / lam) ^ M
              * ∏ p ∈ s, (1 + Real.exp lam * ((shiftPhase ρ x p).roots.card / p))
          + 2 * (2 * Real.exp 1 / M) ^ M * (s.card : ℝ) ^ M
              * (2 * (R : ℝ) ^ M / (apSample X P₀ aa).card)) := by
  have hpos : ∀ p ∈ s, 0 < p := fun p hp => (hs p hp).pos
  have hfun : (fun n => ee (totalPhaseA a s ρ x n))
      = fun n => ∏ p ∈ s, ee ((shiftPhaseA a ρ x p).θ n) := by
    funext n
    rw [ee_phaseA_eq_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [shiftPhaseA, shiftPhase_eq (hpos p hp) (hk p hp), theta_ofShifts]
  rw [hfun]
  have hroots : ∀ p, ((shiftPhaseA a ρ x p).roots.card : ℝ) = (shiftPhase ρ x p).roots.card := by
    intro p; rw [shiftPhaseA_roots]
  simp only [← hroots]
  refine norm_sampleAvg_prod_ee_le X P₀ aa hP₀ ha hne s hs hsP hR1 hR (shiftPhaseA a ρ x)
    (fun p => if GoodPrime ρ p ∧ 1 ≤ a p then θ₀ else 0) (fun p _ => by split_ifs <;> simp [hθ0])
    (fun p hp => ?_) hM hlam' hlam
  split_ifs with h
  · rw [shiftPhaseA, shiftPhase_eq (hpos p hp) (hk p hp),
      sum_sq_ofShifts_eq ρ _ (hpos p hp) (hk p hp) h.1]
    exact hθ p hp h.2
  · exact Finset.sum_nonneg fun b _ => sq_nonneg _

end PhaseA

/-! ### Frequency separation at the scaled frequency `a_p · q` -/

section FreqA

variable {K s : ℕ}

/-- `vecMul` is linear in the frequency. -/
lemma vecMul_const_mul (k : ℤ) (q : (Fin K → Fin s) → ℤ) (c : Fin K → Fin (s + 1)) :
    (kronPow K (diffZ s)).vecMul (fun a => k * q a) c
      = k * (kronPow K (diffZ s)).vecMul q c := by
  simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- Hence `coeffAL` is linear in the frequency: scaling the phase coefficients by an integer is
the same as scaling the frequency. -/
lemma coeffAL_const_mul (bb : ℕ) {N : ℕ} (k : ℤ) (q : (Fin K → Fin s) → ℤ)
    (i : AtomLayer K s N) :
    coeffAL bb (fun a => k * q a) i = (k : ℝ) * coeffAL bb q i := by
  unfold coeffAL
  rw [vecMul_const_mul]
  push_cast
  ring

/-- **The `a`-side frequency separation.**  Scaling the phase coefficients by a positive integer
`ap ≤ Ca` leaves the frequency-separation seed `freqSeed bb K` *unchanged*; the only cost is the
enlargement of the layer budget from the Fourier box `D` to `Ca·D`.

This is the decisive step of the `a`-side: a priori the rescaling could destroy the good-prime
gain entirely, since `dist(k·x, ℤ)` can vanish while `dist(x, ℤ) > 0`.  It does not, because
`sum_sq_distZ_freqDepthB_ge` has no hypothesis on the Fourier box at all — the box enters only
through the admissibility of the selected depth. -/
theorem sum_sq_distZ_coeffA_ge_gen {bb : ℕ} (hbb : 2 ≤ bb) {N D Ca : ℕ}
    (hN : 1 + Nat.clog bb (2 ^ K * (Ca * D)) ≤ N)
    {ap : ℕ} (hap : 1 ≤ ap) (hapC : ap ≤ Ca)
    {q : (Fin K → Fin s) → ℤ} (hq : q ≠ 0) (hqD : ∀ a, |q a| ≤ (D : ℤ)) :
    freqSeed bb K ≤ ∑ i : AtomLayer K s N, distZ ((ap : ℝ) * coeffAL bb q i) ^ 2 := by
  classical
  set q' : (Fin K → Fin s) → ℤ := fun a => (ap : ℤ) * q a with hq'def
  have hap0 : (0 : ℤ) < ap := by exact_mod_cast hap
  have hq' : q' ≠ 0 := by
    intro h
    refine hq (funext fun a => ?_)
    have hz : (ap : ℤ) * q a = 0 := congrFun h a
    rcases mul_eq_zero.1 hz with h1 | h1
    · exact absurd h1 hap0.ne'
    · simpa using h1
  have hq'D : ∀ a, |q' a| ≤ ((Ca * D : ℕ) : ℤ) := by
    intro a
    have h1 : |q' a| = (ap : ℤ) * |q a| := by
      rw [hq'def]; simp [abs_mul, abs_of_pos hap0]
    have h2 : (ap : ℤ) ≤ (Ca : ℤ) := by exact_mod_cast hapC
    have h3 : |q a| ≤ (D : ℤ) := hqD a
    have h4 : (0 : ℤ) ≤ |q a| := abs_nonneg _
    rw [h1]
    push_cast
    nlinarith
  have h := sum_sq_distZ_coeff_ge_gen (K := K) (s := s) hbb (N := N) (D := Ca * D) hN hq' hq'D
  refine h.trans_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [coeffAL_const_mul]
  push_cast
  ring_nf

end FreqA


/-! ### §4C for the concrete `a`-weighted grid vector -/

section SvalA

variable {K s : ℕ}

/-- The **`a`-weighted** real small-prime vector in base `bb`:
`S^a_u(n) = ∑_α A_{uα} ∑_{jj} ω_{sm,a}(n + ρ(α,jj)) / bb^{layer jj}`.  `a = 1` is `Sval`. -/
noncomputable def SvalA (bb : ℕ) (a : ℕ → ℕ) (sm : Finset ℕ) {N : ℕ}
    (ρ : AtomLayer K s N → ℕ) (n : ℕ) (u : Fin K → Fin s) : ℝ :=
  ∑ α, ((kronPow K (diffZ s) u α : ℤ) : ℝ) *
    ∑ jj : Fin N, (omegaOnA a sm (n + ρ (α, jj)) : ℝ) / (bb : ℝ) ^ layer K jj

@[simp] lemma SvalA_one (bb : ℕ) (sm : Finset ℕ) {N : ℕ} (ρ : AtomLayer K s N → ℕ) (n : ℕ)
    (u : Fin K → Fin s) : SvalA bb (fun _ => 1) sm ρ n u = Sval bb sm ρ n u := by
  unfold SvalA Sval; simp

/-- `q · S^a(n) = Φ_a(n)`: the frequency pairing of the `a`-weighted small-prime vector is the
`a`-weighted total phase of the coefficients `coeffAL bb q`.  Base-free algebra. -/
lemma sum_mul_SvalA (bb : ℕ) (a : ℕ → ℕ) (sm : Finset ℕ) {N : ℕ} (ρ : AtomLayer K s N → ℕ)
    (q : (Fin K → Fin s) → ℤ) (n : ℕ) :
    ∑ u, (q u : ℝ) * SvalA bb a sm ρ n u = totalPhaseA a sm ρ (coeffAL bb q) n := by
  unfold SvalA totalPhaseA coeffAL
  simp only [Finset.mul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun jj _ => ?_
  simp only [Matrix.vecMul, dotProduct]
  push_cast
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

/-- **The character identity** for the `a`-weighted vector: `∏_u e(q_u S^a_u(n)) = e(Φ_a(n))`. -/
theorem torusChar_SvalA (bb : ℕ) (a : ℕ → ℕ) (sm : Finset ℕ) {N : ℕ}
    (ρ : AtomLayer K s N → ℕ) (q : (Fin K → Fin s) → ℤ) (n : ℕ) :
    ∏ u, fourier (q u) ((SvalA bb a sm ρ n u : ℝ) : UnitAddCircle)
      = ee (totalPhaseA a sm ρ (coeffAL bb q) n) := by
  rw [← sum_mul_SvalA, ee_sum]
  exact Finset.prod_congr rfl fun u _ => fourier_unitAddCircle _ _

/-- **The `a`-side seed on the atom/layer index set.**  With the layer budget enlarged from the
box `D` to `Ca·D`, every *active* prime (`1 ≤ a_p`) gets the full seed `freqSeed bb K`. -/
theorem sum_sq_distZ_coeffA_ge_of_bound {bb : ℕ} (hbb : 2 ≤ bb) {N D Ca : ℕ}
    (hN : 1 + Nat.clog bb (2 ^ K * (Ca * D)) ≤ N) {a : ℕ → ℕ} (hCa : ∀ p, a p ≤ Ca)
    {q : (Fin K → Fin s) → ℤ} (hq : q ≠ 0) (hqD : ∀ u, |q u| ≤ (D : ℤ)) (p : ℕ) (hp : 1 ≤ a p) :
    freqSeed bb K ≤ ∑ i : AtomLayer K s N, distZ ((a p : ℝ) * coeffAL bb q i) ^ 2 :=
  sum_sq_distZ_coeffA_ge_gen hbb hN hp (hCa p) hq hqD

open Classical in
/-- **§4C for the grid's `a`-weighted small-prime vector, base `bb`.**  Identical in shape to
`norm_sampleAvg_torusChar_Sval_le` — same four error terms, same roots — with the contraction
restricted to the good primes that are *active* for `a`. -/
theorem norm_sampleAvg_torusChar_SvalA_le (bb : ℕ) (X P₀ aa : ℕ) (hP₀ : 0 < P₀)
    (ha : aa < P₀) (hne : (apSample X P₀ aa).Nonempty)
    (a : ℕ → ℕ) (sm : Finset ℕ) (hs : ∀ p ∈ sm, p.Prime) (hsP : ∀ p ∈ sm, p.Coprime P₀)
    {R : ℕ} (hR1 : 1 ≤ R) (hR : ∀ p ∈ sm, p ≤ R)
    {N : ℕ} (ρ : AtomLayer K s N → ℕ) (hk : ∀ p ∈ sm, 2 * Fintype.card (AtomLayer K s N) ≤ p)
    {q : (Fin K → Fin s) → ℤ} {θ₀ : ℝ} (hθ0 : 0 ≤ θ₀)
    (hsep : ∀ p ∈ sm, 1 ≤ a p → θ₀ ≤ ∑ i : AtomLayer K s N, distZ ((a p : ℝ) * coeffAL bb q i) ^ 2)
    {M : ℕ} (hM : 1 ≤ M) {lam' lam : ℝ} (hlam' : 1 ≤ lam') (hlam : 0 < lam) :
    ‖sampleAvg (apSample X P₀ aa) (fun n u => ((SvalA bb a sm ρ n u : ℝ) : UnitAddCircle))
        (fun y => ∏ u, fourier (q u) (y u))‖
      ≤ Real.exp (-∑ p ∈ sm, 4 * (if GoodPrime ρ p ∧ 1 ≤ a p then θ₀ else 0) / p)
        + ((sm.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ M)).card
            * (2 ^ M * (2 * (R : ℝ) ^ M / (apSample X P₀ aa).card))
          + (∏ p ∈ sm, (1 + lam' * (2 * (shiftPhase ρ (coeffAL bb q) p).roots.card / p)))
              / lam' ^ M
          + 2 * (2 * Real.exp 1 / lam) ^ M
              * ∏ p ∈ sm, (1 + Real.exp lam * ((shiftPhase ρ (coeffAL bb q) p).roots.card / p))
          + 2 * (2 * Real.exp 1 / M) ^ M * (sm.card : ℝ) ^ M
              * (2 * (R : ℝ) ^ M / (apSample X P₀ aa).card)) := by
  have h := norm_sampleAvg_ee_phaseA_le X P₀ aa hP₀ ha hne a sm hs hsP hR1 hR ρ (coeffAL bb q)
    hk hθ0 hsep hM hlam' hlam
  unfold sampleAvg at h ⊢
  simp only [id] at h
  rw [show (∑ n ∈ apSample X P₀ aa, ∏ u, fourier (q u)
      ((fun n u => ((SvalA bb a sm ρ n u : ℝ) : UnitAddCircle)) n u))
      = ∑ n ∈ apSample X P₀ aa, ee (totalPhaseA a sm ρ (coeffAL bb q) n) from
    Finset.sum_congr rfl fun n _ => torusChar_SvalA bb a sm ρ q n]
  exact h

end SvalA

end NormalNumbers.G4
