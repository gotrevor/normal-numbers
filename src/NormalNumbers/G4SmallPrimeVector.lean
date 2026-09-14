/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Grid
import NormalNumbers.G4PhaseDecomp
import NormalNumbers.G4Wiring

/-!
# G4 disjunctivity, §4C instantiated: the concrete small-prime vector and its characters

Draft §7–§8.  The small-prime vector of the grid frame is

  `Sval bb sm ρ n a = ∑_α A_{aα} ∑_{K<j≤J} bb^{−j} ω_{sm}(n + ρ_{α,j})`,     `A = D_s^{⊗K}`,

read modulo one.  For a frequency `q`, the character `∏_a e(q_a · S_a(n))` is `e(Φ(n))` with
`Φ = totalPhase sm ρ x`, `x_{α,j} = w_α 4^{−j}`, `w = q ᵥ* A` (`torusChar_Sval`).  So
`G4PhaseDecomp.norm_sampleAvg_ee_phase_le` applies verbatim, with

* `θ₀ = 4^{−4} 8^{−K}` from `G4FreqSep.sum_sq_distZ_freqDepth_ge` — the frequency-depth layer
  `j_α = freqDepth K w_α` lies in `(K, J]` when `J ≥ K + 1 + ⌈log₄(2^K D)⌉`
  (`sum_sq_distZ_coeff_ge`), and
* every prime of `sm` good (`goodPrime_of_not_dvd`): the shifts are injective and no prime of
  `sm` divides a nonzero shift difference.

**`norm_sampleAvg_torusChar_Sval_le`** is §4C for the concrete vector: uniformly over
`0 ≠ q`, `‖q‖∞ ≤ D`,

  `‖avg_{n<X, n≡a(P₀)} ∏_a e(q_a S_a(n))‖ ≤ exp(−4·4^{−4}8^{−K} ∑_{p∈sm} 1/p) + (four errors)`.

What separates this from `Frame.PropC` is only the reindexing `Fin K → Fin s ≃ Fin r` of the
wiring's `Torus r`, and the numerical choice of `M, λ, λ'` against `Λ = (2D+1)^r` (C4,
`G4Schedule.schedule_budget`).
-/

open Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

variable {K s : ℕ}

/-! ### Layers and the index set -/

/-- The retained layer `j = K + 1 + jj`, `jj < J − K`. -/
def layer (K : ℕ) {N : ℕ} (jj : Fin N) : ℕ := K + 1 + jj

lemma lt_layer (K : ℕ) {N : ℕ} (jj : Fin N) : K < layer K jj := by unfold layer; omega

lemma layer_le (K : ℕ) {N : ℕ} (jj : Fin N) : layer K jj ≤ K + N := by
  unfold layer; have := jj.isLt; omega

/-- The atom/layer index set `ι = atoms × (K, K+N]`. -/
abbrev AtomLayer (K s N : ℕ) := (Fin K → Fin (s + 1)) × Fin N

/-- The shift of the pair `(α, jj)`: `ρ_{α, K+1+jj}`. -/
def shiftAL (B Q D₀ : ℕ) {N : ℕ} (i : AtomLayer K s N) : ℕ := shiftG B Q D₀ i.1 (layer K i.2)

/-- The phase coefficients of the frequency `q` in base `bb`: `x_{α,j} = w_α / bb^j`,
`w = q ᵥ* D_s^{⊗K}`. -/
noncomputable def coeffAL (bb : ℕ) {N : ℕ} (q : (Fin K → Fin s) → ℤ) (i : AtomLayer K s N) : ℝ :=
  ((kronPow K (diffZ s)).vecMul q i.1 : ℤ) / (bb : ℝ) ^ layer K i.2

/-- The real small-prime vector in base `bb`:
`S_a(n) = ∑_α A_{aα} ∑_{jj} ω_{sm}(n + ρ(α,jj)) / bb^{layer jj}`. -/
noncomputable def Sval (bb : ℕ) (sm : Finset ℕ) {N : ℕ} (ρ : AtomLayer K s N → ℕ) (n : ℕ)
    (a : Fin K → Fin s) : ℝ :=
  ∑ α, ((kronPow K (diffZ s) a α : ℤ) : ℝ) *
    ∑ jj : Fin N, (omegaOn sm (n + ρ (α, jj)) : ℝ) / (bb : ℝ) ^ layer K jj

/-- `q · S(n) = Φ(n)`: the frequency pairing of the small-prime vector is the total phase of
the coefficients `coeffAL bb q`.  Base-free algebra. -/
lemma sum_mul_Sval (bb : ℕ) (sm : Finset ℕ) {N : ℕ} (ρ : AtomLayer K s N → ℕ)
    (q : (Fin K → Fin s) → ℤ) (n : ℕ) :
    ∑ a, (q a : ℝ) * Sval bb sm ρ n a = totalPhase sm ρ (coeffAL bb q) n := by
  unfold Sval totalPhase coeffAL
  simp only [Finset.mul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun jj _ => ?_
  simp only [Matrix.vecMul, dotProduct]
  push_cast
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- A one-dimensional character on the unit circle in terms of `ee`. -/
lemma fourier_unitAddCircle (m : ℤ) (x : ℝ) :
    fourier m (x : UnitAddCircle) = ee (m * x) := by
  rw [fourier_coe_apply, ee]
  congr 1
  push_cast
  ring

/-- **The character identity**: `∏_a e(q_a S_a(n)) = e(Φ(n))`. -/
theorem torusChar_Sval (bb : ℕ) (sm : Finset ℕ) {N : ℕ} (ρ : AtomLayer K s N → ℕ)
    (q : (Fin K → Fin s) → ℤ) (n : ℕ) :
    ∏ a, fourier (q a) ((Sval bb sm ρ n a : ℝ) : UnitAddCircle)
      = ee (totalPhase sm ρ (coeffAL bb q) n) := by
  rw [← sum_mul_Sval, ee_sum]
  exact Finset.prod_congr rfl fun a _ => fourier_unitAddCircle _ _

/-! ### The uniform lower bound on the phase energy -/

/-- **Frequency separation on the atom/layer index set, base four**: if
`J − K = N ≥ 1 + ⌈log₄(2^K D)⌉` (so every frequency-depth layer is retained) then for `0 ≠ q`,
`‖q‖∞ ≤ D`, `∑_i dist(x_i, ℤ)² ≥ 4^{−4} 8^{−K}`.  The base-`b` seed `θ₀(b) = b^{−4}(2/b²)^K`
is the `G4FreqSep` port (campaign G4B step 5); everything downstream takes the seed as a
hypothesis `hsep`, so only this lemma is pinned. -/
theorem sum_sq_distZ_coeff_ge {N D : ℕ} (hN : 1 + Nat.clog 4 (2 ^ K * D) ≤ N)
    {q : (Fin K → Fin s) → ℤ} (hq : q ≠ 0) (hqD : ∀ a, |q a| ≤ (D : ℤ)) :
    1 / (4 : ℝ) ^ 4 * (1 / 8 : ℝ) ^ K ≤ ∑ i : AtomLayer K s N, distZ (coeffAL 4 q i) ^ 2 := by
  classical
  refine (sum_sq_distZ_freqDepth_ge K s hq).trans ?_
  -- the depth of atom `α` as a layer index
  have hdepth : ∀ α : Fin K → Fin (s + 1),
      freqDepth K ((kronPow K (diffZ s)).vecMul q α) - (K + 1) < N := by
    intro α
    have := freqDepth_le K s D hqD α
    omega
  let φ : (Fin K → Fin (s + 1)) → AtomLayer K s N :=
    fun α => (α, ⟨freqDepth K ((kronPow K (diffZ s)).vecMul q α) - (K + 1), hdepth α⟩)
  have hφ : Function.Injective φ := fun α β h => congrArg Prod.fst h
  have hlayer : ∀ α, layer K (φ α).2 = freqDepth K ((kronPow K (diffZ s)).vecMul q α) := by
    intro α
    simp only [φ, layer]
    have := lt_freqDepth K ((kronPow K (diffZ s)).vecMul q α)
    omega
  calc ∑ α, distZ (((kronPow K (diffZ s)).vecMul q α : ℤ) /
          (4 : ℝ) ^ freqDepth K ((kronPow K (diffZ s)).vecMul q α)) ^ 2
      = ∑ α, distZ (coeffAL 4 q (φ α)) ^ 2 := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [coeffAL, hlayer]
        push_cast
        rfl
    _ = ∑ i ∈ Finset.univ.image φ, distZ (coeffAL 4 q i) ^ 2 := by
        rw [Finset.sum_image (fun α _ β _ h => hφ h)]
    _ ≤ ∑ i, distZ (coeffAL 4 q i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => by positivity)

/-! ### Good primes from global distinctness -/

/-- A prime not dividing any nonzero shift difference, with injective shifts, is good. -/
theorem goodPrime_of_not_dvd {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ι → ℕ)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : 0 < p)
    (hdiff : ∀ i i', i ≠ i' → ¬ (p : ℤ) ∣ (ρ i : ℤ) - ρ i') : GoodPrime ρ p := by
  intro i i' h
  by_contra hne
  refine hdiff i i' hne ?_
  unfold root at h
  have hi : ρ i % p < p := Nat.mod_lt _ hp
  have hi' : ρ i' % p < p := Nat.mod_lt _ hp
  have key : ∀ b, b < p → (p - b) % p = if b = 0 then 0 else p - b := by
    intro b hb
    split_ifs with h0
    · subst h0; simp
    · exact Nat.mod_eq_of_lt (by omega)
  rw [key _ hi, key _ hi'] at h
  have hmodeq : ρ i ≡ ρ i' [MOD p] := by
    unfold Nat.ModEq
    split_ifs at h <;> omega
  have := (Nat.modEq_iff_dvd).1 hmodeq
  rw [← neg_sub, dvd_neg] at this
  exact this

/-- The shifts of the grid are injective on the atom/layer set. -/
theorem shiftAL_injective (B Q D₀ J : ℕ) (hB : s * J < B) (hJQ : J < Q)
    (hD : ∀ α : Fin K → Fin (s + 1), gridV B α ≤ D₀) {N : ℕ} (hN : K + N ≤ J) :
    Function.Injective (shiftAL B Q D₀ (K := K) (s := s) (N := N)) := by
  rintro ⟨α, jj⟩ ⟨β, jj'⟩ h
  have := shiftG_injective B Q D₀ J hB hJQ hD (lt_layer K jj) ((layer_le K jj).trans hN)
    (lt_layer K jj') ((layer_le K jj').trans hN) h
  obtain ⟨h1, h2⟩ := this
  have h1' : K + 1 + (jj : ℕ) = K + 1 + (jj' : ℕ) := h1
  exact Prod.ext h2 (Fin.ext (show (jj : ℕ) = jj' by omega))

/-! ### §4C for the concrete small-prime vector -/

open Classical in
/-- **Uniform joint small-prime Fourier control for the grid's small-prime vector, in base
`bb`.**  With `ρ = shiftAL`, a frequency-separation seed `θ₀ ≤ ∑_i dist(x_i, ℤ)²` for the
coefficients `coeffAL bb q` (`hsep`), and every prime of `sm` good, the sample average of the
character `q` of `S` is at most `exp(−4θ₀ ∑_{p∈sm} 1/p)` plus the four §4C errors, uniformly
for `0 ≠ q` in the box `‖q‖∞ ≤ D`.  Base four: `θ₀ = 4^{−4}8^{−K}` by
`sum_sq_distZ_coeff_ge`. -/
theorem norm_sampleAvg_torusChar_Sval_le (bb : ℕ) (X P₀ a : ℕ) (hP₀ : 0 < P₀)
    (ha : a < P₀) (hne : (apSample X P₀ a).Nonempty)
    (sm : Finset ℕ) (hs : ∀ p ∈ sm, p.Prime) (hsP : ∀ p ∈ sm, p.Coprime P₀)
    {R : ℕ} (hR1 : 1 ≤ R) (hR : ∀ p ∈ sm, p ≤ R)
    {N : ℕ} (ρ : AtomLayer K s N → ℕ) (hk : ∀ p ∈ sm, 2 * Fintype.card (AtomLayer K s N) ≤ p)
    (hgood : ∀ p ∈ sm, GoodPrime ρ p)
    {q : (Fin K → Fin s) → ℤ} {θ₀ : ℝ} (hθ0 : 0 ≤ θ₀)
    (hsep : θ₀ ≤ ∑ i : AtomLayer K s N, distZ (coeffAL bb q i) ^ 2)
    {M : ℕ} (hM : 1 ≤ M) {lam' lam : ℝ} (hlam' : 1 ≤ lam') (hlam : 0 < lam) :
    ‖sampleAvg (apSample X P₀ a) (fun n a => ((Sval bb sm ρ n a : ℝ) : UnitAddCircle))
        (fun y => ∏ a, fourier (q a) (y a))‖
      ≤ Real.exp (-∑ p ∈ sm, 4 * θ₀ / p)
        + ((sm.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ M)).card
            * (2 ^ M * (2 * (R : ℝ) ^ M / (apSample X P₀ a).card))
          + (∏ p ∈ sm, (1 + lam' * (2 * (shiftPhase ρ (coeffAL bb q) p).roots.card / p)))
              / lam' ^ M
          + 2 * (2 * Real.exp 1 / lam) ^ M
              * ∏ p ∈ sm, (1 + Real.exp lam * ((shiftPhase ρ (coeffAL bb q) p).roots.card / p))
          + 2 * (2 * Real.exp 1 / M) ^ M * (sm.card : ℝ) ^ M
              * (2 * (R : ℝ) ^ M / (apSample X P₀ a).card)) := by
  have h := norm_sampleAvg_ee_phase_le X P₀ a hP₀ ha hne sm hs hsP hR1 hR ρ (coeffAL bb q) hk hθ0
    hsep hM hlam' hlam
  have hgood' : ∀ p ∈ sm, (if GoodPrime ρ p then θ₀ else 0) = θ₀ :=
    fun p hp => if_pos (hgood p hp)
  rw [Finset.sum_congr rfl (fun p hp => by rw [hgood' p hp])] at h
  unfold sampleAvg at h ⊢
  simp only [id] at h
  rw [show (∑ n ∈ apSample X P₀ a, ∏ a, fourier (q a)
      ((fun n a => ((Sval bb sm ρ n a : ℝ) : UnitAddCircle)) n a))
      = ∑ n ∈ apSample X P₀ a, ee (totalPhase sm ρ (coeffAL bb q) n) from
    Finset.sum_congr rfl fun n _ => torusChar_Sval bb sm ρ q n]
  exact h

end NormalNumbers.G4
