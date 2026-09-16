/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4FrameW
import NormalNumbers.G4PhaseA

/-!
# The concrete frame for an `a`-weighted small-prime vector, and `PropA`/`PropB`/`PropC`

`gridFrameW` retains the small primes through the *indicator* vector `Sval` (`omegaOn sm`).  For
the master additive weight `w_{a,c}(n) = ∑_{p∣n}(a_p + c_p(v_p(n)−1))` the retained part is the
`a`-weighted count `omegaOnA a sm`, so the frame's small-prime field must be `SvalA`
(`G4PhaseA`).  This module builds that frame and discharges the three properties that do not
touch §4D.

  `gridFrameWA W a bb hbb G X hne sm γ hη hε D : Frame`

is `gridFrameW W bb hbb G X hne sm γ hη hε D` with the single field `S` replaced, so **every**
other field is definitionally unchanged.  Consequently `PropA` and `PropB` — which read `w`, `x`,
`d`, `t`, `θ`, `γ`, `A` and never `S` — transfer by `exact`, with no new proof.

**`PropC` transfers with no loss of seed**, which is the point of `G4PhaseA`: take `sm` already
filtered to the *active* primes `{p : 1 ≤ a_p}` — legitimate, because an inactive prime
contributes `0` to `omegaOnA` and so may be dropped from the retained vector for free — and then
the per-prime seed `if GoodPrime ρ p ∧ 1 ≤ a p then θ₀ else 0` of
`norm_sampleAvg_torusChar_SvalA_le` collapses to the constant `θ₀`.  The conclusion is
*literally* `gridFrame_propC`'s `smallPrimeBound`, with the same four error terms.

`gridFrameWA_propC_gen` then discharges the seed at `θ₀ = freqSeed bb K`, under the **only**
quantitative cost of a general bounded `a`: the layer budget grows from
`1 + ⌈log_bb(2^K·D)⌉` to `1 + ⌈log_bb(2^K·Ca·D)⌉`, an additive `⌈log_bb Ca⌉`.

Sanity instances: `a = 1` gives back `gridFrameW` (`gridFrameWA_one`), and `a = 1_S` gives the
prime-subset frame at the filtered small primes (`omegaOnA_indicator`) — i.e. the prime-subset
campaign is this one at `a = 1_S`.
-/

open MeasureTheory Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-- **The concrete frame with an `a`-weighted small-prime vector.**  Only the field `S` differs
from `gridFrameW`. -/
noncomputable def gridFrameWA (W : TWeight) (a : ℕ → ℕ) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams)
    (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) : Frame :=
  { gridFrameW W bb hbb G X hne sm γ hη hε D with
    S := fun n ν =>
      ((SvalA bb a sm (shiftAL G.B G.Q G.D₀ (N := G.N)) n (G.rowEquiv.symm ν) : ℝ) :
        UnitAddCircle) }

@[simp] lemma gridFrameWA_r (W : TWeight) (a : ℕ → ℕ) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams)
    (X : ℕ) (hne) (sm : Finset ℕ) (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (D : ℕ) : (gridFrameWA W a bb hbb G X hne sm γ hη hε D).r = G.rDim := rfl

@[simp] lemma gridFrameWA_P (W : TWeight) (a : ℕ → ℕ) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams)
    (X : ℕ) (hne) (sm : Finset ℕ) (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (D : ℕ) : (gridFrameWA W a bb hbb G X hne sm γ hη hε D).P = apSample X G.P₀ G.b₀ := rfl

@[simp] lemma gridFrameWA_D (W : TWeight) (a : ℕ → ℕ) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams)
    (X : ℕ) (hne) (sm : Finset ℕ) (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (D : ℕ) : (gridFrameWA W a bb hbb G X hne sm γ hη hε D).D = D := rfl

/-- `a = 1` is the unweighted frame. -/
lemma gridFrameWA_one (W : TWeight) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    gridFrameWA W (fun _ => 1) bb hbb G X hne sm γ hη hε D
      = gridFrameW W bb hbb G X hne sm γ hη hε D := by
  unfold gridFrameWA
  dsimp only
  simp only [SvalA_one]
  rfl

/-- **`PropA` for the `a`-weighted frame.**  `PropA` never reads `S`, and every other field is
definitionally `gridFrameW`'s. -/
theorem gridFrameWA_propA (W : TWeight) (a : ℕ → ℕ) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams)
    (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ) :
    (gridFrameWA W a bb hbb G X hne sm γ hη hε D).PropA :=
  gridFrameW_propA W bb hbb G X hne sm γ hη hε D

/-- The frame character at the `a`-weighted vector, reindexed by the row equivalence. -/
lemma torusChar_gridFrameWA_S (W : TWeight) (a : ℕ → ℕ) (bb : ℕ) (hbb : 2 ≤ bb)
    (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ)
    (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ)
    (q : Fin G.rDim → ℤ) (n : ℕ) :
    torusChar q ((gridFrameWA W a bb hbb G X hne sm γ hη hε D).S n)
      = ∏ u : Fin G.K → Fin G.s, fourier (q (G.rowEquiv u))
          (((SvalA bb a sm (shiftAL G.B G.Q G.D₀ (N := G.N)) n u : ℝ) : UnitAddCircle)) := by
  unfold torusChar
  rw [← Equiv.prod_comp G.rowEquiv
    (fun ν => fourier (q ν) ((gridFrameWA W a bb hbb G X hne sm γ hη hε D).S n ν))]
  exact Finset.prod_congr rfl fun u _ => by simp [gridFrameWA]

/-- **`PropC` for the `a`-weighted frame**, with `sm` the *active* small primes (`1 ≤ a_p`).
The bound is literally `gridFrame_propC`'s `smallPrimeBound`: the four §4C error terms do not
see `a` at all (`shiftPhaseA_roots`), and the good-prime contraction keeps the full seed `θ₀` on
every prime of `sm`. -/
theorem gridFrameWA_propC (W : TWeight) (a : ℕ → ℕ) (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams)
    (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ) (γ : Torus G.rDim)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) {D : ℕ}
    (hs : ∀ p ∈ sm, p.Prime) (hsP : ∀ p ∈ sm, ¬ p ∣ G.P₀) (hact : ∀ p ∈ sm, 1 ≤ a p)
    {R : ℕ} (hR1 : 1 ≤ R) (hR : ∀ p ∈ sm, p ≤ R)
    {θ₀ : ℝ} (hθ0 : 0 ≤ θ₀)
    (hsep : ∀ q : (Fin G.K → Fin G.s) → ℤ, q ≠ 0 → (∀ u, |q u| ≤ (D : ℤ)) → ∀ p ∈ sm,
      θ₀ ≤ ∑ i : G.Idx, distZ ((a p : ℝ) * coeffAL bb q i) ^ 2)
    {M : ℕ} (hM : 1 ≤ M) {lam' lam : ℝ} (hlam' : 1 ≤ lam') (hlam : 0 < lam) :
    (gridFrameWA W a bb hbb G X hne sm γ hη hε D).PropC
      (smallPrimeBound sm (Fintype.card G.Idx) R M (apSample X G.P₀ G.b₀).card lam' lam θ₀) := by
  classical
  intro q hq hq0
  set ρ := shiftAL G.B G.Q G.D₀ (N := G.N) with hρ
  set q' : (Fin G.K → Fin G.s) → ℤ := fun u => q (G.rowEquiv u) with hq'
  have hq'0 : q' ≠ 0 := by
    intro h
    refine hq0 (funext fun ν => ?_)
    obtain ⟨u, rfl⟩ := G.rowEquiv.surjective ν
    exact congrFun h u
  have hq'D : ∀ u, |q' u| ≤ (D : ℤ) := fun u => (mem_fourierBox.1 hq) _
  have hsP' : ∀ p ∈ sm, Nat.Coprime p G.P₀ := fun p hp =>
    ((hs p hp).coprime_iff_not_dvd).2 (hsP p hp)
  have hgood : ∀ p ∈ sm, GoodPrime ρ p := fun p hp =>
    G.goodPrime_of_not_dvd_P₀ (hs p hp) (hsP p hp)
  have hk : ∀ p ∈ sm, 2 * Fintype.card G.Idx ≤ p := fun p hp =>
    G.two_mul_card_le_of_not_dvd (hs p hp) (hsP p hp)
  have key := norm_sampleAvg_torusChar_SvalA_le bb X G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ hne a sm hs
    hsP' hR1 hR ρ hk hθ0 (fun p hp _ => hsep q' hq'0 hq'D p hp) hM hlam' hlam
  -- every prime of `sm` is good and active, so the per-prime seed is the constant `θ₀`
  have hif : ∀ p ∈ sm, 4 * (if GoodPrime ρ p ∧ 1 ≤ a p then θ₀ else 0) / (p : ℝ)
      = 4 * θ₀ / (p : ℝ) := fun p hp => by rw [if_pos ⟨hgood p hp, hact p hp⟩]
  rw [Finset.sum_congr rfl hif] at key
  have hsame : sampleAvg (gridFrameWA W a bb hbb G X hne sm γ hη hε D).P
      (gridFrameWA W a bb hbb G X hne sm γ hη hε D).S (torusChar q)
      = sampleAvg (apSample X G.P₀ G.b₀)
          (fun n u => ((SvalA bb a sm ρ n u : ℝ) : UnitAddCircle))
          (fun y => ∏ u, fourier (q' u) (y u)) := by
    unfold sampleAvg
    congr 1
    exact Finset.sum_congr rfl fun n _ =>
      torusChar_gridFrameWA_S W a bb hbb G X hne sm γ hη hε D q n
  rw [hsame]
  refine key.trans ?_
  unfold smallPrimeBound
  have hp0 : ∀ p ∈ sm, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hs p hp).pos
  have hprod1 : (∏ p ∈ sm, (1 + lam' * (2 * ((shiftPhase ρ (coeffAL bb q') p).roots.card : ℝ) / p)))
      ≤ ∏ p ∈ sm, (1 + lam' * (2 * (Fintype.card G.Idx : ℝ) / p)) := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have := hp0 p hp
      positivity
    · have hpp := hp0 p hp
      have := card_roots_shiftPhase_le ρ (coeffAL bb q') p
      have hlam'0 : (0 : ℝ) ≤ lam' := by linarith
      gcongr
  have hprod2 :
      (∏ p ∈ sm, (1 + Real.exp lam * (((shiftPhase ρ (coeffAL bb q') p).roots.card : ℝ) / p)))
      ≤ ∏ p ∈ sm, (1 + Real.exp lam * ((Fintype.card G.Idx : ℝ) / p)) := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have := hp0 p hp
      positivity
    · have hpp := hp0 p hp
      have := card_roots_shiftPhase_le ρ (coeffAL bb q') p
      gcongr
  have hlam'pos : (0 : ℝ) < lam' ^ M := by positivity
  have hc : (0 : ℝ) ≤ 2 * (2 * Real.exp 1 / lam) ^ M := by positivity
  gcongr

/-- **`PropC` for the `a`-weighted frame, seed discharged.**  `θ₀ = freqSeed bb K`, under the
enlarged layer budget `1 + ⌈log_bb(2^K·Ca·D)⌉ ≤ N`.  That enlargement — an *additive*
`⌈log_bb Ca⌉` on a budget of size `Θ(K)` — is the entire quantitative cost of a general bounded
multiplier. -/
theorem gridFrameWA_propC_gen (W : TWeight) (a : ℕ → ℕ) (bb : ℕ) (hbb : 2 ≤ bb)
    (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ)
    (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) {D Ca : ℕ}
    (hs : ∀ p ∈ sm, p.Prime) (hsP : ∀ p ∈ sm, ¬ p ∣ G.P₀) (hact : ∀ p ∈ sm, 1 ≤ a p)
    (hCa : ∀ p, a p ≤ Ca)
    {R : ℕ} (hR1 : 1 ≤ R) (hR : ∀ p ∈ sm, p ≤ R)
    (hN : 1 + Nat.clog bb (2 ^ G.K * (Ca * D)) ≤ G.N)
    {M : ℕ} (hM : 1 ≤ M) {lam' lam : ℝ} (hlam' : 1 ≤ lam') (hlam : 0 < lam) :
    (gridFrameWA W a bb hbb G X hne sm γ hη hε D).PropC
      (smallPrimeBound sm (Fintype.card G.Idx) R M (apSample X G.P₀ G.b₀).card lam' lam
        (freqSeed bb G.K)) :=
  gridFrameWA_propC W a bb hbb G X hne sm γ hη hε hs hsP hact hR1 hR
    (freqSeed_nonneg (by exact_mod_cast hbb) G.K)
    (fun q hq hqD p hp => sum_sq_distZ_coeffA_ge_gen hbb hN (hact p hp) (hCa p) hq hqD)
    hM hlam' hlam

end NormalNumbers.G4
