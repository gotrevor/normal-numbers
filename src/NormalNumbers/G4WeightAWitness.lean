/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightAFrame
import NormalNumbers.G4SubsetCWitness
import NormalNumbers.G4ScheduleBudget

/-!
# The §5 schedule interface for the master additive weight `w_{a,c}`

`ScheduleWitnessAU a c Ca A bb ℓ w` is `ScheduleWitnessSU` with exactly three fields moved, and
they are the *only* places a general bounded multiplier `a` is visible in the whole machine:

* `hN` — the layer budget grows from `1 + ⌈log_bb(2^K·D)⌉` to `1 + ⌈log_bb(2^K·(Ca·D))⌉`, an
  **additive** `⌈log_bb Ca⌉` (`G4PhaseA`, `gridFrameWA_propC_gen`);
* `hbig` — the large-prime average is `Ca` copies of the subset one (`bigAvgA_le'`);
* `hfar` — the far tail is dominated at `Ca · w_c` (`farAvgW_le_effC_smul`);

plus the retained small primes in `hbudget`, which are the **active** ones `{p : 1 ≤ a_p}`.
A–B never see the weight, and `hjunk` is unchanged because the valuation junk does not involve
`a` at all.

`hN_holdsA` settles the registered 🚦 trigger of `DIRECTION.md` in the negative: the schedule's
`N = 100K²` against `2^K · Dj ≤ 2^{3K}` leaves room for any `Ca ≤ 2^K`, so the enlargement
`D → Ca·D` **is** absorbable and no schedule quantity is capped from above by `N` in a way that
`⌈log_bb Ca⌉` breaks.
-/

open MeasureTheory Finset
open scoped BigOperators ArithmeticFunction.Omega

namespace NormalNumbers.G4

open PrimeLambert GridParams

/-- **What §5 must supply for `∑_n w_{a,c}(n)/bbⁿ`** at the omitted cylinder. -/
structure ScheduleWitnessAU (a c : ℕ → ℕ) (Ca : ℕ) (A : ℝ) (bb ℓ w : ℕ) where
  /-- grid parameters -/
  G : GridParams
  hK : 0 < G.K
  hr : 1 ≤ G.rDim
  hP₀ : 0 < G.P₀
  hΩ : (1 : ℝ) ≤ ((Ω G.P₀ : ℕ) : ℝ)
  /-- outer scale -/
  X : ℕ
  hne : (apSample X G.P₀ G.b₀).Nonempty
  /-- resolution and tube fraction -/
  η : ℝ
  hη : 0 < η
  ε : ℝ
  hε : 0 < ε
  hε1 : ε < 1
  /-- cylinder depth for B -/
  M : ℕ
  hM : 1 / ((bb : ℝ) ^ ℓ) ^ M ≤ η
  /-- spectral bound -/
  Lg : ℝ
  hlog : Real.log (1 + tensorGram G.K G.s).det ≤ Lg
  /-- **B** -/
  δ₁ : ℝ
  hδ₁ : 0 ≤ δ₁
  hB : ∀ g : ℕ, (1 - ε) * G.rDim ≤ g → g ≤ G.rDim →
    (((bb ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim * η ^ g * Real.exp (Lg / 2)
      * (Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (G.hDim + g)) ^ g
      ≤ δ₁ / 2 ^ G.rDim
  /-- small-prime cutoff and the medium cutoff -/
  R : ℕ
  hR : 2 ≤ R
  Y : ℕ
  hRY : R ≤ Y
  /-- Jackson degree, and the **enlarged** layer budget -/
  D : ℕ
  hN : 1 + Nat.clog bb (2 ^ G.K * (Ca * D)) ≤ G.N
  /-- **C** moment order and Laplace parameters -/
  Mc : ℕ
  hMc : 1 ≤ Mc
  lam' : ℝ
  hlam' : 1 ≤ lam'
  lam : ℝ
  hlam : 0 < lam
  /-- **D** size bounds -/
  Mx : ℝ
  hMx1 : 1 ≤ Mx
  hMx : ∀ n ∈ apSample X G.P₀ G.b₀, ∀ i : G.Idx,
    ((n + shiftAL G.B G.Q G.D₀ i : ℕ) : ℝ) ≤ Mx
  Dm : ℕ
  hDm : ∀ α, G.d α ≤ Dm
  ρmax : ℕ
  hρm : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ ρmax
  δbig : ℝ
  δjunk : ℝ
  δfar : ℝ
  hbig : (Ca : ℝ) * (Real.sqrt (4 * (1 + Real.log (Nat.log 2 Y) - Real.log (Nat.log 2 R))
        * rowL2 bb G.K
      + 2 * (Y : ℝ) ^ 2 * (rowL1 bb G.K) ^ 2 / (apSample X G.P₀ G.b₀).card)
      + (Real.log Mx / Real.log Y) * rowL1 bb G.K) ≤ δbig * (ε * η)
  hjunk : (effC c G.P₀ A * junkShiftBound G.P₀ X ρmax / ((apSample X G.P₀ G.b₀).card : ℝ))
      * rowL1 bb G.K ≤ δjunk * (ε * η)
  hfar : ((Ca : ℝ) * effC c G.P₀ A) * ((2 : ℝ) ^ G.K *
      ((farBound bb (G.K + G.N) (farC G X Dm) / Real.log 2
          + ((Ω G.P₀ : ℕ) : ℝ) * ((1 / (bb : ℝ)) ^ (G.K + G.N + 1) * (bb / (bb - 1))))
        + farJunkBound bb (G.K + G.N) (junkA G.P₀ X) (junkB X Dm)
            / ((apSample X G.P₀ G.b₀).card : ℝ))) ≤ δfar * (ε * η)
  /-- **the closed budget**, over the *active* small primes -/
  hbudget : δ₁ + (δbig + δjunk + δfar) + 2 * (1 / (ε * η * Real.sqrt (D + 1)))
    + (((2 * D + 1) ^ G.rDim : ℕ) : ℝ)
      * smallPrimeBound ((smallPrimes R G.P₀).filter (fun p => 1 ≤ a p)) (Fintype.card G.Idx)
          R Mc (apSample X G.P₀ G.b₀).card lam' lam (freqSeed bb G.K) < 1

variable (a c : ℕ → ℕ) {Ca : ℕ} (hCa : ∀ p, a p ≤ Ca) {A : ℝ} (hT : Tame c A)

/-- **`PropB` for the `a`-weighted frame.**  `PropB` never reads `S`. -/
theorem gridFrameWA_propB_of_bound (W : TWeight) (a : ℕ → ℕ) (bb : ℕ) (hbb : 2 ≤ bb)
    (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (sm : Finset ℕ)
    (γ : Torus G.rDim) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (D : ℕ)
    {ℓ w : ℕ} (hw : w < bb ^ ℓ)
    (homit : ∀ m, orbit bb (W.lambert bb) m ∉
      Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ))
    (M : ℕ) (hM : 1 / ((bb : ℝ) ^ ℓ) ^ M ≤ η) (hε1 : ε < 1) (hr : 1 ≤ G.rDim)
    {Lg : ℝ} (hlog : Real.log (1 + tensorGram G.K G.s).det ≤ Lg)
    {δ₁ : ℝ} (hδ : 0 ≤ δ₁)
    (hbound : ∀ g : ℕ, (1 - ε) * G.rDim ≤ g → g ≤ G.rDim →
      (((bb ^ ℓ - 1) ^ M : ℕ) : ℝ) ^ G.hDim * η ^ g * Real.exp (Lg / 2)
        * (Real.sqrt (2 * Real.pi * Real.exp 1 / g) * Real.sqrt (G.hDim + g)) ^ g
        ≤ δ₁ / 2 ^ G.rDim) :
    (gridFrameWA W a bb hbb G X hne sm γ hη hε D).PropB δ₁ :=
  gridFrameW_propB_of_bound W bb hbb G X hne sm γ hη hε D hw homit M hM hε1 hr hlog hδ hbound

/-- **The residual obligation for `∑_n w_{a,c}(n)/bbⁿ`.** -/
theorem separatingFrameExistsW_weightA_of_witness (h1 : 1 ≤ Ca) (bb : ℕ) (hbb : 3 ≤ bb)
    (hw : ∀ ℓ w : ℕ, w < bb ^ ℓ →
      (∀ m, orbit bb ((TWeight.weightA a c hCa hT).lambert bb) m ∉
        Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ)) →
      Nonempty (ScheduleWitnessAU a c Ca A bb ℓ w)) :
    SeparatingFrameExistsW bb ((TWeight.weightA a c hCa hT).lambert bb) := by
  have hbb2 : 2 ≤ bb := by omega
  intro x y hx hxy hy hno
  obtain ⟨ℓ, w, hwℓ, hsub⟩ := exists_cylinder_subset bb hbb2 hx hxy hy
  have homit : ∀ m, orbit bb ((TWeight.weightA a c hCa hT).lambert bb) m ∉
      Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ) :=
    fun m h => hno m (hsub h)
  obtain ⟨W⟩ := hw ℓ w hwℓ homit
  have hA : (gridFrameWA (TWeight.weightA a c hCa hT) a bb hbb2 W.G W.X W.hne
      ((smallPrimes W.R W.G.P₀).filter (fun p => 1 ≤ a p)) (frozenGammaAC a c bb W.G)
      W.hη W.hε W.D).PropA :=
    gridFrameWA_propA (TWeight.weightA a c hCa hT) a bb hbb2 W.G W.X W.hne _ _ W.hη W.hε W.D
  have hB : (gridFrameWA (TWeight.weightA a c hCa hT) a bb hbb2 W.G W.X W.hne
      ((smallPrimes W.R W.G.P₀).filter (fun p => 1 ≤ a p)) (frozenGammaAC a c bb W.G)
      W.hη W.hε W.D).PropB W.δ₁ :=
    gridFrameWA_propB_of_bound (TWeight.weightA a c hCa hT) a bb hbb2 W.G W.X W.hne _ _
      W.hη W.hε W.D hwℓ homit W.M W.hM W.hε1 W.hr W.hlog W.hδ₁ W.hB
  have hC := gridFrameWA_propC_gen (TWeight.weightA a c hCa hT) a bb hbb2 W.G W.X W.hne
      ((smallPrimes W.R W.G.P₀).filter (fun p => 1 ≤ a p)) (frozenGammaAC a c bb W.G)
      W.hη W.hε (R := W.R) (Ca := Ca)
      (fun p hp => (mem_smallPrimes.1 (Finset.mem_filter.1 hp).1).1)
      (fun p hp => (mem_smallPrimes.1 (Finset.mem_filter.1 hp).1).2.2)
      (fun p hp => (Finset.mem_filter.1 hp).2) hCa
      (by have := W.hR; omega)
      (fun p hp => (mem_smallPrimes.1 (Finset.mem_filter.1 hp).1).2.1) W.hN W.hMc W.hlam'
      W.hlam
  have hD := gridFrameWA_weightA_propD_of_bounds a c hCa h1 hT bb hbb W.G W.X W.R W.Y W.hne
      W.hP₀ W.hΩ W.hK W.hR W.hRY W.hMx1 W.hMx W.hDm W.hρm W.hη W.hε W.D W.hbig W.hjunk W.hfar
  exact ⟨_, W.δ₁, W.δbig + W.δjunk + W.δfar, _, _, _, hA, hB, hC, hD,
    Frame.propJackson _,
    smallPrimeBound_nonneg _ _ _ _ _ (by linarith [W.hlam']) W.hlam, W.hbudget⟩

/-- **The conditional headline for `w_{a,c}`.** -/
theorem isDisjunctive_weightA_of_witness (h1 : 1 ≤ Ca) (bb : ℕ) (hbb : 3 ≤ bb)
    (hw : ∀ ℓ w : ℕ, w < bb ^ ℓ →
      (∀ m, orbit bb ((TWeight.weightA a c hCa hT).lambert bb) m ∉
        Set.Ico ((w : ℝ) / (bb : ℝ) ^ ℓ) (((w : ℝ) + 1) / (bb : ℝ) ^ ℓ)) →
      Nonempty (ScheduleWitnessAU a c Ca A bb ℓ w)) :
    IsDisjunctive bb ((TWeight.weightA a c hCa hT).lambert bb) :=
  isDisjunctive_of_framesW (separatingFrameExistsW_weightA_of_witness a c hCa hT h1 bb hbb hw)

/-! ### The layer budget absorbs `Ca`: the registered trigger does not fire -/

/-- **`hN` at the enlarged Fourier box.**  The schedule's `N = 100K²` against
`2^K · Dj K k₄ ≤ 2^{3K}` absorbs any `Ca ≤ 2^K`. -/
lemma hN_holdsA {b K k₄ Ca : ℕ} (hb : 2 ≤ b) (hK4 : K = 4 * k₄) (hK : 100 ≤ K)
    (hCa : Ca ≤ 2 ^ K) :
    1 + Nat.clog b (2 ^ K * (Ca * Sched.Dj K k₄)) ≤ Sched.N K := by
  have hbase : 2 ^ K * (Ca * Sched.Dj K k₄) ≤ 2 ^ (Sched.N K - 1) := by
    have h1 : 2 ^ K * (Ca * Sched.Dj K k₄) ≤ 2 ^ K * (2 ^ K * Sched.Dj K k₄) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hCa)
    have h2 : 2 ^ K * Sched.Dj K k₄ ≤ 2 ^ (3 * K) := by
      have hk : 25 ≤ k₄ := by omega
      have h3 := Sched.two_Dj_add_one_le hK4 hk
      have h4 : (4 : ℕ) ^ K = 2 ^ (2 * K) := by rw [pow_mul]; norm_num
      calc 2 ^ K * Sched.Dj K k₄ ≤ 2 ^ K * 2 ^ (2 * K) := by
            rw [← h4]; exact Nat.mul_le_mul_left _ (by omega)
        _ = 2 ^ (3 * K) := by rw [← pow_add]; ring_nf
    have h5 : 2 ^ K * (2 ^ K * Sched.Dj K k₄) ≤ 2 ^ K * 2 ^ (3 * K) :=
      Nat.mul_le_mul_left _ h2
    refine (h1.trans h5).trans ?_
    rw [← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    unfold Sched.N
    have : 4 * K + 1 ≤ 100 * K ^ 2 := by nlinarith
    omega
  have h := (Nat.clog_le_iff_le_pow (by norm_num)).2 hbase
  have h' := Nat.clog_anti_left (b := b) (c := 2) (n := 2 ^ K * (Ca * Sched.Dj K k₄))
    (by norm_num) hb
  have hN : 1 ≤ Sched.N K := Sched.N_pos (by omega)
  omega

end NormalNumbers.G4
