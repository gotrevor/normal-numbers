/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4FarTail
import NormalNumbers.G4SubsetWeight
import NormalNumbers.G4SubsetSchedule
import NormalNumbers.G4SubsetJunk

/-!
# The far tail restricted to `S`-primes

`G4FarTail.sum_omegaR_add_le` bounds the progression mean of `ω` by `log(X/|P|) + log log X`, an
all-primes harmonic sum; in the base-2 frame that term is `≈ e` and forces `e ≤ 2^{O(K²)}`
(`G4.SchedB.hypE_frame_excludes_logRate`).  For `ω_S` the same Jensen argument, with the
`S`-smooth squarefree divisor count `2^{ω_S(m)} = #{A ⊆ S-primes : ∏A ∣ m}` in place of `d(m)`,
gives `log(X/|P|) + F_S(X)` (`sum_omegaS_add_le`): the far tail sees only the `S`-mass.
This is the first half of the decoupling the reopen node `SRestrictedFrame` asks for.
-/

open Finset Real

namespace NormalNumbers.G4

open PrimeLambert

variable (S : ℕ → Prop) [DecidablePred S]

/-- The `S`-primes `≤ N`. -/
def sPrimesLe (N : ℕ) : Finset ℕ := (N + 1).primesBelow.filter S

lemma two_pow_omegaSN_eq {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    (2 : ℝ) ^ omegaSN S m
      = ∑ A ∈ (sPrimesLe S N).powerset, if (∏ p ∈ A, p) ∣ m then (1 : ℝ) else 0 := by
  classical
  rw [Finset.sum_boole]
  have hfil : (sPrimesLe S N).powerset.filter (fun A => (∏ p ∈ A, p) ∣ m)
      = (m.primeFactors.filter S).powerset := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, sPrimesLe]
    constructor
    · rintro ⟨hA, hd⟩ p hp
      have hp' := hA hp
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp'
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hp'.1.2, (Finset.dvd_prod_of_mem _ hp).trans hd, by omega⟩, hp'.2⟩
    · intro hA
      refine ⟨fun p hp => ?_, ?_⟩
      · have := hA hp
        rw [Finset.mem_filter, Nat.mem_primeFactors] at this
        rw [Finset.mem_filter, Nat.mem_primesBelow]
        exact ⟨⟨by have := Nat.le_of_dvd (by omega) this.1.2.1; omega, this.1.1⟩, this.2⟩
      · refine Finset.prod_primes_dvd m (fun p hp => ?_) (fun p hp => ?_)
        · have := hA hp
          rw [Finset.mem_filter, Nat.mem_primeFactors] at this
          exact this.1.1.prime
        · have := hA hp
          rw [Finset.mem_filter, Nat.mem_primeFactors] at this
          exact this.1.2.1
  rw [hfil, Finset.card_powerset]
  unfold omegaSN
  push_cast
  ring

/-- `∑_{1 ≤ m ≤ N} 2^{ω_S(m)} ≤ (N+1)·exp(F_S(N+1))`. -/
lemma sum_two_pow_omegaSN_le (N : ℕ) :
    ∑ m ∈ Finset.Ico 1 (N + 1), (2 : ℝ) ^ omegaSN S m
      ≤ (N + 1 : ℕ) * Real.exp (MertensAP.sumInvPrimesIn S (N + 1)) := by
  classical
  have hpos : ∀ A ∈ (sPrimesLe S N).powerset, 0 < ∏ p ∈ A, p := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    refine Finset.prod_pos fun p hp => ?_
    have := hA hp
    rw [sPrimesLe, Finset.mem_filter, Nat.mem_primesBelow] at this
    exact this.1.2.pos
  calc ∑ m ∈ Finset.Ico 1 (N + 1), (2 : ℝ) ^ omegaSN S m
      = ∑ m ∈ Finset.Ico 1 (N + 1), ∑ A ∈ (sPrimesLe S N).powerset,
          if (∏ p ∈ A, p) ∣ m then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.mem_Ico] at hm
        exact two_pow_omegaSN_eq S (by omega) (by omega)
    _ = ∑ A ∈ (sPrimesLe S N).powerset, ∑ m ∈ Finset.Ico 1 (N + 1),
          if (∏ p ∈ A, p) ∣ m then (1 : ℝ) else 0 := Finset.sum_comm
    _ ≤ ∑ A ∈ (sPrimesLe S N).powerset, ((N + 1 : ℕ) : ℝ) * ∏ p ∈ A, (p : ℝ)⁻¹ := by
        refine Finset.sum_le_sum fun A hA => ?_
        rw [Finset.sum_boole]
        have := card_multiples_Ico_le (N + 1) (∏ p ∈ A, p) (hpos A hA)
        refine this.trans (le_of_eq ?_)
        rw [div_eq_mul_inv, Nat.cast_prod, Finset.prod_inv_distrib]
    _ = ((N + 1 : ℕ) : ℝ) * ∏ p ∈ sPrimesLe S N, (1 + (p : ℝ)⁻¹) := by
        rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ ((N + 1 : ℕ) : ℝ) * Real.exp (MertensAP.sumInvPrimesIn S (N + 1)) := by
        gcongr
        unfold MertensAP.sumInvPrimesIn
        rw [Real.exp_sum]
        have hs : sPrimesLe S N = (N + 1).primesBelow.filter S := rfl
        rw [hs]
        refine Finset.prod_le_prod (fun p _ => by positivity) fun p _ => ?_
        have := Real.add_one_le_exp ((p : ℝ)⁻¹)
        linarith

/-- **The `S`-restricted far tail.**  For `P ⊆ [0, X)` nonempty and `ρ ≥ 1`,
`∑_{n∈P} ω_S(n+ρ) · log 2 ≤ |P|·(log((X+ρ)/|P|) + F_S(X+ρ))`. -/
theorem sum_omegaS_add_le {X : ℕ} (P : Finset ℕ) (hP : P ⊆ Finset.range X) (hne : P.Nonempty)
    {ρ : ℕ} (hρ : 1 ≤ ρ) :
    (∑ n ∈ P, omegaS S (n + ρ)) * Real.log 2
      ≤ P.card * (Real.log (((X + ρ : ℕ) : ℝ) / P.card)
          + MertensAP.sumInvPrimesIn S (X + ρ)) := by
  classical
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  have hX : 1 ≤ X := by
    obtain ⟨n, hn⟩ := hne
    have := Finset.mem_range.1 (hP hn); omega
  set N := X + ρ - 1 with hN
  have hN1 : N + 1 = X + ρ := by omega
  have hx : ∀ n ∈ P, 0 < (2 : ℝ) ^ omegaSN S (n + ρ) := fun _ _ => by positivity
  have hstep : (∑ n ∈ P, omegaS S (n + ρ)) * Real.log 2
      = ∑ n ∈ P, Real.log ((2 : ℝ) ^ omegaSN S (n + ρ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Real.log_pow]; rfl
  have hshift : ∑ n ∈ P, (2 : ℝ) ^ omegaSN S (n + ρ)
      ≤ ∑ m ∈ Finset.Ico 1 (N + 1), (2 : ℝ) ^ omegaSN S m := by
    rw [← Finset.sum_image (f := fun m => (2 : ℝ) ^ omegaSN S m) (s := P) (g := fun n => n + ρ)
      (fun a _ b _ h => by simpa using h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    have := Finset.mem_range.1 (hP hn)
    rw [Finset.mem_Ico]; omega
  have hbound := (hshift.trans (sum_two_pow_omegaSN_le S N))
  rw [hN1] at hbound
  have hsum0 : 0 < ∑ n ∈ P, (2 : ℝ) ^ omegaSN S (n + ρ) := Finset.sum_pos hx hne
  rw [hstep]
  refine (sum_log_le_card_mul_log_avg P hne _ hx).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  have hXρ : (0 : ℝ) < ((X + ρ : ℕ) : ℝ) := by exact_mod_cast (show 0 < X + ρ by omega)
  calc Real.log ((∑ n ∈ P, (2 : ℝ) ^ omegaSN S (n + ρ)) / P.card)
      ≤ Real.log (((X + ρ : ℕ) : ℝ) * Real.exp (MertensAP.sumInvPrimesIn S (X + ρ)) / P.card) :=
        Real.log_le_log (div_pos hsum0 hc) (div_le_div_of_nonneg_right hbound hc.le)
    _ = Real.log (((X + ρ : ℕ) : ℝ) / P.card) + MertensAP.sumInvPrimesIn S (X + ρ) := by
        rw [mul_div_right_comm, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]

end NormalNumbers.G4

namespace NormalNumbers.G4

open PrimeLambert GridParams

variable (S : ℕ → Prop) [DecidablePred S]

/-- Primes `≥ A` add at most `1/A` each: `F_S(M) ≤ F_S(A) + (M − A)/A`. -/
lemma sumInvPrimesIn_le_add {A M : ℕ} (hA : 1 ≤ A) :
    MertensAP.sumInvPrimesIn S M ≤ MertensAP.sumInvPrimesIn S A + ((M - A : ℕ) : ℝ) / A := by
  classical
  unfold MertensAP.sumInvPrimesIn
  rw [← Finset.sum_filter_add_sum_filter_not ((M.primesBelow).filter S) (fun p => p < A)]
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  set F := ((M.primesBelow).filter S).filter (fun p => ¬ p < A) with hF
  have h1 : ∑ p ∈ ((M.primesBelow).filter S).filter (fun p => p < A), (p : ℝ)⁻¹
      ≤ ∑ p ∈ (A.primesBelow).filter S, (p : ℝ)⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro p hp
    simp only [Finset.mem_filter, Nat.mem_primesBelow] at hp ⊢
    exact ⟨⟨hp.2, hp.1.1.2⟩, hp.1.2⟩
  have h2 : ∑ p ∈ F, (p : ℝ)⁻¹ ≤ ∑ p ∈ F, (A : ℝ)⁻¹ := by
    refine Finset.sum_le_sum fun p hp => ?_
    simp only [hF, Finset.mem_filter, Nat.mem_primesBelow] at hp
    have : (A : ℝ) ≤ p := by exact_mod_cast (show A ≤ p by omega)
    exact inv_anti₀ hAr this
  have hsub : F ⊆ Finset.Ico A M := by
    intro p hp
    simp only [hF, Finset.mem_filter, Nat.mem_primesBelow, Finset.mem_Ico] at hp ⊢
    omega
  have h3 : (F.card : ℝ) ≤ ((M - A : ℕ) : ℝ) := by
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    exact_mod_cast this
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  have h4 : (F.card : ℝ) * (A : ℝ)⁻¹ ≤ ((M - A : ℕ) : ℝ) / A := by
    rw [div_eq_mul_inv]; gcongr
  linarith

/-- **The `S`-far-tail constant** `C_S = log((X+Dm)/|P|) + F_S(X+Dm)`: `farC` with the
all-primes `log log(X+Dm)` replaced by the `S`-mass. -/
noncomputable def farCS (G : GridParams) (X Dm : ℕ) : ℝ :=
  Real.log (((X + Dm : ℕ) : ℝ) / (apSample X G.P₀ G.b₀).card)
    + MertensAP.sumInvPrimesIn S (X + Dm)

/-- **The AP-mean of `ω_S` at layer `j`**: `∑_{n∈P} ω_S(n + ρ_{α,j}) ≤ |P| (C_S + 2j)/log 2`. -/
theorem sum_omegaS_shiftG_le (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (α : G.Atom) {j : ℕ} (hj : 1 ≤ j) :
    ∑ n ∈ apSample X G.P₀ G.b₀, omegaS S (n + shiftG G.B G.Q G.D₀ α j)
      ≤ (apSample X G.P₀ G.b₀).card * ((farCS S G X Dm + 2 * j) / Real.log 2) := by
  set P := apSample X G.P₀ G.b₀ with hP
  set ρ := shiftG G.B G.Q G.D₀ α j with hρ
  have hρ1 : 1 ≤ ρ := shiftG_pos G α hj
  have hρle : ρ ≤ j * Dm := by
    rw [hρ]; unfold shiftG
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_left j (hDm α))
  have hPsub : P ⊆ Finset.range X := Finset.filter_subset _ _
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX1 : 1 ≤ X := by
    have h1 := hne.card_pos
    have h2 := Finset.card_le_card hPsub
    rw [Finset.card_range] at h2
    omega
  set A : ℕ := X + Dm with hA
  have hA1 : 1 ≤ A := by omega
  have hXρ : X + ρ ≤ j * A := by
    rw [hA, Nat.mul_add]
    have : X ≤ j * X := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- the `S`-mass at `X + ρ`
  have hF : MertensAP.sumInvPrimesIn S (X + ρ) ≤ MertensAP.sumInvPrimesIn S A + j := by
    have h1 := sumInvPrimesIn_le_add S (M := X + ρ) hA1
    have hAr : (0 : ℝ) < A := by exact_mod_cast hA1
    have h2 : ((X + ρ - A : ℕ) : ℝ) / A ≤ j := by
      rw [div_le_iff₀ hAr]
      have : X + ρ - A ≤ j * A := by omega
      exact_mod_cast this
    linarith
  -- the sample-density term at `X + ρ`
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hL : Real.log (((X + ρ : ℕ) : ℝ) / P.card) ≤ Real.log ((A : ℝ) / P.card) + j := by
    have hpos : (0 : ℝ) < ((X + ρ : ℕ) : ℝ) / P.card := by
      have : (0 : ℝ) < ((X + ρ : ℕ) : ℝ) := by exact_mod_cast (show 0 < X + ρ by omega)
      positivity
    have hAr : (0 : ℝ) < A := by exact_mod_cast hA1
    calc Real.log (((X + ρ : ℕ) : ℝ) / P.card) ≤ Real.log ((j : ℝ) * (A / P.card)) := by
          apply Real.log_le_log hpos
          rw [← mul_div_assoc]
          apply div_le_div_of_nonneg_right _ hc.le
          exact_mod_cast hXρ
      _ = Real.log j + Real.log ((A : ℝ) / P.card) :=
          Real.log_mul (by positivity) (by positivity)
      _ ≤ Real.log ((A : ℝ) / P.card) + j := by
          have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < j); linarith
  have hmain := sum_omegaS_add_le S P hPsub hne hρ1
  have hfcs : farCS S G X Dm = Real.log ((A : ℝ) / P.card) + MertensAP.sumInvPrimesIn S A := by
    rw [farCS, ← hP]
  have hk : (∑ n ∈ P, omegaS S (n + ρ)) * Real.log 2 ≤ P.card * (farCS S G X Dm + 2 * j) := by
    refine hmain.trans ?_
    rw [hfcs]; exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  rw [mul_div_assoc', le_div_iff₀ hlog2]
  exact hk

lemma farCS_nonneg (G : GridParams) (X : ℕ) (hne : (apSample X G.P₀ G.b₀).Nonempty) (Dm : ℕ) :
    0 ≤ farCS S G X Dm := by
  have hP : (apSample X G.P₀ G.b₀).card ≤ X := by
    have hsub : apSample X G.P₀ G.b₀ ⊆ Finset.range X := Finset.filter_subset _ _
    simpa using Finset.card_le_card hsub
  have hc : (0 : ℝ) < (apSample X G.P₀ G.b₀).card := by exact_mod_cast hne.card_pos
  unfold farCS
  have h1 : 0 ≤ Real.log (((X + Dm : ℕ) : ℝ) / (apSample X G.P₀ G.b₀).card) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hc, one_mul]
    exact_mod_cast (show (apSample X G.P₀ G.b₀).card ≤ X + Dm by omega)
  have h2 := MertensAP.sumInvPrimesIn_nonneg (S := S) (X + Dm)
  linarith

theorem sum_abs_farPartW_subset_leS (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty)
    {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) (a : Fin G.K → Fin G.s) :
    ∑ n ∈ apSample X G.P₀ G.b₀, |farPartW (TWeight.subset S) bb G n a|
      ≤ (apSample X G.P₀ G.b₀).card * ((2 : ℝ) ^ G.K / Real.log 2
          * farBound bb (G.K + G.N) (farCS S G X Dm)) := by
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  set P := apSample X G.P₀ G.b₀ with hP
  set J := G.K + G.N with hJ
  set C := farCS S G X Dm with hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set f0 : G.Atom → ℕ → ℕ → ℝ := fun α n i =>
    omegaR (n + shiftG G.B G.Q G.D₀ α (J + i + 1)) / (bb : ℝ) ^ (J + i + 1) with hf0def
  set f : G.Atom → ℕ → ℕ → ℝ := fun α n i =>
    omegaS S (n + shiftG G.B G.Q G.D₀ α (J + i + 1)) / (bb : ℝ) ^ (J + i + 1) with hf
  set g : G.Atom → ℕ → ℕ → ℝ := fun α n i =>
    ((TWeight.subset S).wN (n + shiftG G.B G.Q G.D₀ α (J + i + 1)) : ℝ)
      / (bb : ℝ) ^ (J + i + 1) with hg
  have hf0 : ∀ α n i, 0 ≤ f α n i := fun α n i => by
    simp only [hf]; unfold omegaS; positivity
  have hff0 : ∀ α n i, f α n i ≤ f0 α n i := by
    intro α n i
    simp only [hf, hf0def]
    exact div_le_div_of_nonneg_right (omegaS_le_omegaR (S := S) _) (by positivity)
  have hg0 : ∀ α n i, 0 ≤ g α n i := fun α n i => by
    simp only [hg]; positivity
  have hgf : ∀ α n i, g α n i ≤ f α n i := by
    intro α n i
    simp only [hg, hf]
    rw [TWeight.subset_wN]
  have hfs : ∀ α, ∀ n ∈ P, Summable (f α n) := fun α n hn =>
    Summable.of_nonneg_of_le (fun i => hf0 α n i) (fun i => hff0 α n i) (summable_far bb hbb G hn α)
  have hgs : ∀ α, ∀ n ∈ P, Summable (g α n) := fun α n hn =>
    Summable.of_nonneg_of_le (fun i => hg0 α n i) (fun i => hgf α n i) (hfs α n hn)
  have hpt : ∀ n ∈ P, |farPartW (TWeight.subset S) bb G n a|
      ≤ ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * ∑' i, f α n i := by
    intro n hn
    unfold farPartW
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine le_trans (le_of_eq (abs_of_nonneg (tsum_nonneg fun i => hg0 α n i))) ?_
    exact Summable.tsum_le_tsum (fun i => hgf α n i) (hgs α n hn) (hfs α n hn)
  have hlayer : ∀ α i, ∑ n ∈ P, f α n i
      ≤ P.card * ((C + 2 * ((J : ℝ) + i + 1)) * (1 / (bb : ℝ)) ^ (J + i + 1)) / Real.log 2 := by
    intro α i
    simp only [hf]
    rw [← Finset.sum_div]
    have := sum_omegaS_shiftG_le S G X hne hDm α (j := J + i + 1) (by omega)
    have hbpos : (0 : ℝ) < bb := by linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (bb : ℝ) ^ (J + i + 1))]
    refine this.trans (le_of_eq ?_)
    rw [one_div_pow, ← hP, ← hC]
    field_simp
    push_cast
    ring
  have hbound := hasSum_farBound hbr C J
  have hbound_sum : HasSum (fun i : ℕ => P.card * ((C + 2 * ((J : ℝ) + i + 1))
      * (1 / (bb : ℝ)) ^ (J + i + 1)) / Real.log 2)
      (P.card * farBound bb J C / Real.log 2) :=
    (hbound.mul_left (P.card : ℝ)).div_const (Real.log 2)
  calc ∑ n ∈ P, |farPartW (TWeight.subset S) bb G n a|
      ≤ ∑ n ∈ P, ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * ∑' i, f α n i :=
        Finset.sum_le_sum hpt
    _ = ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)| * ∑' i, ∑ n ∈ P, f α n i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← Finset.mul_sum, Summable.tsum_finsetSum (hfs α)]
    _ ≤ ∑ α : G.Atom, |((kronPow G.K (diffZ G.s) a α : ℤ) : ℝ)|
          * (P.card * farBound bb J C / Real.log 2) := by
        refine Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [← hbound_sum.tsum_eq]
        refine Summable.tsum_le_tsum (hlayer α) ?_ hbound_sum.summable
        exact summable_sum fun n hn => hfs α n hn
    _ = _ := by
        rw [← Finset.sum_mul, sum_abs_kronPow_diffZ]
        ring

/-- **`farAvgS` in closed form**: the same bound as `farAvg_le`. -/
theorem farAvgS_leS (bb : ℕ) (hbb : 2 ≤ bb) (G : GridParams) (X : ℕ)
    (hne : (apSample X G.P₀ G.b₀).Nonempty) {Dm : ℕ} (hDm : ∀ α, G.d α ≤ Dm) :
    farAvgS S bb G X ≤ (2 : ℝ) ^ G.K / Real.log 2 * farBound bb (G.K + G.N) (farCS S G X Dm) := by
  have hbr : (2 : ℝ) ≤ bb := by exact_mod_cast hbb
  set P := apSample X G.P₀ G.b₀ with hP
  set Bd : ℝ := (2 : ℝ) ^ G.K / Real.log 2 * farBound bb (G.K + G.N) (farCS S G X Dm) with hBd
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC := farCS_nonneg S G X hne Dm
  have hBd0 : 0 ≤ Bd := by
    rw [hBd]
    have h1 : 0 ≤ (2 : ℝ) ^ G.K / Real.log 2 := by positivity
    have h2 := farBound_nonneg hbr (G.K + G.N) hC
    positivity
  have hrow : ∀ ν : Fin G.rDim,
      (P.card : ℝ)⁻¹ * ∑ n ∈ P, |farPartW (TWeight.subset S) bb G n (G.rowEquiv.symm ν)|
        ≤ Bd := by
    intro ν
    have hc : (0 : ℝ) < P.card := by exact_mod_cast hne.card_pos
    have := sum_abs_farPartW_subset_leS S bb hbb G X hne hDm (G.rowEquiv.symm ν)
    rw [← hP] at this
    calc (P.card : ℝ)⁻¹ * ∑ n ∈ P, |farPartW (TWeight.subset S) bb G n (G.rowEquiv.symm ν)|
        ≤ (P.card : ℝ)⁻¹ * (P.card * Bd) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = Bd := by field_simp
  unfold farAvgS
  rw [← hP]
  have hswap : (P.card : ℝ)⁻¹ * ∑ n ∈ P, (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim,
        |farPartW (TWeight.subset S) bb G n (G.rowEquiv.symm ν)|
      = (G.rDim : ℝ)⁻¹ * ∑ ν : Fin G.rDim, (P.card : ℝ)⁻¹ * ∑ n ∈ P,
        |farPartW (TWeight.subset S) bb G n (G.rowEquiv.symm ν)| := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hswap]
  have hr : ((Finset.univ : Finset (Fin G.rDim)).card : ℝ) = G.rDim := by simp
  rw [← hr]
  exact avg_le_of_forall_le _ _ hBd0 fun ν _ => hrow ν

end NormalNumbers.G4
