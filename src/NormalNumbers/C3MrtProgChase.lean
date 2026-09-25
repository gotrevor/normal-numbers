/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtProgInner

/-!
# The `ε`-chase and the uniform rung along an extra progression — brick 4a of obligation A

`multi_correlation_of_uniform_rung` and `rung_multi_uniform` (laps 49, 52), transcribed with
`progLcm Mo d` in place of `Finset.univ.lcm d`.

The only arithmetic that changes is the base-point bound: `univLcm_le_pow` gave `lcm d ≤ Y^K`,
and now `progLcm Mo d ≤ Mo · Y^K` (`progLcm_le_mul_pow`), so the threshold
`N₀ = Y^K·A^I + Y^K + 2` becomes `Mo·Y^K·A^I + Mo·Y^K + 2`.  `Mo` is quantified before `N`, so
nothing else moves — in particular the budget `K^{K²}` and the truncation are untouched.

Output: `progression_log_rung_class`, the log-averaged `K`-point correlation bound over the class
of `r` mod `Mo`, on `KPointLogElliott K` + `TwistedPrimeSumSavingAllLevels` alone.  Brick 4b is the
weight bridge from this class-indexed form to the progression-variable form that
`ProgressionLogRung` states.
-/

open Filter Finset

namespace NormalNumbers

namespace CastingOut

/-- `lcm(Mo, lcm d) ≤ Mo · Y^K` for a tuple with all entries positive and `≤ Y`. -/
theorem progLcm_le_mul_pow {K Y Mo : ℕ} (hMo : 0 < Mo) (d : Fin K → ℕ) (hd : ∀ i, 0 < d i)
    (hdY : ∀ i, d i ≤ Y) : progLcm Mo d ≤ Mo * Y ^ K := by
  have hdvd : progLcm Mo d ∣ Mo * (Finset.univ : Finset (Fin K)).lcm d :=
    Nat.lcm_dvd (Dvd.intro _ rfl) (Dvd.intro_left _ rfl)
  have hpos : 0 < Mo * (Finset.univ : Finset (Fin K)).lcm d :=
    Nat.mul_pos hMo (univLcm_pos d hd)
  exact le_trans (Nat.le_of_dvd hpos hdvd)
    (Nat.mul_le_mul_left Mo (univLcm_le_pow d hd hdY))

open scoped Classical in
/-- **The `K`-fold `ε`-chase along a progression.**  `multi_correlation_of_uniform_rung` over the
class of `r` mod `Mo`. -/
theorem multi_correlation_of_uniform_rung_prog {K : ℕ} (hK : 0 < K) {Mo : ℕ} (hMo : 0 < Mo)
    (r : ℕ) (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (hrungU : ∀ εr : ℝ, 0 < εr → ∀ Y : ℕ, ∃ A : ℕ, 2 ≤ A ∧ ∃ I : ℕ,
      ∀ d : Fin K → ℕ, (∀ i, d i ≤ Y) → (∀ i, 0 < d i) →
        (∃ n : ℕ, ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1) →
        ∀ a : ℕ, a < progLcm Mo d →
          (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) → ∀ m : ℕ, I ≤ m →
          ‖∑ j ∈ Finset.Ioc 0 (A ^ m), (Erdos67b.harmonicWeight j : ℂ) *
              ∏ i : Fin K, zOmInt (z i)
                (Erdos67b.integerAffine (progLcm Mo d / d i)
                  (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ) j)‖
            ≤ (1 + Real.log ((A ^ I : ℕ) : ℝ)) + (m : ℝ) * (εr * Real.log A))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖∑ n ∈ (range N).filter (fun n => n ≡ r [MOD Mo]),
          harmW n * ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1)‖
        ≤ C + ε * Real.log N := by
  classical
  have hKpow : (0 : ℝ) ≤ (K : ℝ) ^ (K * K) := by positivity
  have hMass : (0 : ℝ) ≤ ∏ i : Fin K, sqfWMass (z i) :=
    Finset.prod_nonneg fun i _ => sqfWMass_nonneg (z i)
  set M : ℝ := (K : ℝ) ^ (K * K) * ∏ i : Fin K, sqfWMass (z i) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨εr, hεr0, hεrM⟩ : ∃ s : ℝ, 0 < s ∧ s * M ≤ ε / 2 := by
    refine ⟨ε / (2 * (M + 1)), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hε.le, hM0]
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, (K : ℝ) ^ (K * K) * truncB z Y K ≤ ε / 2 := by
    have t : Filter.Tendsto (fun Y : ℕ => (K : ℝ) ^ (K * K) * truncB z Y K)
        Filter.atTop (nhds 0) := by
      simpa using (truncB_tendsto z K).const_mul ((K : ℝ) ^ (K * K))
    obtain ⟨Y, hy⟩ := (t.eventually_lt_const (by positivity : (0 : ℝ) < ε / 2)).exists
    exact ⟨Y, hy.le⟩
  obtain ⟨A, hA2, I, hrU⟩ := hrungU εr hεr0 Y
  have hlogA : 0 ≤ Real.log A := Real.log_natCast_nonneg A
  have hlogAI : 0 ≤ Real.log ((A ^ I : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_pow _ _ (by omega)
  refine ⟨(K : ℝ) * truncA z Y K + ε / 2 + (∏ i : Fin K, sqfWPartial (z i) Y)
      + (3 + (1 + Real.log ((A ^ I : ℕ) : ℝ)) + Real.log A) * M,
    Mo * Y ^ K * A ^ I + Mo * Y ^ K + 2, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg hNR
  set R : ℝ := (1 + Real.log ((A ^ I : ℕ) : ℝ)) + εr * Real.log N with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hrung : ∀ d : Fin K → ℕ, (∀ i, d i ≤ Y) → (∀ i, 0 < d i) →
      (∃ n : ℕ, ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1) →
      ∀ a : ℕ, a < progLcm Mo d → (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) →
        ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A ((N - 1 - a) / progLcm Mo d)),
            (Erdos67b.harmonicWeight j : ℂ) *
              ∏ i : Fin K, zOmInt (z i)
                (Erdos67b.integerAffine (progLcm Mo d / d i)
                  (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ) j)‖ ≤ R := by
    intro d hdY hdpos hsolv a ha hadvd
    set L : ℕ := progLcm Mo d with hLdef
    have hL : 0 < L := progLcm_pos hMo d hdpos
    have hLY : L ≤ Mo * Y ^ K := progLcm_le_mul_pow hMo d hdpos hdY
    have haY : a < Mo * Y ^ K := lt_of_lt_of_le ha hLY
    set J : ℕ := (N - 1 - a) / L with hJdef
    have hJge : A ^ I ≤ J := by
      rw [hJdef, Nat.le_div_iff_mul_le hL]
      have h1 : A ^ I * L ≤ Mo * Y ^ K * A ^ I := by
        rw [mul_comm]; exact Nat.mul_le_mul_right _ hLY
      omega
    have hJpos : 0 < J := lt_of_lt_of_le (Nat.one_le_pow _ _ (by omega)) hJge
    set m : ℕ := Nat.log A J with hmdef
    have hmI : I ≤ m := by
      rw [hmdef]
      calc I = Nat.log A (A ^ I) := (Nat.log_pow (by omega) I).symm
        _ ≤ Nat.log A J := Nat.log_mono_right hJge
    refine le_trans (hrU d hdY hdpos hsolv a ha hadvd m hmI) ?_
    have hAmJ : A ^ m ≤ J := Nat.pow_log_le_self A (by omega)
    have hJN : J ≤ N := le_trans (Nat.div_le_self _ _) (by omega)
    have hcast : ((A : ℝ)) ^ m ≤ (N : ℝ) := by exact_mod_cast le_trans hAmJ hJN
    have hlogpow : (m : ℝ) * Real.log A ≤ Real.log N := by
      have := Real.log_le_log (by positivity) hcast
      rwa [Real.log_pow] at this
    have hfin : (m : ℝ) * (εr * Real.log A) ≤ εr * Real.log N := by
      have h := mul_le_mul_of_nonneg_left hlogpow hεr0.le
      calc (m : ℝ) * (εr * Real.log A) = εr * ((m : ℝ) * Real.log A) := by ring
        _ ≤ εr * Real.log N := h
    rw [hRdef]
    linarith
  have hmain := multi_bound_of_rung_prog hK hMo r z hz Y N A hA2 hR0 hrung
  refine le_trans hmain ?_
  have hTB : 0 ≤ truncB z Y K := truncB_nonneg z Y K
  have h1 : ((1 + Real.log N) * (K : ℝ) ^ (K * K)) * truncB z Y K
      ≤ (1 + Real.log N) * (ε / 2) := by
    have := mul_le_mul_of_nonneg_left hY (by linarith : (0 : ℝ) ≤ 1 + Real.log N)
    calc ((1 + Real.log N) * (K : ℝ) ^ (K * K)) * truncB z Y K
        = (1 + Real.log N) * ((K : ℝ) ^ (K * K) * truncB z Y K) := by ring
      _ ≤ (1 + Real.log N) * (ε / 2) := this
  have h2 : (3 + R + Real.log A) * M
      ≤ (3 + (1 + Real.log ((A ^ I : ℕ) : ℝ)) + Real.log A) * M + (ε / 2) * Real.log N := by
    have hstep : (3 + R + Real.log A) * M
        = (3 + (1 + Real.log ((A ^ I : ℕ) : ℝ)) + Real.log A) * M
          + (εr * M) * Real.log N := by rw [hRdef]; ring
    have hlast : (εr * M) * Real.log N ≤ (ε / 2) * Real.log N :=
      mul_le_mul_of_nonneg_right hεrM hL0
    linarith
  rw [hM] at h2 ⊢
  linarith

open scoped Classical in
/-- **The `K`-point rung, uniformly over the progression-admissible tuples below `Y`.**
`rung_multi_uniform` (lap 52) with `progLcm Mo d` in place of `Finset.univ.lcm d`; the base point
is bounded by `Mo · Y^K` (`progLcm_le_mul_pow`) instead of `Y^K`. -/
theorem rung_multi_uniform_prog {K : ℕ} (hK : 0 < K) {Mo : ℕ} (hMo : 0 < Mo)
    (helliott : KPointLogElliott K) (hsave : TwistedPrimeSumSavingAllLevels)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (hz01 : z 0 ≠ 1)
    (εr : ℝ) (hεr : 0 < εr) (Y : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∃ I : ℕ,
      ∀ d : Fin K → ℕ, (∀ i, d i ≤ Y) → (∀ i, 0 < d i) →
        (∃ n : ℕ, ∀ i : Fin K, d i ∣ n + (i : ℕ) + 1) →
        ∀ a : ℕ, a < progLcm Mo d →
          (∀ i : Fin K, d i ∣ a + (i : ℕ) + 1) → ∀ m : ℕ, I ≤ m →
          ‖∑ j ∈ Finset.Ioc 0 (A ^ m), (Erdos67b.harmonicWeight j : ℂ) *
              ∏ i : Fin K, zOmInt (z i)
                (Erdos67b.integerAffine (progLcm Mo d / d i)
                  (((a + (i : ℕ) + 1) / d i : ℕ) : ℤ) j)‖
            ≤ (1 + Real.log ((A ^ I : ℕ) : ℝ)) + (m : ℝ) * (εr * Real.log A) := by
  classical
  set s : Finset ((Fin K → ℕ) × ℕ) :=
    (Fintype.piFinset fun _ : Fin K => Finset.range (Y + 1)) ×ˢ
      Finset.range (Mo * Y ^ K + 1) with hs
  have hmem : ∀ (d : Fin K → ℕ) (a : ℕ), (∀ i, d i ≤ Y) → (∀ i, 0 < d i) →
      a < progLcm Mo d → ((d, a) : (Fin K → ℕ) × ℕ) ∈ s := by
    intro d a hdY hdpos ha
    have hle : progLcm Mo d ≤ Mo * Y ^ K := progLcm_le_mul_pow hMo d hdpos hdY
    simp only [hs, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨fun i => Nat.lt_succ_of_le (hdY i), by omega⟩
  set B : (Fin K → ℕ) × ℕ → ℕ → ℕ → ℕ → Prop := fun p A i m =>
    ‖∑ j ∈ Finset.Ioc 0 (A ^ m), (Erdos67b.harmonicWeight j : ℂ) *
        ∏ k : Fin K, zOmInt (z k)
          (Erdos67b.integerAffine (progLcm Mo p.1 / p.1 k)
            (((p.2 + (k : ℕ) + 1) / p.1 k : ℕ) : ℤ) j)‖
      ≤ (1 + Real.log ((A ^ i : ℕ) : ℝ)) + (m : ℝ) * (εr * Real.log A) with hB
  have hBmono : ∀ (p : (Fin K → ℕ) × ℕ) (A i i' m : ℕ), 1 ≤ A → i ≤ i' →
      B p A i m → B p A i' m := by
    intro p A i i' m hA1 hii h
    have : Real.log ((A ^ i : ℕ) : ℝ) ≤ Real.log ((A ^ i' : ℕ) : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (by positivity))
      exact_mod_cast Nat.pow_le_pow_right hA1 hii
    rw [hB] at h ⊢
    linarith
  obtain ⟨A₁, hA₁⟩ := exists_common_threshold s
    (fun p A₀ => 2 ≤ A₀ ∧ ((∀ i, 0 < p.1 i) → (∀ i : Fin K, p.1 i ∣ p.2 + (i : ℕ) + 1) →
      ∀ A : ℕ, A₀ ≤ A → ∃ i₀ : ℕ, ∀ m : ℕ, i₀ ≤ m → B p A i₀ m))
    (by
      intro p _ m n hmn hm
      exact ⟨le_trans hm.1 hmn, fun h1 h2 A hA => hm.2 h1 h2 A (le_trans hmn hA)⟩)
    (by
      intro p _
      by_cases h1 : ∀ i, 0 < p.1 i
      · by_cases h2 : ∀ i : Fin K, p.1 i ∣ p.2 + (i : ℕ) + 1
        · obtain ⟨A₀, hA₀2, hA₀⟩ := rung_multi_of_named_inputs hK helliott hsave z hz hz01
            (fun i => progLcm Mo p.1 / p.1 i)
            (fun i => ((p.2 + (i : ℕ) + 1) / p.1 i : ℕ))
            (nondegenerateForms_prog hMo p.1 h1 h2) εr hεr
          exact ⟨A₀, hA₀2, fun _ _ A hA => hA₀ A hA⟩
        · exact ⟨2, le_rfl, fun _ h => absurd h h2⟩
      · exact ⟨2, le_rfl, fun h _ => absurd h h1⟩)
  set A : ℕ := max 2 A₁ with hAdef
  have hA2 : 2 ≤ A := le_max_left _ _
  have hA1A : A₁ ≤ A := le_max_right _ _
  have hA1 : 1 ≤ A := by omega
  obtain ⟨I, hI⟩ := exists_common_threshold s
    (fun p i => (∀ j, 0 < p.1 j) → (∀ j : Fin K, p.1 j ∣ p.2 + (j : ℕ) + 1) →
      ∀ m : ℕ, i ≤ m → B p A i m)
    (by
      intro p _ i i' hii hi h1 h2 m hm
      exact hBmono p A i i' m hA1 hii (hi h1 h2 m (le_trans hii hm)))
    (by
      intro p hp
      by_cases h1 : ∀ j, 0 < p.1 j
      · by_cases h2 : ∀ j : Fin K, p.1 j ∣ p.2 + (j : ℕ) + 1
        · obtain ⟨i₀, hi₀⟩ := (hA₁ p hp).2 h1 h2 A hA1A
          exact ⟨i₀, fun _ _ m hm => hi₀ m hm⟩
        · exact ⟨0, fun _ h => absurd h h2⟩
      · exact ⟨0, fun h => absurd h h1⟩)
  refine ⟨A, hA2, I, fun d hdY hdpos _ a ha hadvd m hm => ?_⟩
  exact hI (d, a) (hmem d a hdY hdpos ha) hdpos hadvd m hm

/-- **The log-averaged `K`-point correlation over a residue class** — obligation A in
class-indexed form, on `KPointLogElliott K` + `TwistedPrimeSumSavingAllLevels` alone. -/
theorem progression_log_rung_class {K : ℕ} (hK : 0 < K) {Mo : ℕ} (hMo : 0 < Mo) (r : ℕ)
    (helliott : KPointLogElliott K) (hsave : TwistedPrimeSumSavingAllLevels)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (hz01 : z 0 ≠ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖∑ n ∈ (range N).filter (fun n => n ≡ r [MOD Mo]),
          harmW n * ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1)‖
        ≤ C + ε * Real.log N :=
  multi_correlation_of_uniform_rung_prog hK hMo r z hz
    (fun εr hεr Y => rung_multi_uniform_prog hK hMo helliott hsave z hz hz01 εr hεr Y) ε hε

#print axioms progLcm_le_mul_pow
#print axioms multi_correlation_of_uniform_rung_prog
#print axioms rung_multi_uniform_prog
#print axioms progression_log_rung_class

end CastingOut

end NormalNumbers
