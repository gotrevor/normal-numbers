/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-R: `GoodDenBoundPrim` is FALSE without normality — the constant-digit witness

Laps 31–39 reduced the crux's tail cell to `GoodDenBoundPrim y D`:
`#{q ≤ Q : ‖qy‖ ≤ 2/(Tq), gcd = 1} ≤ (D/T) log Q`, and lap 39 showed the count is *equal*
(up to `T ↦ (T−4)/2` and an additive `3`) to the count of large digits of `y`.

This module produces the kernel witness that settles what is left: the hypothesis is **not an
unconditional Diophantine fact**.  Let

    ζ_T := (√(T² + 4) − T)/2 ,

the fixed point of the Gauss map with `ζ⁻¹ = T + ζ`, i.e. the quadratic irrational
`[0; T, T, T, …]`.  *Every* one of its convergent denominators is a primitive `T`-good
denominator (`nearInt_convDen_le` at a digit exactly `T`), and `qₚ ≤ (T+1)ᵖ`, so

    goodDenCountPrim ζ_T T ((T+1)^P) ≥ P − 2 ≈ log Q / log(T+1),

which beats `(D/T) log Q` as soon as `D log(T+1) < T`.  So `GoodDenBoundPrim` fails for `ζ_T`.

**What this decides.**  `goodDenCountPrim_le_log` (lap 34) gives `≤ 1 + log Q/log(T/4)` for every
irrational, and `ζ_T` shows that free rate is **attained**: spacing arguments are exactly sharp
and cannot be improved by any amount of Diophantine bookkeeping.  Combined with lap 39's
equivalence, `GoodDenBoundPrim (φx) D` is neither weaker nor differently-shaped than the crux —
it is the Gauss–Kuzmin tail law for the image, and it can only be proved from statistics of the
image, never from the arithmetic of `Φ` alone.  This closes the Diophantine detour as a detour.
-/
import NormalNumbers.VandeheyS7Legendre

namespace NormalNumbers.VandeheyS7

open NormalNumbers Filter

/-- `ζ_T = [0; T, T, T, …]`, the fixed point of the Gauss map with digit `T`. -/
noncomputable def constCF (T : ℕ) : ℝ := (Real.sqrt ((T:ℝ)^2 + 4) - T) / 2

section
variable {T : ℕ}

lemma sq_sqrt_constCF (T : ℕ) : Real.sqrt ((T:ℝ)^2 + 4) ^ 2 = (T:ℝ)^2 + 4 :=
  Real.sq_sqrt (by positivity)

lemma lt_sqrt_constCF (T : ℕ) : (T:ℝ) < Real.sqrt ((T:ℝ)^2 + 4) := by
  nlinarith [sq_sqrt_constCF T, Real.sqrt_nonneg ((T:ℝ)^2 + 4), Nat.cast_nonneg (α := ℝ) T]

lemma sqrt_constCF_lt (hT : 1 ≤ T) : Real.sqrt ((T:ℝ)^2 + 4) < (T:ℝ) + 2 := by
  have h1 : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  nlinarith [sq_sqrt_constCF T, Real.sqrt_nonneg ((T:ℝ)^2 + 4)]

lemma constCF_mem (hT : 1 ≤ T) : constCF T ∈ Set.Ioo (0:ℝ) 1 := by
  constructor
  · have := lt_sqrt_constCF T; rw [constCF]; linarith
  · have := sqrt_constCF_lt hT; rw [constCF]; linarith

/-- The defining quadratic: `ζ (T + ζ) = 1`. -/
lemma constCF_mul (T : ℕ) : constCF T * ((T:ℝ) + constCF T) = 1 := by
  have hs := sq_sqrt_constCF T
  rw [constCF]; nlinarith [hs]

lemma constCF_inv (hT : 1 ≤ T) : (constCF T)⁻¹ = (T:ℝ) + constCF T := by
  have h0 : constCF T ≠ 0 := (constCF_mem hT).1.ne'
  field_simp
  linarith [constCF_mul T]

/-- The Gauss map fixes `ζ_T`. -/
lemma gaussMap_constCF (hT : 1 ≤ T) : gaussMap (constCF T) = constCF T := by
  have hmem := constCF_mem hT
  rw [gaussMap, if_neg hmem.1.ne', constCF_inv hT]
  rw [show ((T:ℝ) + constCF T) = constCF T + ((T:ℕ):ℝ) by ring]
  rw [Int.fract_add_natCast, Int.fract_eq_self.2 ⟨hmem.1.le, hmem.2⟩]

/-- Every digit of `ζ_T` is `T`. -/
lemma cfDigit_constCF (hT : 1 ≤ T) : ∀ i : ℕ, cfDigit (constCF T) i = T := by
  intro i
  induction i with
  | zero =>
      have hmem := constCF_mem hT
      refine (cfDigit_zero_eq_iff hmem hT).2 ⟨?_, ?_⟩
      · rw [div_lt_iff₀ (by positivity)]
        nlinarith [constCF_mul T, hmem.1, hmem.2]
      · rw [le_div_iff₀ (by exact_mod_cast hT : (0:ℝ) < (T:ℝ))]
        nlinarith [constCF_mul T, hmem.1, hmem.2]
  | succ i ih => rw [cfDigit_succ, gaussMap_constCF hT]; exact ih

lemma digitWord_constCF (hT : 1 ≤ T) (p : ℕ) :
    digitWord (constCF T) p = List.replicate p T := by
  rw [digitWord]
  rw [List.eq_replicate_iff]
  refine ⟨by simp, ?_⟩
  intro b hb
  simp only [List.mem_map, List.mem_range] at hb
  obtain ⟨i, -, rfl⟩ := hb
  exact cfDigit_constCF hT i

lemma irrational_constCF (hT : 1 ≤ T) : Irrational (constCF T) := by
  have hnsq : ¬ IsSquare ((T:ℕ)^2 + 4) := by
    rintro ⟨r, hr⟩
    have hrT : T < r := by nlinarith
    have h2 : (T + 1) * (T + 1) ≤ r * r := Nat.mul_le_mul hrT hrT
    have hTe : T = 1 := by nlinarith
    subst hTe
    have hr2 : 2 ≤ r := by omega
    have hr3 : r ≤ 2 := by nlinarith
    interval_cases r
    norm_num at hr
  have hirr : Irrational (Real.sqrt (((T^2 + 4 : ℕ) : ℝ))) :=
    irrational_sqrt_natCast_iff.2 hnsq
  have hcast : ((T^2 + 4 : ℕ) : ℝ) = (T:ℝ)^2 + 4 := by push_cast; ring
  rw [hcast] at hirr
  have h2 := (hirr.sub_natCast T).div_natCast (m := 2) (by norm_num)
  rw [constCF]
  simpa using h2

/-- `qₚ(ζ_T) ≤ (T+1)^p`. -/
lemma cfK_constCF_le (hT : 1 ≤ T) (p : ℕ) :
    cfK (digitWord (constCF T) p) ≤ (T + 1) ^ p := by
  have h := cfK_le_prod (digitWord (constCF T) p)
  rw [digitWord_constCF hT p] at h ⊢
  simpa [List.map_replicate, List.prod_replicate] using h

/-- **Every convergent denominator of `ζ_T` is a primitive `T`-good denominator.** -/
lemma good_cfK_constCF (hT : 1 ≤ T) {p : ℕ} (hp : 3 ≤ p) :
    nearInt ((cfK (digitWord (constCF T) p) : ℝ) * constCF T)
        ≤ 2 / ((T : ℝ) * (cfK (digitWord (constCF T) p) : ℝ)) ∧
      Nat.Coprime (round ((cfK (digitWord (constCF T) p) : ℝ) * constCF T)).natAbs
        (cfK (digitWord (constCF T) p)) := by
  have hirr := irrational_constCF hT
  have hmem := constCF_mem hT
  refine ⟨nearInt_convDen_le hirr hmem hT (by omega) (le_of_eq (cfDigit_constCF hT p).symm), ?_⟩
  rw [round_eq_cfNum hirr hmem hp]
  simpa using coprime_cfNum_cfK (digitWord_ne_nil (by omega : 0 < p))

/-- **The lower bound on the count.**  `goodDenCountPrim ζ_T T ((T+1)^P) ≥ P − 2`. -/
theorem goodDenCountPrim_constCF_ge (hT : 1 ≤ T) {P : ℕ} (hP : 3 ≤ P) :
    P - 2 ≤ goodDenCountPrim (constCF T) T ((T + 1) ^ P) := by
  classical
  have hirr := irrational_constCF hT
  have hmem := constCF_mem hT
  set y := constCF T with hy
  set S : Finset ℕ := (Finset.Icc 3 P) with hS
  have hmaps : ∀ p ∈ S, cfK (digitWord y p) ∈ (Finset.Icc 1 ((T + 1) ^ P)).filter
      (fun q : ℕ => nearInt ((q : ℝ) * y) ≤ 2 / ((T : ℝ) * q) ∧
        Nat.Coprime (round ((q : ℝ) * y)).natAbs q) := by
    intro p hp
    obtain ⟨hp3, hpP⟩ := Finset.mem_Icc.1 hp
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨one_le_cfK _ (digitWord_pos hirr hmem p), ?_⟩,
      good_cfK_constCF hT hp3⟩
    exact le_trans (cfK_constCF_le hT p) (Nat.pow_le_pow_right (by omega) hpP)
  have hinj : Set.InjOn (fun p => cfK (digitWord y p)) (S : Set ℕ) := by
    intro a ha b hb hab
    obtain ⟨ha3, -⟩ := Finset.mem_Icc.1 (Finset.mem_coe.1 ha)
    obtain ⟨hb3, -⟩ := Finset.mem_Icc.1 (Finset.mem_coe.1 hb)
    by_contra hne
    rcases Nat.lt_or_ge a b with h | h
    · exact absurd hab (cfK_digitWord_lt hirr hmem (by omega) h).ne
    · have : b < a := by omega
      exact absurd hab.symm (cfK_digitWord_lt hirr hmem (by omega) this).ne
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simpa [goodDenCountPrim, hS, Nat.card_Icc] using this

/-- **The refutation.**  `GoodDenBoundPrim ζ_T D` is false whenever `D log(T+1) < T`; in
particular for every fixed `D` once `T` is large.  So the Diophantine hypothesis is not an
unconditional fact about irrationals, and the free rate `log Q / log T` is attained. -/
theorem not_goodDenBoundPrim_constCF (hT : 1 ≤ T) {D : ℝ}
    (hD : D * Real.log ((T:ℝ) + 1) < (T:ℝ)) : ¬ GoodDenBoundPrim (constCF T) D := by
  intro hgd
  have hTR : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  have hTpos : (0:ℝ) < (T:ℝ) := by linarith
  have hlogpos : (0:ℝ) < Real.log ((T:ℝ) + 1) := Real.log_pos (by linarith)
  -- the eventual bound holds along `Q = (T+1)^P`
  have hev := hgd T hT
  have htend : Tendsto (fun P : ℕ => (T + 1) ^ P) atTop atTop :=
    tendsto_atTop_mono (fun P => (Nat.lt_pow_self (by omega : 1 < T + 1)).le) tendsto_id
  have hcomp := htend.eventually hev
  -- choose `P` large
  obtain ⟨N, hN⟩ := (hcomp.and (eventually_ge_atTop 3)).exists_forall_of_atTop
  set c : ℝ := D * Real.log ((T:ℝ) + 1) / T with hc
  have hc1 : c < 1 := by rw [hc, div_lt_one hTpos]; exact hD
  obtain ⟨P, hP3, hPbig, hPN⟩ : ∃ P : ℕ, 3 ≤ P ∧ (2:ℝ) < (1 - c) * P ∧ N ≤ P := by
    obtain ⟨P, hP⟩ := exists_nat_gt (max ((2:ℝ) / (1 - c)) (max 3 N))
    refine ⟨P, ?_, ?_, ?_⟩
    · have : ((3:ℕ):ℝ) ≤ (P:ℝ) := le_of_lt (lt_of_le_of_lt (le_trans (le_max_left _ _)
        (le_max_right _ _)) hP)
      exact_mod_cast this
    · have h2 : (2:ℝ) / (1 - c) < P := lt_of_le_of_lt (le_max_left _ _) hP
      rw [div_lt_iff₀ (by linarith)] at h2
      linarith
    · have : ((N:ℕ):ℝ) ≤ (P:ℝ) := le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _)
        (le_max_right _ _)) hP)
      exact_mod_cast this
  have hbound := (hN P hPN).1
  have hlow := goodDenCountPrim_constCF_ge (T := T) hT hP3
  have hlowR : ((P:ℝ) - 2) ≤ (goodDenCountPrim (constCF T) T ((T + 1) ^ P) : ℝ) := by
    have : ((P - 2 : ℕ) : ℝ) ≤ (goodDenCountPrim (constCF T) T ((T + 1) ^ P) : ℝ) := by
      exact_mod_cast hlow
    have hcast : ((P - 2 : ℕ) : ℝ) = (P:ℝ) - 2 := by
      have h2 : (2:ℕ) ≤ P := by omega
      rw [Nat.cast_sub h2]; norm_num
    linarith [hcast ▸ this]
  have hlogQ : Real.log (((T + 1) ^ P : ℕ) : ℝ) = P * Real.log ((T:ℝ) + 1) := by
    push_cast
    rw [Real.log_pow]
  rw [hlogQ] at hbound
  have : (P:ℝ) - 2 ≤ c * P := by
    refine le_trans hlowR (le_trans hbound (le_of_eq ?_))
    rw [hc]; field_simp
  linarith
end

section Audit

#print axioms goodDenCountPrim_constCF_ge
#print axioms not_goodDenBoundPrim_constCF

end Audit

end NormalNumbers.VandeheyS7
