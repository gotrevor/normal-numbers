/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SqrtTwoRoutes.Balanced
import NormalNumbers.Disjunctive

/-!
# Integer Pell certificates for binary words of sqrt(2)

The certificate records a bounded adjacent-Pell synthesis of a dyadic
denominator together with the strict integer inequalities locating one orbit
point in a prescribed binary cylinder.  The uniform supply statement remains
an open target.
-/

namespace NormalNumbers.SqrtTwoRoutes

open Set NormalNumbers

def pellWordNumerator (n : ℕ) (u v : ℤ) : ℤ :=
  u * pellP n + v * pellP (n + 1)

/-- A finite integer witness that the `m`-th orbit point lies strictly inside
the binary cylinder indexed by `A` at word length `L`. -/
@[blueprint (title := "An integer Pell certificate for a binary word")]
def PellWordCertificate (L A m n : ℕ) (u v : ℤ) : Prop :=
  let Q : ℤ := (2 : ℤ) ^ m
  let S : ℤ := (2 : ℤ) ^ L
  let P : ℤ := pellWordNumerator n u v
  1 ≤ n ∧
    pellQ n ^ 2 ≤ Q ∧ Q < pellQ (n + 1) ^ 2 ∧
    u * pellQ n + v * pellQ (n + 1) = Q ∧
    u ^ 2 ≤ 16 * Q ∧ v ^ 2 ≤ 16 * Q ∧
    0 ≤ P ∧
    (S * P + A) ^ 2 < 2 * (S * Q) ^ 2 ∧
      2 * (S * Q) ^ 2 < (S * P + A + 1) ^ 2

/-- The certificate inequalities place the exact orbit point strictly inside
the requested binary cylinder. -/
theorem pellWordCertificate_orbit_mem_Ioo {L A m n : ℕ} {u v : ℤ}
    (hcert : PellWordCertificate L A m n u v) (hA : A < 2 ^ L) :
    orbit 2 (Real.sqrt 2) m ∈
      Set.Ioo ((A : ℝ) / (2 : ℝ) ^ L) (((A : ℝ) + 1) / (2 : ℝ) ^ L) := by
  dsimp [PellWordCertificate] at hcert
  rcases hcert with ⟨hn, hqlo, hqhi, hden, hu, hv, hPnonneg, hslo, hshi⟩
  let Q : ℤ := (2 : ℤ) ^ m
  let S : ℤ := (2 : ℤ) ^ L
  let P : ℤ := pellWordNumerator n u v
  let B : ℤ := S * P + A
  have hB : B = S * P + (A : ℤ) := rfl
  have hQeq : (Q : ℝ) = (2 : ℝ) ^ m := by dsimp [Q]; norm_cast
  have hSeq : (S : ℝ) = (2 : ℝ) ^ L := by dsimp [S]; norm_cast
  have hSpos : 0 < (S : ℝ) := by rw [hSeq]; positivity
  have hQpos : 0 < (Q : ℝ) := by rw [hQeq]; positivity
  have hAcast : 0 ≤ (A : ℝ) := by positivity
  have hAhi : (A : ℝ) + 1 ≤ (S : ℝ) := by
    rw [hSeq]
    exact_mod_cast Nat.succ_le_of_lt hA
  have hPcast : 0 ≤ (P : ℝ) := by exact_mod_cast hPnonneg
  have hBcast : (B : ℝ) = (S : ℝ) * (P : ℝ) + A := by
    dsimp [B]
    push_cast
    ring
  have hB1cast : ((B + 1 : ℤ) : ℝ) =
      (S : ℝ) * (P : ℝ) + (A : ℝ) + 1 := by
    rw [Int.cast_add, hBcast]
    push_cast
    ring
  have hBnonneg : 0 ≤ B := by
    dsimp [B, S, P]
    positivity
  have hBpos : 0 ≤ (B : ℝ) := by exact_mod_cast hBnonneg
  have hB1pos : 0 < ((B + 1 : ℤ) : ℝ) := by
    have : 0 ≤ (B : ℝ) := hBpos
    push_cast
    linarith
  have hSQreal : ((S * Q : ℤ) : ℝ) = (S : ℝ) * (Q : ℝ) := by push_cast; rfl
  have hXpos : 0 < ((S * Q : ℤ) : ℝ) := by
    rw [hSQreal]
    exact mul_pos hSpos hQpos
  have hsq : (Real.sqrt 2 * ((S * Q : ℤ) : ℝ)) ^ 2 =
      2 * ((S * Q : ℤ) : ℝ) ^ 2 := by
    calc
      (Real.sqrt 2 * ((S * Q : ℤ) : ℝ)) ^ 2 =
          (Real.sqrt 2) ^ 2 * ((S * Q : ℤ) : ℝ) ^ 2 := by ring
      _ = 2 * ((S * Q : ℤ) : ℝ) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]
  have hcenter : 0 < Real.sqrt 2 * ((S * Q : ℤ) : ℝ) :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) hXpos
  have hsloR : (B : ℝ) ^ 2 < 2 * ((S * Q : ℤ) : ℝ) ^ 2 := by
    dsimp [B, Q, S, P] at hslo ⊢
    exact_mod_cast hslo
  have hshiR : 2 * ((S * Q : ℤ) : ℝ) ^ 2 < ((B + 1 : ℤ) : ℝ) ^ 2 := by
    dsimp [B, Q, S, P] at hshi ⊢
    exact_mod_cast hshi
  have hB_lt : (B : ℝ) < Real.sqrt 2 * ((S * Q : ℤ) : ℝ) := by
    have hsqlo : (B : ℝ) ^ 2 <
        (Real.sqrt 2 * ((S * Q : ℤ) : ℝ)) ^ 2 := by rw [hsq]; exact hsloR
    exact (sq_lt_sq₀ hBpos hcenter.le).mp hsqlo
  have hlt_B1 : Real.sqrt 2 * ((S * Q : ℤ) : ℝ) < ((B + 1 : ℤ) : ℝ) := by
    have hsqhi : (Real.sqrt 2 * ((S * Q : ℤ) : ℝ)) ^ 2 <
        ((B + 1 : ℤ) : ℝ) ^ 2 := by rw [hsq]; exact hshiR
    exact (sq_lt_sq₀ hcenter.le hB1pos.le).mp hsqhi
  have hdelta :
      (A : ℝ) / (2 : ℝ) ^ L < Real.sqrt 2 * (Q : ℝ) - (P : ℝ) ∧
        Real.sqrt 2 * (Q : ℝ) - (P : ℝ) <
          ((A : ℝ) + 1) / (2 : ℝ) ^ L := by
    have hB_lt' := hB_lt
    rw [hBcast, hSQreal, hQeq] at hB_lt'
    have hB1_lt' := hlt_B1
    rw [hB1cast, hSQreal, hQeq] at hB1_lt'
    constructor
    · rw [div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ L)]
      rw [← hSeq, hQeq]
      nlinarith [hB_lt']
    · rw [lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ L)]
      rw [← hSeq, hQeq]
      nlinarith [hB1_lt']
  have hδ0 : 0 < Real.sqrt 2 * (Q : ℝ) - (P : ℝ) := by
    have hAlo : 0 ≤ (A : ℝ) / (2 : ℝ) ^ L := by positivity
    linarith [hdelta.1]
  have hδ1 : Real.sqrt 2 * (Q : ℝ) - (P : ℝ) < 1 := by
    have hAhiR : ((A : ℝ) + 1) / (2 : ℝ) ^ L ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ L)]
      exact_mod_cast Nat.succ_le_of_lt hA
    linarith [hdelta.2, hAhiR]
  have hfract : Int.fract (Real.sqrt 2 * (2 : ℝ) ^ m - (P : ℝ)) =
      Real.sqrt 2 * (2 : ℝ) ^ m - (P : ℝ) :=
    Int.fract_eq_self.mpr ⟨by rw [hQeq] at hδ0; linarith, by rw [hQeq] at hδ1; linarith⟩
  have hfract' : Int.fract (Real.sqrt 2 * (2 : ℝ) ^ m) =
      Real.sqrt 2 * (2 : ℝ) ^ m - (P : ℝ) := by
    rw [Int.fract_sub_intCast] at hfract
    exact hfract
  have horbit : orbit 2 (Real.sqrt 2) m = Real.sqrt 2 * (Q : ℝ) - (P : ℝ) := by
    unfold orbit
    change Int.fract (Real.sqrt 2 * (2 : ℝ) ^ m) = _
    rw [hfract', hQeq]
  rw [horbit]
  exact hdelta

/-- A uniform supply of integer certificates would imply binary
disjunctivity of `sqrt 2`. -/
def PellWordCertificateSupply : Prop :=
  ∀ L A : ℕ, A < 2 ^ L → ∃ m n : ℕ, ∃ u v : ℤ,
    PellWordCertificate L A m n u v

@[blueprint (title := "Uniform Pell word certificates imply sqrt(2) disjunctivity")]
theorem pellWordCertificateSupply_implies_disjunctive
    (hsupply : PellWordCertificateSupply) :
    IsDisjunctive 2 (Real.sqrt 2) := by
  intro a c ha hac hc
  have hgap : 0 < c - a := sub_pos.mpr hac
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one
    (show 0 < (c - a) / 2 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hsmall : 2 / (2 : ℝ) ^ L < c - a := by
    have hL' : (1 / 2 : ℝ) ^ L < (c - a) / 2 := hL
    have hrewrite : (1 / 2 : ℝ) ^ L = 1 / (2 : ℝ) ^ L := by
      rw [one_div_pow]
    rw [hrewrite] at hL'
    have hpow : 0 < (2 : ℝ) ^ L := by positivity
    rw [div_lt_iff₀ hpow]
    have hmul := mul_lt_mul_of_pos_right hL' (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ L)
    have hleft : (1 / (2 : ℝ) ^ L) * (2 * (2 : ℝ) ^ L) = 2 := by
      field_simp [ne_of_gt hpow]
    have hright : ((c - a) / 2) * (2 * (2 : ℝ) ^ L) = (c - a) * (2 : ℝ) ^ L := by ring
    nlinarith [hmul]
  let S : ℝ := (2 : ℝ) ^ L
  let A : ℕ := ⌊a * S⌋₊ + 1
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hsmall' : 2 < (c - a) * S := by
    dsimp [S] at *
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ L)] at hsmall
    nlinarith
  have hfloorlo : (⌊a * S⌋₊ : ℝ) ≤ a * S := Nat.floor_le (by positivity)
  have hfloorhi : a * S < (⌊a * S⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hAlo : a < (A : ℝ) / S := by
    rw [lt_div_iff₀ hSpos]
    dsimp [A]
    push_cast
    exact hfloorhi
  have hAhi : ((A : ℝ) + 1) / S < c := by
    rw [div_lt_iff₀ hSpos]
    dsimp [A]
    push_cast
    nlinarith [hfloorlo, hsmall']
  have hAvalid : A < 2 ^ L := by
    have hAhi' : (A : ℝ) + 1 < (2 : ℝ) ^ L := by
      have hAhiMul := (div_lt_iff₀ hSpos).mp hAhi
      have hcS : c * S ≤ S := mul_le_of_le_one_left hSpos.le hc
      dsimp [S] at hAhiMul ⊢
      nlinarith [hcS]
    have hNat : A + 1 < 2 ^ L := by exact_mod_cast hAhi'
    omega
  obtain ⟨m, n, u, v, hcert⟩ := hsupply L A hAvalid
  have hcell := pellWordCertificate_orbit_mem_Ioo hcert hAvalid
  refine ⟨m, ?_⟩
  constructor
  · exact le_of_lt (lt_trans hAlo hcell.1)
  · exact lt_trans hcell.2 hAhi

/-- Disjunctivity supplies every strict integer Pell word certificate. -/
@[blueprint (title := "Sqrt(2) disjunctivity supplies bounded Pell word certificates")]
theorem pellWordCertificateSupply_of_disjunctive
    (hdisj : IsDisjunctive 2 (Real.sqrt 2)) : PellWordCertificateSupply := by
  intro L A hA
  let S : ℝ := (2 : ℝ) ^ L
  let lo : ℝ := ((A : ℝ) + 1 / 3) / S
  let hi : ℝ := ((A : ℝ) + 2 / 3) / S
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hlo_nonneg : 0 ≤ lo := by dsimp [lo]; positivity
  have hlo_lt_hi : lo < hi := by
    dsimp [lo, hi]
    apply div_lt_div_of_pos_right _ hSpos
    norm_num
  have hAplus : (A : ℝ) + 1 ≤ S := by
    dsimp [S]
    exact_mod_cast Nat.succ_le_of_lt hA
  have hhi_le_one : hi ≤ 1 := by
    dsimp [hi]
    rw [div_le_one hSpos]
    linarith
  obtain ⟨m, hm⟩ := hdisj lo hi hlo_nonneg hlo_lt_hi hhi_le_one
  let Q : ℤ := (2 : ℤ) ^ m
  let Si : ℤ := (2 : ℤ) ^ L
  let P : ℤ := ⌊Real.sqrt 2 * (Q : ℝ)⌋
  have hQreal : (Q : ℝ) = (2 : ℝ) ^ m := by dsimp [Q]; norm_cast
  have hSreal : (Si : ℝ) = S := by dsimp [Si, S]; norm_cast
  have hQpos : 0 < (Q : ℝ) := by rw [hQreal]; positivity
  have hfloorle : (P : ℝ) ≤ Real.sqrt 2 * (Q : ℝ) := by
    dsimp [P]
    exact Int.floor_le _
  have hfloorlt : Real.sqrt 2 * (Q : ℝ) < (P : ℝ) + 1 := by
    dsimp [P]
    exact Int.lt_floor_add_one _
  have hPnonneg : 0 ≤ P := Int.floor_nonneg.mpr (by positivity)
  have horbit : orbit 2 (Real.sqrt 2) m = Real.sqrt 2 * (Q : ℝ) - (P : ℝ) := by
    have harg : Real.sqrt 2 * (2 : ℝ) ^ m = Real.sqrt 2 * (Q : ℝ) := by rw [hQreal]
    unfold orbit
    change Int.fract (Real.sqrt 2 * (2 : ℝ) ^ m) = _
    rw [harg, Int.fract]
  have hloCell : (A : ℝ) / (2 : ℝ) ^ L < orbit 2 (Real.sqrt 2) m := by
    have hmlo : lo ≤ orbit 2 (Real.sqrt 2) m := hm.1
    dsimp [lo] at hmlo
    have hthird : (A : ℝ) / (2 : ℝ) ^ L <
        ((A : ℝ) + 1 / 3) / (2 : ℝ) ^ L := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      norm_num
    exact lt_of_lt_of_le hthird hmlo
  have hhiCell : orbit 2 (Real.sqrt 2) m < ((A : ℝ) + 1) / (2 : ℝ) ^ L := by
    have hmhi : orbit 2 (Real.sqrt 2) m < hi := hm.2
    dsimp [hi] at hmhi
    have hthird : ((A : ℝ) + 2 / 3) / (2 : ℝ) ^ L <
        ((A : ℝ) + 1) / (2 : ℝ) ^ L := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      norm_num
    exact lt_trans hmhi hthird
  have hnear : |(P : ℝ) - (Q : ℝ) * Real.sqrt 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [hfloorle, hfloorlt]
  have hQone : 1 ≤ Q := by
    have hpow : 0 < (2 : ℤ) ^ m := by positivity
    dsimp [Q]
    omega
  obtain ⟨n, hn, hqnle, hqnext, huBound, hvBound⟩ :=
    balanced_pell_coefficients Q P hQone hnear
  let u : ℤ := coeffU n P Q
  let v : ℤ := coeffV n P Q
  have hQroot : (Real.sqrt (Q : ℝ)) ^ 2 = (Q : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hqnonneg : 0 ≤ (pellQ n : ℝ) := by exact_mod_cast (pell_positive n).2.1
  have hqnextnonneg : 0 ≤ (pellQ (n + 1) : ℝ) := by
    exact_mod_cast (pell_positive (n + 1)).2.1
  have hqloR : (pellQ n : ℝ) ^ 2 ≤ (Q : ℝ) := by
    have h := (sq_le_sq₀ hqnonneg (Real.sqrt_nonneg _)).mpr hqnle
    rw [hQroot] at h
    exact h
  have hqhiR : (Q : ℝ) < (pellQ (n + 1) : ℝ) ^ 2 := by
    have h := (sq_lt_sq₀ (Real.sqrt_nonneg _) hqnextnonneg).mpr hqnext
    rw [hQroot] at h
    exact h
  have hqlo : pellQ n ^ 2 ≤ Q := by exact_mod_cast hqloR
  have hqhi : Q < pellQ (n + 1) ^ 2 := by exact_mod_cast hqhiR
  have hden : u * pellQ n + v * pellQ (n + 1) = Q := by
    simpa [u, v] using (pell_synthesis n P Q).2
  have hPnum : pellWordNumerator n u v = P := by
    simpa [pellWordNumerator, u, v] using (pell_synthesis n P Q).1
  have huR : (u : ℝ) ^ 2 ≤ 16 * (Q : ℝ) := by
    have habs : |(u : ℝ)| ≤ 4 * Real.sqrt (Q : ℝ) := by simpa [u] using huBound
    have hsq := (sq_le_sq₀ (abs_nonneg (u : ℝ)) (by positivity)).mpr habs
    rw [sq_abs, mul_pow, Real.sq_sqrt (by positivity)] at hsq
    nlinarith [hQroot]
  have hvR : (v : ℝ) ^ 2 ≤ 16 * (Q : ℝ) := by
    have habs : |(v : ℝ)| ≤ 4 * Real.sqrt (Q : ℝ) := by simpa [v] using hvBound
    have hsq := (sq_le_sq₀ (abs_nonneg (v : ℝ)) (by positivity)).mpr habs
    rw [sq_abs, mul_pow, Real.sq_sqrt (by positivity)] at hsq
    nlinarith [hQroot]
  have huInt : u ^ 2 ≤ 16 * Q := by exact_mod_cast huR
  have hvInt : v ^ 2 ≤ 16 * Q := by exact_mod_cast hvR
  have hcellPlo : (A : ℝ) < (Real.sqrt 2 * (Q : ℝ) - (P : ℝ)) * S := by
    rw [horbit] at hloCell
    rw [div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ L)] at hloCell
    dsimp [S]
    nlinarith [hloCell, hSreal]
  have hcellPhi : (Real.sqrt 2 * (Q : ℝ) - (P : ℝ)) * S < (A : ℝ) + 1 := by
    rw [horbit] at hhiCell
    rw [lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ L)] at hhiCell
    dsimp [S]
    nlinarith [hhiCell, hSreal]
  have hSi_nonneg : 0 ≤ Si := by dsimp [Si]; positivity
  have hBi : 0 ≤ Si * P + A := by positivity
  have hBcast : ((Si * P + A : ℤ) : ℝ) = (Si : ℝ) * (P : ℝ) + A := by
    push_cast
    ring
  have hXcast : ((Si * Q : ℤ) : ℝ) = (Si : ℝ) * (Q : ℝ) := by push_cast; rfl
  have hXpos : 0 < ((Si * Q : ℤ) : ℝ) := by
    rw [hXcast, hSreal]
    exact mul_pos (by dsimp [S]; positivity) hQpos
  have hrootXpos : 0 < Real.sqrt 2 * ((Si * Q : ℤ) : ℝ) :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) hXpos
  have hBlo : ((Si * P + A : ℤ) : ℝ) < Real.sqrt 2 * ((Si * Q : ℤ) : ℝ) := by
    rw [hBcast, hXcast, hSreal]
    linear_combination hcellPlo
  have hB1cast : ((Si * P + A + 1 : ℤ) : ℝ) =
      (Si : ℝ) * (P : ℝ) + (A : ℝ) + 1 := by push_cast; ring
  have hBhi : Real.sqrt 2 * ((Si * Q : ℤ) : ℝ) <
      ((Si * P + A + 1 : ℤ) : ℝ) := by
    rw [hB1cast, hXcast, hSreal]
    linear_combination hcellPhi
  have hSq : (Real.sqrt 2 * ((Si * Q : ℤ) : ℝ)) ^ 2 =
      2 * ((Si * Q : ℤ) : ℝ) ^ 2 := by
    calc
      _ = (Real.sqrt 2) ^ 2 * ((Si * Q : ℤ) : ℝ) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num)]
  have hcert : PellWordCertificate L A m n u v := by
    dsimp [PellWordCertificate, Q, Si]
    rw [hPnum]
    refine ⟨hn, hqlo, hqhi, hden, huInt, hvInt, hPnonneg, ?_, ?_⟩
    · have hsquare : ((Si * P + A : ℤ) : ℝ) ^ 2 <
          (Real.sqrt 2 * ((Si * Q : ℤ) : ℝ)) ^ 2 :=
        (sq_lt_sq₀ (by exact_mod_cast hBi) hrootXpos.le).mpr hBlo
      rw [hSq] at hsquare
      exact_mod_cast hsquare
    · have hB1nonneg : 0 ≤ ((Si * P + A + 1 : ℤ) : ℝ) := by positivity
      have hsquare : (Real.sqrt 2 * ((Si * Q : ℤ) : ℝ)) ^ 2 <
          ((Si * P + A + 1 : ℤ) : ℝ) ^ 2 :=
        (sq_lt_sq₀ hrootXpos.le hB1nonneg).mpr hBhi
      rw [hSq] at hsquare
      exact_mod_cast hsquare
  exact ⟨m, n, u, v, hcert⟩

end NormalNumbers.SqrtTwoRoutes
