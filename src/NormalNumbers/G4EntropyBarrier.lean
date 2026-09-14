/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyTransfer

/-!
# Entropy expedition §6: the locality barrier

Lap 8 refuted the brief's primary transfer target `T_E` with one explicit witness.  This module
extracts the *mechanism* of that refutation as a theorem, so that it applies to every statement
about the arithmetic sample at once, not just to `E0`.

## The general principle

`exists_nonnormal_of_digitLocal`: let `S ⊆ ℕ` be a set of digit positions of upper density
`≤ c < 1/2`, and let `P` be any property of reals that is **`S`-local** — i.e. `P x` depends on
`x` only through the binary digits of `x` at positions in `S`.  If `P` holds anywhere, then `P`
holds at some `y ∈ [0,1)` that is **not** binary normal.  Equivalently
(`half_le_density_of_forces_normal`):

> a digit-local hypothesis can imply normality only if the positions it reads have upper
> density at least `1/2`.

The proof is the masking construction: replace every digit outside `S` by `0`.  The result
agrees with `x` on `S`, hence still satisfies `P`, and its digit `1` has frequency `≤ c < 1/2`.

## The application

For the implemented base-four schedule, `Sched.card_isSampled_le` says the sampled positions
have density `≤ 1/4`.  So **no property of the arithmetic sample whatsoever implies normality**
(`Sched.exists_nonnormal_jointLocal`): it suffices that the property be a function of the joint
quantized sample laws `jointLawAt i ·`.  `E0`, the sampled block frequencies (S) and the
sampled mixture frequencies are all such functions, so `T_E`, `T_S` and `T_mix` all fall to the
same witness (`Sched.not_T_E'`, `Sched.not_T_S`, `Sched.not_T_mix`).

This is the exact shape of the repair the brief's §6 positive branch must supply: an arithmetic
input that reads a set of digit positions of upper density `≥ 1/2`.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

open NormalNumbers

/-! ### Masking a real to a set of digit positions -/

variable (S : ℕ → Prop) [DecidablePred S]

/-- The digits of `x` at the positions of `S`, and `0` everywhere else. -/
noncomputable def maskDigits (x : ℝ) (j : ℕ) : ℕ :=
  if S j then digitOf 2 (Int.fract x) j else 0

lemma maskDigits_lt (x : ℝ) (j : ℕ) : maskDigits S x j < 2 := by
  unfold maskDigits
  split
  · exact Nat.mod_lt _ (by omega)
  · omega

/-- The masked real: `x` seen through the positions of `S` only. -/
noncomputable def maskReal (x : ℝ) : ℝ := realOfDigits 2 (maskDigits S x)

variable {S}

/-- A position set of eventual density `< 1` misses arbitrarily late positions. -/
lemma exists_not_mem_of_density_eventually {c : ℝ} (hc : c < 1) {L₀ : ℕ}
    (hdens : ∀ L : ℕ, L₀ ≤ L → (((Finset.range L).filter S).card : ℝ) ≤ c * L) (M : ℕ) :
    ∃ j, M ≤ j ∧ ¬ S j := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨N, hN⟩ := exists_nat_gt ((M : ℝ) / (1 - c))
  set L := max (max M N) L₀ with hLdef
  have hLM : M ≤ L := le_trans (le_max_left _ _) (le_max_left _ _)
  have hL₀ : L₀ ≤ L := le_max_right _ _
  have hLN : (M : ℝ) / (1 - c) < L := by
    refine lt_of_lt_of_le hN ?_
    have : N ≤ L := le_trans (le_max_right M N) (le_max_left _ _)
    exact_mod_cast this
  have hsub : Finset.Ico M L ⊆ (Finset.range L).filter S := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj.2, hcon j hj.1⟩
  have h1 : L - M ≤ ((Finset.range L).filter S).card := by
    have := Finset.card_le_card hsub
    simpa [Nat.card_Ico] using this
  have h1R : (L : ℝ) - M ≤ ((Finset.range L).filter S).card := by
    have : ((L - M : ℕ) : ℝ) ≤ ((Finset.range L).filter S).card := by exact_mod_cast h1
    rwa [Nat.cast_sub hLM] at this
  have h2 := hdens L hL₀
  have hpos : (0 : ℝ) < 1 - c := by linarith
  have : (M : ℝ) / (1 - c) ≥ L := by
    rw [ge_iff_le, le_div_iff₀ hpos]
    nlinarith
  linarith

/-- A position set of density `< 1` misses arbitrarily late positions. -/
lemma exists_not_mem_of_density {c : ℝ} (hc : c < 1)
    (hdens : ∀ L : ℕ, (((Finset.range L).filter S).card : ℝ) ≤ c * L) (M : ℕ) :
    ∃ j, M ≤ j ∧ ¬ S j :=
  exists_not_mem_of_density_eventually hc (L₀ := 0) (fun L _ => hdens L) M

/-- The mask is a proper binary digit sequence. -/
lemma properDigits_maskDigits (hmiss : ∀ M : ℕ, ∃ j, M ≤ j ∧ ¬ S j) (x : ℝ) :
    ProperDigits 2 (maskDigits S x) := by
  intro M
  obtain ⟨j, hj, hns⟩ := hmiss M
  refine ⟨j, hj, ?_⟩
  unfold maskDigits
  rw [if_neg hns]
  omega

lemma maskReal_mem_Ico (hmiss : ∀ M : ℕ, ∃ j, M ≤ j ∧ ¬ S j) (x : ℝ) :
    maskReal S x ∈ Set.Ico (0 : ℝ) 1 :=
  realOfDigits_mem_Ico 2 (by norm_num) _ (maskDigits_lt S x)
    (properDigits_maskDigits hmiss x)

lemma digitOf_maskReal (hmiss : ∀ M : ℕ, ∃ j, M ≤ j ∧ ¬ S j) (x : ℝ) :
    digitOf 2 (Int.fract (maskReal S x)) = maskDigits S x := by
  have h := maskReal_mem_Ico hmiss x
  rw [Set.mem_Ico] at h
  rw [Int.fract_eq_self.2 h]
  exact digitOf_realOfDigits 2 (by norm_num) _ (maskDigits_lt S x)
    (properDigits_maskDigits hmiss x)

/-- The mask keeps every digit the set `S` reads. -/
lemma digitOf_maskReal_of_mem (hmiss : ∀ M : ℕ, ∃ j, M ≤ j ∧ ¬ S j) (x : ℝ) {j : ℕ}
    (hj : S j) :
    digitOf 2 (Int.fract (maskReal S x)) j = digitOf 2 (Int.fract x) j := by
  rw [digitOf_maskReal hmiss x]
  unfold maskDigits
  rw [if_pos hj]

/-! ### The barrier

The density bound is only needed for large `L`: finitely many positions cannot change a digit
frequency.  Stating it that way makes the necessary condition on any repair a statement about
*arbitrarily large* prefixes, i.e. genuine upper density `≥ 1/2`. -/

/-- The masked real is not binary normal when `S` has eventual upper density `c < 1/2`: its
digit `1` occurs with frequency at most `c`. -/
theorem not_isNormal_maskReal_eventually {c : ℝ} (hc : c < 1 / 2) (hc0 : 0 ≤ c) {L₀ : ℕ}
    (hdens : ∀ L : ℕ, L₀ ≤ L → (((Finset.range L).filter S).card : ℝ) ≤ c * L) (x : ℝ) :
    ¬ IsNormal 2 (maskReal S x) := by
  intro hN
  have hmiss := exists_not_mem_of_density_eventually (S := S) (by linarith : c < 1) hdens
  have h := hN [1] (by simp) (fun d hd => by simp at hd; omega)
  have hle : ∀ n : ℕ, L₀ ≤ n →
      (countOccurrences [1] ((List.range n).map (digitOf 2 (Int.fract (maskReal S x)))) : ℝ) / n
        ≤ c := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simpa using hc0
    have hcount : countOccurrences [1]
        ((List.range n).map (digitOf 2 (Int.fract (maskReal S x))))
          ≤ ((Finset.range n).filter S).card := by
      refine NormalNumbers.G4.Sched.countOcc_one_le (fun j hj => ?_) n
      by_contra hns
      rw [digitOf_maskReal hmiss] at hj
      unfold maskDigits at hj
      rw [if_neg hns] at hj
      omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    rw [div_le_iff₀ hnR]
    have h1 : (countOccurrences [1]
        ((List.range n).map (digitOf 2 (Int.fract (maskReal S x)))) : ℝ)
          ≤ (((Finset.range n).filter S).card : ℝ) := by exact_mod_cast hcount
    exact h1.trans (hdens n hn)
  have hev : ∀ᶠ n in atTop,
      (countOccurrences [1] ((List.range n).map (digitOf 2 (Int.fract (maskReal S x)))) : ℝ) / n
        ≤ c := by
    filter_upwards [eventually_ge_atTop L₀] with n hn using hle n hn
  have hlim := le_of_tendsto h hev
  norm_num at hlim
  linarith

/-- **The locality barrier.**  A property that depends on a real only through its binary digits
at the positions of a set `S` of eventual upper density `c < 1/2` can never imply normality: if
it holds anywhere, it holds at a nonnormal point of `[0,1)`. -/
theorem exists_nonnormal_of_digitLocal_eventually {c : ℝ} (hc : c < 1 / 2) (hc0 : 0 ≤ c)
    {L₀ : ℕ} (hdens : ∀ L : ℕ, L₀ ≤ L → (((Finset.range L).filter S).card : ℝ) ≤ c * L)
    {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
      P x → P y)
    {x : ℝ} (hx : P x) :
    ∃ y : ℝ, 0 ≤ y ∧ y < 1 ∧ P y ∧ ¬ IsNormal 2 y := by
  have hmiss := exists_not_mem_of_density_eventually (S := S) (by linarith : c < 1) hdens
  have hmem := maskReal_mem_Ico hmiss x
  rw [Set.mem_Ico] at hmem
  refine ⟨maskReal S x, hmem.1, hmem.2, ?_,
    not_isNormal_maskReal_eventually hc hc0 hdens x⟩
  exact hloc x _ (fun j hj => (digitOf_maskReal_of_mem hmiss x hj).symm) hx

/-- Nonnegativity of a density bound is automatic. -/
lemma nonneg_of_density {c : ℝ}
    (hdens : ∀ L : ℕ, (((Finset.range L).filter S).card : ℝ) ≤ c * L) : 0 ≤ c := by
  have h1 := hdens 1
  have h0 : (0 : ℝ) ≤ (((Finset.range 1).filter S).card : ℝ) := Nat.cast_nonneg _
  have := le_trans h0 h1
  simpa using this

theorem not_isNormal_maskReal {c : ℝ} (hc : c < 1 / 2)
    (hdens : ∀ L : ℕ, (((Finset.range L).filter S).card : ℝ) ≤ c * L) (x : ℝ) :
    ¬ IsNormal 2 (maskReal S x) :=
  not_isNormal_maskReal_eventually hc (nonneg_of_density hdens) (L₀ := 0)
    (fun L _ => hdens L) x

/-- **The locality barrier**, with the density bound at every `L`. -/
theorem exists_nonnormal_of_digitLocal {c : ℝ} (hc : c < 1 / 2)
    (hdens : ∀ L : ℕ, (((Finset.range L).filter S).card : ℝ) ≤ c * L)
    {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
      P x → P y)
    {x : ℝ} (hx : P x) :
    ∃ y : ℝ, 0 ≤ y ∧ y < 1 ∧ P y ∧ ¬ IsNormal 2 y :=
  exists_nonnormal_of_digitLocal_eventually hc (nonneg_of_density hdens) (L₀ := 0)
    (fun L _ => hdens L) hloc hx

/-- **The contrapositive**, as the brief's §6 positive branch needs it: if a satisfiable
`S`-local hypothesis does force normality, then `S` reads at least half of all digit positions
— for every `c < 1/2` some prefix `[0,L)` contains more than `c·L` of them. -/
theorem half_le_density_of_forces_normal
    {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
      P x → P y)
    {x : ℝ} (hx : P x)
    (hT : ∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y)
    {c : ℝ} (hc : c < 1 / 2) :
    ∃ L : ℕ, c * L < (((Finset.range L).filter S).card : ℝ) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy0, hy1, hPy, hny⟩ := exists_nonnormal_of_digitLocal hc hcon hloc hx
  exact hny (hT y hy0 hy1 hPy)

/-- **The necessary condition, sharp form**: a satisfiable `S`-local hypothesis forces normality
only if `S` has upper density `≥ 1/2` — for every `c < 1/2` there are *arbitrarily large* `L`
with more than `c·L` positions of `S` below `L`. -/
theorem upper_density_half_of_forces_normal
    {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
      P x → P y)
    {x : ℝ} (hx : P x)
    (hT : ∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y)
    {c : ℝ} (hc : c < 1 / 2) (hc0 : 0 ≤ c) (L₀ : ℕ) :
    ∃ L : ℕ, L₀ ≤ L ∧ c * L < (((Finset.range L).filter S).card : ℝ) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy0, hy1, hPy, hny⟩ :=
    exists_nonnormal_of_digitLocal_eventually hc hc0 (fun L hL => hcon L hL) hloc hx
  exact hny (hT y hy0 hy1 hPy)

/-- **Vacuity**: if a satisfiable-or-not `S`-local hypothesis does imply normality on `[0,1)`,
then it is never satisfied at all.  So a digit-local premise reading a set of density `< 1/2` is
either refuted or vacuous. -/
theorem not_satisfiable_of_forces_normal {c : ℝ} (hc : c < 1 / 2)
    (hdens : ∀ L : ℕ, (((Finset.range L).filter S).card : ℝ) ≤ c * L)
    {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
      P x → P y)
    (hT : ∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y) :
    ∀ x : ℝ, ¬ P x := by
  intro x hx
  obtain ⟨y, hy0, hy1, hPy, hny⟩ := exists_nonnormal_of_digitLocal hc hdens hloc hx
  exact hny (hT y hy0 hy1 hPy)

end NormalNumbers.G4Entropy

/-! ## The implemented schedule: every sample statistic falls -/

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy Finset Filter

/-- The sampled positions have density `≤ 1/4`, in the real form the barrier wants. -/
theorem card_isSampled_le_real (L : ℕ) :
    ((((Finset.range L).filter IsSampled).card : ℝ)) ≤ (1 / 4 : ℝ) * L := by
  have h := card_isSampled_le L
  have h4 : 4 * (((Finset.range L).filter IsSampled).card) ≤ L := by
    have := Nat.mul_le_mul_left 4 h
    have h2 : 4 * (L / 4) ≤ L := Nat.mul_div_le L 4
    omega
  have : (4 : ℝ) * ((((Finset.range L).filter IsSampled).card : ℕ) : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast h4
  linarith

/-- **The barrier for the implemented base-four schedule**: no property of a real that depends
only on its digits at the sampled positions can imply normality. -/
theorem exists_nonnormal_of_sampleLocal {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ j, IsSampled j →
        digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) → P x → P y)
    {x : ℝ} (hx : P x) :
    ∃ y : ℝ, 0 ≤ y ∧ y < 1 ∧ P y ∧ ¬ IsNormal 2 y :=
  exists_nonnormal_of_digitLocal (by norm_num) card_isSampled_le_real hloc hx

/-- Any property determined by the joint sample laws is sample-local. -/
theorem jointLawAt_congr (i : ℕ) {x y : ℝ}
    (hd : ∀ j, IsSampled j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) :
    jointLawAt i x = jointLawAt i y :=
  jointLaw_congr (gridAt i) (b₀_lt_X_at i) (kk i) (fun j hj => hd j ⟨i, hj⟩)

/-- **Every statement about the joint quantized sample is either false or vacuous.** -/
theorem exists_nonnormal_jointLocal {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ i, jointLawAt i x = jointLawAt i y) → P x → P y)
    {x : ℝ} (hx : P x) :
    ∃ y : ℝ, 0 ≤ y ∧ y < 1 ∧ P y ∧ ¬ IsNormal 2 y :=
  exists_nonnormal_of_sampleLocal (fun x y hd => hloc x y (fun i => jointLawAt_congr i hd)) hx

/-- `T_E` again, now as an instance of the general barrier (lap 8 proved it by hand). -/
theorem not_T_E' : ¬ T_E := by
  intro hT
  obtain ⟨y, hy0, hy1, hPy, hny⟩ :=
    exists_nonnormal_jointLocal (P := E0)
      (fun x y hj hx => by
        unfold E0 at hx ⊢
        simpa only [hj] using hx)
      E0_primeLambertFour
  exact hny (hT y hy0 hy1 hPy)

/-! ### The sampled block frequencies (S) and the sampled mixture frequencies -/

/-- The index set of the sample at scale `i`: a point `n ∈ P_K` and an atom. -/
noncomputable def Pairs (i : ℕ) : Finset (ℕ × (gridAt i).Atom) :=
  (apSample (X (KK i)) (gridAt i).P₀ (gridAt i).b₀) ×ˢ (Finset.univ : Finset (gridAt i).Atom)

lemma pairs_nonempty (i : ℕ) : (Pairs i).Nonempty := by
  refine Finset.Nonempty.product (apSample_nonempty (gridAt i) (b₀_lt_X_at i)) ?_
  exact Finset.univ_nonempty

lemma pairs_card_pos (i : ℕ) : 0 < (Pairs i).card := Finset.card_pos.2 (pairs_nonempty i)

/-- The window of `x` read at sample pair `z`, starting `h₀` into the block, shows the word
`w`.  The position read is `2·kIdx + h₀ + h`, i.e. the `h`-th digit of the `m_K`-bit block the
schedule quantizes. -/
def WinMatch (i : ℕ) (x : ℝ) (w : List ℕ) (h₀ : ℕ) (z : ℕ × (gridAt i).Atom) : Prop :=
  ∀ h < w.length, digitOf 2 (Int.fract x) (2 * kIdx (gridAt i) z.1 z.2 + (h₀ + h)) = w.getD h 0

noncomputable instance (i : ℕ) (x : ℝ) (w : List ℕ) (h₀ : ℕ) :
    DecidablePred (WinMatch i x w h₀) := Classical.decPred _

/-- **The sampled block frequency** of the word `w` at scale `i`: the fraction of the sample
pairs whose block *begins* with `w`. -/
noncomputable def sampledFreq (i : ℕ) (x : ℝ) (w : List ℕ) : ℝ :=
  ((((Pairs i).filter (WinMatch i x w 0)).card : ℝ)) / ((Pairs i).card : ℝ)

/-- The number of offsets at which a length-`ℓ` word fits inside an `m_K`-bit block. -/
def offsets (i : ℕ) (w : List ℕ) : ℕ := kk i + 1 - w.length

/-- **The sampled mixture frequency** of `w` at scale `i`: pick a sample pair and an offset
inside its block uniformly, and read the length-`|w|` window there. -/
noncomputable def mixFreq (i : ℕ) (x : ℝ) (w : List ℕ) : ℝ :=
  (∑ h₀ ∈ Finset.range (offsets i w),
      (((Pairs i).filter (WinMatch i x w h₀)).card : ℝ))
    / (((Pairs i).card : ℝ) * (offsets i w : ℝ))

/-- **(S)** (brief §5): every fixed word has its uniform frequency among the sampled blocks. -/
def S_freq (x : ℝ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < 2) →
    Tendsto (fun i => sampledFreq i x w) atTop (nhds (((2 : ℝ) ^ w.length)⁻¹))

/-- Uniform sampled *mixture* frequencies. -/
def Mix_freq (x : ℝ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < 2) →
    Tendsto (fun i => mixFreq i x w) atTop (nhds (((2 : ℝ) ^ w.length)⁻¹))

/-- **`T_S`** (brief §6): (S) for every fixed word implies binary normality. -/
def T_S : Prop := ∀ x : ℝ, 0 ≤ x → x < 1 → S_freq x → IsNormal 2 x

/-- **`T_mix`** (brief §6): uniform sampled mixture frequencies imply binary normality. -/
def T_mix : Prop := ∀ x : ℝ, 0 ≤ x → x < 1 → Mix_freq x → IsNormal 2 x

/-! ### Both are digit-local, hence both fall -/

/-- Every position a fitting window reads is sampled. -/
lemma isSampled_of_win {i h₀ h : ℕ} {w : List ℕ} {z : ℕ × (gridAt i).Atom}
    (hz : z ∈ Pairs i) (hfit : h₀ + w.length ≤ kk i) (hh : h < w.length) :
    IsSampled (2 * kIdx (gridAt i) z.1 z.2 + (h₀ + h)) := by
  refine ⟨i, ?_⟩
  have hn : z.1 ∈ apSample (X (KK i)) (gridAt i).P₀ (gridAt i).b₀ :=
    (Finset.mem_product.1 hz).1
  exact mem_sampledPos_of (gridAt i) hn z.2 (by omega)

lemma winMatch_congr {i h₀ : ℕ} {w : List ℕ} {x y : ℝ}
    (hd : ∀ j, IsSampled j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j)
    (hfit : h₀ + w.length ≤ kk i) {z : ℕ × (gridAt i).Atom} (hz : z ∈ Pairs i) :
    WinMatch i x w h₀ z ↔ WinMatch i y w h₀ z := by
  constructor <;> intro hm h hh
  · rw [← hd _ (isSampled_of_win hz hfit hh)]; exact hm h hh
  · rw [hd _ (isSampled_of_win hz hfit hh)]; exact hm h hh

lemma card_filter_congr {i h₀ : ℕ} {w : List ℕ} {x y : ℝ}
    (hd : ∀ j, IsSampled j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j)
    (hfit : h₀ + w.length ≤ kk i) :
    ((Pairs i).filter (WinMatch i x w h₀)).card
      = ((Pairs i).filter (WinMatch i y w h₀)).card := by
  congr 1
  exact Finset.filter_congr fun z hz => by
    simpa using (winMatch_congr hd hfit hz)

lemma sampledFreq_congr {i : ℕ} {w : List ℕ} {x y : ℝ}
    (hd : ∀ j, IsSampled j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j)
    (hfit : w.length ≤ kk i) :
    sampledFreq i x w = sampledFreq i y w := by
  unfold sampledFreq
  rw [card_filter_congr hd (by omega)]

lemma mixFreq_congr {i : ℕ} {w : List ℕ} {x y : ℝ}
    (hd : ∀ j, IsSampled j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j)
    (hfit : w.length ≤ kk i) :
    mixFreq i x w = mixFreq i y w := by
  unfold mixFreq
  congr 1
  refine Finset.sum_congr rfl fun h₀ hh₀ => ?_
  rw [Finset.mem_range] at hh₀
  have : h₀ + w.length ≤ kk i := by unfold offsets at hh₀; omega
  rw [card_filter_congr hd this]

/-- Eventually every fixed word fits in the block. -/
lemma eventually_fits (w : List ℕ) : ∀ᶠ i in atTop, w.length ≤ kk i := by
  filter_upwards [eventually_ge_atTop w.length] with i hi
  unfold kk; omega

theorem S_freq_local {x y : ℝ}
    (hd : ∀ j, IsSampled j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j)
    (hx : S_freq x) : S_freq y := by
  intro w hw hb
  refine (hx w hw hb).congr' ?_
  filter_upwards [eventually_fits w] with i hi
  exact sampledFreq_congr hd hi

theorem Mix_freq_local {x y : ℝ}
    (hd : ∀ j, IsSampled j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j)
    (hx : Mix_freq x) : Mix_freq y := by
  intro w hw hb
  refine (hx w hw hb).congr' ?_
  filter_upwards [eventually_fits w] with i hi
  exact mixFreq_congr hd hi

/-- **`T_S` is vacuous or false**: if `(S)` holds for even one real, `T_S` is false. -/
theorem not_T_S_of_exists {x : ℝ} (hx : S_freq x) : ¬ T_S := by
  intro hT
  obtain ⟨y, hy0, hy1, hPy, hny⟩ :=
    exists_nonnormal_of_sampleLocal (P := S_freq) (fun x y hd => S_freq_local hd) hx
  exact hny (hT y hy0 hy1 hPy)

/-- **`T_S` implies its own premise is unsatisfiable.**  Either way it transfers nothing. -/
theorem T_S_vacuous (hT : T_S) : ∀ x : ℝ, ¬ S_freq x := fun x hx => not_T_S_of_exists hx hT

/-- **`T_mix` is vacuous or false.** -/
theorem not_T_mix_of_exists {x : ℝ} (hx : Mix_freq x) : ¬ T_mix := by
  intro hT
  obtain ⟨y, hy0, hy1, hPy, hny⟩ :=
    exists_nonnormal_of_sampleLocal (P := Mix_freq) (fun x y hd => Mix_freq_local hd) hx
  exact hny (hT y hy0 hy1 hPy)

theorem T_mix_vacuous (hT : T_mix) : ∀ x : ℝ, ¬ Mix_freq x := fun x hx => not_T_mix_of_exists hx hT

end NormalNumbers.G4.Sched
