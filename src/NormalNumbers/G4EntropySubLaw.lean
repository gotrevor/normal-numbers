/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandPrefix
import NormalNumbers.G4EntropyResidue

/-!
# An arbitrary sub-family of a band's windows, and its residue-restricted capture

`G4EntropyBandPrefix` certifies the law of the **first `a`** windows of band `i`.  The base-`2^k`
upgrade needs more: for a fixed residue class of **read** positions, the local class inside
window `a` of band `i` is

    `q ≡ c − fTW i − a·kk i  (mod k)`,

which *moves with `a`* because `kk i = 40000 + i` is odd for odd `i`.  The fix is to split the
band prefix into the `k` sub-families `{a : a ≡ e (mod k)}`: on each of them the local class is
constant.  A sample-time restriction is exactly what `H₂_empirical_window_restrict_ge` prices, at
`(δ+1)|P_K|/|S|`, so a sub-family of relative size `1/k` costs a factor `√k` in the capture
error — harmless, since the whole budget tends to `0`.

* `subLaw`, `H₂_subLaw_ge` — `preLaw` for an arbitrary nonempty `S ⊆ P_K`.
* `abs_posAvgRes_subLaw_le` — 🎯 its residue-restricted capture bound.
* `posAvgRes_subLaw_eq_digits` — the digit rendering of that average.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### §1  The law of an arbitrary sub-family of sample times -/

open Classical in
/-- The window law at the good atom, restricted to an arbitrary nonempty set `S` of sample
times of level `i`. -/
noncomputable def subLaw (i : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (x : ℝ) :
    FinLaw (Unit → Fin (2 ^ kk i)) :=
  empirical S hS (fun n => fun _ : Unit => ZVec (gridAt i) (kk i) x n (goodAtom i))

open Classical in
lemma H₂_subLaw (i : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (x : ℝ) :
    (subLaw i S hS x).H₂
      = (empirical S hS (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i))).H₂ := by
  classical
  have hmap := (map_empirical (Ω := Fin (2 ^ kk i)) (Ω' := Unit → Fin (2 ^ kk i))
    hS (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i))
    (fun u => fun _ : Unit => u)).symm
  have hH := FinLaw.H₂_map_injective
    (empirical S hS (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i)))
    (g := fun u : Fin (2 ^ kk i) => fun _ : Unit => u) (fun u u' h => congrFun h ())
  rw [← hH, ← hmap]
  rfl

open Classical in
/-- **A sub-family's deficit.**  A set of sample times of relative size `σ = |S|/|P_K|` costs
`(δ+1)/σ`. -/
theorem H₂_subLaw_ge (i : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (hSP : S ⊆ PK i) :
    (kk i : ℝ) - (atomDeficit i + 1) * ((PK i).card : ℝ) / ((S.card : ℕ) : ℝ)
      ≤ (subLaw i S hS (primeLambertAtBase 4)).H₂ := by
  classical
  set f : ℕ → Fin (2 ^ kk i) :=
    fun n => ZVec (gridAt i) (kk i) (primeLambertAtBase 4) n (goodAtom i) with hf
  have hfull : ((kk i : ℝ) - atomDeficit i) ≤ (empirical (PK i) (PK_nonempty i) f).H₂ := by
    have hmap := map_coord_jointLawAt i (primeLambertAtBase 4) (goodAtom i)
    have hd := goodAtom_deficit i
    rw [FinLaw.coordDeficit] at hd
    rw [hmap] at hd
    linarith
  have hrest := H₂_empirical_window_restrict_ge (m := kk i) (PK_nonempty i) hS hSP f
    (δ := atomDeficit i) hfull
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := Finset.card_pos.2 hS
    exact_mod_cast this
  have hPpos : (0 : ℝ) < ((PK i).card : ℝ) := by exact_mod_cast PK_card_pos i
  have hdiv : (atomDeficit i + 1) / ((S.card : ℝ) / ((PK i).card : ℝ))
      = (atomDeficit i + 1) * ((PK i).card : ℝ) / (S.card : ℝ) := by
    field_simp
  rw [hdiv] at hrest
  rw [H₂_subLaw]
  exact hrest

/-! ### §2  The residue-restricted capture bound -/

set_option maxHeartbeats 1000000 in
/-- 🎯 **A certified sub-family, at a fixed residue class of window positions.**  The same bound
as `abs_posAvg_preLaw_le` with `a` replaced by `|S|` — the residue restriction itself is free. -/
theorem abs_posAvgRes_subLaw_le (i : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (hSP : S ⊆ PK i)
    (ℓ k c : ℕ) (hℓ : 0 < ℓ) (hℓm : 2 * ℓ ≤ kk i) (hk : k ∣ ℓ)
    (hne : (resPos (kk i) ℓ k c).Nonempty) (w : Fin (2 ^ ℓ)) :
    |posAvgRes (kk i) ℓ k c (subLaw i S hS (primeLambertAtBase 4)) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (2 * Real.log 2 * (ℓ : ℝ)
          * ((atomDeficit i + 1) * ((PK i).card : ℝ)) / ((S.card : ℝ) * (kk i : ℝ))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := Finset.card_pos.2 hS
    exact_mod_cast this
  have hPpos : (0 : ℝ) < ((PK i).card : ℝ) := by exact_mod_cast PK_card_pos i
  have hkkpos : (0 : ℝ) < (kk i : ℝ) := by
    have := kk_pos' i; exact_mod_cast this
  have hδ : (0 : ℝ) < (atomDeficit i + 1) * ((PK i).card : ℝ) / (S.card : ℝ) := by
    have := atomDeficit_pos i
    positivity
  have hdef : ((kk i : ℝ) - (atomDeficit i + 1) * ((PK i).card : ℝ) / (S.card : ℝ))
      * (Fintype.card Unit : ℝ) ≤ (subLaw i S hS (primeLambertAtBase 4)).H₂ := by
    simp only [Fintype.card_unit, Nat.cast_one, mul_one]
    exact H₂_subLaw_ge i S hS hSP
  have hmain := abs_posAvgRes_sub_le (m := kk i) (ℓ := ℓ) (k := k) (c := c) hℓ (by omega) hk
    (subLaw i S hS (primeLambertAtBase 4)) w hδ hdef hne
  refine hmain.trans ?_
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hhalf : (kk i : ℝ) / 2 ≤ (kk i : ℝ) - ℓ + 1 := by
    have : (2 : ℝ) * ℓ ≤ (kk i : ℝ) := by exact_mod_cast hℓm
    linarith
  have hden : (0 : ℝ) < (kk i : ℝ) - ℓ + 1 := by
    have : (2 : ℝ) * ℓ ≤ (kk i : ℝ) := by exact_mod_cast hℓm
    linarith
  have hstep : Real.log 2 * (ℓ : ℝ) * ((atomDeficit i + 1) * ((PK i).card : ℝ) / (S.card : ℝ))
      / ((kk i : ℝ) - ℓ + 1)
      ≤ 2 * Real.log 2 * (ℓ : ℝ) * ((atomDeficit i + 1) * ((PK i).card : ℝ))
          / ((S.card : ℝ) * (kk i : ℝ)) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have hd0 : (0 : ℝ) < atomDeficit i + 1 := by
      have := atomDeficit_pos i; linarith
    have hc : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * ((atomDeficit i + 1) * ((PK i).card : ℝ)) := by
      positivity
    have hexp : Real.log 2 * (ℓ : ℝ) * ((atomDeficit i + 1) * ((PK i).card : ℝ) / (S.card : ℝ))
        * ((S.card : ℝ) * (kk i : ℝ))
        = (Real.log 2 * (ℓ : ℝ) * ((atomDeficit i + 1) * ((PK i).card : ℝ))) * (kk i : ℝ) := by
      field_simp
    rw [hexp]
    nlinarith [hc, hhalf, hkkpos]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by norm_num)

/-! ### §3  The digit rendering -/

open Classical in
/-- **The sub-family's residue-restricted count rendering.** -/
theorem posAvgRes_subLaw_eq_count (i : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (ℓ k c : ℕ) (x : ℝ)
    (w : Fin (2 ^ ℓ)) :
    posAvgRes (kk i) ℓ k c (subLaw i S hS x) w
      = (∑ p ∈ resPos (kk i) ℓ k c,
            ((S.filter fun n =>
              posAt (kk i) ℓ (p : ℕ) (ZVec (gridAt i) (kk i) x n (goodAtom i)) = w).card : ℝ))
        / ((S.card : ℝ) * (((resPos (kk i) ℓ k c).card : ℕ) : ℝ)) := by
  classical
  have hp : ∀ p : Fin (kk i - ℓ + 1),
      ((subLaw i S hS x).map
          (fun z : Unit → Fin (2 ^ kk i) => posAt (kk i) ℓ (p : ℕ) (z default))).prob {w}
        = ((S.filter fun n =>
              posAt (kk i) ℓ (p : ℕ) (ZVec (gridAt i) (kk i) x n (goodAtom i)) = w).card : ℝ)
          / (S.card : ℝ) := by
    intro p
    rw [subLaw, FinLaw.prob, Finset.sum_singleton]
    exact map_empirical_p hS _ _ w
  rw [posAvgRes, posSumRes]
  simp only [Fintype.card_unit, Nat.cast_one, one_mul, Finset.univ_unique,
    Finset.sum_singleton, hp]
  rw [← Finset.sum_div, div_div]

open Classical in
/-- **The sub-family's residue-restricted digit rendering.** -/
theorem posAvgRes_subLaw_eq_digits (i : ℕ) (S : Finset ℕ) (hS : S.Nonempty) (ℓ k c : ℕ)
    (hℓm : ℓ ≤ kk i) (x : ℝ) (w : Fin (2 ^ ℓ)) :
    posAvgRes (kk i) ℓ k c (subLaw i S hS x) w
      = (∑ p ∈ resPos (kk i) ℓ k c,
            ((S.filter fun n =>
              blockVal (Int.fract x) (2 * kIdx (gridAt i) n (goodAtom i) + (p : ℕ)) ℓ
                = (w : ℕ)).card : ℝ))
        / ((S.card : ℝ) * (((resPos (kk i) ℓ k c).card : ℕ) : ℝ)) := by
  classical
  rw [posAvgRes_subLaw_eq_count i S hS ℓ k c x w]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  have hZ : ∀ n : ℕ, ZVec (gridAt i) (kk i) x n (goodAtom i)
      = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n (goodAtom i)) (kk i),
        blockVal_lt _ _ _⟩ :=
    fun n => Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n (goodAtom i))
  have hfit : (p : ℕ) + ℓ ≤ kk i := by
    have := p.isLt
    omega
  refine Finset.filter_congr fun n _ => ?_
  rw [hZ n, posAt_blockVal _ _ _ _ _ hfit]
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

end NormalNumbers.G4.Sched
