import Mathlib

/-!
# The digit-sum law of `L` uniform base-`b` digits, modulo `b − 1`

Pure counting, no analysis: the number of words `v : Fin L → Fin b` whose digit sum lies in a
prescribed class mod `q = b − 1` is `(b^L − 1)/q + [class = 0]`.

The mechanism is the convolution identity `c = u + δ₀` on `ZMod q`, where `c j` counts the digits
`d < b` with `d ≡ j`: every class is hit once by `d = j`, and the class `0` is hit twice
(`d = 0` and `d = q`).  Since `u ∗ u = q · u`, the `L`-fold convolution collapses to
`(b^L − 1)/q · u + δ₀`.  Formalized as the integer identity `q · cnt + 1 = b^L + q·[t = 0]`,
which avoids all division.
-/

namespace NormalNumbers.CastingOut

open Finset

variable {q : ℕ}

/-- Words of length `L` over `Fin b` whose digit sum is `t` in `ZMod q`. -/
noncomputable def sumCount (b q L : ℕ) (t : ZMod q) : ℕ :=
  open Classical in
  (univ.filter (fun v : Fin L → Fin b => (∑ i, ((v i : ℕ) : ZMod q)) = t)).card

theorem sumCount_zero (b q : ℕ) (t : ZMod q) :
    sumCount b q 0 t = if t = 0 then 1 else 0 := by
  classical
  unfold sumCount
  by_cases h : t = 0 <;> simp [h, eq_comm]

/-- Peeling the first letter. -/
theorem sumCount_succ (b q L : ℕ) (t : ZMod q) :
    sumCount b q (L + 1) t = ∑ d : Fin b, sumCount b q L (t - ((d : ℕ) : ZMod q)) := by
  classical
  unfold sumCount
  simp only [Finset.card_filter]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (L + 1) => Fin b))
      (fun v : Fin (L + 1) → Fin b => if (∑ i, ((v i : ℕ) : ZMod q)) = t then 1 else 0),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro d _
  refine Finset.sum_congr rfl ?_
  intro v _
  have hs : (∑ i, (((Fin.consEquiv (fun _ : Fin (L + 1) => Fin b)) (d, v) i : Fin b) : ℕ)
      : ZMod q) = ((d : ℕ) : ZMod q) + ∑ i, ((v i : ℕ) : ZMod q) := by
    simp [Fin.consEquiv, Fin.sum_univ_succ]
  rw [hs]
  congr 1
  simp [eq_sub_iff_add_eq, add_comm]

/-- The digit fibre count: for `b = q + 1` with `q ≥ 1`, exactly one digit `d < b` lies in each
class, plus a second one (`d = q`) in the class `0`. -/
theorem card_digit_fibre (q : ℕ) (hq : 1 ≤ q) (t : ZMod q) :
    ((univ : Finset (Fin (q + 1))).filter (fun d : Fin (q + 1) => ((d : ℕ) : ZMod q) = t)).card
      = 1 + (if t = 0 then 1 else 0) := by
  classical
  have hne : NeZero q := ⟨by omega⟩
  have hcard :
      ((univ : Finset (Fin (q + 1))).filter (fun d : Fin (q + 1) => ((d : ℕ) : ZMod q) = t)).card
      = ((range (q + 1)).filter (fun d : ℕ => ((d : ℕ) : ZMod q) = t)).card := by
    rw [Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_eq_sum_range (fun d : ℕ => if ((d : ℕ) : ZMod q) = t then 1 else 0) (q + 1)]
  rw [hcard, Finset.range_add_one, Finset.filter_insert]
  have hq0 : ((q : ℕ) : ZMod q) = 0 := by simp
  have hsingle : (range q).filter (fun d : ℕ => ((d : ℕ) : ZMod q) = t) = {t.val} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, hdt⟩
      have h := congrArg ZMod.val hdt
      rwa [ZMod.val_natCast_of_lt hd] at h
    · rintro rfl
      exact ⟨ZMod.val_lt t, by simp [ZMod.natCast_val, ZMod.cast_id]⟩
  have hqnot : t.val ≠ q := by have := ZMod.val_lt t; omega
  by_cases ht : t = 0
  · have hqt : ((q : ℕ) : ZMod q) = t := by rw [hq0, ht]
    rw [if_pos hqt, hsingle, Finset.card_insert_of_notMem (by simpa using fun h => hqnot h.symm)]
    simp [ht]
  · have hqne : ¬ (((q : ℕ) : ZMod q) = t) := by rw [hq0]; exact fun h => ht h.symm
    rw [if_neg hqne, hsingle]
    simp [ht]

/-- **The closed count.**  `q · sumCount + 1 = b^L + q·[t = 0]`, with `b = q + 1`. -/
theorem sumCount_closed (q : ℕ) (hq : 1 ≤ q) (L : ℕ) (t : ZMod q) :
    q * sumCount (q + 1) q L t + 1 = (q + 1) ^ L + q * (if t = 0 then 1 else 0) := by
  classical
  induction L generalizing t with
  | zero => rw [sumCount_zero]; ring
  | succ L ih =>
      set S := ∑ d : Fin (q + 1), sumCount (q + 1) q L (t - ((d : ℕ) : ZMod q)) with hS
      set e : ℕ := if t = 0 then 1 else 0 with he
      have hfib : (∑ d : Fin (q + 1), (if t - ((d : ℕ) : ZMod q) = 0 then 1 else 0)) = 1 + e := by
        rw [he, ← card_digit_fibre q hq t, Finset.card_filter]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        congr 1
        simp [sub_eq_zero, eq_comm]
      have hsum : (∑ d : Fin (q + 1),
            (q * sumCount (q + 1) q L (t - ((d : ℕ) : ZMod q)) + 1))
          = ∑ d : Fin (q + 1),
              ((q + 1) ^ L + q * (if t - ((d : ℕ) : ZMod q) = 0 then 1 else 0)) :=
        Finset.sum_congr rfl (fun d _ => ih _)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        smul_eq_mul, mul_one, hfib, ← hS] at hsum
      rw [sumCount_succ, ← hS, pow_succ]
      have hexp : q * (1 + e) = q + q * e := by ring
      rw [hexp] at hsum
      linarith

end NormalNumbers.CastingOut
