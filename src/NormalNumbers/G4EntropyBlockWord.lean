/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyPosition
import NormalNumbers.G4EntropyConcat
import NormalNumbers.DisjunctiveCorollaries

/-!
# Entropy expedition — rendering one scale as one block (rung 2)

Rung 3 (`G4EntropyConcat`) turns a family of finite blocks with converging window frequencies
into one normal real.  This module builds the family out of the base-four schedule: the scale-`i`
block is the concatenation, over all sample times `n ∈ P_i` and all atoms `α`, of the `m_i`-bit
window of `x` at digit position `2·kIdx(n,α)`.

* `nthP`/`nthA` — fixed enumerations of `P_i` and of the atoms (any enumeration works).
* `wpos i w` — the digit position opening the `w`-th window, `w < |P_i|·|Atom_i|`.
* `blen i = |P_i|·|Atom_i|·m_i` and `bdig x i j` — the block's length and digits.
* `goodCount` — the windows of `v` that fit inside a single sampled window; this is *literally*
  the numerator of `tendsto_occursCountP_primeLambertFour`.
* `cyc_bounds` — the cyclic count of the block differs from `goodCount` by at most one `|v|` per
  sampled window, i.e. by a `|v|/m_i` fraction of the block.

Nothing here claims anything about the normality of `G₄`: the digits are `G₄`'s, the number
built from them in rung 3 is not `G₄`.
-/

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert
open NormalNumbers.BlockConcat Filter Finset

/-! ### Enumerations -/

lemma atom_card_pos (i : ℕ) : 0 < Fintype.card (gridAt i).Atom := by
  rw [card_Atom_gridAt i]
  positivity

lemma kk_pos (i : ℕ) : 0 < kk i := by unfold kk; omega

/-- The `a`-th sample time at scale `i`, under a fixed enumeration of `P_i`. -/
noncomputable def nthP (i a : ℕ) : ℕ :=
  ((PK i).equivFin.symm ⟨a % (PK i).card, Nat.mod_lt _ (PK_card_pos i)⟩ : ℕ)

/-- The `e`-th atom at scale `i`, under a fixed enumeration. -/
noncomputable def nthA (i e : ℕ) : (gridAt i).Atom :=
  (Fintype.equivFin (gridAt i).Atom).symm
    ⟨e % Fintype.card (gridAt i).Atom, Nat.mod_lt _ (atom_card_pos i)⟩

lemma sum_range_nthP {β : Type*} [AddCommMonoid β] (i : ℕ) (g : ℕ → β) :
    ∑ a ∈ Finset.range (PK i).card, g (nthP i a) = ∑ n ∈ PK i, g n := by
  rw [← Fin.sum_univ_eq_sum_range (fun a => g (nthP i a))]
  have hstep : ∀ a : Fin (PK i).card,
      g (nthP i (a : ℕ)) = g (((PK i).equivFin.symm a : ℕ)) := by
    intro a
    have hfin : (⟨(a : ℕ) % (PK i).card, Nat.mod_lt _ (PK_card_pos i)⟩ : Fin (PK i).card) = a := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt a.isLt
    rw [nthP, hfin]
  rw [Finset.sum_congr rfl fun a _ => hstep a]
  rw [Equiv.sum_comp (PK i).equivFin.symm (fun x : (PK i : Finset ℕ) => g (x : ℕ))]
  exact Finset.sum_coe_sort (PK i) g

lemma sum_range_nthA {β : Type*} [AddCommMonoid β] (i : ℕ) (g : (gridAt i).Atom → β) :
    ∑ e ∈ Finset.range (Fintype.card (gridAt i).Atom), g (nthA i e) = ∑ α, g α := by
  rw [← Fin.sum_univ_eq_sum_range (fun e => g (nthA i e))]
  have hstep : ∀ e : Fin (Fintype.card (gridAt i).Atom),
      g (nthA i (e : ℕ)) = g ((Fintype.equivFin (gridAt i).Atom).symm e) := by
    intro e
    have hfin : (⟨(e : ℕ) % Fintype.card (gridAt i).Atom,
        Nat.mod_lt _ (atom_card_pos i)⟩ : Fin (Fintype.card (gridAt i).Atom)) = e := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt e.isLt
    rw [nthA, hfin]
  rw [Finset.sum_congr rfl fun e _ => hstep e]
  exact Equiv.sum_comp (Fintype.equivFin (gridAt i).Atom).symm g

/-! ### The block -/

/-- The number of sampled windows at scale `i`. -/
noncomputable def nwin (i : ℕ) : ℕ := (PK i).card * Fintype.card (gridAt i).Atom

lemma nwin_pos (i : ℕ) : 0 < nwin i := Nat.mul_pos (PK_card_pos i) (atom_card_pos i)

/-- The digit position opening the `w`-th sampled window. -/
noncomputable def wpos (i w : ℕ) : ℕ :=
  2 * kIdx (gridAt i) (nthP i (w / Fintype.card (gridAt i).Atom))
      (nthA i (w % Fintype.card (gridAt i).Atom))

lemma wpos_mk (i a e : ℕ) (he : e < Fintype.card (gridAt i).Atom) :
    wpos i (a * Fintype.card (gridAt i).Atom + e)
      = 2 * kIdx (gridAt i) (nthP i a) (nthA i e) := by
  have hA := atom_card_pos i
  have hcomm : a * Fintype.card (gridAt i).Atom + e
      = Fintype.card (gridAt i).Atom * a + e := by ring
  rw [wpos, hcomm, Nat.mul_add_div hA, Nat.div_eq_of_lt he, Nat.mul_add_mod,
    Nat.mod_eq_of_lt he]
  simp

/-- The length of the scale-`i` block. -/
noncomputable def blen (i : ℕ) : ℕ := nwin i * kk i

lemma blen_pos (i : ℕ) : 0 < blen i := Nat.mul_pos (nwin_pos i) (kk_pos i)

/-- The `j`-th digit of the scale-`i` block of `x`: `G₄`'s digit at the `j`-th sampled position. -/
noncomputable def samplePosIn (i j : ℕ) : ℕ := wpos i (j / kk i) + j % kk i

/-- The block's digits. -/
noncomputable def bdig (x : ℝ) (i j : ℕ) : ℕ := digitOf 2 (Int.fract x) (samplePosIn i j)

lemma bdig_lt (x : ℝ) (i j : ℕ) : bdig x i j < 2 := Nat.mod_lt _ (by omega)

/-! ### The dictionary: a window of the block is a window of `x` at a sampled position -/

/-- Inside the `w`-th sampled window, a window of `v` that fits is exactly an occurrence of `v`
in `x` at the corresponding sampled digit position. -/
lemma matchesAt_per_blen_iff (x : ℝ) (i w p : ℕ) (v : List ℕ)
    (hw : w < nwin i) (hp : p + v.length ≤ kk i) :
    MatchesAt (per blen (bdig x) i) v (w * kk i + p) ↔ OccursAt 2 x v (wpos i w + p) := by
  have hm := kk_pos i
  have hkey : ∀ j < v.length,
      per blen (bdig x) i (w * kk i + p + j) = digitOf 2 (Int.fract x) (wpos i w + p + j) := by
    intro j hj
    have hlt : p + j < kk i := by omega
    have hmod : (w * kk i + p + j) % blen i = w * kk i + p + j := by
      refine Nat.mod_eq_of_lt ?_
      have : w * kk i + p + j < w * kk i + kk i := by omega
      refine lt_of_lt_of_le this ?_
      have : w + 1 ≤ nwin i := hw
      calc w * kk i + kk i = (w + 1) * kk i := by ring
        _ ≤ nwin i * kk i := Nat.mul_le_mul_right _ this
        _ = blen i := rfl
    have hcomm : w * kk i + p + j = kk i * w + (p + j) := by ring
    have hdiv : (w * kk i + p + j) / kk i = w := by
      rw [hcomm, Nat.mul_add_div hm, Nat.div_eq_of_lt hlt, Nat.add_zero]
    have hmd : (w * kk i + p + j) % kk i = p + j := by
      rw [hcomm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    unfold per bdig samplePosIn
    rw [hmod, hdiv, hmd]
    congr 1
    omega
  constructor
  · intro h j hj
    have h' := h j hj
    rw [hkey j hj] at h'
    rw [h']
    exact (List.getD_eq_getElem v 0 hj)
  · intro h j hj
    rw [hkey j hj, h j hj]
    exact (List.getD_eq_getElem v 0 hj).symm

/-! ### The cyclic count against the sampled occurrence count -/

open Classical in
/-- The numerator of `tendsto_occursCountP_primeLambertFour`: the number of triples `(n, α, p)`
with `p` a window position admitting a full copy of `v`, at which `v` occurs in `x`. -/
noncomputable def goodCount (i : ℕ) (x : ℝ) (v : List ℕ) : ℕ :=
  ∑ c : (gridAt i).Atom × Fin (kk i - v.length + 1),
    ((PK i).filter fun n => OccursAt 2 x v (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card

/-- Counting on `[0, m)` versus on the fitting positions `[0, m − ℓ + 1)`: the two differ by at
most `ℓ`. -/
lemma card_filter_fit (Q : ℕ → Prop) [DecidablePred Q] {m ℓ : ℕ} (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) :
    ((Finset.range (m - ℓ + 1)).filter Q).card ≤ ((Finset.range m).filter Q).card ∧
      ((Finset.range m).filter Q).card ≤ ((Finset.range (m - ℓ + 1)).filter Q).card + ℓ := by
  classical
  have hle : m - ℓ + 1 ≤ m := by omega
  have hsplit : ((Finset.range m).filter Q).card
      = ((Finset.range (m - ℓ + 1)).filter Q).card
        + ((Finset.Ico (m - ℓ + 1) m).filter Q).card := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le (m - ℓ + 1)) hle, Finset.filter_union]
    refine (Finset.card_union_of_disjoint ?_)
    exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive 0 _ _)
  have hedge : ((Finset.Ico (m - ℓ + 1) m).filter Q).card ≤ ℓ := by
    refine le_trans (Finset.card_filter_le _ _) ?_
    rw [Nat.card_Ico]
    omega
  omega

/-- The cyclic count of the scale-`i` block, split into its `nwin i` sampled windows. -/
lemma cyc_eq_sum (x : ℝ) (i : ℕ) (v : List ℕ) :
    cyc blen (bdig x) v i
      = ∑ w ∈ Finset.range (nwin i),
          ((Finset.range (kk i)).filter
            (fun p => MatchesAt (per blen (bdig x) i) v (w * kk i + p))).card := by
  classical
  unfold cyc winCount
  have : blen i = nwin i * kk i := rfl
  rw [this]
  exact card_filter_range_mul _ _

open Classical in
/-- The per-window sampled count, summed over the windows, is exactly `goodCount`. -/
lemma sum_fit_eq_goodCount (x : ℝ) (i : ℕ) (v : List ℕ) :
    ∑ w ∈ Finset.range (nwin i),
        ((Finset.range (kk i - v.length + 1)).filter
          (fun p => OccursAt 2 x v (wpos i w + p))).card
      = goodCount i x v := by
  classical
  set A := Fintype.card (gridAt i).Atom with hA
  set ℓ := v.length with hℓ
  have hnwin : nwin i = (PK i).card * A := rfl
  rw [hnwin, sum_range_mul]
  have hstep : ∀ a ∈ Finset.range (PK i).card,
      ∑ e ∈ Finset.range A,
        ((Finset.range (kk i - ℓ + 1)).filter
          (fun p => OccursAt 2 x v (wpos i (a * A + e) + p))).card
      = ∑ α : (gridAt i).Atom,
          ((Finset.range (kk i - ℓ + 1)).filter
            (fun p => OccursAt 2 x v (2 * kIdx (gridAt i) (nthP i a) α + p))).card := by
    intro a _
    rw [← sum_range_nthA i (fun α =>
      ((Finset.range (kk i - ℓ + 1)).filter
        (fun p => OccursAt 2 x v (2 * kIdx (gridAt i) (nthP i a) α + p))).card)]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [wpos_mk i a e (Finset.mem_range.1 he)]
  rw [Finset.sum_congr rfl hstep]
  rw [sum_range_nthP i (fun n => ∑ α : (gridAt i).Atom,
    ((Finset.range (kk i - ℓ + 1)).filter
      (fun p => OccursAt 2 x v (2 * kIdx (gridAt i) n α + p))).card)]
  -- now reorder `∑ n ∑ α ∑ p` into `∑ (α, p) ∑ n`
  unfold goodCount
  rw [Fintype.sum_prod_type]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm, ← Fin.sum_univ_eq_sum_range (fun p =>
    ∑ n ∈ PK i, if OccursAt 2 x v (2 * kIdx (gridAt i) n α + p) then 1 else 0)]

open Classical in
/-- **Rung 2's counting endpoint.**  The cyclic window count of the scale-`i` block is the
sampled occurrence count of `v`, up to one `|v|` per sampled window. -/
theorem cyc_bounds (x : ℝ) (i : ℕ) (v : List ℕ) (hv : 0 < v.length) (hvm : v.length ≤ kk i) :
    goodCount i x v ≤ cyc blen (bdig x) v i ∧
      cyc blen (bdig x) v i ≤ goodCount i x v + nwin i * v.length := by
  classical
  set ℓ := v.length with hℓ
  have hbound : ∀ w ∈ Finset.range (nwin i),
      ((Finset.range (kk i - ℓ + 1)).filter
          (fun p => OccursAt 2 x v (wpos i w + p))).card
        ≤ ((Finset.range (kk i)).filter
          (fun p => MatchesAt (per blen (bdig x) i) v (w * kk i + p))).card
      ∧ ((Finset.range (kk i)).filter
          (fun p => MatchesAt (per blen (bdig x) i) v (w * kk i + p))).card
        ≤ ((Finset.range (kk i - ℓ + 1)).filter
          (fun p => OccursAt 2 x v (wpos i w + p))).card + ℓ := by
    intro w hw
    have hwlt := Finset.mem_range.1 hw
    have hcongr : ((Finset.range (kk i - ℓ + 1)).filter
        (fun p => MatchesAt (per blen (bdig x) i) v (w * kk i + p))).card
        = ((Finset.range (kk i - ℓ + 1)).filter
          (fun p => OccursAt 2 x v (wpos i w + p))).card := by
      congr 1
      refine Finset.filter_congr fun p hp => ?_
      have hple : p + ℓ ≤ kk i := by
        have := Finset.mem_range.1 hp
        omega
      simpa using matchesAt_per_blen_iff x i w p v hwlt hple
    have := card_filter_fit (fun p => MatchesAt (per blen (bdig x) i) v (w * kk i + p))
      (m := kk i) (ℓ := ℓ) hv hvm
    rw [hcongr] at this
    exact this
  rw [cyc_eq_sum x i v, ← sum_fit_eq_goodCount x i v]
  constructor
  · exact Finset.sum_le_sum fun w hw => (hbound w hw).1
  · calc ∑ w ∈ Finset.range (nwin i),
          ((Finset.range (kk i)).filter
            (fun p => MatchesAt (per blen (bdig x) i) v (w * kk i + p))).card
        ≤ ∑ w ∈ Finset.range (nwin i),
            (((Finset.range (kk i - ℓ + 1)).filter
              (fun p => OccursAt 2 x v (wpos i w + p))).card + ℓ) :=
          Finset.sum_le_sum fun w hw => (hbound w hw).2
      _ = (∑ w ∈ Finset.range (nwin i),
            ((Finset.range (kk i - ℓ + 1)).filter
              (fun p => OccursAt 2 x v (wpos i w + p))).card) + nwin i * ℓ := by
          rw [Finset.sum_add_distrib]
          simp [mul_comm]

/-! ### The block frequency limit -/

lemma tendsto_kk_atTop : Tendsto (fun i => (kk i : ℝ)) atTop atTop := by
  have : ∀ i : ℕ, (i : ℝ) ≤ (kk i : ℝ) := by
    intro i
    have : i ≤ kk i := by unfold kk; omega
    exact_mod_cast this
  exact tendsto_atTop_mono this tendsto_natCast_atTop_atTop

lemma tendsto_blen_atTop : Tendsto (fun i => (blen i : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun i => ?_) tendsto_kk_atTop
  have : kk i ≤ blen i := by
    have := nwin_pos i
    calc kk i = 1 * kk i := (one_mul _).symm
      _ ≤ nwin i * kk i := Nat.mul_le_mul_right _ this
  exact_mod_cast this

open Classical in
/-- **Rung 2's endpoint.**  The cyclic window frequency of the scale-`i` block of `G₄`'s sampled
digits tends to `2^{−|v|}` for every finite binary word `v`.  This is exactly the hypothesis
`isNormal_realOfDigits_seq` consumes. -/
theorem tendsto_cyc_div_blen (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    Tendsto (fun i => (cyc blen (bdig (primeLambertAtBase 4)) v i : ℝ) / (blen i : ℝ))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
  classical
  -- the sampled frequency, with the denominator regrouped as `nwin i * (m − ℓ + 1)`
  have hgood : Tendsto (fun i => (goodCount i (primeLambertAtBase 4) v : ℝ)
      / ((nwin i : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ))) atTop
      (nhds (1 / (2 : ℝ) ^ v.length)) := by
    refine (tendsto_occursCountP_primeLambertFour v hlen hv).congr fun i => ?_
    unfold goodCount nwin
    push_cast
    ring_nf
  -- the position-window correction
  have hratio : Tendsto (fun i => ((kk i - v.length + 1 : ℕ) : ℝ) / (kk i : ℝ))
      atTop (nhds 1) := by
    have hsmall : Tendsto (fun i => ((v.length : ℝ) - 1) / (kk i : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_kk_atTop
    have hcomb := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub hsmall
    rw [sub_zero] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [eventually_ge_atTop v.length] with i hi
    have hle : v.length ≤ kk i := by unfold kk; omega
    have hkpos : (0 : ℝ) < (kk i : ℝ) := by
      have := kk_pos i; exact_mod_cast this
    have hcast : ((kk i - v.length + 1 : ℕ) : ℝ) = (kk i : ℝ) - (v.length : ℝ) + 1 := by
      have h1 : (kk i - v.length + 1 : ℕ) = kk i + 1 - v.length := by omega
      rw [h1, Nat.cast_sub (by omega)]
      push_cast; ring
    rw [hcast]
    field_simp
    ring
  have hmain : Tendsto (fun i => (goodCount i (primeLambertAtBase 4) v : ℝ) / (blen i : ℝ))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
    have hprod := hgood.mul hratio
    rw [mul_one] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop v.length] with i hi
    have hle : v.length ≤ kk i := by unfold kk; omega
    have hkpos : (0 : ℝ) < (kk i : ℝ) := by
      have := kk_pos i; exact_mod_cast this
    have hwpos : (0 : ℝ) < (nwin i : ℝ) := by
      have := nwin_pos i; exact_mod_cast this
    have hmpos : (0 : ℝ) < ((kk i - v.length + 1 : ℕ) : ℝ) := by
      have h0 : 0 < kk i - v.length + 1 := by omega
      exact_mod_cast h0
    have hblen : (blen i : ℝ) = (nwin i : ℝ) * (kk i : ℝ) := by
      unfold blen; push_cast; ring
    rw [hblen]
    field_simp
  -- the seam: at most one `|v|` per sampled window
  have hseam : Tendsto (fun i => (cyc blen (bdig (primeLambertAtBase 4)) v i : ℝ) / (blen i : ℝ)
      - (goodCount i (primeLambertAtBase 4) v : ℝ) / (blen i : ℝ)) atTop (nhds 0) := by
    have hz : Tendsto (fun i => (v.length : ℝ) / (kk i : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_kk_atTop
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_ge_atTop v.length] with i hi
    have hle : v.length ≤ kk i := by unfold kk; omega
    have hkpos : (0 : ℝ) < (kk i : ℝ) := by
      have := kk_pos i; exact_mod_cast this
    have hwpos : (0 : ℝ) < (nwin i : ℝ) := by
      have := nwin_pos i; exact_mod_cast this
    have hblen : (blen i : ℝ) = (nwin i : ℝ) * (kk i : ℝ) := by
      unfold blen; push_cast; ring
    have hbpos : (0 : ℝ) < (blen i : ℝ) := by rw [hblen]; positivity
    obtain ⟨h1, h2⟩ := cyc_bounds (primeLambertAtBase 4) i v hlen hle
    have h1R : (goodCount i (primeLambertAtBase 4) v : ℝ)
        ≤ (cyc blen (bdig (primeLambertAtBase 4)) v i : ℝ) := by exact_mod_cast h1
    have h2R : (cyc blen (bdig (primeLambertAtBase 4)) v i : ℝ)
        ≤ (goodCount i (primeLambertAtBase 4) v : ℝ) + (nwin i : ℝ) * (v.length : ℝ) := by
      exact_mod_cast h2
    rw [Real.norm_eq_abs, div_sub_div_same, abs_div, abs_of_pos hbpos,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ (cyc blen (bdig (primeLambertAtBase 4)) v i : ℝ)
        - (goodCount i (primeLambertAtBase 4) v : ℝ)),
      div_le_div_iff₀ hbpos hkpos, hblen]
    nlinarith [hwpos, hkpos]
  have hsum := hseam.add hmain
  rw [zero_add] at hsum
  refine hsum.congr fun i => ?_
  ring

/-! ### The normal real -/

/-- The digit sequence of the assembled real: `G₄`'s digits read along the sampled positions,
block after block, each block repeated. -/
noncomputable def sampleDigits (x : ℝ) : ℕ → ℕ := seq blen (bdig x)

/-- **The headline of rung 2+3.**  `G₄`'s binary digits, read along the arithmetic sample of
the base-four schedule and assembled block-by-block with repetitions, form a **normal
sequence**.

This is NOT a claim about the normality of `G₄`: the digits are `G₄`'s, the sequence they are
assembled into is a different object. -/
theorem isNormalSequence_sampleDigits :
    IsNormalSequence 2 (sampleDigits (primeLambertAtBase 4)) := by
  refine isNormalSequence_seq (le_refl 2) blen (bdig (primeLambertAtBase 4))
    blen_pos (fun i j => bdig_lt _ i j) tendsto_blen_atTop ?_
  intro v hv hvb
  have hlen : 0 < v.length := List.length_pos_iff.2 hv
  have hv2 : ∀ j, ∀ h : j < v.length, v[j] < 2 := fun j h => hvb _ (List.getElem_mem h)
  simpa [one_div] using tendsto_cyc_div_blen v hlen hv2

/-- **The normal real.**  `realOfDigits 2` of the sampled digit sequence is normal in base 2. -/
theorem isNormal_sampleReal :
    IsNormal 2 (realOfDigits 2 (sampleDigits (primeLambertAtBase 4))) := by
  refine isNormal_realOfDigits_seq (le_refl 2) blen (bdig (primeLambertAtBase 4))
    blen_pos (fun i j => bdig_lt _ i j) tendsto_blen_atTop ?_
  intro v hv hvb
  have hlen : 0 < v.length := List.length_pos_iff.2 hv
  have hv2 : ∀ j, ∀ h : j < v.length, v[j] < 2 := fun j h => hvb _ (List.getElem_mem h)
  simpa [one_div] using tendsto_cyc_div_blen v hlen hv2

/-! ### The position map, free of `x` -/

/-- **The sampled position sequence**, defined from the base-four schedule alone — it does not
mention `G₄` or any other real.  `samplePos j` is the digit position whose digit sits at index
`j` of the assembled sequence. -/
noncomputable def samplePos (j : ℕ) : ℕ :=
  samplePosIn (grp blen j) ((j - Tacc blen (grp blen j)) % blen (grp blen j))

/-- The assembled sequence *is* `x`'s digits read along `samplePos`. -/
lemma sampleDigits_eq (x : ℝ) (j : ℕ) :
    sampleDigits x j = digitOf 2 (Int.fract x) (samplePos j) := rfl

lemma nthP_mem (i a : ℕ) : nthP i a ∈ PK i := by
  unfold nthP
  exact Finset.coe_mem _

/-- Every value of `samplePos` is a genuine sampled position of the schedule: the `p`-th digit
of the `m_i`-bit window opened at `2·kIdx(n,α)` for a sample time `n ∈ P_i` and an atom `α`. -/
theorem samplePos_spec (j : ℕ) :
    ∃ i n α p, n ∈ PK i ∧ p < kk i ∧
      samplePos j = 2 * kIdx (gridAt i) n α + p := by
  set i := grp blen j with hi
  set r := (j - Tacc blen (grp blen j)) % blen (grp blen j) with hr
  refine ⟨i, nthP i (r / kk i / Fintype.card (gridAt i).Atom),
    nthA i (r / kk i % Fintype.card (gridAt i).Atom), r % kk i,
    nthP_mem _ _, Nat.mod_lt _ (kk_pos i), ?_⟩
  unfold samplePos samplePosIn wpos
  rfl

/-- **The headline, in the position language.**  There is an `x`-independent sequence of sampled
digit positions along which `G₄`'s binary digits form a normal sequence. -/
theorem isNormalSequence_digits_along_samplePos :
    IsNormalSequence 2
      (fun j => digitOf 2 (Int.fract (primeLambertAtBase 4)) (samplePos j)) := by
  have hfun : (fun j => digitOf 2 (Int.fract (primeLambertAtBase 4)) (samplePos j))
      = sampleDigits (primeLambertAtBase 4) := by
    funext j
    exact (sampleDigits_eq _ j).symm
  rw [hfun]
  exact isNormalSequence_sampleDigits

/-- **The normal real, in the position language.** -/
theorem isNormal_realOfDigits_samplePos :
    IsNormal 2 (realOfDigits 2
      (fun j => digitOf 2 (Int.fract (primeLambertAtBase 4)) (samplePos j))) := by
  have hfun : (fun j => digitOf 2 (Int.fract (primeLambertAtBase 4)) (samplePos j))
      = sampleDigits (primeLambertAtBase 4) := by
    funext j
    exact (sampleDigits_eq _ j).symm
  rw [hfun]
  exact isNormal_sampleReal

/-! ### The headline in the repo's audited vocabulary -/

/-- The assembled real is **disjunctive** in base 2: every finite binary word occurs in it.
(Through the audited `IsNormal.isDisjunctive`, which is the predicate `isDisjunctive_two` is
stated in.) -/
theorem isDisjunctive_sampleReal :
    IsDisjunctive 2 (realOfDigits 2
      (fun j => digitOf 2 (Int.fract (primeLambertAtBase 4)) (samplePos j))) :=
  isNormal_realOfDigits_samplePos.isDisjunctive (le_refl 2)

/-- Hence the assembled real is irrational. -/
theorem irrational_sampleReal :
    Irrational (realOfDigits 2
      (fun j => digitOf 2 (Int.fract (primeLambertAtBase 4)) (samplePos j))) :=
  isDisjunctive_sampleReal.irrational

end NormalNumbers.G4.Sched
