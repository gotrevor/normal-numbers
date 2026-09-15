/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandHead
import NormalNumbers.G4EntropyMTowerAssembly

/-!
# The **wide** band: scale range `[Xlo (KK i), Xlo (KK (i+1))]`

`G4EntropyBandTrunc` certifies the band's truncations at every `X' ∈ [Xlo (KK i), X (KK i)]`,
and `G4EntropyBandHead` raises the band floor to `bandLoH i = 2·Xlo (KK i)` so that *every*
mid-band cutoff is above the certificate floor.  What that leaves is the **head ratio problem**:
at a cutoff `X'` just above the floor `wFloor i = gridDm·bandLoH i` the visited part of the
sample is a vanishing fraction of the certified truncation `PKtr i X'`, so the restriction price
is unpayable — and the head is *not* absorbable by the trivial bound, because band `i`'s floor
`≈ Xlo (KK i) = 2^{50·2^{m_i}}` already contains `2^{48·2^{m_i}}` sample times while the previous
band, topping out at `X (KK (i−1))`, contains only `2^{98·2^{m_{i−1}}}` — a tower fewer.

**The fix is to widen the previous band, not to lower the floor.**  `entropy_E1_tile` certifies
grid level `KK i` at *every* outer scale in `[Xlo (KK i), Xlo (KK (i+1))]`, so band `i` may run
all the way up to `Xlo (KK (i+1))` instead of stopping at `X (KK i) = Xlo (KK i)²`.  Then the
scale ranges of consecutive bands **tile**, and band `i+1`'s uncertifiable head, of scale
`≲ 8·gridDm_{i+1}·Xlo (KK (i+1))`, is compared against band `i`'s *full* length, of scale
`≈ Xlo (KK (i+1))`.  The ratio is

  `8·gridDm_{i+1}·(|Atom_{i+1}|·kk_{i+1}/P₀^{(i+1)}) / (|Atom_i|·kk_i/P₀^{(i)})
      ≈ 2^{2·2^{21·KK_{i+1}²}} · 2^{−2·2^{m_{i+1}}}`,

which is astronomically small because `m ≥ K³ ≫ 21K²`: the denser lower band drowns the sparser
upper band's head.  That is the content of `head_frac_tiny` downstream.

This module builds the wide band and its certified capture bound.  Nothing here changes
`bandT`, `bandTtr` or `fullReal`.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### E1 at every scale of the tile -/

/-- **`entropy_E1_tile` at family index `i`.**  The joint law of the truncated sample carries all
but `50√K` bits per window, at every `X' ∈ [Xlo (KK i), Xlo (KK (i+1))]` — the *whole* tile, not
just up to `X (KK i)`. -/
theorem deficit_primeLambertFour_wide (i X' : ℕ) (hlo : Xlo (KK i) ≤ X')
    (hhi : X' ≤ Xlo (KK (i + 1))) :
    ((kk i : ℝ) - 50 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (jointLaw (gridAt i) (b₀_lt_of_Xlo_le_at hlo) (kk i) (primeLambertAtBase 4)).H₂ := by
  have hhi' : X' ≤ Xlo (KK i + 4) := by rwa [← KK_succ i]
  have hE1 := entropy_E1_tile (K := KK i) (k₄ := kk i) (X' := X') rfl (KK_ge i) hlo hhi'
    (b₀_lt_of_Xlo_le_at hlo)
  refine le_trans (le_of_eq ?_) hE1.le
  rw [card_Atom_gridAt]
  ring

/-! ### The wide band and its truncations -/

/-- The wide band's **position** floor, `4·Xlo (KK i)`: four times the certificate floor, so that
it also clears the previous band's position ceiling `2·Xlo (KK i) + kk (i−1)`. -/
noncomputable def wLo (i : ℕ) : ℕ := 4 * Xlo (KK i)

/-- The wide band's `n`-floor: `gridDm · wLo i`.  Every sample time of the band is at least this,
which puts every atom's window start above `wLo i`. -/
noncomputable def wFloor (i : ℕ) : ℕ := gridDm (KK i) (N (KK i)) * wLo i

lemma Xlo_le_wFloor (i : ℕ) : Xlo (KK i) ≤ wFloor i := by
  show Xlo (KK i) ≤ gridDm (KK i) (N (KK i)) * wLo i
  have hDm : 1 ≤ gridDm (KK i) (N (KK i)) := gridDm_pos _ _
  have hb : wLo i = 4 * Xlo (KK i) := rfl
  have : wLo i ≤ gridDm (KK i) (N (KK i)) * wLo i := Nat.le_mul_of_pos_left _ hDm
  omega

/-- `Xlo K² = X K`: the downward floor is the square root of the scale. -/
lemma Xlo_sq (K : ℕ) : Xlo K * Xlo K = X K := by
  show (Y K ^ 50) * (Y K ^ 50) = 2 ^ (100 * 2 ^ m K)
  rw [← pow_add]
  show (2 ^ (2 ^ m K)) ^ (100 : ℕ) = _
  rw [← pow_mul]
  ring_nf

/-- The wide band's **scale top**: the top of level `i`'s own certified tile. -/
noncomputable def wTop (i : ℕ) : ℕ := Xlo (KK (i + 1))

/-- `18·X (KK i) ≤ wTop i`.  The whole of level `i`'s old scale range, inflated by a constant,
is still far below the top of its tile — the exponents are `100·2^{m_i}` against
`50·2^{m_{i+1}} ≥ 6400·2^{m_i}`. -/
lemma eighteen_X_le_wTop (i : ℕ) : 18 * X (KK i) ≤ wTop i := by
  have hstep := m_step_seven i
  have hone : (1 : ℕ) ≤ 2 ^ m (KK i) := Nat.one_le_two_pow
  have h128 : (2 : ℕ) ^ 7 * 2 ^ m (KK i) ≤ 2 ^ m (KK (i + 1)) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h27 : (2 : ℕ) ^ 7 = 128 := by norm_num
  have hX : X (KK i) = 2 ^ (100 * 2 ^ m (KK i)) := rfl
  have hXlo : wTop i = 2 ^ (50 * 2 ^ m (KK (i + 1))) := by
    show (2 ^ (2 ^ m (KK (i + 1)))) ^ 50 = _
    rw [← pow_mul]; ring_nf
  have h18 : (18 : ℕ) ≤ 2 ^ 5 := by norm_num
  have hmain : 2 ^ 5 * X (KK i) ≤ wTop i := by
    rw [hX, hXlo, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 18 * X (KK i) ≤ 2 ^ 5 * X (KK i) := Nat.mul_le_mul_right _ h18
    _ ≤ wTop i := hmain

/-- **The tile tops grow super-quadratically.**  `wTop (i+1)` dwarfs `wTop i²` by the factor
that carries `|Atom|·kk` — exponents `100·2^{m_{i+1}}` against `50·2^{m_{i+2}} ≥ 6400·2^{m_{i+1}}`.
-/
lemma wTop_growth (i : ℕ) :
    2 ^ (KK i ^ 3 + 2 * KK i + 1) * wTop i * wTop i ≤ wTop (i + 1) := by
  have hstep1 := m_step_seven (i + 1)
  have hstep0 := m_step_seven i
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by have := KK_ge i; omega)
    unfold m
    omega
  have hKcube : KK i ≤ KK i ^ 3 := Nat.le_self_pow (by norm_num) _
  have hlt1 : m (KK (i + 1)) < 2 ^ m (KK (i + 1)) := Nat.lt_two_pow_self
  have hone : (1 : ℕ) ≤ 2 ^ m (KK (i + 1)) := Nat.one_le_two_pow
  have h128 : (2 : ℕ) ^ 7 * 2 ^ m (KK (i + 1)) ≤ 2 ^ m (KK (i + 1 + 1)) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h27 : (2 : ℕ) ^ 7 = 128 := by norm_num
  have hw1 : wTop i = 2 ^ (50 * 2 ^ m (KK (i + 1))) := by
    show (2 ^ (2 ^ m (KK (i + 1)))) ^ 50 = _
    rw [← pow_mul]; ring_nf
  have hw2 : wTop (i + 1) = 2 ^ (50 * 2 ^ m (KK (i + 1 + 1))) := by
    show (2 ^ (2 ^ m (KK (i + 1 + 1)))) ^ 50 = _
    rw [← pow_mul]; ring_nf
  rw [hw1, hw2, ← pow_add, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The gate holds at the band's own top**, with room to spare. -/
theorem wgate_wTop (i : ℕ) : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ wTop i := by
  have hDm : gridDm (KK i) (N (KK i)) ≤ Xlo (KK i) := gridDm_le_Xlo (KK_hundred i)
  have hP : 2 * (gridAt i).P₀ ≤ Xlo (KK i) := two_mul_P₀_le_Xlo (KK_hundred i)
  have hsq : Xlo (KK i) * Xlo (KK i) = X (KK i) := Xlo_sq (KK i)
  have hXle : Xlo (KK i) ≤ X (KK i) := Xlo_le_X (KK i)
  have hwf : wFloor i = gridDm (KK i) (N (KK i)) * (4 * Xlo (KK i)) := rfl
  have hmono : gridDm (KK i) (N (KK i)) * (4 * Xlo (KK i)) ≤ Xlo (KK i) * (4 * Xlo (KK i)) :=
    Nat.mul_le_mul_right _ hDm
  have hexp : Xlo (KK i) * (4 * Xlo (KK i)) = 4 * X (KK i) := by
    rw [← hsq]; ring
  have h18 := eighteen_X_le_wTop i
  omega

lemma wLo_eq (i : ℕ) : wLo i = 4 * Xlo (KK i) := rfl

lemma wFloor_eq (i : ℕ) : wFloor i = gridDm (KK i) (N (KK i)) * wLo i := rfl

lemma wTop_eq (i : ℕ) : wTop i = Xlo (KK (i + 1)) := rfl

/-- The window length is negligible against the certificate floor. -/
lemma kk_lt_Xlo (i : ℕ) : kk i + 1 ≤ Xlo (KK i) := by
  have hK1 : 1 ≤ KK i := KK_one_le i
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by omega)
    unfold m
    omega
  have hkkK : kk i ≤ KK i := by unfold KK; omega
  have hpow : KK i ≤ KK i ^ 3 := Nat.le_self_pow (by norm_num) _
  have hm : m (KK i) < 2 ^ m (KK i) := Nat.lt_two_pow_self
  have hone : (1 : ℕ) ≤ 2 ^ m (KK i) := Nat.one_le_two_pow
  have hbig : 50 * 2 ^ m (KK i) < 2 ^ (50 * 2 ^ m (KK i)) := Nat.lt_two_pow_self
  have hXlo : Xlo (KK i) = 2 ^ (50 * 2 ^ m (KK i)) := by
    show (2 ^ (2 ^ m (KK i))) ^ 50 = _
    rw [← pow_mul]; ring_nf
  omega

/-- The wide band's **position ceiling**: every window of band `i` ends below it. -/
noncomputable def wPosTop (i : ℕ) : ℕ := 2 * wTop i + kk i

/-- **The bands' position ranges stay ordered.**  This is where the floor multiple `4` (rather
than `2`) is spent: `wLo (i+1) = 4·Xlo (KK (i+1))` clears `wPosTop i = 2·Xlo (KK (i+1)) + kk i`
with a whole `Xlo` to spare. -/
theorem wPosTop_le_wLo_succ (i : ℕ) : wPosTop i ≤ wLo (i + 1) := by
  have h : kk (i + 1) + 1 ≤ Xlo (KK (i + 1)) := kk_lt_Xlo (i + 1)
  have hkk : kk i ≤ kk (i + 1) := by unfold kk; omega
  have h1 : wPosTop i = 2 * Xlo (KK (i + 1)) + kk i := rfl
  have h2 : wLo (i + 1) = 4 * Xlo (KK (i + 1)) := rfl
  omega

lemma wPosTop_eq (i : ℕ) : wPosTop i = 2 * wTop i + kk i := rfl

attribute [local irreducible] Xlo
attribute [irreducible] wLo wFloor wTop wPosTop

open Classical in
/-- The wide band, truncated at the outer scale `X'`: the truncated sample above the raised
floor.  Unlike `bandTtr`, this is **not** tied to the scale `X (KK i)`; `X'` may run all the way
to `Xlo (KK (i+1))`. -/
noncomputable def bandWtr (i X' : ℕ) : Finset ℕ :=
  (PKtr i X').filter (fun n => wFloor i ≤ n)

lemma bandWtr_subset (i X' : ℕ) : bandWtr i X' ⊆ PKtr i X' := Finset.filter_subset _ _

/-! **The gate** is the hypothesis `4·wFloor i + 4·P₀ ≤ X'`, written out at each use (never as a
`def`: a `Prop`-valued abbreviation for it sits in the local context of every downstream proof and
sends `whnf` into the schedule's tower terms). -/

lemma Xlo_le_of_wgate {i X' : ℕ} (h : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') :
    Xlo (KK i) ≤ X' := by
  have := Xlo_le_wFloor i
  omega

lemma two_P₀_le_of_wgate {i X' : ℕ} (h : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') :
    2 * (gridAt i).P₀ ≤ X' := by omega

/-- **The wide band keeps at least half of the truncated sample**, at every cutoff above the
gate.  Same count as `card_bandTtr_ge`, with `M = wFloor i` in place of `3·Dm·X (KK (i−1))`. -/
theorem card_bandWtr_ge (i X' : ℕ) (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') :
    ((PKtr i X').card : ℝ) ≤ 2 * ((bandWtr i X').card : ℝ) := by
  classical
  have hP₀pos : 0 < (gridAt i).P₀ := (gridAt i).P₀_pos
  have hP₀R : (0 : ℝ) < ((gridAt i).P₀ : ℝ) := by exact_mod_cast hP₀pos
  set M : ℕ := wFloor i with hM
  have hdrop : (PKtr i X').filter (fun n => ¬ M ≤ n)
      ⊆ (PKtr i X').filter (fun n => n < M) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, by have := hn.2; omega⟩
  have hcount : (((PKtr i X').filter (fun n => n < M)).card : ℝ)
      ≤ (M : ℝ) / ((gridAt i).P₀ : ℝ) + 1 := by
    have h := card_filter_lt_apSample_le X' (gridAt i).P₀ (gridAt i).b₀ M hP₀pos
    have hR : ((((PKtr i X').filter (fun n => n < M)).card : ℕ) : ℝ)
        ≤ ((M / (gridAt i).P₀ + 1 : ℕ) : ℝ) := by exact_mod_cast h
    refine hR.trans ?_
    push_cast
    have : ((M / (gridAt i).P₀ : ℕ) : ℝ) ≤ (M : ℝ) / ((gridAt i).P₀ : ℝ) := Nat.cast_div_le
    linarith
  have hbig : (X' : ℝ) / (2 * ((gridAt i).P₀ : ℝ)) ≤ ((PKtr i X').card : ℝ) :=
    card_apSample_ge_half X' (gridAt i).P₀ (gridAt i).b₀ hP₀pos (gridAt i).b₀_lt_P₀
      (two_P₀_le_of_wgate hg)
  have hgateR : (4 : ℝ) * (M : ℝ) + 4 * ((gridAt i).P₀ : ℝ) ≤ (X' : ℝ) := by
    have h' : ((4 * M + 4 * (gridAt i).P₀ : ℕ) : ℝ) ≤ (X' : ℝ) := Nat.cast_le.2 hg
    push_cast at h'
    linarith
  have hhalf : 2 * ((M : ℝ) / ((gridAt i).P₀ : ℝ) + 1) ≤ ((PKtr i X').card : ℝ) := by
    refine le_trans ?_ hbig
    rw [le_div_iff₀ (show (0:ℝ) < 2 * ((gridAt i).P₀ : ℝ) by linarith)]
    have hexp : 2 * ((M : ℝ) / ((gridAt i).P₀ : ℝ) + 1) * (2 * ((gridAt i).P₀ : ℝ))
        = 4 * (M : ℝ) + 4 * ((gridAt i).P₀ : ℝ) := by
      field_simp
      ring
    rw [hexp]
    linarith
  have hsplit : ((PKtr i X').card : ℝ)
      = ((bandWtr i X').card : ℝ)
        + (((PKtr i X').filter (fun n => ¬ M ≤ n)).card : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := PKtr i X') (p := fun n => M ≤ n)
    have hb : bandWtr i X' = (PKtr i X').filter (fun n => M ≤ n) := rfl
    rw [hb, ← h]
    push_cast
    ring
  have hdropR : ((((PKtr i X').filter (fun n => ¬ M ≤ n)).card : ℕ) : ℝ)
      ≤ (((PKtr i X').filter (fun n => n < M)).card : ℝ) :=
    Nat.cast_le.2 (Finset.card_le_card hdrop)
  linarith

lemma bandWtr_nonempty {i X' : ℕ} (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') : (bandWtr i X').Nonempty := by
  classical
  rw [← Finset.card_pos]
  have h := card_bandWtr_ge i X' hg
  have hP : (0 : ℝ) < ((PKtr i X').card : ℝ) := by
    have := Finset.card_pos.2 (PKtr_nonempty (Xlo_le_of_wgate hg))
    exact_mod_cast this
  have : (0 : ℝ) < ((bandWtr i X').card : ℝ) := by linarith
  exact_mod_cast this

/-! ### The certified wide band law -/

open Classical in
/-- The joint window law of the wide band's sample times below the outer scale `X'`. -/
noncomputable def bandWLaw (i X' : ℕ) (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') (x : ℝ) :
    FinLaw ((gridAt i).Atom → Fin (2 ^ kk i)) :=
  empirical (bandWtr i X') (bandWtr_nonempty hg) (ZVec (gridAt i) (kk i) x)

set_option maxHeartbeats 1000000 in
/-- **The wide band keeps the joint certification**, with the same `101√K` per-window deficit as
`H₂_bandTLawTr_ge`, now at every cutoff of the *whole tile*. -/
theorem H₂_bandWLaw_ge (i X' : ℕ) (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') (hhi : X' ≤ Xlo (KK (i + 1))) :
    ((kk i : ℝ) - 101 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (bandWLaw i X' hg (primeLambertAtBase 4)).H₂ := by
  classical
  have hlo : Xlo (KK i) ≤ X' := Xlo_le_of_wgate hg
  have hApos : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
    have : 0 < Fintype.card (gridAt i).Atom := Fintype.card_pos
    exact_mod_cast this
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS400 : (400 : ℝ) ≤ Real.sqrt ((KK i : ℕ) : ℝ) := by
    have h : (160000 : ℝ) ≤ ((KK i : ℕ) : ℝ) := by exact_mod_cast KK_ge i
    have h2 : Real.sqrt (160000 : ℝ) ≤ Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_le_sqrt h
    have h400 : Real.sqrt (160000 : ℝ) = 400 := by
      rw [show (160000 : ℝ) = 400 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h400 ▸ h2]
  have hA1 : (1 : ℝ) ≤ (Fintype.card (gridAt i).Atom : ℝ) := by
    have : 1 ≤ Fintype.card (gridAt i).Atom := Fintype.card_pos
    exact_mod_cast this
  have hfull : ((kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
      - 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ))
      ≤ (empirical (PKtr i X') (PKtr_nonempty hlo)
          (ZVec (gridAt i) (kk i) (primeLambertAtBase 4))).H₂ := by
    have h := deficit_primeLambertFour_wide i X' hlo hhi
    have hlaw : jointLaw (gridAt i) (b₀_lt_of_Xlo_le_at hlo) (kk i) (primeLambertAtBase 4)
        = empirical (PKtr i X') (PKtr_nonempty hlo)
            (ZVec (gridAt i) (kk i) (primeLambertAtBase 4)) := rfl
    rw [hlaw] at h
    linarith [h, sub_mul (kk i : ℝ) (50 * Real.sqrt (KK i))
      (Fintype.card (gridAt i).Atom : ℝ)]
  have hrest := H₂_empirical_restrict_ge (PKtr_nonempty hlo) (bandWtr_nonempty hg)
    (bandWtr_subset i X') (ZVec (gridAt i) (kk i) (primeLambertAtBase 4))
    (M := (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ))
    (δ := 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ))
    (fun T hT => H₂_vector_le i T hT _) hfull
  have hPpos : (0 : ℝ) < ((PKtr i X').card : ℝ) := by
    have := Finset.card_pos.2 (PKtr_nonempty hlo)
    exact_mod_cast this
  have hTpos : (0 : ℝ) < ((bandWtr i X').card : ℝ) := by
    have := Finset.card_pos.2 (bandWtr_nonempty hg)
    exact_mod_cast this
  have hσ : (1 : ℝ) / 2 ≤ ((bandWtr i X').card : ℝ) / ((PKtr i X').card : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num) hPpos]
    linarith [card_bandWtr_ge i X' hg]
  have hδpos : (0 : ℝ) < 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1 := by
    have := Real.sqrt_pos.2 hKpos
    positivity
  have hcost : (50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1)
      / (((bandWtr i X').card : ℝ) / ((PKtr i X').card : ℝ))
      ≤ 2 * (50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (1 : ℝ) ≤ 2 * (((bandWtr i X').card : ℝ) / ((PKtr i X').card : ℝ)) := by linarith
    nlinarith [hδpos, h2]
  have hlaw2 : bandWLaw i X' hg (primeLambertAtBase 4)
      = empirical (bandWtr i X') (bandWtr_nonempty hg)
          (ZVec (gridAt i) (kk i) (primeLambertAtBase 4)) := rfl
  rw [hlaw2]
  have hfin : (2 : ℝ) ≤ Real.sqrt ((KK i : ℕ) : ℝ) * (Fintype.card (gridAt i).Atom : ℝ) := by
    nlinarith [hS400, hA1]
  have hexp : ((kk i : ℝ) - 101 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      = (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
        - 101 * (Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ)) := by ring
  rw [hexp]
  linarith [hrest, hcost, hfin]

set_option maxHeartbeats 1000000 in
/-- **The wide band's capture bound.**  Every `ℓ`-word's frequency over the `(n, α, p)` triples
of the wide band below `X'` is within `2√(808 log 2·ℓ/√K)` of `2^{−ℓ}`, at **every** cutoff of
the tile `[Xlo (KK i), Xlo (KK (i+1))]` above the gate. -/
theorem abs_posAvg_bandWLaw_le (i X' ℓ : ℕ) (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') (hhi : X' ≤ Xlo (KK (i + 1)))
    (hℓ : 0 < ℓ) (hℓm : 2 * ℓ ≤ kk i) (w : Fin (2 ^ ℓ)) :
    |posAvg (kk i) ℓ (bandWLaw i X' hg (primeLambertAtBase 4)) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (808 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : 0 < Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_pos.2 hKpos
  have hδ : (0 : ℝ) < 101 * Real.sqrt (KK i) := by linarith [hS0]
  have hmain := abs_posAvg_sub_le hℓ (by omega)
    (bandWLaw i X' hg (primeLambertAtBase 4)) w hδ (H₂_bandWLaw_ge i X' hg hhi)
  refine hmain.trans ?_
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hhalf : (kk i : ℝ) / 2 ≤ (kk i : ℝ) - ℓ + 1 := by
    have : (2 : ℝ) * ℓ ≤ (kk i : ℝ) := by exact_mod_cast hℓm
    linarith
  have hden : (0 : ℝ) < (kk i : ℝ) - ℓ + 1 := by
    have : (2 : ℝ) * ℓ ≤ (kk i : ℝ) := by exact_mod_cast hℓm
    linarith
  have hkk4 : (KK i : ℝ) = 4 * (kk i : ℝ) := by unfold KK; push_cast; ring
  have hsq : Real.sqrt ((KK i : ℕ) : ℝ) * Real.sqrt ((KK i : ℕ) : ℝ) = 4 * (kk i : ℝ) := by
    rw [Real.mul_self_sqrt hKpos.le, hkk4]
  have hstep : Real.log 2 * (ℓ : ℝ) * (101 * Real.sqrt (KK i)) / ((kk i : ℝ) - ℓ + 1)
      ≤ 808 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i) := by
    rw [div_le_div_iff₀ hden hS0]
    have hkey : Real.log 2 * (ℓ : ℝ) * (101 * Real.sqrt (KK i)) * Real.sqrt ((KK i : ℕ) : ℝ)
        = 404 * Real.log 2 * (ℓ : ℝ) * (kk i : ℝ) := by
      linear_combination (101 * Real.log 2 * (ℓ : ℝ)) * hsq
    rw [hkey]
    have hc : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * (kk i : ℝ) := by positivity
    have hstep2 := mul_le_mul_of_nonneg_left hhalf
      (by positivity : (0:ℝ) ≤ 808 * Real.log 2 * (ℓ : ℝ))
    linarith [hc, hstep2]
  have hpos1 : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * (101 * Real.sqrt (KK i))
      / ((kk i : ℝ) - ℓ + 1) := by positivity
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by norm_num)

/-! ### The wide band's geometry -/

/-- **The wide band**: the whole tile's sample above the floor. -/
noncomputable def bandW (i : ℕ) : Finset ℕ := bandWtr i (wTop i)

lemma bandW_subset (i : ℕ) : bandW i ⊆ PKtr i (wTop i) := bandWtr_subset i (wTop i)

lemma mem_bandWtr_lt {i X' n : ℕ} (hn : n ∈ bandWtr i X') : n < X' := by
  classical
  have h := (Finset.mem_filter.1 hn).1
  rw [PKtr, apSample, Finset.mem_filter, Finset.mem_range] at h
  exact h.1

lemma wFloor_le_of_mem_bandWtr {i X' n : ℕ} (hn : n ∈ bandWtr i X') : wFloor i ≤ n := by
  classical
  exact (Finset.mem_filter.1 hn).2

/-- **Every window of the wide band starts above the position floor.** -/
theorem wLo_le_pos_of_mem_bandWtr (i X' : ℕ) {n : ℕ} (hn : n ∈ bandWtr i X')
    (α : (gridAt i).Atom) : wLo i ≤ 2 * kIdx (gridAt i) n α := by
  classical
  have hmem : gridDm (KK i) (N (KK i)) * wLo i ≤ n := by
    rw [← wFloor_eq]; exact wFloor_le_of_mem_bandWtr hn
  have hnPK : n ∈ PKtr i X' := (Finset.mem_filter.1 hn).1
  obtain ⟨hk, -⟩ := kIdx_spec (gridAt i) (X := X') hnPK α
  have hd : (gridAt i).d α ≤ gridDm (KK i) (N (KK i)) :=
    gridOf.d_le (K := KK i) (N := N (KK i)) (hK := KK_one_le i) α
  have hdpos : 0 < (gridAt i).d α := (gridAt i).d_pos α
  have ht : (gridAt i).t α < (gridAt i).d α := (gridAt i).t_lt_d α
  have hmono : (gridAt i).d α * wLo i ≤ gridDm (KK i) (N (KK i)) * wLo i :=
    Nat.mul_le_mul_right _ hd
  have h1 : (gridAt i).d α * wLo i ≤ n := le_trans hmono hmem
  have h2 : n < (gridAt i).d α * (kIdx (gridAt i) n α + 1) := by
    have hexp : (gridAt i).d α * (kIdx (gridAt i) n α + 1)
        = (gridAt i).d α * kIdx (gridAt i) n α + (gridAt i).d α := by ring
    omega
  have hstrict : (gridAt i).d α * wLo i
      < (gridAt i).d α * (kIdx (gridAt i) n α + 1) := by omega
  have hlt : wLo i < kIdx (gridAt i) n α + 1 :=
    lt_of_mul_lt_mul_left hstrict (Nat.zero_le _)
  omega

/-- **Every window of the wide band ends below the position ceiling.** -/
theorem pos_lt_wPosTop (i X' : ℕ) (hX : X' ≤ wTop i) {n : ℕ} (hn : n ∈ PKtr i X')
    (α : (gridAt i).Atom) {p : ℕ} (hp : p < kk i) :
    2 * kIdx (gridAt i) n α + p < wPosTop i := by
  classical
  have hnX : n < X' := by
    rw [PKtr, apSample, Finset.mem_filter, Finset.mem_range] at hn
    exact hn.1
  have hk := kIdx_le_self (gridAt i) n α
  have hpt := wPosTop_eq i
  omega

/-- **`windows_eq_or_disjoint` at a truncated scale.**  The proof of `windows_eq_or_disjoint`
uses the sample only through `kIdx_congr_Q`, which is generic in the outer scale. -/
theorem windows_eq_or_disjoint_at (i X' : ℕ) {n n' : ℕ} (hn : n ∈ PKtr i X')
    (hn' : n' ∈ PKtr i X') (α β : (gridAt i).Atom) :
    kIdx (gridAt i) n α = kIdx (gridAt i) n' β ∨
      2 * kIdx (gridAt i) n α + kk i ≤ 2 * kIdx (gridAt i) n' β ∨
      2 * kIdx (gridAt i) n' β + kk i ≤ 2 * kIdx (gridAt i) n α := by
  have hcong := kIdx_congr_Q (gridAt i) (two_le_card_Atom i) (N_pos_gridAt i) hn hn' α β
  have hQ : kk i < (gridAt i).Q := by
    have hgt : gridUmax (KK i) (N (KK i)) + KK i + N (KK i) + 2
        ≤ gridQ (KK i) (N (KK i)) := gridQ_gt _ _
    have hQeq : (gridAt i).Q = gridQ (KK i) (N (KK i)) := rfl
    have hkkK : kk i ≤ KK i := by unfold KK; omega
    omega
  rcases Nat.lt_trichotomy (kIdx (gridAt i) n α) (kIdx (gridAt i) n' β) with h | h | h
  · right; left
    have hdvd : (gridAt i).Q ∣ kIdx (gridAt i) n' β - kIdx (gridAt i) n α :=
      (Nat.modEq_iff_dvd' (le_of_lt h)).1 hcong
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · exact Or.inl h
  · right; right
    have hdvd : (gridAt i).Q ∣ kIdx (gridAt i) n α - kIdx (gridAt i) n' β :=
      (Nat.modEq_iff_dvd' (le_of_lt h)).1 hcong.symm
    have := Nat.le_of_dvd (by omega) hdvd
    omega

lemma bandW_nonempty (i : ℕ) : (bandW i).Nonempty := bandWtr_nonempty (wgate_wTop i)

/-! ### The wide band's granularity wall -/

lemma card_PKtr_le (i X' : ℕ) : (PKtr i X').card ≤ X' := by
  have : PKtr i X' ⊆ Finset.range X' := by
    intro n hn
    rw [PKtr, apSample, Finset.mem_filter] at hn
    exact hn.1
  simpa using Finset.card_le_card this

/-- **The granularity wall for the wide bands.**  Everything band `i` produces — every atom,
every sample time, every digit of every window — is smaller than the number of sample times of
band `i+1`.  Same statement as `granule_exceeds_previous_scale`, at the tile tops. -/
theorem granuleW_exceeds_previous_scale (i : ℕ) :
    (Fintype.card (gridAt i).Atom : ℝ) * ((PKtr i (wTop i)).card : ℝ) * (kk i : ℝ)
      < ((PKtr (i + 1) (wTop (i + 1))).card : ℝ) := by
  have hP₀pos : 0 < (gridAt (i + 1)).P₀ := (gridAt (i + 1)).P₀_pos
  have h2P : 2 * (gridAt (i + 1)).P₀ ≤ wTop i := by
    have h := two_mul_P₀_le_Xlo (KK_hundred (i + 1))
    rw [wTop_eq]
    exact h
  -- the numerator, in ℕ
  have hAtom : Fintype.card (gridAt i).Atom ≤ 2 ^ (KK i ^ 3 + KK i) := card_Atom_le_two_pow i
  have hkk : kk i ≤ 2 ^ (KK i) := by
    have h1 : kk i ≤ KK i := by unfold KK; omega
    have h2 : KK i < 2 ^ KK i := Nat.lt_two_pow_self
    omega
  have hcard : (PKtr i (wTop i)).card ≤ wTop i := card_PKtr_le i (wTop i)
  have hnum : Fintype.card (gridAt i).Atom * (PKtr i (wTop i)).card * kk i
      * (2 * (gridAt (i + 1)).P₀) < wTop (i + 1) := by
    have hstep : Fintype.card (gridAt i).Atom * (PKtr i (wTop i)).card * kk i
        * (2 * (gridAt (i + 1)).P₀)
        ≤ 2 ^ (KK i ^ 3 + KK i) * wTop i * 2 ^ (KK i) * wTop i := by
      refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hAtom hcard) hkk) h2P
    have hgrow := wTop_growth i
    have hexp : 2 ^ (KK i ^ 3 + KK i) * wTop i * 2 ^ (KK i) * wTop i
        = 2 ^ (KK i ^ 3 + 2 * KK i) * wTop i * wTop i := by
      rw [show KK i ^ 3 + 2 * KK i = (KK i ^ 3 + KK i) + KK i by ring, pow_add]
      ring
    have hdouble : 2 ^ (KK i ^ 3 + 2 * KK i + 1) * wTop i * wTop i
        = 2 * (2 ^ (KK i ^ 3 + 2 * KK i) * wTop i * wTop i) := by
      rw [pow_succ]; ring
    have hTpos : 0 < wTop i := by
      have := Xlo_pos (KK (i + 1))
      rw [wTop_eq]; exact this
    have hprod : 0 < 2 ^ (KK i ^ 3 + 2 * KK i) * wTop i * wTop i := by positivity
    omega
  -- the denominator
  have hbig : (wTop (i + 1) : ℝ) / (2 * ((gridAt (i + 1)).P₀ : ℝ))
      ≤ ((PKtr (i + 1) (wTop (i + 1))).card : ℝ) :=
    card_apSample_ge_half (wTop (i + 1)) (gridAt (i + 1)).P₀ (gridAt (i + 1)).b₀ hP₀pos
      (gridAt (i + 1)).b₀_lt_P₀ (two_P₀_le_of_wgate (wgate_wTop (i + 1)))
  have hP₀R : (0 : ℝ) < ((gridAt (i + 1)).P₀ : ℝ) := by exact_mod_cast hP₀pos
  refine lt_of_lt_of_le ?_ hbig
  rw [lt_div_iff₀ (by linarith)]
  have hnumR : ((Fintype.card (gridAt i).Atom * (PKtr i (wTop i)).card * kk i
      * (2 * (gridAt (i + 1)).P₀) : ℕ) : ℝ) < ((wTop (i + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnum
  push_cast at hnumR
  linarith

/-! ### Same-atom window gaps at a truncated scale -/

lemma P₀_le_sub_of_mem_at (i X' : ℕ) {n n' : ℕ} (hn : n ∈ PKtr i X') (hn' : n' ∈ PKtr i X')
    (hlt : n < n') : (gridAt i).P₀ ≤ n' - n := by
  have h1 : n % (gridAt i).P₀ = (gridAt i).b₀ := (Finset.mem_filter.1 hn).2
  have h2 : n' % (gridAt i).P₀ = (gridAt i).b₀ := (Finset.mem_filter.1 hn').2
  have hdvd : (gridAt i).P₀ ∣ n' - n := by
    have : n ≡ n' [MOD (gridAt i).P₀] := by
      unfold Nat.ModEq
      rw [h1, h2]
    exact (Nat.modEq_iff_dvd' (le_of_lt hlt)).1 this
  exact Nat.le_of_dvd (by omega) hdvd

/-- `window_gap_same_atom` at a truncated scale. -/
theorem window_gap_same_atom_at (i X' : ℕ) (α : (gridAt i).Atom) {n n' : ℕ}
    (hn : n ∈ PKtr i X') (hn' : n' ∈ PKtr i X') (hlt : n < n') :
    2 * kIdx (gridAt i) n α + kk i ≤ 2 * kIdx (gridAt i) n' α := by
  have hd : 0 < (gridAt i).d α := (gridAt i).d_pos α
  obtain ⟨hk, -⟩ := kIdx_spec (gridAt i) (X := X') hn α
  obtain ⟨hk', -⟩ := kIdx_spec (gridAt i) (X := X') hn' α
  have hkle : kIdx (gridAt i) n α ≤ kIdx (gridAt i) n' α := by
    by_contra hcon
    push_neg at hcon
    have hmul : (gridAt i).d α * kIdx (gridAt i) n' α
        < (gridAt i).d α * kIdx (gridAt i) n α := (Nat.mul_lt_mul_left hd).mpr hcon
    omega
  have hsub : (gridAt i).d α * (kIdx (gridAt i) n' α - kIdx (gridAt i) n α) = n' - n := by
    rw [Nat.mul_sub]
    omega
  have hP₀ := P₀_le_sub_of_mem_at i X' hn hn' hlt
  have hMprod : (gridAt i).d α ^ 2 ≤ (gridAt i).Mprod :=
    Nat.le_of_dvd (gridAt i).Mprod_pos ((gridAt i).sq_d_dvd_Mprod α)
  have hP₀ge : (gridAt i).d α * (gridAt i).freezeQ ≤ (gridAt i).P₀ := by
    have h1 : (gridAt i).d α * (gridAt i).freezeQ
        ≤ (gridAt i).d α ^ 2 * (gridAt i).freezeQ := by
      have hsq : (gridAt i).d α ≤ (gridAt i).d α ^ 2 := Nat.le_self_pow (by norm_num) _
      exact Nat.mul_le_mul_right _ hsq
    calc (gridAt i).d α * (gridAt i).freezeQ
        ≤ (gridAt i).d α ^ 2 * (gridAt i).freezeQ := h1
      _ ≤ (gridAt i).Mprod * (gridAt i).freezeQ := Nat.mul_le_mul_right _ hMprod
      _ = (gridAt i).P₀ := rfl
  have hfq : kk i < (gridAt i).freezeQ :=
    lt_of_le_of_lt (kk_le_card_Idx i) (card_Idx_lt_freezeQ (gridAt i) (card_Idx_gridAt_pos i))
  have hgap : (gridAt i).d α * kk i
      ≤ (gridAt i).d α * (kIdx (gridAt i) n' α - kIdx (gridAt i) n α) := by
    rw [hsub]
    refine le_trans ?_ hP₀
    refine le_trans ?_ hP₀ge
    exact Nat.mul_le_mul_left _ (le_of_lt hfq)
  have hgap' : kk i ≤ kIdx (gridAt i) n' α - kIdx (gridAt i) n α :=
    le_of_mul_le_mul_left hgap hd
  omega

end NormalNumbers.G4.Sched
