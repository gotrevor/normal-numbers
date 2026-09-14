/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyJoint

/-!
# The joint (`t`-wise) sampled-word frequency theorem for `G₄`

`G4EntropyJoint` proved the abstract `t`-wise capacity bound: for an injective blocking
`blk : B → Fin t → A` the total deficit on the `ℓt`-bit *pattern* coordinates is bounded by the
**same** `Δ` that bounds the deficit of the whole joint law.  This module instantiates it at the
implemented base-four schedule and renders it on the binary digits of `G₄`.

* `blkSched` — the blocking: enumerate the atoms and cut into consecutive `t`-blocks.
* `patFreq` — the frequency of an `ℓt`-bit pattern over `(n, block, aligned position)`.
* `abs_patFreq_sub_le_of_deficit` / `abs_patFreq_sub_le_primeLambertFour` — the capacity bound,
  `2√(400 log 2 · ℓt/√K)` at `entropy_E1`'s `δ = 50√K`: the `t = 1` bound with `ℓ ↦ ℓt`.
* `tendsto_occursCountJoint_primeLambertFour` — **the endpoint.**  For every `t`, every `ℓ`, and
  all binary words `v₀,…,v_{t−1}` of length `ℓ`,

    `#{(n, b, j) : ∀ s, OccursAt 2 G₄ (v s) (2·kIdx(n, blkSched b s) + jℓ)} / (|P_K|·|B|·⌊m_K/ℓ⌋)`
      `→ 2^{−ℓt}`,

  i.e. the `t` sampled windows of a block **decorrelate**: a prescribed word at each of `t`
  prescribed sampled positions occurs with exactly the independent frequency.  Every previous
  result in this expedition is the case `t = 1`.

**This is not a normality claim.**  The sampled positions have density `≤ ½(3/K⁴)^K`; see
`REFLECTION-2026-09-14-entropy.md`.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The blocking at the schedule -/

/-- The number of complete `t`-blocks of atoms at scale `i`. -/
noncomputable def nblk (i t : ℕ) : ℕ := Fintype.card (gridAt i).Atom / t

lemma blkSched_lt {i t : ℕ} (b : Fin (nblk i t)) (s : Fin t) :
    (b : ℕ) * t + (s : ℕ) < Fintype.card (gridAt i).Atom := by
  have hb : (b : ℕ) < Fintype.card (gridAt i).Atom / t := b.isLt
  have hs : (s : ℕ) < t := s.isLt
  have h1 : ((b : ℕ) + 1) * t ≤ (Fintype.card (gridAt i).Atom / t) * t :=
    Nat.mul_le_mul_right t (by omega)
  have h2 : (Fintype.card (gridAt i).Atom / t) * t ≤ Fintype.card (gridAt i).Atom :=
    Nat.div_mul_le_self _ _
  have h3 : ((b : ℕ) + 1) * t = (b : ℕ) * t + t := by ring
  omega

/-- **The blocking.**  Enumerate the atoms and cut them into consecutive blocks of `t`. -/
noncomputable def blkSched (i t : ℕ) : Fin (nblk i t) → Fin t → (gridAt i).Atom :=
  fun b s => (Fintype.equivFin (gridAt i).Atom).symm ⟨(b : ℕ) * t + (s : ℕ), blkSched_lt b s⟩

/-- Distinct `(block, slot)` pairs name distinct atoms. -/
theorem blkSched_injective (i t : ℕ) :
    Function.Injective (fun p : Fin (nblk i t) × Fin t => blkSched i t p.1 p.2) := by
  rintro ⟨b, s⟩ ⟨b', s'⟩ h
  simp only [blkSched] at h
  have h1 : (b : ℕ) * t + (s : ℕ) = (b' : ℕ) * t + (s' : ℕ) :=
    congrArg Fin.val ((Fintype.equivFin (gridAt i).Atom).symm.injective h)
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have hs : (s : ℕ) = (s' : ℕ) := by
    have h2 := congrArg (· % t) h1
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt s'.isLt] using h2
  have hb : (b : ℕ) = (b' : ℕ) := by
    have : (b : ℕ) * t = (b' : ℕ) * t := by omega
    exact Nat.eq_of_mul_eq_mul_right ht this
  exact Prod.ext (Fin.ext hb) (Fin.ext hs)

/-- The atom set is at least as large as the scale. -/
lemma KK_le_card_Atom (i : ℕ) : KK i ≤ Fintype.card (gridAt i).Atom := by
  rw [card_Atom_gridAt i]
  have h1 : KK i ^ 2 + 1 ≤ (KK i ^ 2 + 1) ^ KK i :=
    Nat.le_self_pow (by have := KK_ge i; omega) _
  have h2 : KK i ≤ KK i ^ 2 + 1 := by nlinarith [KK_one_le i]
  omega

/-- There is at least one block once `t` atoms exist. -/
lemma nblk_pos {i t : ℕ} (ht : 0 < t) (hcard : t ≤ Fintype.card (gridAt i).Atom) :
    0 < nblk i t :=
  Nat.one_le_div_iff ht |>.2 hcard

/-! ### The pattern frequency -/

/-- **The frequency of an `ℓt`-bit pattern** over the triples `(n, block, aligned position)`:
the `j`-th aligned `ℓ`-block of each of the `t` windows of block `b`, packed. -/
noncomputable def patFreq (i ℓ t : ℕ) (x : ℝ) (w : Fin (2 ^ (ℓ * t))) : ℝ :=
  (∑ c : Fin (nblk i t) × Fin (kk i / ℓ),
      ((jointLawAt i x).map (patCoord (kk i) ℓ t (blkSched i t) c)).prob {w})
    / (Fintype.card (Fin (nblk i t) × Fin (kk i / ℓ)) : ℝ)

/-- **The `t`-wise capacity inequality at the schedule.**  A per-window deficit of `δ` bits
controls every `ℓt`-bit pattern to within `2√(2 log 2 · ℓ t δ/m_K)` — the `t = 1` bound
`abs_blockFreqT_sub_le_of_deficit` with `ℓ ↦ ℓt` (and a factor `2` for the atoms the blocking
leaves over). -/
theorem abs_patFreq_sub_le_of_deficit (i ℓ t : ℕ) (hℓ : 0 < ℓ) (hℓm : ℓ ≤ kk i) (ht : 0 < t)
    (hcard : 2 * t ≤ Fintype.card (gridAt i).Atom) (x : ℝ) (w : Fin (2 ^ (ℓ * t)))
    {δ : ℝ} (hδ : 0 < δ)
    (hdef : ((kk i : ℝ) - δ) * (Fintype.card (gridAt i).Atom : ℝ) ≤ (jointLawAt i x).H₂) :
    |patFreq i ℓ t x w - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * Real.sqrt (2 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) * δ / (kk i : ℝ)) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < Fintype.card (gridAt i).Atom := by omega
  have hnb : 0 < nblk i t := nblk_pos ht (by omega)
  haveI : Nonempty (Fin (nblk i t)) := Fin.pos_iff_nonempty.1 hnb
  have hk0 : (0 : ℝ) < (kk i : ℝ) := by
    have : 0 < kk i := by unfold kk; omega
    exact_mod_cast this
  have hCR : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by exact_mod_cast hC
  have hΔ0 : (0 : ℝ) < δ * (Fintype.card (gridAt i).Atom : ℝ) := by positivity
  have hΔ : (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
      - δ * (Fintype.card (gridAt i).Atom : ℝ) ≤ (jointLawAt i x).H₂ := by
    rw [← sub_mul]; exact hdef
  have hmain := abs_avg_patCoord_prob_opt (A := (gridAt i).Atom) (B := Fin (nblk i t))
    (m := kk i) (ℓ := ℓ) (t := t) hℓ hℓm ht (blkSched i t) (blkSched_injective i t)
    (jointLawAt i x) w hΔ0 hΔ
  have hN : (Fintype.card (Fin (nblk i t) × Fin (kk i / ℓ)) : ℝ)
      = (Fintype.card (Fin (nblk i t)) : ℝ) * ((kk i / ℓ : ℕ) : ℝ) := by
    simp [Fintype.card_prod]
  rw [hN] at hmain
  rw [patFreq, hN]
  refine (hmain.trans ?_)
  -- `|B| = ⌊C/t⌋ ≥ C/(2t)`, so `C/|B| ≤ 2t`
  have hcf : (Fintype.card (Fin (nblk i t)) : ℝ) = ((nblk i t : ℕ) : ℝ) := by
    rw [Fintype.card_fin]
  have hbR : (0 : ℝ) < ((nblk i t : ℕ) : ℝ) := by exact_mod_cast hnb
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hlb : (Fintype.card (gridAt i).Atom : ℝ) ≤ 2 * (t : ℝ) * ((nblk i t : ℕ) : ℝ) := by
    have hnat : Fintype.card (gridAt i).Atom ≤ 2 * t * nblk i t := by
      have h1 : t * nblk i t + Fintype.card (gridAt i).Atom % t
          = Fintype.card (gridAt i).Atom := by
        rw [nblk]; exact Nat.div_add_mod _ _
      have h2 : Fintype.card (gridAt i).Atom % t < t := Nat.mod_lt _ ht
      have h4 : t ≤ t * nblk i t := Nat.le_mul_of_pos_right t hnb
      have h5 : 2 * t * nblk i t = 2 * (t * nblk i t) := by ring
      omega
    exact_mod_cast hnat
  have hstep : Real.log 2 * (ℓ : ℝ) * (δ * (Fintype.card (gridAt i).Atom : ℝ))
      / ((Fintype.card (Fin (nblk i t)) : ℝ) * (kk i : ℝ))
      ≤ 2 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) * δ / (kk i : ℝ) := by
    rw [hcf, div_le_div_iff₀ (by positivity) hk0]
    have hkey : Real.log 2 * (ℓ : ℝ) * δ
        * ((Fintype.card (gridAt i).Atom : ℝ) - 2 * (t : ℝ) * ((nblk i t : ℕ) : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    nlinarith [hkey, hbR, hk0, htR, hlog2, hδ, hCR]
  have hpos1 : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * (δ * (Fintype.card (gridAt i).Atom : ℝ))
      / ((Fintype.card (Fin (nblk i t)) : ℝ) * (kk i : ℝ)) := by
    rw [hcf]; positivity
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by norm_num)

/-- **The `t`-wise capacity bound for `G₄`.**  `entropy_E1` supplies `δ = 50√K` and
`m_K = K/4`, so

    `|patFreq i ℓ t G₄ w − 2^{−ℓt}| ≤ 2√(400 log 2 · ℓ t/√K)`

for every `ℓ ≤ m_K` — exactly `abs_blockFreqT_sub_le_primeLambertFour` with `ℓ ↦ ℓt` and the
constant doubled. -/
theorem abs_patFreq_sub_le_primeLambertFour (i ℓ t : ℕ) (hℓ : 0 < ℓ) (hℓm : ℓ ≤ kk i)
    (ht : 0 < t) (hcard : 2 * t ≤ Fintype.card (gridAt i).Atom) (w : Fin (2 ^ (ℓ * t))) :
    |patFreq i ℓ t (primeLambertAtBase 4) w - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * Real.sqrt (400 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) / Real.sqrt (KK i)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : 0 < Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_pos.2 hKpos
  have hδ : (0 : ℝ) < 50 * Real.sqrt (KK i) := by positivity
  have hE1 := entropy_E1 (K := KK i) (k₄ := kk i) rfl (KK_ge i)
  have hcardA : (Fintype.card (gridAt i).Atom : ℝ) = (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ) := by
    rw [card_Atom_gridAt i]
  have hdef : ((kk i : ℝ) - 50 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (jointLawAt i (primeLambertAtBase 4)).H₂ := by
    rw [hcardA, sub_mul]
    exact hE1.le
  refine (abs_patFreq_sub_le_of_deficit i ℓ t hℓ hℓm ht hcard _ w hδ hdef).trans ?_
  have harg : 2 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) * (50 * Real.sqrt (KK i)) / (kk i : ℝ)
      = 400 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) / Real.sqrt (KK i) := by
    have hkk4 : (KK i : ℝ) = 4 * (kk i : ℝ) := by unfold KK; push_cast; ring
    have hk0 : (0 : ℝ) < (kk i : ℝ) := by linarith
    have hsq : Real.sqrt ((KK i : ℕ) : ℝ) * Real.sqrt ((KK i : ℕ) : ℝ) = 4 * (kk i : ℝ) := by
      rw [Real.mul_self_sqrt hKpos.le, hkk4]
    rw [div_eq_div_iff hk0.ne' hS0.ne']
    linear_combination (100 * Real.log 2 * (ℓ : ℝ) * (t : ℝ)) * hsq
  rw [harg]

/-- **The `t`-wise frequency theorem.**  For fixed `ℓ` and `t`, every pattern's frequency tends
to `2^{−ℓt}`; the patterns may vary with the scale. -/
theorem tendsto_patFreq_primeLambertFour (ℓ t : ℕ) (hℓ : 0 < ℓ) (ht : 0 < t)
    (w : ∀ i, Fin (2 ^ (ℓ * t))) :
    Tendsto (fun i => patFreq i ℓ t (primeLambertAtBase 4) (w i) - 1 / (2 : ℝ) ^ (ℓ * t))
      atTop (nhds 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hinner : Tendsto (fun i => 400 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) / Real.sqrt (KK i))
      atTop (nhds 0) := by
    have hsqrt : Tendsto (fun i => Real.sqrt (KK i)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_KK_atTop
    exact hsqrt.const_div_atTop _
  have hsq : Tendsto (fun i => 2 * Real.sqrt (400 * Real.log 2 * (ℓ : ℝ) * (t : ℝ)
      / Real.sqrt (KK i))) atTop (nhds 0) := by
    have := hinner.sqrt
    simpa using this.const_mul (2 : ℝ)
  refine squeeze_zero_norm' ?_ hsq
  filter_upwards [eventually_ge_atTop ℓ, eventually_ge_atTop (2 * t)] with i h1 h2
  have hℓm : ℓ ≤ kk i := by unfold kk; omega
  have hcard : 2 * t ≤ Fintype.card (gridAt i).Atom := by
    have := KK_le_card_Atom i
    have hKi : i ≤ KK i := by unfold KK kk; omega
    omega
  simpa [Real.norm_eq_abs] using abs_patFreq_sub_le_primeLambertFour i ℓ t hℓ hℓm ht hcard (w i)

/-! ### The digit rendering -/

/-- Unpacking the pattern coordinate into its `t` component blocks. -/
lemma patCoord_eq_pack_iff {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (m ℓ t : ℕ) (blk : B → Fin t → A) (c : B × Fin (m / ℓ)) (z : A → Fin (2 ^ m))
    (u : Fin t → Fin (2 ^ ℓ)) :
    patCoord m ℓ t blk c z = packFin t ℓ u
      ↔ ∀ s : Fin t, blkAt m ℓ (c.2 : ℕ) (z (blk c.1 s)) = u s := by
  constructor
  · intro h s
    exact congrFun ((packFin t ℓ).injective h) s
  · intro h
    exact congrArg (packFin t ℓ) (funext h)

open Classical in
/-- **The count rendering.**  `patFreq` is the density, among the `|P_K|·|B|·⌊m_K/ℓ⌋` triples
`(n, b, j)`, of those whose `j`-th aligned block of each of the `t` windows of `b` spells the
corresponding component of `w`. -/
theorem patFreq_eq_count (i ℓ t : ℕ) (x : ℝ) (w : Fin (2 ^ (ℓ * t))) :
    patFreq i ℓ t x w
      = (∑ c : Fin (nblk i t) × Fin (kk i / ℓ),
            (((PK i).filter fun n =>
              patCoord (kk i) ℓ t (blkSched i t) c
                (ZVec (gridAt i) (kk i) x n) = w).card : ℝ))
        / (((PK i).card : ℝ)
            * (Fintype.card (Fin (nblk i t) × Fin (kk i / ℓ)) : ℝ)) := by
  classical
  have hp : ∀ c : Fin (nblk i t) × Fin (kk i / ℓ),
      ((jointLawAt i x).map (patCoord (kk i) ℓ t (blkSched i t) c)).prob {w}
        = (((PK i).filter fun n =>
              patCoord (kk i) ℓ t (blkSched i t) c
                (ZVec (gridAt i) (kk i) x n) = w).card : ℝ)
          / ((PK i).card : ℝ) := by
    intro c
    rw [FinLaw.prob, Finset.sum_singleton]
    exact map_empirical_p (apSample_nonempty (gridAt i) (b₀_lt_X_at i)) _ _ w
  have hsum : (∑ c : Fin (nblk i t) × Fin (kk i / ℓ),
        ((jointLawAt i x).map (patCoord (kk i) ℓ t (blkSched i t) c)).prob {w})
      = (∑ c : Fin (nblk i t) × Fin (kk i / ℓ),
          (((PK i).filter fun n =>
            patCoord (kk i) ℓ t (blkSched i t) c
              (ZVec (gridAt i) (kk i) x n) = w).card : ℝ))
        / ((PK i).card : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => hp c
  rw [patFreq, hsum, div_div]

open Classical in
/-- **The digit rendering.**  The event is: for every `s < t`, the `ℓ` binary digits of `x`
beginning at position `2·kIdx(n, blkSched b s) + jℓ` spell the `s`-th component word. -/
theorem patFreq_eq_digits (i ℓ t : ℕ) (hℓ : 0 < ℓ) (x : ℝ) (u : Fin t → Fin (2 ^ ℓ)) :
    patFreq i ℓ t x (packFin t ℓ u)
      = (∑ c : Fin (nblk i t) × Fin (kk i / ℓ),
            (((PK i).filter fun n => ∀ s : Fin t,
              blockVal (Int.fract x)
                (2 * kIdx (gridAt i) n (blkSched i t c.1 s) + (c.2 : ℕ) * ℓ) ℓ
                  = (u s : ℕ)).card : ℝ))
        / (((PK i).card : ℝ)
            * (Fintype.card (Fin (nblk i t) × Fin (kk i / ℓ)) : ℝ)) := by
  classical
  rw [patFreq_eq_count i ℓ t x (packFin t ℓ u)]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  have halign : ((c.2 : ℕ) + 1) * ℓ ≤ kk i := by
    have h1 : (c.2 : ℕ) < kk i / ℓ := c.2.isLt
    have h2 : (kk i / ℓ) * ℓ ≤ kk i := Nat.div_mul_le_self _ _
    have h3 : ((c.2 : ℕ) + 1) * ℓ ≤ (kk i / ℓ) * ℓ := Nat.mul_le_mul_right ℓ (by omega)
    omega
  refine Finset.filter_congr fun n _ => ?_
  rw [patCoord_eq_pack_iff]
  constructor
  · intro h s
    have hZ : ZVec (gridAt i) (kk i) x n (blkSched i t c.1 s)
        = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n (blkSched i t c.1 s)) (kk i),
            blockVal_lt _ _ _⟩ :=
      Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n (blkSched i t c.1 s))
    have := h s
    rw [hZ, blkAt_blockVal _ _ _ _ _ halign] at this
    exact congrArg Fin.val this
  · intro h s
    have hZ : ZVec (gridAt i) (kk i) x n (blkSched i t c.1 s)
        = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n (blkSched i t c.1 s)) (kk i),
            blockVal_lt _ _ _⟩ :=
      Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n (blkSched i t c.1 s))
    rw [hZ, blkAt_blockVal _ _ _ _ _ halign]
    exact Fin.ext (h s)

open Classical in
/-- **THE ENDPOINT: the joint (`t`-wise) sampled-word frequency theorem for `G₄`.**

For every `t`, every word length `ℓ`, and any `t` binary words `v₀,…,v_{t−1}` of length `ℓ`,
the proportion of triples `(n, b, j)` at which, *simultaneously for every `s < t`*, the word
`v s` occurs in the binary expansion of `G₄` at position `2·kIdx(n, blkSched b s) + jℓ`, tends
to `2^{−ℓt}`.

This is the first statement that consumes `entropy_E1`'s joint hypothesis **as a joint
hypothesis**: the `t` sampled windows of a block are asymptotically independent.  Taking `t = 1`
recovers `tendsto_occursCountT_primeLambertFour`.

It is a statement about the *sampled* positions only, and is **not** a normality claim. -/
theorem tendsto_occursCountJoint_primeLambertFour (t ℓ : ℕ) (ht : 0 < t) (hℓ : 0 < ℓ)
    (v : Fin t → List ℕ) (hlen : ∀ s, (v s).length = ℓ)
    (hv : ∀ s : Fin t, ∀ j, ∀ h : j < (v s).length, (v s)[j] < 2) :
    Tendsto (fun i =>
      (∑ c : Fin (nblk i t) × Fin (kk i / ℓ),
          (((PK i).filter fun n => ∀ s : Fin t,
            OccursAt 2 (primeLambertAtBase 4) (v s)
              (2 * kIdx (gridAt i) n (blkSched i t c.1 s) + (c.2 : ℕ) * ℓ)).card : ℝ))
        / (((PK i).card : ℝ)
            * (Fintype.card (Fin (nblk i t) × Fin (kk i / ℓ)) : ℝ)))
      atTop (nhds (1 / (2 : ℝ) ^ (ℓ * t))) := by
  classical
  set u : Fin t → Fin (2 ^ ℓ) := fun s =>
    ⟨wordVal (v s), by
      have := wordVal_lt (hv s)
      rw [hlen s] at this
      exact this⟩ with hu
  have hmain : Tendsto (fun i => patFreq i ℓ t (primeLambertAtBase 4) (packFin t ℓ u))
      atTop (nhds (1 / (2 : ℝ) ^ (ℓ * t))) := by
    have := tendsto_patFreq_primeLambertFour ℓ t hℓ ht (fun _ => packFin t ℓ u)
    have hlim : Tendsto (fun _ : ℕ => (1 : ℝ) / (2 : ℝ) ^ (ℓ * t)) atTop
        (nhds (1 / (2 : ℝ) ^ (ℓ * t))) := tendsto_const_nhds
    simpa using this.add hlim
  refine hmain.congr fun i => ?_
  rw [patFreq_eq_digits i ℓ t hℓ _ u]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  refine Finset.filter_congr fun n _ => ?_
  constructor
  · intro h s
    have hb := blockVal_eq_wordVal_iff (y := primeLambertAtBase 4)
      (p := 2 * kIdx (gridAt i) n (blkSched i t c.1 s) + (c.2 : ℕ) * ℓ) (hv s)
    have hs := h s
    rw [hlen s] at hb
    exact hb.1 hs
  · intro h s
    have hb := blockVal_eq_wordVal_iff (y := primeLambertAtBase 4)
      (p := 2 * kIdx (gridAt i) n (blkSched i t c.1 s) + (c.2 : ℕ) * ℓ) (hv s)
    rw [hlen s] at hb
    exact hb.2 (h s)

end NormalNumbers.G4.Sched
