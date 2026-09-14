/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyJointSched

/-!
# The `t`-wise bound at independent per-window offsets

`G4EntropyJoint`/`G4EntropyJointSched` proved the `t`-wise decorrelation at the **common**
aligned position `jℓ` of each of the `t` windows of a block.  The objective as stated asks for a
position `p_s` **per window**: `G₄`'s block at `2·kIdx(n, α_s) + p_s` spells `w_s`.

The mechanism here is a change of window, not new information theory.  Given an offset vector
`pp` and a common cut length `D`, let `cutTuple` replace each window by its `D`-bit sub-window
beginning at that window's own offset.  Then

* `H₂_cutTuple_ge` — cutting costs at most `|A|(m − D)` bits (`H₂_lowTuple_ge` generalized from a
  common truncation to a per-coordinate one), so an `m`-window deficit `Δ` becomes a `D`-window
  deficit of **the same** `Δ`; and
* `blkAt_cutCoord` — the aligned `ℓ`-blocks of the cut window at `α` are exactly the blocks of
  the original window at the positions `ρ α + jℓ`.

Feeding this into `abs_avg_patCoord_prob_opt` gives `abs_avg_patPos_prob_opt`: the `t` windows
decorrelate at `t` **independently chosen** offsets, with the bound `2√(log 2·ℓΔ/(|B|·D))` —
the aligned bound with `m` replaced by the cut length `D ≤ m − max pp`.  Taking `pp = 0`,
`D = m` recovers `abs_avg_patCoord_prob_opt` exactly.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

/-! ### Cutting a window down to a `D`-bit sub-window at its own offset -/

/-- The `D`-bit sub-window of an `m`-bit window beginning at position `a`. -/
def cutCoord (m D a : ℕ) (z : Fin (2 ^ m)) : Fin (2 ^ D) :=
  ⟨(z : ℕ) / 2 ^ (m - a - D) % 2 ^ D, Nat.mod_lt _ (by positivity)⟩

@[simp] lemma cutCoord_val (m D a : ℕ) (z : Fin (2 ^ m)) :
    ((cutCoord m D a z : Fin (2 ^ D)) : ℕ) = (z : ℕ) / 2 ^ (m - a - D) % 2 ^ D := rfl

/-- The cut applied coordinatewise, each window at its own offset. -/
def cutTuple {A : Type*} (m D : ℕ) (ρ : A → ℕ) (z : A → Fin (2 ^ m)) : A → Fin (2 ^ D) :=
  fun α => cutCoord m D (ρ α) (z α)

/-- Everything of the window outside the cut: the top `a` bits and the bottom `m − a − D`. -/
def outCoord (m D a : ℕ) (z : Fin (2 ^ m)) : Fin (2 ^ m) × Fin (2 ^ m) :=
  (⟨(z : ℕ) / 2 ^ (m - a), lt_of_le_of_lt (Nat.div_le_self _ _) z.isLt⟩,
   ⟨(z : ℕ) % 2 ^ (m - a - D), lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by norm_num) (by omega))⟩)

/-- **The cut and its complement determine the window.** -/
lemma cut_out_injective {m D a : ℕ} (hD : a + D ≤ m) {z z' : Fin (2 ^ m)}
    (hc : cutCoord m D a z = cutCoord m D a z') (ho : outCoord m D a z = outCoord m D a z') :
    z = z' := by
  set b := m - a - D with hb
  have hbD : b + D = m - a := by omega
  have hhi : (z : ℕ) / 2 ^ (m - a) = (z' : ℕ) / 2 ^ (m - a) :=
    congrArg Fin.val (congrArg Prod.fst ho)
  have hlo : (z : ℕ) % 2 ^ b = (z' : ℕ) % 2 ^ b :=
    congrArg Fin.val (congrArg Prod.snd ho)
  have hmid : (z : ℕ) / 2 ^ b % 2 ^ D = (z' : ℕ) / 2 ^ b % 2 ^ D := congrArg Fin.val hc
  have hdd : ∀ y : ℕ, y / 2 ^ b / 2 ^ D = y / 2 ^ (m - a) := by
    intro y; rw [Nat.div_div_eq_div_mul, ← pow_add, hbD]
  have hdiv : (z : ℕ) / 2 ^ b = (z' : ℕ) / 2 ^ b := by
    have h1 := Nat.div_add_mod ((z : ℕ) / 2 ^ b) (2 ^ D)
    have h2 := Nat.div_add_mod ((z' : ℕ) / 2 ^ b) (2 ^ D)
    rw [hdd z, hhi] at h1
    rw [hdd z'] at h2
    omega
  refine Fin.ext ?_
  have h1 := Nat.div_add_mod (z : ℕ) (2 ^ b)
  have h2 := Nat.div_add_mod (z' : ℕ) (2 ^ b)
  rw [hdiv, hlo] at h1
  omega

/-- The coordinate family: the whole cut tuple, plus each window's complement. -/
def cutFam {A : Type*} (m D : ℕ) (ρ : A → ℕ) :
    Option A → (A → Fin (2 ^ m)) → (A → Fin (2 ^ D)) × (Fin (2 ^ m) × Fin (2 ^ m))
  | none => fun z => (cutTuple m D ρ z, (⟨0, Nat.pow_pos (by norm_num)⟩,
      ⟨0, Nat.pow_pos (by norm_num)⟩))
  | some α => fun z => ((fun _ => ⟨0, Nat.pow_pos (by norm_num)⟩), outCoord m D (ρ α) (z α))

set_option maxHeartbeats 1000000 in
/-- **Cutting costs at most `|A|·(m − D)` bits.**  The per-coordinate generalization of
`H₂_lowTuple_ge`: each window may be cut at its own offset. -/
theorem H₂_cutTuple_ge {A : Type*} [Fintype A] [DecidableEq A] {m D : ℕ} (hDm : D ≤ m)
    (ρ : A → ℕ) (hρ : ∀ α, ρ α + D ≤ m) (L : FinLaw (A → Fin (2 ^ m))) :
    L.H₂ - (Fintype.card A : ℝ) * ((m : ℝ) - D) ≤ (L.map (cutTuple m D ρ)).H₂ := by
  classical
  have hinj : Function.Injective
      (fun z : A → Fin (2 ^ m) => fun i => cutFam m D ρ i z) := by
    intro z z' h
    funext α
    have h1 : cutCoord m D (ρ α) (z α) = cutCoord m D (ρ α) (z' α) := by
      have := congrArg Prod.fst (congrFun h none)
      simp only [cutFam] at this
      exact congrFun this α
    have h2 : outCoord m D (ρ α) (z α) = outCoord m D (ρ α) (z' α) := by
      have := congrArg Prod.snd (congrFun h (some α))
      simpa [cutFam] using this
    exact cut_out_injective (hρ α) h1 h2
  have hsub := L.H₂_le_sum_H₂_map (fun i => cutFam m D ρ i) hinj
  rw [Fintype.sum_option] at hsub
  -- the cut tuple keeps its entropy
  have hcutH : (L.map (cutFam m D ρ none)).H₂ = (L.map (cutTuple m D ρ)).H₂ := by
    refine L.H₂_map_congr_comp (cutTuple m D ρ)
      (g := fun v : A → Fin (2 ^ D) => (v, ((⟨0, Nat.pow_pos (by norm_num)⟩ : Fin (2 ^ m)),
        (⟨0, Nat.pow_pos (by norm_num)⟩ : Fin (2 ^ m)))))
      (fun v v' hv => by simpa using congrArg Prod.fst hv) _ (fun z => rfl)
  -- each complement carries at most `m − D` bits
  have houtH : ∀ α : A, (L.map (cutFam m D ρ (some α))).H₂ ≤ ((m : ℝ) - D) := by
    intro α
    have ha : ρ α + D ≤ m := hρ α
    have hpos : 0 < 2 ^ (m - D) := Nat.pow_pos (by norm_num)
    set T : Finset ((A → Fin (2 ^ D)) × (Fin (2 ^ m) × Fin (2 ^ m))) :=
      Finset.image
        (fun q : Fin (2 ^ (ρ α)) × Fin (2 ^ (m - ρ α - D)) =>
          (((fun _ => ⟨0, Nat.pow_pos (by norm_num)⟩) : A → Fin (2 ^ D)),
            ((⟨(q.1 : ℕ), lt_of_lt_of_le q.1.isLt
                (Nat.pow_le_pow_right (by norm_num) (by omega))⟩ : Fin (2 ^ m)),
             (⟨(q.2 : ℕ), lt_of_lt_of_le q.2.isLt
                (Nat.pow_le_pow_right (by norm_num) (by omega))⟩ : Fin (2 ^ m)))))
        Finset.univ with hT
    have hsupp : ∀ v, (L.map (cutFam m D ρ (some α))).p v ≠ 0 → v ∈ T := by
      intro v hv
      rw [FinLaw.map_p] at hv
      have hne : (Finset.univ.filter
          (fun z : A → Fin (2 ^ m) => cutFam m D ρ (some α) z = v)).Nonempty := by
        by_contra hcon
        rw [Finset.not_nonempty_iff_eq_empty] at hcon
        rw [hcon] at hv
        simp at hv
      obtain ⟨z, hz⟩ := hne
      rw [Finset.mem_filter] at hz
      have hz2 := hz.2
      have hhi : (z α : ℕ) / 2 ^ (m - ρ α) < 2 ^ (ρ α) := by
        refine Nat.div_lt_iff_lt_mul (by positivity) |>.2 ?_
        have : (2 : ℕ) ^ (m - ρ α) * 2 ^ (ρ α) = 2 ^ m := by
          rw [← pow_add]; congr 1; omega
        rw [mul_comm] at this
        omega
      have hlo : (z α : ℕ) % 2 ^ (m - ρ α - D) < 2 ^ (m - ρ α - D) :=
        Nat.mod_lt _ (by positivity)
      refine Finset.mem_image.2 ⟨(⟨_, hhi⟩, ⟨_, hlo⟩), Finset.mem_univ _, ?_⟩
      rw [← hz2]
      simp only [cutFam, outCoord]
    have hcard : T.card ≤ 2 ^ (m - D) := by
      calc T.card ≤ (Finset.univ :
            Finset (Fin (2 ^ (ρ α)) × Fin (2 ^ (m - ρ α - D)))).card := Finset.card_image_le
        _ = 2 ^ (ρ α) * 2 ^ (m - ρ α - D) := by simp
        _ = 2 ^ (m - D) := by rw [← pow_add]; congr 1; omega
    have h := (L.map (cutFam m D ρ (some α))).H₂_le_logb hpos T hsupp hcard
    have hlg : Real.logb 2 ((2 ^ (m - D) : ℕ) : ℝ) = ((m : ℝ) - D) := by
      rw [show ((2 ^ (m - D) : ℕ) : ℝ) = (2 : ℝ) ^ (m - D) by push_cast; ring,
        Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
      rw [Nat.cast_sub hDm]
    rwa [hlg] at h
  have hsum : ∑ α : A, (L.map (cutFam m D ρ (some α))).H₂
      ≤ (Fintype.card A : ℝ) * ((m : ℝ) - D) := by
    calc ∑ α : A, (L.map (cutFam m D ρ (some α))).H₂
        ≤ ∑ _α : A, ((m : ℝ) - D) := Finset.sum_le_sum fun α _ => houtH α
      _ = (Fintype.card A : ℝ) * ((m : ℝ) - D) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [hcutH] at hsub
  linarith

/-! ### The cut window's aligned blocks are the original window's offset blocks -/

/-- **The dictionary.**  The `j`-th aligned `ℓ`-block of the cut window at offset `a` is the
`ℓ`-block of the original window at position `a + jℓ`. -/
theorem blkAt_cutCoord {m D ℓ j a : ℕ} (hD : a + D ≤ m) (hj : (j + 1) * ℓ ≤ D)
    (z : Fin (2 ^ m)) :
    blkAt D ℓ j (cutCoord m D a z) = posAt m ℓ (a + j * ℓ) z := by
  refine Fin.ext ?_
  rw [blkAt_val, posAt_val, cutCoord_val]
  have hstep : (m - a - D) + (D - (j + 1) * ℓ) = m - (a + j * ℓ) - ℓ := by
    have : (j + 1) * ℓ = j * ℓ + ℓ := by ring
    omega
  have hℓj : ℓ ≤ (j + 1) * ℓ := Nat.le_mul_of_pos_left ℓ (by omega)
  rw [mod_div_mod_eq (by omega : (D - (j + 1) * ℓ) + ℓ ≤ D)]
  rw [Nat.div_div_eq_div_mul, ← pow_add, hstep]

/-! ### The `t`-wise bound at an arbitrary offset vector -/

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The offset a blocking and an offset vector attach to an atom (`0` on atoms the blocking
misses). -/
noncomputable def shiftOf (t : ℕ) (blk : B → Fin t → A) (pp : Fin t → ℕ) (α : A) : ℕ :=
  open Classical in
  if h : ∃ p : B × Fin t, blk p.1 p.2 = α then pp h.choose.2 else 0

lemma shiftOf_blk {t : ℕ} {blk : B → Fin t → A}
    (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2)) (pp : Fin t → ℕ)
    (b : B) (s : Fin t) : shiftOf t blk pp (blk b s) = pp s := by
  classical
  have hex : ∃ p : B × Fin t, blk p.1 p.2 = blk b s := ⟨(b, s), rfl⟩
  rw [shiftOf, dif_pos hex]
  have hch : hex.choose = (b, s) := hblk hex.choose_spec
  rw [hch]

/-- **The position-vector pattern coordinate.**  For each of the `t` windows of a block, the
`ℓ`-block at *that window's own* offset `pp s`, shifted by the common aligned index `j`, all
packed into one `ℓt`-bit word. -/
def patPos (m ℓ t D : ℕ) (pp : Fin t → ℕ) (blk : B → Fin t → A) (c : B × Fin (D / ℓ))
    (z : A → Fin (2 ^ m)) : Fin (2 ^ (ℓ * t)) :=
  packFin t ℓ (fun s => posAt m ℓ (pp s + (c.2 : ℕ) * ℓ) (z (blk c.1 s)))

/-- **The `t`-wise capacity bound at independent per-window offsets.**  A total deficit of `Δ`
on the joint law controls every `ℓt`-bit pattern read at the `t` *independently chosen* offsets
`pp 0, …, pp (t−1)` to within

    `2√(log 2 · ℓ · Δ / (|B| · D))`,

where `D` is any common cut length with `pp s + D ≤ m` for every `s`.  Taking `pp = 0` and
`D = m` is exactly `abs_avg_patCoord_prob_opt`: the offsets are free, and the only price is the
shortened window `D ≤ m − max pp`. -/
theorem abs_avg_patPos_prob_opt {m ℓ t D : ℕ} (hℓ : 0 < ℓ) (hℓD : ℓ ≤ D) (ht : 0 < t)
    (hDm : D ≤ m) [Nonempty B]
    (pp : Fin t → ℕ) (hpp : ∀ s, pp s + D ≤ m)
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    |(∑ c : B × Fin (D / ℓ), (L.map (patPos m ℓ t D pp blk c)).prob {w})
        / (Fintype.card (B × Fin (D / ℓ)) : ℝ) - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * Δ / ((Fintype.card B : ℝ) * (D : ℝ))) := by
  classical
  set ρ : A → ℕ := shiftOf t blk pp with hρdef
  have hbs : ∀ (b : B) (s : Fin t), ρ (blk b s) = pp s := fun b s => shiftOf_blk hblk pp b s
  have hρle : ∀ α, ρ α + D ≤ m := by
    intro α
    by_cases h : ∃ p : B × Fin t, blk p.1 p.2 = α
    · obtain ⟨p, rfl⟩ := h
      rw [hbs p.1 p.2]
      exact hpp p.2
    · have hz : ρ α = 0 := by rw [hρdef, shiftOf, dif_neg h]
      omega
  set L' := L.map (cutTuple m D ρ) with hL'
  have hΔ' : (D : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L'.H₂ := by
    have hcut := H₂_cutTuple_ge hDm ρ hρle L
    have hid : (D : ℝ) * (Fintype.card A : ℝ)
        = (m : ℝ) * (Fintype.card A : ℝ)
          - (Fintype.card A : ℝ) * ((m : ℝ) - (D : ℝ)) := by ring
    rw [hid, hL']
    linarith
  have hmain := abs_avg_patCoord_prob_opt (A := A) (B := B) (m := D) (ℓ := ℓ) (t := t)
    hℓ hℓD ht blk hblk L' w hΔ0 hΔ'
  have hterm : ∀ c : B × Fin (D / ℓ),
      (L'.map (patCoord D ℓ t blk c)).prob {w}
        = (L.map (patPos m ℓ t D pp blk c)).prob {w} := by
    intro c
    have halign : ((c.2 : ℕ) + 1) * ℓ ≤ D := by
      have h1 : (c.2 : ℕ) < D / ℓ := c.2.isLt
      have h2 : (D / ℓ) * ℓ ≤ D := Nat.div_mul_le_self _ _
      have h3 : ((c.2 : ℕ) + 1) * ℓ ≤ (D / ℓ) * ℓ := Nat.mul_le_mul_right ℓ (by omega)
      omega
    have hfun : (fun z : A → Fin (2 ^ m) => patCoord D ℓ t blk c (cutTuple m D ρ z))
        = patPos m ℓ t D pp blk c := by
      funext z
      rw [patCoord, patPos]
      congr 1
      funext s
      show blkAt D ℓ (c.2 : ℕ) (cutCoord m D (ρ (blk c.1 s)) (z (blk c.1 s)))
        = posAt m ℓ (pp s + (c.2 : ℕ) * ℓ) (z (blk c.1 s))
      rw [hbs c.1 s]
      exact blkAt_cutCoord (hpp s) halign _
    rw [hL', FinLaw.prob_singleton_map_map, hfun]
  have hsum : (∑ c : B × Fin (D / ℓ), (L.map (patPos m ℓ t D pp blk c)).prob {w})
      = ∑ c : B × Fin (D / ℓ), (L'.map (patCoord D ℓ t blk c)).prob {w} :=
    Finset.sum_congr rfl fun c _ => (hterm c).symm
  rw [hsum]
  exact hmain

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The schedule instance: `t` windows, `t` independent offsets -/

/-- The largest offset of an offset vector. -/
def ppMax {t : ℕ} (pp : Fin t → ℕ) : ℕ := Finset.univ.sup pp

lemma le_ppMax {t : ℕ} (pp : Fin t → ℕ) (s : Fin t) : pp s ≤ ppMax pp :=
  Finset.le_sup (Finset.mem_univ s)

/-- **The frequency of an `ℓt`-bit pattern read at `t` independent offsets**, averaged over the
triples `(n, block, common aligned shift)`. -/
noncomputable def posPatFreq (i ℓ t : ℕ) (pp : Fin t → ℕ) (x : ℝ) (w : Fin (2 ^ (ℓ * t))) : ℝ :=
  (∑ c : Fin (nblk i t) × Fin ((kk i - ppMax pp) / ℓ),
      ((jointLawAt i x).map
        (patPos (kk i) ℓ t (kk i - ppMax pp) pp (blkSched i t) c)).prob {w})
    / (Fintype.card (Fin (nblk i t) × Fin ((kk i - ppMax pp) / ℓ)) : ℝ)

/-- **The capacity inequality at independent offsets.**  A per-window deficit of `δ` bits
controls every pattern read at the offsets `pp` to within `2√(2 log 2 · ℓ t δ/(m_K − max pp))`. -/
theorem abs_posPatFreq_sub_le_of_deficit (i ℓ t : ℕ) (hℓ : 0 < ℓ) (ht : 0 < t)
    (pp : Fin t → ℕ) (hfit : 2 * (ppMax pp + ℓ) ≤ kk i)
    (hcard : 2 * t ≤ Fintype.card (gridAt i).Atom) (x : ℝ) (w : Fin (2 ^ (ℓ * t)))
    {δ : ℝ} (hδ : 0 < δ)
    (hdef : ((kk i : ℝ) - δ) * (Fintype.card (gridAt i).Atom : ℝ) ≤ (jointLawAt i x).H₂) :
    |posPatFreq i ℓ t pp x w - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * Real.sqrt (2 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) * δ
          / ((kk i : ℝ) - (ppMax pp : ℕ))) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < Fintype.card (gridAt i).Atom := by omega
  have hnb : 0 < nblk i t := nblk_pos ht (by omega)
  haveI : Nonempty (Fin (nblk i t)) := Fin.pos_iff_nonempty.1 hnb
  set R := ppMax pp with hR
  set D := kk i - R with hD
  have hDm : D ≤ kk i := by omega
  have hℓD : ℓ ≤ D := by omega
  have hpp : ∀ s, pp s + D ≤ kk i := by
    intro s
    have := le_ppMax pp s
    omega
  have hDR : (D : ℝ) = (kk i : ℝ) - (R : ℝ) := by
    rw [hD, Nat.cast_sub (by omega)]
  have hD0 : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := by omega
    exact_mod_cast this
  have hCR : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by exact_mod_cast hC
  have hΔ0 : (0 : ℝ) < δ * (Fintype.card (gridAt i).Atom : ℝ) := by positivity
  have hΔ : (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
      - δ * (Fintype.card (gridAt i).Atom : ℝ) ≤ (jointLawAt i x).H₂ := by
    rw [← sub_mul]; exact hdef
  have hmain := abs_avg_patPos_prob_opt (A := (gridAt i).Atom) (B := Fin (nblk i t))
    (m := kk i) (ℓ := ℓ) (t := t) (D := D) hℓ hℓD ht hDm pp hpp (blkSched i t)
    (blkSched_injective i t) (jointLawAt i x) w hΔ0 hΔ
  have hN : (Fintype.card (Fin (nblk i t) × Fin (D / ℓ)) : ℝ)
      = (Fintype.card (Fin (nblk i t)) : ℝ) * ((D / ℓ : ℕ) : ℝ) := by
    simp [Fintype.card_prod]
  rw [posPatFreq, ← hR, ← hD]
  refine hmain.trans ?_
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
      / ((Fintype.card (Fin (nblk i t)) : ℝ) * (D : ℝ))
      ≤ 2 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) * δ / ((kk i : ℝ) - (R : ℝ)) := by
    rw [hcf, ← hDR, div_le_div_iff₀ (by positivity) hD0]
    have hkey : Real.log 2 * (ℓ : ℝ) * δ
        * ((Fintype.card (gridAt i).Atom : ℝ) - 2 * (t : ℝ) * ((nblk i t : ℕ) : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    nlinarith [hkey, hbR, hD0, htR, hlog2, hδ, hCR]
  have hpos1 : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * (δ * (Fintype.card (gridAt i).Atom : ℝ))
      / ((Fintype.card (Fin (nblk i t)) : ℝ) * (D : ℝ)) := by
    rw [hcf]; positivity
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by norm_num)

end NormalNumbers.G4.Sched
