/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyPosition

/-!
# The joint (`t`-wise) capacity bound: the sampled windows decorrelate

Everything proved so far about `jointLaw` projects it to **one** coordinate: `entropy_E1` bounds
the entropy of the whole vector `Z_K = (Z_α)_{α∈Atom}`, and `G4EntropyTiling` /
`G4EntropyPosition` then read off a single window's word frequencies.  The joint content is
untouched, and it is exactly what a near-maximal joint entropy is *for*: the coordinates are
asymptotically **independent**.

This module proves the abstract half.  Fix a *blocking* — an injective family
`blk : B → Fin t → A` of `t`-tuples of distinct atoms — and read the `j`-th aligned `ℓ`-block of
each of the `t` windows of a block, packed into one `ℓt`-bit word (`patCoord`).  Then:

* `sum_patCoord_deficit_le` — **the deficit is not multiplied by `t`**:
  `∑_{b,j} (ℓt − H₂(L.map (patCoord b j))) ≤ Δ`, the *same* `Δ` as the `t = 1` statement
  `sum_block_deficit_tile_le`, and again with zero slack.  The bits ledger closes exactly:
  the `t|B|` covered atoms contribute `⌊m/ℓ⌋·ℓt + t(m%ℓ) = tm` bits per block and the
  `|A| − t|B|` uncovered ones `m` each.
* `abs_avg_patCoord_prob_le` / `abs_avg_patCoord_prob_opt` — hence every *pattern*
  `w ∈ Fin (2^{ℓt})` has its average probability within `2√(log 2 · tℓδ/m)` of `2^{−ℓt}`:
  the `t = 1` bound with `ℓ ↦ tℓ`, which is what pinning `t` words at once costs.

Taking `t = 2` already says something new about `G₄`: for a typical pair of sampled windows, the
two `ℓ`-blocks are jointly uniform, i.e. *independent*.  Disjunctivity gives one word at a time;
this gives a prescribed pattern at `t` prescribed sampled positions simultaneously.

The whole argument is the `t = 1` one with the atom set `A` replaced by the block set `B` and the
alphabet `Fin (2^ℓ)` by `Fin (2^{ℓt})` — no new information theory, only a bits ledger.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

namespace FinLaw

variable {Ω : Type*} [Fintype Ω]

/-- A law supported on one atom has zero entropy. -/
theorem H₂_map_const_le {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (L : FinLaw Ω) (c : Ω') :
    (L.map (fun _ => c)).H₂ ≤ 0 := by
  classical
  have h := (L.map (fun _ : Ω => c)).H₂_le_logb (N := 1) one_pos {c}
    (fun ω' hω' => by
      by_contra hc
      rw [FinLaw.map_p] at hω'
      refine hω' (Finset.sum_eq_zero fun ω hω => ?_)
      rw [Finset.mem_filter] at hω
      exact absurd (hω.2 ▸ Finset.mem_singleton_self c) hc)
    (by simp)
  simpa using h

end FinLaw

/-! ### Packing a `t`-tuple of `ℓ`-bit words into one `ℓt`-bit word -/

/-- `(Fin t → Fin (2^ℓ)) ≃ Fin (2^{ℓt})`. -/
def packFin (t ℓ : ℕ) : (Fin t → Fin (2 ^ ℓ)) ≃ Fin (2 ^ (ℓ * t)) :=
  finFunctionFinEquiv.trans (finCongr (pow_mul 2 ℓ t).symm)

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- **The pattern coordinate.**  The `j`-th aligned `ℓ`-block of each of the `t` windows of
block `b`, packed into one `ℓt`-bit word. -/
def patCoord (m ℓ t : ℕ) (blk : B → Fin t → A) (c : B × Fin (m / ℓ))
    (z : A → Fin (2 ^ m)) : Fin (2 ^ (ℓ * t)) :=
  packFin t ℓ (fun s => fullCoord m ℓ (blk c.1 s, c.2) z)

/-- The block remainder coordinate: the `t` window remainders, packed. -/
def patRem (m ℓ t : ℕ) (hℓ : 0 < ℓ) (blk : B → Fin t → A) (b : B)
    (z : A → Fin (2 ^ m)) : Fin (2 ^ (ℓ * t)) :=
  packFin t ℓ (fun s => remCoord m ℓ hℓ (z (blk b s)))

/-- The coordinate of an atom the blocking misses; covered atoms get a constant. -/
noncomputable def leftCoord (m ℓ t : ℕ) (hm : m ≤ ℓ * t) (blk : B → Fin t → A) (α : A)
    (z : A → Fin (2 ^ m)) : Fin (2 ^ (ℓ * t)) :=
  open Classical in
  if (∃ p : B × Fin t, blk p.1 p.2 = α) then ⟨0, Nat.pow_pos (by norm_num)⟩
  else Fin.castLE (Nat.pow_le_pow_right (by norm_num) hm) (z α)

/-- The three families, as one indexed family of coordinate maps. -/
noncomputable def jointFam (m ℓ t : ℕ) (hℓ : 0 < ℓ) (hm : m ≤ ℓ * t) (blk : B → Fin t → A) :
    ((B × Fin (m / ℓ)) ⊕ B ⊕ A) → (A → Fin (2 ^ m)) → Fin (2 ^ (ℓ * t)) :=
  Sum.elim (patCoord m ℓ t blk) (Sum.elim (patRem m ℓ t hℓ blk) (leftCoord m ℓ t hm blk))

/-! ### The three bits bounds -/

/-- The block remainder carries at most `t·(m % ℓ)` bits. -/
theorem H₂_map_patRem_le {m ℓ t : ℕ} (hℓ : 0 < ℓ) (blk : B → Fin t → A)
    (L : FinLaw (A → Fin (2 ^ m))) (b : B) :
    (L.map (patRem m ℓ t hℓ blk b)).H₂ ≤ ((m % ℓ : ℕ) : ℝ) * (t : ℝ) := by
  classical
  have heq : (L.map (patRem m ℓ t hℓ blk b)).H₂
      = (L.map (fun z : A → Fin (2 ^ m) => fun s => remCoord m ℓ hℓ (z (blk b s)))).H₂ :=
    FinLaw.H₂_map_congr_comp L _ (packFin t ℓ).injective _ (fun _ => rfl)
  rw [heq]
  set M := L.map (fun z : A → Fin (2 ^ m) => fun s => remCoord m ℓ hℓ (z (blk b s))) with hM
  have hpos : 0 < (2 ^ (m % ℓ)) ^ t := by positivity
  set T : Finset (Fin t → Fin (2 ^ ℓ)) :=
    Finset.univ.filter (fun v => ∀ s, (v s : ℕ) < 2 ^ (m % ℓ)) with hT
  have hsupp : ∀ v : Fin t → Fin (2 ^ ℓ), M.p v ≠ 0 → v ∈ T := by
    intro v hv
    rw [hM, FinLaw.map_p] at hv
    have hne : (Finset.univ.filter (fun z : A → Fin (2 ^ m) =>
        (fun s => remCoord m ℓ hℓ (z (blk b s))) = v)).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      rw [hcon] at hv
      simp at hv
    obtain ⟨z, hz⟩ := hne
    rw [Finset.mem_filter] at hz
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun s => ?_⟩
    have := congrFun hz.2 s
    rw [← this, remCoord_val]
    exact Nat.mod_lt _ (by positivity)
  have hcard : T.card ≤ (2 ^ (m % ℓ)) ^ t := by
    have hle : T.card ≤ (Finset.univ : Finset (Fin t → Fin (2 ^ (m % ℓ)))).card := by
      refine Finset.card_le_card_of_injOn
        (fun v => fun s => (⟨(v s : ℕ) % 2 ^ (m % ℓ), Nat.mod_lt _ (by positivity)⟩ :
          Fin (2 ^ (m % ℓ))))
        (fun v _ => Finset.mem_univ _) ?_
      intro a ha c hc hac
      simp only [hT, Finset.mem_coe, Finset.mem_filter] at ha hc
      funext s
      have h1 := congrFun hac s
      have h2 : (a s : ℕ) % 2 ^ (m % ℓ) = (c s : ℕ) % 2 ^ (m % ℓ) := congrArg Fin.val h1
      rw [Nat.mod_eq_of_lt (ha.2 s), Nat.mod_eq_of_lt (hc.2 s)] at h2
      exact Fin.ext h2
    simpa [Finset.card_univ, Fintype.card_fun] using hle
  refine (M.H₂_le_logb hpos T hsupp hcard).trans_eq ?_
  rw [show (((2 ^ (m % ℓ)) ^ t : ℕ) : ℝ) = (2 : ℝ) ^ ((m % ℓ) * t) by
    push_cast; rw [← pow_mul]]
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  push_cast
  ring

/-- An atom the blocking covers contributes nothing; one it misses contributes at most `m`. -/
theorem H₂_map_leftCoord_le {m ℓ t : ℕ} (hm : m ≤ ℓ * t) (blk : B → Fin t → A)
    (L : FinLaw (A → Fin (2 ^ m))) (α : A) :
    (L.map (leftCoord m ℓ t hm blk α)).H₂
      ≤ (if (∃ p : B × Fin t, blk p.1 p.2 = α) then (0 : ℝ) else (m : ℝ)) := by
  classical
  by_cases hcov : ∃ p : B × Fin t, blk p.1 p.2 = α
  · rw [if_pos hcov]
    have hfun : leftCoord m ℓ t hm blk α
        = fun _ : A → Fin (2 ^ m) => (⟨0, Nat.pow_pos (by norm_num)⟩ : Fin (2 ^ (ℓ * t))) := by
      funext z; simp only [leftCoord]; rw [if_pos hcov]
    rw [hfun]
    exact FinLaw.H₂_map_const_le L _
  · rw [if_neg hcov]
    have heq : (L.map (leftCoord m ℓ t hm blk α)).H₂
        = (L.map (fun z : A → Fin (2 ^ m) => z α)).H₂ := by
      refine FinLaw.H₂_map_congr_comp L _ (Fin.castLE_injective
        (Nat.pow_le_pow_right (by norm_num) hm)) _ (fun z => ?_)
      simp only [leftCoord]; rw [if_neg hcov]
    rw [heq]
    exact H₂_le_of_block _

/-- The three families together determine the sample vector. -/
theorem jointFam_injective {m ℓ t : ℕ} (hℓ : 0 < ℓ) (hm : m ≤ ℓ * t)
    (blk : B → Fin t → A) :
    Function.Injective (fun z : A → Fin (2 ^ m) =>
      fun i : (B × Fin (m / ℓ)) ⊕ B ⊕ A => jointFam m ℓ t hℓ hm blk i z) := by
  classical
  intro z z' h
  funext α
  by_cases hcov : ∃ p : B × Fin t, blk p.1 p.2 = α
  · obtain ⟨p, rfl⟩ := hcov
    refine tile_injective hℓ (fun j hj => ?_) ?_
    · have hc := congrFun h (Sum.inl (p.1, (⟨j, hj⟩ : Fin (m / ℓ))))
      simp only [jointFam, Sum.elim_inl] at hc
      have hf := congrFun ((packFin t ℓ).injective hc) p.2
      exact hf
    · have hc := congrFun h (Sum.inr (Sum.inl p.1))
      simp only [jointFam, Sum.elim_inr, Sum.elim_inl] at hc
      exact congrFun ((packFin t ℓ).injective hc) p.2
  · have hc := congrFun h (Sum.inr (Sum.inr α))
    simp only [jointFam, Sum.elim_inr, leftCoord] at hc
    simp only [if_neg hcov] at hc
    exact Fin.castLE_injective _ hc

/-- **The `t`-wise deficit budget, with zero slack.**  A total deficit of `Δ` bits on the joint
law leaves a total deficit of at most `Δ` on the `|B|·⌊m/ℓ⌋` pattern coordinates — the *same*
`Δ`, not `tΔ`. -/
theorem sum_patCoord_deficit_le {m ℓ t : ℕ} (hℓ : 0 < ℓ) (hm : m ≤ ℓ * t)
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) {Δ : ℝ}
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    ∑ c : B × Fin (m / ℓ), ((ℓ * t : ℕ) - (L.map (patCoord m ℓ t blk c)).H₂ : ℝ) ≤ Δ := by
  classical
  have hsub := L.H₂_le_sum_H₂_map (jointFam m ℓ t hℓ hm blk) (jointFam_injective hℓ hm blk)
  have hsplit : ∑ i : (B × Fin (m / ℓ)) ⊕ B ⊕ A, (L.map (jointFam m ℓ t hℓ hm blk i)).H₂
      = (∑ c : B × Fin (m / ℓ), (L.map (patCoord m ℓ t blk c)).H₂)
        + ((∑ b : B, (L.map (patRem m ℓ t hℓ blk b)).H₂)
          + ∑ α : A, (L.map (leftCoord m ℓ t hm blk α)).H₂) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    rfl
  rw [hsplit] at hsub
  -- the uncovered atoms
  set U : Finset A := Finset.univ.filter (fun α => ¬ ∃ p : B × Fin t, blk p.1 p.2 = α) with hU
  have hcovimg : (Finset.univ.filter (fun α : A => ∃ p : B × Fin t, blk p.1 p.2 = α))
      = Finset.univ.image (fun p : B × Fin t => blk p.1 p.2) := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  have hcardU : U.card + Fintype.card B * t = Fintype.card A := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset A)) (p := fun α => ∃ p : B × Fin t, blk p.1 p.2 = α)
    rw [hcovimg, Finset.card_image_of_injective _ hblk] at h1
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1 ⊢
    rw [hU]
    omega
  -- the three sums
  have hrem : ∑ b : B, (L.map (patRem m ℓ t hℓ blk b)).H₂
      ≤ (Fintype.card B : ℝ) * (((m % ℓ : ℕ) : ℝ) * (t : ℝ)) := by
    calc ∑ b : B, (L.map (patRem m ℓ t hℓ blk b)).H₂
        ≤ ∑ _b : B, ((m % ℓ : ℕ) : ℝ) * (t : ℝ) :=
          Finset.sum_le_sum fun b _ => H₂_map_patRem_le hℓ blk L b
      _ = (Fintype.card B : ℝ) * (((m % ℓ : ℕ) : ℝ) * (t : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hleft : ∑ α : A, (L.map (leftCoord m ℓ t hm blk α)).H₂ ≤ (U.card : ℝ) * (m : ℝ) := by
    calc ∑ α : A, (L.map (leftCoord m ℓ t hm blk α)).H₂
        ≤ ∑ α : A, (if (∃ p : B × Fin t, blk p.1 p.2 = α) then (0 : ℝ) else (m : ℝ)) :=
          Finset.sum_le_sum fun α _ => H₂_map_leftCoord_le hm blk L α
      _ = (U.card : ℝ) * (m : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
  -- the constant sum
  have hconst : ∑ _c : B × Fin (m / ℓ), ((ℓ * t : ℕ) : ℝ)
      = ((Fintype.card B : ℝ) * ((m / ℓ : ℕ) : ℝ)) * ((ℓ : ℝ) * (t : ℝ)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_sub_distrib, hconst]
  -- arithmetic
  set NB : ℝ := (Fintype.card B : ℝ)
  set R : ℝ := ((m / ℓ : ℕ) : ℝ)
  set MR : ℝ := ((m % ℓ : ℕ) : ℝ)
  set UC : ℝ := (U.card : ℝ)
  have hdm : R * (ℓ : ℝ) + MR = (m : ℝ) := by
    have := Nat.div_add_mod m ℓ
    have hc : ((ℓ * (m / ℓ) + m % ℓ : ℕ) : ℝ) = ((m : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hc
    linarith [hc]
  have hcr : UC + (t : ℝ) * NB = (Fintype.card A : ℝ) := by
    have hc : ((U.card + Fintype.card B * t : ℕ) : ℝ) = ((Fintype.card A : ℕ) : ℝ) := by
      exact_mod_cast hcardU
    push_cast at hc
    linarith [hc]
  have hkey1 : NB * R * ((ℓ : ℝ) * (t : ℝ)) + NB * (MR * (t : ℝ)) = (m : ℝ) * (t : ℝ) * NB := by
    linear_combination (NB * (t : ℝ)) * hdm
  have hkey2 : (m : ℝ) * (t : ℝ) * NB + UC * (m : ℝ) = (m : ℝ) * (Fintype.card A : ℝ) := by
    linear_combination (m : ℝ) * hcr
  linarith [hsub, hrem, hleft, hkey1, hkey2]

/-- **The averaged `t`-wise bound.**  Every pattern's average probability is within
`(2 log2 Δ)/(2 s N) + s/2` of `2^{−ℓt}`, for every `s > 0`. -/
theorem abs_avg_patCoord_prob_le {m ℓ t : ℕ} (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (ht : 0 < t)
    (hm : m ≤ ℓ * t) [Nonempty B]
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) {Δ s : ℝ}
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) (hs : 0 < s) :
    |(∑ c : B × Fin (m / ℓ), (L.map (patCoord m ℓ t blk c)).prob {w})
        / (Fintype.card (B × Fin (m / ℓ)) : ℝ) - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ (2 * Real.log 2 * Δ) / (2 * s * (Fintype.card (B × Fin (m / ℓ)) : ℝ)) + s / 2 := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hr1 : 1 ≤ m / ℓ := Nat.one_le_div_iff hℓ |>.2 hℓm
  haveI : Nonempty (Fin (m / ℓ)) := Fin.pos_iff_nonempty.1 (by omega)
  have hι : 0 < Fintype.card (B × Fin (m / ℓ)) := Fintype.card_pos
  refine abs_avg_sub_le hι
    (fun c => (L.map (patCoord m ℓ t blk c)).prob {w})
    (fun c => 2 * Real.log 2 * (((ℓ * t : ℕ) : ℝ) - (L.map (patCoord m ℓ t blk c)).H₂))
    (1 / (2 : ℝ) ^ (ℓ * t)) (2 * Real.log 2 * Δ) s ?_ ?_ ?_ hs
  · intro c
    have h := H₂_le_of_block (L.map (patCoord m ℓ t blk c))
    nlinarith [hlog2, h]
  · intro c
    exact abs_prob_singleton_sub_le (ℓ := ℓ * t) (Nat.mul_pos hℓ ht) _ w
  · have hsum := sum_patCoord_deficit_le hℓ hm blk hblk L hΔ
    rw [← Finset.mul_sum]
    nlinarith [hlog2, hsum]

/-- **The optimized `t`-wise capacity bound.**  A total entropy deficit of `Δ` on the joint law
controls every `t`-word *pattern* to within

    `2√(log 2 · ℓ · Δ / (|B|·m))`.

With `Δ = δ·|A|` and a blocking of `|B| ≈ |A|/t` blocks this is `2√(log 2 · tℓδ/m)` — the
`t = 1` bound `abs_avg_block_prob_tile_opt` with `ℓ ↦ tℓ`, which is exactly the price of pinning
`t` words at once rather than one. -/
theorem abs_avg_patCoord_prob_opt {m ℓ t : ℕ} (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (ht : 0 < t)
    (hm : m ≤ ℓ * t) [Nonempty B]
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    |(∑ c : B × Fin (m / ℓ), (L.map (patCoord m ℓ t blk c)).prob {w})
        / (Fintype.card (B × Fin (m / ℓ)) : ℝ) - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * Δ / ((Fintype.card B : ℝ) * (m : ℝ))) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := lt_of_lt_of_le hℓ hℓm
    exact_mod_cast this
  have hNB : (0 : ℝ) < (Fintype.card B : ℝ) := by
    have : 0 < Fintype.card B := Fintype.card_pos
    exact_mod_cast this
  have hr1 : 1 ≤ m / ℓ := Nat.one_le_div_iff hℓ |>.2 hℓm
  have hrR : (0 : ℝ) < ((m / ℓ : ℕ) : ℝ) := by exact_mod_cast hr1
  have hN : (Fintype.card (B × Fin (m / ℓ)) : ℝ)
      = (Fintype.card B : ℝ) * ((m / ℓ : ℕ) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  set Aa : ℝ := 2 * Real.log 2 * (ℓ : ℝ) * Δ / ((Fintype.card B : ℝ) * (m : ℝ)) with hAa
  have hApos : 0 < Aa := by rw [hAa]; positivity
  set s : ℝ := Real.sqrt (2 * Aa) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : s * s = 2 * Aa := Real.mul_self_sqrt (by linarith)
  have hmain := abs_avg_patCoord_prob_le hℓ hℓm ht hm blk hblk L w hΔ hs
  rw [hN] at hmain
  have hstep : (2 * Real.log 2 * Δ)
      / (2 * s * ((Fintype.card B : ℝ) * ((m / ℓ : ℕ) : ℝ))) ≤ Aa / s := by
    rw [hAa, div_le_div_iff₀ (by positivity) hs]
    have hcount := two_mul_div_le (m := m) (ℓ := ℓ) hℓ hℓm
    have key : (0 : ℝ) ≤ (Real.log 2 * Δ * s)
        * (2 * ((m / ℓ : ℕ) : ℝ) * (ℓ : ℝ) - (m : ℝ)) :=
      mul_nonneg (by positivity) (by linarith)
    field_simp
    nlinarith [key, hNB, hrR, hs, hlog2, hΔ0, hmR, hℓR]
  have hopt : Aa / s + s / 2 = s := by
    have hA2 : Aa = s * s / 2 := by linarith [hs2]
    rw [hA2]
    field_simp
    norm_num
  have hfin : |(∑ c : B × Fin (m / ℓ), (L.map (patCoord m ℓ t blk c)).prob {w})
      / ((Fintype.card B : ℝ) * ((m / ℓ : ℕ) : ℝ)) - 1 / (2 : ℝ) ^ (ℓ * t)| ≤ s := by
    linarith [hmain, hstep, hopt]
  have hval : s = 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * Δ
      / ((Fintype.card B : ℝ) * (m : ℝ))) := by
    rw [hsdef, hAa]
    rw [show 2 * (2 * Real.log 2 * (ℓ : ℝ) * Δ / ((Fintype.card B : ℝ) * (m : ℝ)))
        = 2 ^ 2 * (Real.log 2 * (ℓ : ℝ) * Δ / ((Fintype.card B : ℝ) * (m : ℝ))) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [hN, ← hval]
  exact hfin

end NormalNumbers.G4Entropy
