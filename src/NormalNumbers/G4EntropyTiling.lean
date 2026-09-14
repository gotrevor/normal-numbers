/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyRender

/-!
# The disjoint tiling: removing the `ℓ²/m` floor from the capacity inequality

`G4EntropyWord`'s block family uses `m/ℓ + 1` coordinates, the last of which **overlaps** its
predecessor; that overlap costs `|A|·ℓ` slack in `sum_block_deficit_le`, and that slack is the
whole source of the `√(ℓ²/m_K)` term in lap 28's capacity inequality.  The slack is avoidable:
replace the overlapping last coordinate by the **remainder** coordinate — the low `m % ℓ` bits
— and the `m/ℓ` full blocks together with it *tile* the window exactly.  The alphabet budget is
then `m` bits on the nose and the slack is **zero**:

    `∑_{α, j < m/ℓ} (ℓ − H₂ of block (α,j)) ≤ Δ`.

Consequence (`abs_blockFreqT_sub_le_of_deficit`): a deficit of `δ` bits per window controls
words of length `ℓ` to within `2√(log 2 · ℓ δ / m_K)` — **no** deficit-free floor.  So the
`o(√K)` ceiling for `G₄` is due entirely to `entropy_E1`'s `δ = 50√K`, and not at all to the
sampling geometry: with a deficit `δ` the control reaches every `ℓ = o(m_K/δ)`.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

/-! ### The remainder coordinate -/

/-- The low `m % ℓ` bits of an `m`-bit window, viewed in the `ℓ`-bit alphabet. -/
def remCoord (m ℓ : ℕ) (hℓ : 0 < ℓ) (z : Fin (2 ^ m)) : Fin (2 ^ ℓ) :=
  ⟨(z : ℕ) % 2 ^ (m % ℓ), lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
    (Nat.pow_le_pow_right (by norm_num) (Nat.mod_lt _ hℓ).le)⟩

@[simp] lemma remCoord_val (m ℓ : ℕ) (hℓ : 0 < ℓ) (z : Fin (2 ^ m)) :
    ((remCoord m ℓ hℓ z : Fin (2 ^ ℓ)) : ℕ) = (z : ℕ) % 2 ^ (m % ℓ) := rfl

/-- The prefix recursion: agreeing on the first `j` aligned blocks forces the top bits to
agree.  (Same argument as `G4EntropyWord.prefix_congr`, which is private there.) -/
private lemma tile_prefix_congr {m ℓ : ℕ} {z z' : ℕ} (hz : z < 2 ^ m) (hz' : z' < 2 ^ m)
    (h : ∀ j < m / ℓ, z / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ
      = z' / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ) :
    ∀ j ≤ m / ℓ, z / 2 ^ (m - j * ℓ) = z' / 2 ^ (m - j * ℓ) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.zero_mul, Nat.sub_zero]
    rw [Nat.div_eq_of_lt hz, Nat.div_eq_of_lt hz']
  | succ j ih =>
    intro hj
    have hjr : j ≤ m / ℓ := by omega
    have hle : (j + 1) * ℓ ≤ m :=
      le_trans (Nat.mul_le_mul_right ℓ hj) (Nat.div_mul_le_self m ℓ)
    have hsplit : m - j * ℓ = (m - (j + 1) * ℓ) + ℓ := by
      have : (j + 1) * ℓ = j * ℓ + ℓ := by ring
      omega
    have key : ∀ w : ℕ, w / 2 ^ (m - (j + 1) * ℓ)
        = 2 ^ ℓ * (w / 2 ^ (m - j * ℓ)) + (w / 2 ^ (m - (j + 1) * ℓ)) % 2 ^ ℓ := by
      intro w
      have hdd : w / 2 ^ (m - (j + 1) * ℓ) / 2 ^ ℓ = w / 2 ^ (m - j * ℓ) := by
        rw [Nat.div_div_eq_div_mul, ← pow_add, ← hsplit]
      have hdm := Nat.div_add_mod (w / 2 ^ (m - (j + 1) * ℓ)) (2 ^ ℓ)
      rw [hdd] at hdm
      exact hdm.symm
    calc z / 2 ^ (m - (j + 1) * ℓ)
        = 2 ^ ℓ * (z / 2 ^ (m - j * ℓ)) + (z / 2 ^ (m - (j + 1) * ℓ)) % 2 ^ ℓ := key z
      _ = 2 ^ ℓ * (z' / 2 ^ (m - j * ℓ)) + (z' / 2 ^ (m - (j + 1) * ℓ)) % 2 ^ ℓ := by
          rw [ih hjr, h j (by omega)]
      _ = z' / 2 ^ (m - (j + 1) * ℓ) := (key z').symm

/-- **The tiling coordinates determine the window.**  The `m/ℓ` full aligned blocks together
with the low `m % ℓ` bits tile an `m`-bit value exactly. -/
theorem tile_injective {m ℓ : ℕ} (hℓ : 0 < ℓ) {z z' : Fin (2 ^ m)}
    (hblk : ∀ j < m / ℓ, blkAt m ℓ j z = blkAt m ℓ j z')
    (hrem : remCoord m ℓ hℓ z = remCoord m ℓ hℓ z') : z = z' := by
  have hcoord : ∀ j < m / ℓ, (z : ℕ) / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ
      = (z' : ℕ) / 2 ^ (m - (j + 1) * ℓ) % 2 ^ ℓ := fun j hj => congrArg Fin.val (hblk j hj)
  have hpre := tile_prefix_congr z.isLt z'.isLt hcoord (m / ℓ) le_rfl
  have ht : m - m / ℓ * ℓ = m % ℓ := by
    have := Nat.div_add_mod m ℓ
    have : ℓ * (m / ℓ) = m / ℓ * ℓ := by ring
    omega
  rw [ht] at hpre
  have hlow : (z : ℕ) % 2 ^ (m % ℓ) = (z' : ℕ) % 2 ^ (m % ℓ) := congrArg Fin.val hrem
  refine Fin.ext ?_
  have h1 := Nat.div_add_mod (z : ℕ) (2 ^ (m % ℓ))
  have h2 := Nat.div_add_mod (z' : ℕ) (2 ^ (m % ℓ))
  rw [hpre, hlow] at h1
  omega

/-! ### The mixed coordinate family on the joint sample -/

/-- The `(α, j)` tiling coordinate: for `j < m/ℓ` the `j`-th aligned `ℓ`-block of the window at
`α`, and for the final index the low `m % ℓ` bits of that window. -/
def tileCoord {A : Type*} (m ℓ : ℕ) (hℓ : 0 < ℓ) (i : A × Fin (m / ℓ + 1))
    (z : A → Fin (2 ^ m)) : Fin (2 ^ ℓ) :=
  Fin.lastCases (remCoord m ℓ hℓ (z i.1)) (fun j => blkAt m ℓ (j : ℕ) (z i.1)) i.2

/-- The full-block coordinate, indexed by the `m/ℓ` genuinely disjoint blocks. -/
def fullCoord {A : Type*} (m ℓ : ℕ) (i : A × Fin (m / ℓ)) (z : A → Fin (2 ^ m)) : Fin (2 ^ ℓ) :=
  blkAt m ℓ (i.2 : ℕ) (z i.1)

lemma fullCoord_pair {A : Type*} (m ℓ : ℕ) (α : A) (j : Fin (m / ℓ)) :
    fullCoord m ℓ (α, j) = fun z => blkAt m ℓ (j : ℕ) (z α) := rfl

lemma tileCoord_of_lt {A : Type*} {m ℓ : ℕ} (hℓ : 0 < ℓ) (α : A) (j : Fin (m / ℓ + 1))
    (hj : (j : ℕ) < m / ℓ) (z : A → Fin (2 ^ m)) :
    tileCoord m ℓ hℓ (α, j) z = blkAt m ℓ (j : ℕ) (z α) := by
  obtain ⟨jv, hjv⟩ := j
  simp only [tileCoord]
  rw [show (⟨jv, hjv⟩ : Fin (m / ℓ + 1)) = Fin.castSucc ⟨jv, hj⟩ from rfl, Fin.lastCases_castSucc]

@[simp] lemma tileCoord_castSucc {A : Type*} {m ℓ : ℕ} (hℓ : 0 < ℓ) (α : A)
    (j : Fin (m / ℓ)) (z : A → Fin (2 ^ m)) :
    tileCoord m ℓ hℓ (α, j.castSucc) z = blkAt m ℓ (j : ℕ) (z α) := by
  simp [tileCoord]

@[simp] lemma tileCoord_last {A : Type*} {m ℓ : ℕ} (hℓ : 0 < ℓ) (α : A)
    (z : A → Fin (2 ^ m)) :
    tileCoord m ℓ hℓ (α, Fin.last (m / ℓ)) z = remCoord m ℓ hℓ (z α) := by
  simp [tileCoord]

theorem tileCoord_injective {A : Type*} {m ℓ : ℕ} (hℓ : 0 < ℓ) :
    Function.Injective
      (fun z : A → Fin (2 ^ m) => fun i : A × Fin (m / ℓ + 1) => tileCoord m ℓ hℓ i z) := by
  intro z z' h
  funext α
  refine tile_injective hℓ (fun j hj => ?_) ?_
  · have hc := congrFun h (α, (⟨j, hj⟩ : Fin (m / ℓ)).castSucc)
    simp only at hc
    have hjj : ((⟨j, hj⟩ : Fin (m / ℓ)).castSucc : ℕ) < m / ℓ := by simpa using hj
    rw [tileCoord_of_lt hℓ α _ hjj, tileCoord_of_lt hℓ α _ hjj] at hc
    exact hc
  · have hc := congrFun h (α, Fin.last (m / ℓ))
    simp only at hc
    rw [tileCoord_last, tileCoord_last] at hc
    exact hc

/-- The remainder coordinate lives in an alphabet of `2^{m % ℓ}` values, so its entropy is at
most `m % ℓ` bits. -/
theorem H₂_map_rem_le {A : Type*} [Fintype A] [DecidableEq A] {m ℓ : ℕ} (hℓ : 0 < ℓ)
    (L : FinLaw (A → Fin (2 ^ m))) (α : A) :
    (L.map (fun z => remCoord m ℓ hℓ (z α))).H₂ ≤ ((m % ℓ : ℕ) : ℝ) := by
  classical
  have hpos : 0 < 2 ^ (m % ℓ) := by positivity
  set T : Finset (Fin (2 ^ ℓ)) := Finset.univ.filter (fun v : Fin (2 ^ ℓ) => (v : ℕ) < 2 ^ (m % ℓ))
    with hT
  have hsupp : ∀ v : Fin (2 ^ ℓ), (L.map (fun z => remCoord m ℓ hℓ (z α))).p v ≠ 0 → v ∈ T := by
    intro v hv
    rw [FinLaw.map_p] at hv
    have hne : (Finset.univ.filter (fun z : A → Fin (2 ^ m) =>
        remCoord m ℓ hℓ (z α) = v)).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      rw [hcon] at hv
      simp at hv
    obtain ⟨z, hz⟩ := hne
    rw [Finset.mem_filter] at hz
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hz.2]
    exact Nat.mod_lt _ hpos
  have hcard : T.card ≤ 2 ^ (m % ℓ) := by
    classical
    have hle : T.card ≤ (Finset.range (2 ^ (m % ℓ))).card := by
      refine Finset.card_le_card_of_injOn (fun v => (v : ℕ)) (fun v hv => ?_)
        (fun a _ b _ hab => Fin.ext hab)
      simp only [hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hv ⊢
      exact hv.2
    simpa using hle
  refine (L.map (fun z => remCoord m ℓ hℓ (z α))).H₂_le_logb hpos T hsupp hcard |>.trans_eq ?_
  rw [show ((2 ^ (m % ℓ) : ℕ) : ℝ) = (2 : ℝ) ^ (m % ℓ) by push_cast; ring,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]

/-! ### The zero-slack deficit budget -/

/-- **The tiling deficit budget.**  With the window tiled exactly, the *full* `ℓ`-blocks carry a
total entropy deficit of at most `Δ` — no `|A|·ℓ` slack. -/
theorem sum_block_deficit_tile_le {A : Type*} [Fintype A] [DecidableEq A] {m ℓ : ℕ}
    (hℓ : 0 < ℓ) (L : FinLaw (A → Fin (2 ^ m))) {Δ : ℝ}
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    ∑ i : A × Fin (m / ℓ), ((ℓ : ℝ) - (L.map (fullCoord m ℓ i)).H₂) ≤ Δ := by
  classical
  have hsub := L.H₂_le_sum_H₂_map (fun i : A × Fin (m / ℓ + 1) => tileCoord m ℓ hℓ i)
    (tileCoord_injective hℓ)
  -- split the coordinate sum into the full blocks and the remainders
  have hsplit : ∑ i : A × Fin (m / ℓ + 1), (L.map (tileCoord m ℓ hℓ i)).H₂
      = ∑ i : A × Fin (m / ℓ), (L.map (fullCoord m ℓ i)).H₂
        + ∑ α : A, (L.map (fun z => remCoord m ℓ hℓ (z α))).H₂ := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hfun : tileCoord m ℓ hℓ (α, j.castSucc) = fullCoord m ℓ (α, j) := by
        funext z
        rw [fullCoord_pair]
        exact tileCoord_of_lt hℓ α j.castSucc (by simpa using j.isLt) z
      rw [hfun]
    · have hfun : tileCoord m ℓ hℓ (α, Fin.last (m / ℓ))
          = (fun z => remCoord m ℓ hℓ (z α)) := by
        funext z
        exact tileCoord_last hℓ α z
      rw [hfun]
  have hrem : ∑ α : A, (L.map (fun z => remCoord m ℓ hℓ (z α))).H₂
      ≤ (Fintype.card A : ℝ) * ((m % ℓ : ℕ) : ℝ) := by
    calc ∑ α : A, (L.map (fun z => remCoord m ℓ hℓ (z α))).H₂
        ≤ ∑ _α : A, ((m % ℓ : ℕ) : ℝ) :=
          Finset.sum_le_sum fun α _ => H₂_map_rem_le hℓ L α
      _ = (Fintype.card A : ℝ) * ((m % ℓ : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hexp : ∑ i : A × Fin (m / ℓ), ((ℓ : ℝ) - (L.map (fullCoord m ℓ i)).H₂)
      = (Fintype.card A : ℝ) * ((m / ℓ : ℕ) : ℝ) * (ℓ : ℝ)
        - ∑ i : A × Fin (m / ℓ), (L.map (fullCoord m ℓ i)).H₂ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    congr 1
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have htile : ((m / ℓ : ℕ) : ℝ) * (ℓ : ℝ) + ((m % ℓ : ℕ) : ℝ) = (m : ℝ) := by
    have := Nat.div_add_mod m ℓ
    have hcast : ((ℓ * (m / ℓ) + m % ℓ : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast this
    push_cast at hcast
    linarith
  rw [hsplit] at hsub
  rw [hexp]
  have hmul : (Fintype.card A : ℝ) * (((m / ℓ : ℕ) : ℝ) * (ℓ : ℝ) + ((m % ℓ : ℕ) : ℝ))
      = (Fintype.card A : ℝ) * (m : ℝ) := by rw [htile]
  nlinarith [hsub, hΔ, hrem, hmul]

end NormalNumbers.G4Entropy
