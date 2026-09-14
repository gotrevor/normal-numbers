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

/-! ### The averaged word probability, with the tiling budget -/

/-- `⌊m/ℓ⌋ ≥ m/(2ℓ)` for `0 < ℓ ≤ m`: the number of disjoint blocks is within a factor two of
the ideal `m/ℓ`. -/
lemma two_mul_div_le {m ℓ : ℕ} (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) :
    (m : ℝ) ≤ 2 * ((m / ℓ : ℕ) : ℝ) * (ℓ : ℝ) := by
  have hr1 : 1 ≤ m / ℓ := Nat.one_le_div_iff hℓ |>.2 hℓm
  have hnat : m < (m / ℓ + 1) * ℓ := by
    have h1 := Nat.div_add_mod m ℓ
    have h2 : m % ℓ < ℓ := Nat.mod_lt _ hℓ
    have h3 : (m / ℓ + 1) * ℓ = ℓ * (m / ℓ) + ℓ := by ring
    omega
  have hnat2 : m < 2 * (m / ℓ) * ℓ := by nlinarith [hnat, hr1]
  exact_mod_cast hnat2.le

/-- **Abstract form, tiled.**  A joint entropy within `Δ` of the maximum forces the `ℓ`-block
word probabilities, averaged over the coordinates and the `⌊m/ℓ⌋` *disjoint* block positions,
to within `2 log 2 · Δ/(2tN) + t/2` of `2^{−ℓ}`.  Compare
`abs_avg_block_prob_sub_le`, whose numerator carries an extra `|A|·ℓ`. -/
theorem abs_avg_block_prob_tile_le {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    {m ℓ : ℕ} (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ))
    {Δ t : ℝ} (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) (ht : 0 < t) :
    |(∑ c : A × Fin (m / ℓ), (L.map (fullCoord m ℓ c)).prob {w})
        / (Fintype.card (A × Fin (m / ℓ)) : ℝ) - 1 / (2 : ℝ) ^ ℓ|
      ≤ (2 * Real.log 2 * Δ) / (2 * t * (Fintype.card (A × Fin (m / ℓ)) : ℝ)) + t / 2 := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hr1 : 1 ≤ m / ℓ := Nat.one_le_div_iff hℓ |>.2 hℓm
  haveI : Nonempty (Fin (m / ℓ)) := Fin.pos_iff_nonempty.1 (by omega)
  have hι : 0 < Fintype.card (A × Fin (m / ℓ)) := Fintype.card_pos
  refine abs_avg_sub_le hι
    (fun c => (L.map (fullCoord m ℓ c)).prob {w})
    (fun c => 2 * Real.log 2 * ((ℓ : ℝ) - (L.map (fullCoord m ℓ c)).H₂))
    (1 / (2 : ℝ) ^ ℓ) (2 * Real.log 2 * Δ) t ?_ ?_ ?_ ht
  · intro c
    have h := H₂_le_of_block (L.map (fullCoord m ℓ c))
    nlinarith [hlog2, h]
  · intro c
    exact abs_prob_singleton_sub_le hℓ _ w
  · have hsum := sum_block_deficit_tile_le (A := A) (ℓ := ℓ) hℓ L hΔ
    rw [← Finset.mul_sum]
    nlinarith [hlog2, hsum]

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The tiled sampled frequency of a word -/

/-- **The frequency of `w` among the `⌊m_K/ℓ⌋ disjoint` `ℓ`-blocks of the scale-`i` sampled
windows.**  Same as `blockFreq` but over a genuine tiling: no block position is counted twice. -/
noncomputable def blockFreqT (i ℓ : ℕ) (x : ℝ) (w : Fin (2 ^ ℓ)) : ℝ :=
  (∑ c : (gridAt i).Atom × Fin (kk i / ℓ),
      ((jointLawAt i x).map (fullCoord (kk i) ℓ c)).prob {w})
    / (Fintype.card ((gridAt i).Atom × Fin (kk i / ℓ)) : ℝ)

/-- **The capacity inequality, without the sampling floor.**  A per-window deficit of `δ` bits
controls every word of length `ℓ ≤ m_K` to within `2√(log 2 · ℓδ/m_K)`, uniformly in the word
and in `x`.  Unlike `abs_blockFreq_sub_le_of_deficit` there is **no** `√(ℓ²/m_K)` term: at
`δ → 0` the bound goes to `0`, as it must. -/
theorem abs_blockFreqT_sub_le_of_deficit (i ℓ : ℕ) (hℓ : 0 < ℓ) (hℓm : ℓ ≤ kk i) (x : ℝ)
    (w : Fin (2 ^ ℓ)) {δ : ℝ} (hδ : 0 < δ)
    (hdef : ((kk i : ℝ) - δ) * (Fintype.card (gridAt i).Atom : ℝ) ≤ (jointLawAt i x).H₂) :
    |blockFreqT i ℓ x w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / (kk i : ℝ)) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hk0 : (0 : ℝ) < (kk i : ℝ) := by
    have : 0 < kk i := by unfold kk; omega
    exact_mod_cast this
  have hC0 : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
    rw [card_Atom_gridAt]
    have : 0 < (KK i ^ 2 + 1) ^ KK i := Nat.pow_pos (by omega)
    exact_mod_cast this
  have hr1 : 1 ≤ kk i / ℓ := Nat.one_le_div_iff hℓ |>.2 hℓm
  haveI : Nonempty (Fin (kk i / ℓ)) := Fin.pos_iff_nonempty.1 (by omega)
  have hN : (Fintype.card ((gridAt i).Atom × Fin (kk i / ℓ)) : ℝ)
      = (Fintype.card (gridAt i).Atom : ℝ) * ((kk i / ℓ : ℕ) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hrpos : (0 : ℝ) < ((kk i / ℓ : ℕ) : ℝ) := by exact_mod_cast hr1
  have hΔ : (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
      - δ * (Fintype.card (gridAt i).Atom : ℝ) ≤ (jointLawAt i x).H₂ := by
    have : ((kk i : ℝ) - δ) * (Fintype.card (gridAt i).Atom : ℝ)
        = (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
          - δ * (Fintype.card (gridAt i).Atom : ℝ) := by ring
    linarith [hdef, this.symm.le, this.le]
  -- the optimized parameter
  set A : ℝ := 2 * Real.log 2 * (ℓ : ℝ) * δ / (kk i : ℝ) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set t : ℝ := Real.sqrt (2 * A) with htdef
  have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
  have ht2 : t * t = 2 * A := Real.mul_self_sqrt (by linarith)
  have hmain := abs_avg_block_prob_tile_le (A := (gridAt i).Atom) (m := kk i) (ℓ := ℓ)
    hℓ hℓm (jointLawAt i x) w hΔ ht
  rw [hN] at hmain
  -- the error term against `A / t`
  have hstep : (2 * Real.log 2 * (δ * (Fintype.card (gridAt i).Atom : ℝ)))
      / (2 * t * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i / ℓ : ℕ) : ℝ))) ≤ A / t := by
    rw [hA, div_le_div_iff₀ (by positivity) ht]
    have hcount := two_mul_div_le (m := kk i) (ℓ := ℓ) hℓ hℓm
    have key : (0 : ℝ) ≤ (Real.log 2 * δ * (Fintype.card (gridAt i).Atom : ℝ) * t)
        * (2 * ((kk i / ℓ : ℕ) : ℝ) * (ℓ : ℝ) - (kk i : ℝ)) :=
      mul_nonneg (by positivity) (by linarith)
    have hne : (kk i : ℝ) ≠ 0 := hk0.ne'
    field_simp
    nlinarith [key, hC0, hrpos, ht, hlog2, hδ]
  have hopt : A / t + t / 2 = t := by
    have hA2 : A = t * t / 2 := by linarith [ht2]
    rw [hA2]
    field_simp
    norm_num
  have hfin : |blockFreqT i ℓ x w - 1 / (2 : ℝ) ^ ℓ| ≤ t := by
    rw [blockFreqT, hN]
    linarith [hmain, hstep, hopt]
  have hval : t = 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / (kk i : ℝ)) := by
    rw [htdef, hA]
    rw [show 2 * (2 * Real.log 2 * (ℓ : ℝ) * δ / (kk i : ℝ))
        = 2 ^ 2 * (Real.log 2 * (ℓ : ℝ) * δ / (kk i : ℝ)) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [← hval]
  exact hfin

/-! ### `G₄`: the ceiling is the deficit's, and nothing else's -/

/-- **The tiled capacity bound at the implemented schedule.**  `entropy_E1` supplies
`δ = 50√K`, and `m_K = K/4`, so

    `|blockFreqT i ℓ G₄ w − 2^{−ℓ}| ≤ 2√(200 log 2 · ℓ/√K)`   for every `ℓ ≤ m_K`. -/
theorem abs_blockFreqT_sub_le_primeLambertFour (i ℓ : ℕ) (hℓ : 0 < ℓ) (hℓm : ℓ ≤ kk i)
    (w : Fin (2 ^ ℓ)) :
    |blockFreqT i ℓ (primeLambertAtBase 4) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (200 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : 0 < Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_pos.2 hKpos
  have hδ : (0 : ℝ) < 50 * Real.sqrt (KK i) := by positivity
  have hE1 := entropy_E1 (K := KK i) (k₄ := kk i) rfl (KK_ge i)
  have hcard : (Fintype.card (gridAt i).Atom : ℝ) = (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ) := by
    rw [card_Atom_gridAt i]
  have hdef : ((kk i : ℝ) - 50 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (jointLawAt i (primeLambertAtBase 4)).H₂ := by
    rw [hcard, sub_mul]
    exact hE1.le
  refine (abs_blockFreqT_sub_le_of_deficit i ℓ hℓ hℓm _ w hδ hdef).trans ?_
  have harg : Real.log 2 * (ℓ : ℝ) * (50 * Real.sqrt (KK i)) / (kk i : ℝ)
      = 200 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i) := by
    have hkk4 : (KK i : ℝ) = 4 * (kk i : ℝ) := by unfold KK; push_cast; ring
    have hKS : (KK i : ℝ) = Real.sqrt ((KK i : ℕ) : ℝ) * Real.sqrt ((KK i : ℕ) : ℝ) :=
      (Real.mul_self_sqrt hKpos.le).symm
    have hk0 : (0 : ℝ) < (kk i : ℝ) := by linarith
    rw [div_eq_div_iff hk0.ne' hS0.ne']
    have hsq : Real.sqrt ((KK i : ℕ) : ℝ) * Real.sqrt ((KK i : ℕ) : ℝ) = 4 * (kk i : ℝ) := by
      rw [← hKS, hkk4]
    linear_combination (50 * Real.log 2 * (ℓ : ℝ)) * hsq
  rw [harg]

/-- **The tiled frequency theorem with a growing word length.**  For `G₄`, every word length
`ℓ(K) = o(√K)` is controlled — the words may vary with the scale.  Same ceiling as lap 26's
`tendsto_blockFreq_growing`, but now attributable **entirely** to `entropy_E1`'s deficit
`δ = 50√K`: with a deficit `δ_K` the bound reads `2√(log 2 · ℓδ_K/m_K)`, so the controlled
range is exactly `ℓ = o(m_K/δ_K)`. -/
theorem tendsto_blockFreqT_growing (ℓ : ℕ → ℕ) (hpos : ∀ᶠ i in atTop, 0 < ℓ i)
    (hle : ∀ᶠ i in atTop, ℓ i ≤ kk i)
    (hgrow : Tendsto (fun i => (ℓ i : ℝ) / Real.sqrt (KK i)) atTop (nhds 0))
    (w : ∀ i, Fin (2 ^ ℓ i)) :
    Tendsto (fun i => blockFreqT i (ℓ i) (primeLambertAtBase 4) (w i) - 1 / (2 : ℝ) ^ (ℓ i))
      atTop (nhds 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hinner : Tendsto (fun i => 200 * Real.log 2 * (ℓ i : ℝ) / Real.sqrt (KK i))
      atTop (nhds 0) := by
    have h := hgrow.const_mul (200 * Real.log 2)
    simp only [mul_zero] at h
    refine h.congr fun i => ?_
    rw [mul_div_assoc]
  have hsq : Tendsto (fun i => 2 * Real.sqrt (200 * Real.log 2 * (ℓ i : ℝ)
      / Real.sqrt (KK i))) atTop (nhds 0) := by
    have := hinner.sqrt
    simpa using this.const_mul (2 : ℝ)
  refine squeeze_zero_norm' ?_ hsq
  filter_upwards [hpos, hle] with i hp hl
  simpa [Real.norm_eq_abs] using
    abs_blockFreqT_sub_le_primeLambertFour i (ℓ i) hp hl (w i)

/-! ### The faithfulness rendering of the tiled frequency

The tiled blocks are *aligned*: for `j < m_K/ℓ` one has `(j+1)ℓ ≤ m_K`, so `blkAt_blockVal`
applies directly and the `j`-th block is the `ℓ`-window at `p + jℓ` — no `min` correction, as
`blockFreq` needed for its overlapping last coordinate.
-/

open Classical in
/-- **The count rendering.**  `blockFreqT` is the density, among the
`|P_K|·|Atom_K|·⌊m_K/ℓ⌋` triples `(n, α, j)`, of those whose `j`-th tiled block is `w`. -/
theorem blockFreqT_eq_count (i ℓ : ℕ) (x : ℝ) (w : Fin (2 ^ ℓ)) :
    blockFreqT i ℓ x w
      = (∑ c : (gridAt i).Atom × Fin (kk i / ℓ),
            (((PK i).filter fun n =>
              blkAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ))
        / (((PK i).card : ℝ)
            * (Fintype.card ((gridAt i).Atom × Fin (kk i / ℓ)) : ℝ)) := by
  classical
  have hp : ∀ c : (gridAt i).Atom × Fin (kk i / ℓ),
      ((jointLawAt i x).map (fullCoord (kk i) ℓ c)).prob {w}
        = (((PK i).filter fun n =>
              blkAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ)
          / ((PK i).card : ℝ) := by
    intro c
    rw [FinLaw.prob, Finset.sum_singleton]
    exact map_empirical_p (apSample_nonempty (gridAt i) (b₀_lt_X_at i)) _ _ w
  have hsum : (∑ c : (gridAt i).Atom × Fin (kk i / ℓ),
        ((jointLawAt i x).map (fullCoord (kk i) ℓ c)).prob {w})
      = (∑ c : (gridAt i).Atom × Fin (kk i / ℓ),
          (((PK i).filter fun n =>
            blkAt (kk i) ℓ (c.2 : ℕ) (ZVec (gridAt i) (kk i) x n c.1) = w).card : ℝ))
        / ((PK i).card : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => hp c
  rw [blockFreqT, hsum, div_div]

open Classical in
/-- **The digit rendering.**  The event is: the `ℓ` binary digits of `x` beginning at position
`2·kIdx(n,α) + jℓ` spell `w`.  Exactly aligned — the blocks tile the window. -/
theorem blockFreqT_eq_digits (i ℓ : ℕ) (hℓ : 0 < ℓ) (x : ℝ) (w : Fin (2 ^ ℓ)) :
    blockFreqT i ℓ x w
      = (∑ c : (gridAt i).Atom × Fin (kk i / ℓ),
            (((PK i).filter fun n =>
              blockVal (Int.fract x) (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ) * ℓ) ℓ
                = (w : ℕ)).card : ℝ))
        / (((PK i).card : ℝ)
            * (Fintype.card ((gridAt i).Atom × Fin (kk i / ℓ)) : ℝ)) := by
  classical
  rw [blockFreqT_eq_count i ℓ x w]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  have hZ : ∀ n : ℕ, ZVec (gridAt i) (kk i) x n c.1
      = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n c.1) (kk i), blockVal_lt _ _ _⟩ :=
    fun n => Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n c.1)
  have halign : ((c.2 : ℕ) + 1) * ℓ ≤ kk i := by
    have h1 : (c.2 : ℕ) < kk i / ℓ := c.2.isLt
    have h2 : (kk i / ℓ) * ℓ ≤ kk i := Nat.div_mul_le_self _ _
    have h3 : ((c.2 : ℕ) + 1) * ℓ ≤ (kk i / ℓ) * ℓ := Nat.mul_le_mul_right ℓ (by omega)
    omega
  refine Finset.filter_congr fun n _ => ?_
  rw [hZ n, blkAt_blockVal _ _ _ _ _ halign]
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

open Classical in
/-- **The tiled headline over `OccursAt`.**  For every finite binary word `w` and every word
length `ℓ(K) = o(√K)`, the proportion of triples `(n, α, j)` at which `w` occurs in the binary
expansion of `G₄` at position `2·kIdx(n,α) + j|w|` tends to `2^{−|w|}`. -/
theorem tendsto_occursCountT_primeLambertFour (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ i, ∀ h : i < v.length, v[i] < 2) :
    Tendsto (fun i =>
      (∑ c : (gridAt i).Atom × Fin (kk i / v.length),
          (((PK i).filter fun n =>
            OccursAt 2 (primeLambertAtBase 4) v
              (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ) * v.length)).card : ℝ))
        / (((PK i).card : ℝ)
            * (Fintype.card ((gridAt i).Atom × Fin (kk i / v.length)) : ℝ)))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
  classical
  have hmain : Tendsto (fun i => blockFreqT i v.length (primeLambertAtBase 4)
      ⟨wordVal v, wordVal_lt hv⟩) atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
    have hgrow : Tendsto (fun i => (v.length : ℝ) / Real.sqrt (KK i)) atTop (nhds 0) := by
      have hsqrt : Tendsto (fun i => Real.sqrt (KK i)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_KK_atTop
      exact hsqrt.const_div_atTop _
    have hle : ∀ᶠ i in atTop, v.length ≤ kk i := by
      filter_upwards [eventually_ge_atTop v.length] with i hi
      unfold kk
      omega
    have := tendsto_blockFreqT_growing (fun _ => v.length)
      (Filter.Eventually.of_forall fun _ => hlen) hle hgrow
      (fun _ => ⟨wordVal v, wordVal_lt hv⟩)
    have hlim : Tendsto (fun _ : ℕ => (1 : ℝ) / (2 : ℝ) ^ v.length) atTop
        (nhds (1 / (2 : ℝ) ^ v.length)) := tendsto_const_nhds
    simpa using this.add hlim
  refine hmain.congr fun i => ?_
  rw [blockFreqT_eq_digits i v.length hlen]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  refine Finset.filter_congr fun n _ => ?_
  exact blockVal_eq_wordVal_iff (y := primeLambertAtBase 4) hv

end NormalNumbers.G4.Sched
