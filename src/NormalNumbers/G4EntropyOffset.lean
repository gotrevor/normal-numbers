/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyTiling

/-!
# All offsets, not just the aligned ones

`G4EntropyTiling` controls the frequency of a word `w` among the `⌊m/ℓ⌋` blocks of the sampled
window that start at positions `0, ℓ, 2ℓ, …` — one *aligned* tiling.  Normality counts
occurrences at **every** position of the window, so the honest statement averages over the `ℓ`
offset classes `r = 0, …, ℓ−1`.

The reduction is free of loss.  Dropping the top `r` bits of each window is the map
`lowCoord`; the pair (top `r` bits, low `m−r` bits) is injective, so by generalized
subadditivity

    `H₂ L ≤ H₂ (L.map lowTuple) + |A|·r`,

i.e. a window law with deficit `δ·|A|` on `m` bits truncates to a window law with the **same**
deficit `δ·|A|` on `m − r` bits (the maximum drops by exactly `|A|·r` too).  The aligned tiling
of the truncated window is the offset-`r` tiling of the original, so every offset class inherits
the tiled capacity bound with `m` replaced by `m − r`.

* `FinLaw.map_map`, `FinLaw.H₂_map_injective` — pushforward algebra.
* `H₂_lowTuple_ge` — the truncation costs at most `|A|·r` bits.
* `abs_avg_block_prob_tile_opt` — the abstract, `t`-optimized form of
  `abs_avg_block_prob_tile_le` (the tiled capacity bound for a `FinLaw`, no schedule).
* `abs_avg_block_prob_offset_le` — the same bound for the offset-`r` tiling.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

namespace FinLaw

variable {Ω Ω' Ω'' : Type*} [Fintype Ω] [Fintype Ω'] [Fintype Ω'']

/-- **Entropy is invariant under an injective post-composition.** -/
theorem H₂_map_comp_injective [DecidableEq Ω'] [DecidableEq Ω''] (L : FinLaw Ω) (f : Ω → Ω')
    {g : Ω' → Ω''} (hg : Function.Injective g) :
    (L.map (fun ω => g (f ω))).H₂ = (L.map f).H₂ := by
  classical
  have key : ∀ ω' : Ω', (L.map (fun ω => g (f ω))).p (g ω') = (L.map f).p ω' := by
    intro ω'
    rw [map_p, map_p]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    refine Finset.filter_congr fun ω _ => ?_
    exact ⟨fun h => hg h, fun h => by rw [h]⟩
  have hzero : ∀ ω'' ∈ (Finset.univ : Finset Ω'') \ Finset.univ.image g,
      Real.negMulLog ((L.map (fun ω => g (f ω))).p ω'') = 0 := by
    intro ω'' hω''
    rw [Finset.mem_sdiff, Finset.mem_image] at hω''
    have hmass : (L.map (fun ω => g (f ω))).p ω'' = 0 := by
      rw [map_p]
      refine Finset.sum_eq_zero fun ω hω => ?_
      rw [Finset.mem_filter] at hω
      exact absurd ⟨f ω, Finset.mem_univ _, hω.2⟩ hω''.2
    rw [hmass, Real.negMulLog_zero]
  have hsum : ∑ ω'' : Ω'', Real.negMulLog ((L.map (fun ω => g (f ω))).p ω'')
      = ∑ ω' : Ω', Real.negMulLog ((L.map f).p ω') := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image g))
      (fun ω'' _ h => hzero ω'' (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩))]
    rw [Finset.sum_image (fun a _ b _ h => hg h)]
    exact Finset.sum_congr rfl fun ω' _ => by rw [key ω']
  rw [H₂, H₂, hsum]

/-- Composite form, with the composition supplied pointwise: this keeps the two pushforwards
syntactically equal at the use site, which matters because unifying two `FinLaw.map`s forces
the elaborator through their `DecidableEq` instances. -/
theorem H₂_map_congr_comp [DecidableEq Ω'] [DecidableEq Ω''] (L : FinLaw Ω) (f : Ω → Ω')
    {g : Ω' → Ω''} (hg : Function.Injective g) (F : Ω → Ω'') (hF : ∀ ω, F ω = g (f ω)) :
    (L.map F).H₂ = (L.map f).H₂ := by
  have hFe : F = fun ω => g (f ω) := funext hF
  rw [hFe]
  exact L.H₂_map_comp_injective f hg

end FinLaw

/-! ### Truncating the top `r` bits -/

/-- The low `m − r` bits of an `m`-bit window. -/
def lowCoord (m r : ℕ) (z : Fin (2 ^ m)) : Fin (2 ^ (m - r)) :=
  ⟨(z : ℕ) % 2 ^ (m - r), Nat.mod_lt _ (by positivity)⟩

/-- The top `r` bits, kept inside the `m`-bit alphabet. -/
def hiCoord (m r : ℕ) (z : Fin (2 ^ m)) : Fin (2 ^ m) :=
  ⟨(z : ℕ) / 2 ^ (m - r), lt_of_le_of_lt (Nat.div_le_self _ _) z.isLt⟩

/-- The truncation applied coordinatewise. -/
def lowTuple {A : Type*} (m r : ℕ) (z : A → Fin (2 ^ m)) : A → Fin (2 ^ (m - r)) :=
  fun α => lowCoord m r (z α)

/-- The low part re-embedded into the `m`-bit alphabet. -/
def embLow (m r : ℕ) (v : Fin (2 ^ (m - r))) : Fin (2 ^ m) :=
  ⟨(v : ℕ), lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le m r))⟩

/-- The high part's alphabet re-embedded into the `m`-bit alphabet. -/
def embHi (m r : ℕ) (hr : r ≤ m) (u : Fin (2 ^ r)) : Fin (2 ^ m) :=
  ⟨(u : ℕ), lt_of_lt_of_le u.isLt (Nat.pow_le_pow_right (by norm_num) hr)⟩

lemma hiCoord_lt {m r : ℕ} (hr : r ≤ m) (z : Fin (2 ^ m)) :
    ((hiCoord m r z : Fin (2 ^ m)) : ℕ) < 2 ^ r := by
  have hz : (z : ℕ) < 2 ^ r * 2 ^ (m - r) := by
    rw [← pow_add, Nat.add_sub_cancel' hr]
    exact z.isLt
  exact Nat.div_lt_iff_lt_mul (by positivity) |>.2 hz

/-- Reassembling a window from its high and low parts. -/
lemma split_eq {m r : ℕ} (z : Fin (2 ^ m)) :
    (z : ℕ) = 2 ^ (m - r) * ((hiCoord m r z : Fin (2 ^ m)) : ℕ)
      + ((lowCoord m r z : Fin (2 ^ (m - r))) : ℕ) := by
  simp only [hiCoord, lowCoord]
  exact (Nat.div_add_mod _ _).symm

/-- The coordinate family splitting a window into (all low parts) and (each high part). -/
def splitFam {A : Type*} (m r : ℕ) :
    Option A → (A → Fin (2 ^ m)) → (A → Fin (2 ^ m))
  | none => fun z => (fun v => fun α => embLow m r (v α)) (lowTuple m r z)
  | some α => fun z _ => hiCoord m r (z α)

@[simp] lemma splitFam_none {A : Type*} (m r : ℕ) (z : A → Fin (2 ^ m)) :
    splitFam m r none z = fun α => embLow m r (lowCoord m r (z α)) := rfl

@[simp] lemma splitFam_some {A : Type*} (m r : ℕ) (α : A) (z : A → Fin (2 ^ m)) :
    splitFam m r (some α) z = fun _ => hiCoord m r (z α) := rfl

set_option maxHeartbeats 1000000 in
/-- **Truncation costs at most `|A|·r` bits.** -/
theorem H₂_lowTuple_ge {A : Type*} [Fintype A] [DecidableEq A] {m r : ℕ} (hr : r ≤ m)
    (L : FinLaw (A → Fin (2 ^ m))) :
    L.H₂ - (Fintype.card A : ℝ) * r ≤ (L.map (lowTuple m r)).H₂ := by
  have hinj : Function.Injective (fun z : A → Fin (2 ^ m) => fun i => splitFam m r i z) := by
    intro z z' h
    funext α
    have hlow : ((lowCoord m r (z α) : Fin (2 ^ (m - r))) : ℕ)
        = ((lowCoord m r (z' α) : Fin (2 ^ (m - r))) : ℕ) := by
      have := congrFun (congrFun h none) α
      simpa [embLow, Fin.ext_iff] using this
    have hhi : ((hiCoord m r (z α) : Fin (2 ^ m)) : ℕ)
        = ((hiCoord m r (z' α) : Fin (2 ^ m)) : ℕ) := by
      have := congrFun (congrFun h (some α)) α
      simpa [Fin.ext_iff] using this
    have h1 := split_eq (m := m) (r := r) (z α)
    have h2 := split_eq (m := m) (r := r) (z' α)
    exact Fin.ext (by rw [h1, h2, hhi, hlow])
  have hsub := L.H₂_le_sum_H₂_map (fun i => splitFam m r i) hinj
  rw [Fintype.sum_option] at hsub
  -- the low tuple keeps its entropy
  have hlowH : (L.map (splitFam m r none)).H₂ = (L.map (lowTuple m r)).H₂ := by
    have hg : Function.Injective
        (fun v : A → Fin (2 ^ (m - r)) => fun α => embLow m r (v α)) := by
      intro v v' h
      funext α
      have := congrFun h α
      exact Fin.ext (by simpa [embLow, Fin.ext_iff] using this)
    exact L.H₂_map_congr_comp (lowTuple m r) hg (splitFam m r none) (fun z => rfl)
  -- each high part carries at most `r` bits
  have hhiH : ∀ α : A, (L.map (splitFam m r (some α))).H₂ ≤ (r : ℝ) := by
    intro α
    have hpos : 0 < 2 ^ r := by positivity
    set T : Finset (A → Fin (2 ^ m)) :=
      Finset.image (fun u : Fin (2 ^ r) => (fun _ : A => embHi m r hr u)) Finset.univ with hT
    have hsupp : ∀ v : A → Fin (2 ^ m), (L.map (splitFam m r (some α))).p v ≠ 0 → v ∈ T := by
      intro v hv
      rw [FinLaw.map_p] at hv
      have hne : (Finset.univ.filter
          (fun z : A → Fin (2 ^ m) => splitFam m r (some α) z = v)).Nonempty := by
        by_contra hcon
        rw [Finset.not_nonempty_iff_eq_empty] at hcon
        rw [hcon] at hv
        simp at hv
      obtain ⟨z, hz⟩ := hne
      rw [Finset.mem_filter] at hz
      refine Finset.mem_image.mpr
        ⟨⟨((hiCoord m r (z α) : Fin (2 ^ m)) : ℕ), hiCoord_lt hr (z α)⟩, Finset.mem_univ _, ?_⟩
      funext β
      have hzv := congrFun hz.2 β
      rw [← hzv]
      exact Fin.ext (by simp [embHi])
    have hcard : T.card ≤ 2 ^ r := by
      calc T.card ≤ (Finset.univ : Finset (Fin (2 ^ r))).card := Finset.card_image_le
        _ = 2 ^ r := by simp
    have h := (L.map (splitFam m r (some α))).H₂_le_logb hpos T hsupp hcard
    have hlg : Real.logb 2 ((2 ^ r : ℕ) : ℝ) = (r : ℝ) := by
      rw [show ((2 ^ r : ℕ) : ℝ) = (2 : ℝ) ^ r by push_cast; ring, Real.logb, Real.log_pow]
      have : Real.log 2 ≠ 0 := by
        have := Real.log_pos (show (1:ℝ) < 2 by norm_num)
        linarith
      field_simp
    rwa [hlg] at h
  have hsum : ∑ α : A, (L.map (splitFam m r (some α))).H₂ ≤ (Fintype.card A : ℝ) * r := by
    calc ∑ α : A, (L.map (splitFam m r (some α))).H₂
        ≤ ∑ _α : A, (r : ℝ) := Finset.sum_le_sum fun α _ => hhiH α
      _ = (Fintype.card A : ℝ) * r := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [hlowH] at hsub
  linarith

/-! ### The tiled capacity bound, abstract and `t`-optimized -/

/-- `abs_avg_block_prob_tile_le` with the free parameter optimized: a deficit of `δ` bits per
coordinate controls every `ℓ`-block word to within `2√(log 2 · ℓδ/m)`. -/
theorem abs_avg_block_prob_tile_opt {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    {m ℓ : ℕ} (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ))
    {δ : ℝ} (hδ : 0 < δ)
    (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂) :
    |(∑ c : A × Fin (m / ℓ), (L.map (fullCoord m ℓ c)).prob {w})
        / (Fintype.card (A × Fin (m / ℓ)) : ℝ) - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / (m : ℝ)) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := lt_of_lt_of_le hℓ hℓm
    exact_mod_cast this
  have hC0 : (0 : ℝ) < (Fintype.card A : ℝ) := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this
  have hr1 : 1 ≤ m / ℓ := Nat.one_le_div_iff hℓ |>.2 hℓm
  haveI : Nonempty (Fin (m / ℓ)) := Fin.pos_iff_nonempty.1 (by omega)
  have hN : (Fintype.card (A × Fin (m / ℓ)) : ℝ)
      = (Fintype.card A : ℝ) * ((m / ℓ : ℕ) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hrpos : (0 : ℝ) < ((m / ℓ : ℕ) : ℝ) := by exact_mod_cast hr1
  have hΔ : (m : ℝ) * (Fintype.card A : ℝ) - δ * (Fintype.card A : ℝ) ≤ L.H₂ := by
    have he : ((m : ℝ) - δ) * (Fintype.card A : ℝ)
        = (m : ℝ) * (Fintype.card A : ℝ) - δ * (Fintype.card A : ℝ) := by ring
    linarith [hdef, he.symm.le, he.le]
  set Q : ℝ := 2 * Real.log 2 * (ℓ : ℝ) * δ / (m : ℝ) with hQ
  have hQpos : 0 < Q := by rw [hQ]; positivity
  set t : ℝ := Real.sqrt (2 * Q) with htdef
  have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
  have ht2 : t * t = 2 * Q := Real.mul_self_sqrt (by linarith)
  have hmain := abs_avg_block_prob_tile_le (A := A) (m := m) (ℓ := ℓ) hℓ hℓm L w hΔ ht
  rw [hN] at hmain
  have hstep : (2 * Real.log 2 * (δ * (Fintype.card A : ℝ)))
      / (2 * t * ((Fintype.card A : ℝ) * ((m / ℓ : ℕ) : ℝ))) ≤ Q / t := by
    rw [hQ, div_le_div_iff₀ (by positivity) ht]
    have hcount := two_mul_div_le (m := m) (ℓ := ℓ) hℓ hℓm
    have key : (0 : ℝ) ≤ (Real.log 2 * δ * (Fintype.card A : ℝ) * t)
        * (2 * ((m / ℓ : ℕ) : ℝ) * (ℓ : ℝ) - (m : ℝ)) :=
      mul_nonneg (by positivity) (by linarith)
    have hne : (m : ℝ) ≠ 0 := hm0.ne'
    field_simp
    nlinarith [key, hC0, hrpos, ht, hlog2, hδ]
  have hopt : Q / t + t / 2 = t := by
    have hQ2 : Q = t * t / 2 := by linarith [ht2]
    rw [hQ2]
    field_simp
    norm_num
  have hfin : |(∑ c : A × Fin (m / ℓ), (L.map (fullCoord m ℓ c)).prob {w})
      / (Fintype.card (A × Fin (m / ℓ)) : ℝ) - 1 / (2 : ℝ) ^ ℓ| ≤ t := by
    rw [hN]
    linarith [hmain, hstep, hopt]
  have hval : t = 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / (m : ℝ)) := by
    rw [htdef, hQ]
    rw [show 2 * (2 * Real.log 2 * (ℓ : ℝ) * δ / (m : ℝ))
        = 2 ^ 2 * (Real.log 2 * (ℓ : ℝ) * δ / (m : ℝ)) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [← hval]
  exact hfin

/-- **The offset-`r` tiling obeys the same capacity bound**, with `m` replaced by `m − r`:
every one of the `ℓ` offset classes of the window is controlled. -/
theorem abs_avg_block_prob_offset_le {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    {m ℓ r : ℕ} (hℓ : 0 < ℓ) (hr : r + ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m)))
    (w : Fin (2 ^ ℓ)) {δ : ℝ} (hδ : 0 < δ)
    (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂) :
    |(∑ c : A × Fin ((m - r) / ℓ),
          ((L.map (lowTuple m r)).map (fullCoord (m - r) ℓ c)).prob {w})
        / (Fintype.card (A × Fin ((m - r) / ℓ)) : ℝ) - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - r)) := by
  have hrm : r ≤ m := by omega
  have hcast : ((m - r : ℕ) : ℝ) = (m : ℝ) - r := by
    rw [Nat.cast_sub hrm]
  have hℓm' : ℓ ≤ m - r := by omega
  have hC0 : (0 : ℝ) ≤ (Fintype.card A : ℝ) := by positivity
  have htrunc := H₂_lowTuple_ge (A := A) (m := m) (r := r) hrm L
  have hdef' : (((m - r : ℕ) : ℝ) - δ) * (Fintype.card A : ℝ) ≤ (L.map (lowTuple m r)).H₂ := by
    rw [hcast]
    have hexp : ((m : ℝ) - r - δ) * (Fintype.card A : ℝ)
        = ((m : ℝ) - δ) * (Fintype.card A : ℝ) - (Fintype.card A : ℝ) * r := by ring
    rw [hexp]
    linarith
  have h := abs_avg_block_prob_tile_opt (A := A) (m := m - r) (ℓ := ℓ) hℓ hℓm'
    (L.map (lowTuple m r)) w hδ hdef'
  rwa [hcast] at h

end NormalNumbers.G4Entropy
