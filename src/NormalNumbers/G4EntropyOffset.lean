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

/-! ### §2  Every position of the window, not just one tiling -/

/-- The `ℓ`-block of an `m`-bit window starting at position `p` (positions counted from the top,
zero-based). -/
def posAt (m ℓ p : ℕ) (z : Fin (2 ^ m)) : Fin (2 ^ ℓ) :=
  ⟨(z : ℕ) / 2 ^ (m - p - ℓ) % 2 ^ ℓ, Nat.mod_lt _ (by positivity)⟩

@[simp] lemma posAt_val (m ℓ p : ℕ) (z : Fin (2 ^ m)) :
    ((posAt m ℓ p z : Fin (2 ^ ℓ)) : ℕ) = (z : ℕ) / 2 ^ (m - p - ℓ) % 2 ^ ℓ := rfl

/-- Truncating below the window of interest changes nothing: `(z % 2^a)/2^b % 2^c = z/2^b % 2^c`
whenever `b + c ≤ a`. -/
lemma mod_div_mod_eq {z a b c : ℕ} (h : b + c ≤ a) :
    (z % 2 ^ a) / 2 ^ b % 2 ^ c = z / 2 ^ b % 2 ^ c := by
  have hdvd : (2 : ℕ) ^ (b + c) ∣ 2 ^ a := pow_dvd_pow 2 h
  have key : ∀ y : ℕ, y / 2 ^ b % 2 ^ c = y % 2 ^ (b + c) / 2 ^ b := by
    intro y
    rw [pow_add, Nat.mod_mul_right_div_self]
  rw [key, key, Nat.mod_mod_of_dvd _ hdvd]

/-- **The offset-`r` block of the truncated window is the position-`(r + jℓ)` block of the
original.** -/
theorem fullCoord_lowTuple_eq {A : Type*} {m ℓ r j : ℕ} (hp : r + j * ℓ + ℓ ≤ m)
    (α : A) (jj : Fin ((m - r) / ℓ)) (hjj : (jj : ℕ) = j) (z : A → Fin (2 ^ m)) :
    fullCoord (m - r) ℓ (α, jj) (lowTuple m r z) = posAt m ℓ (r + j * ℓ) (z α) := by
  refine Fin.ext ?_
  rw [fullCoord, blkAt_val, posAt_val]
  simp only [lowTuple, lowCoord]
  have he : m - r - (j + 1) * ℓ = m - (r + j * ℓ) - ℓ := by
    have : (j + 1) * ℓ = j * ℓ + ℓ := by ring
    omega
  rw [hjj, he]
  refine mod_div_mod_eq ?_
  omega

/-! ### §3  The offset classes tile the positions -/

/-- `(r, j) ↦ r + jℓ` matches the offset classes with the window positions admitting a full
`ℓ`-block: `r = p % ℓ`, `j = p / ℓ`. -/
def posEquiv (m ℓ : ℕ) (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) :
    ((r : Fin ℓ) × Fin ((m - (r : ℕ)) / ℓ)) ≃ Fin (m - ℓ + 1) where
  toFun q := ⟨(q.1 : ℕ) + (q.2 : ℕ) * ℓ, by
    have hj := q.2.isLt
    have h1 : ((q.2 : ℕ) + 1) * ℓ ≤ m - (q.1 : ℕ) :=
      (Nat.le_div_iff_mul_le hℓ).1 hj
    have hr := q.1.isLt
    have : ((q.2 : ℕ) + 1) * ℓ = (q.2 : ℕ) * ℓ + ℓ := by ring
    omega⟩
  invFun p := ⟨⟨(p : ℕ) % ℓ, Nat.mod_lt _ hℓ⟩, ⟨(p : ℕ) / ℓ, by
    have hp := p.isLt
    have hdm := Nat.div_add_mod (p : ℕ) ℓ
    have hstep : ((p : ℕ) / ℓ + 1) * ℓ ≤ m - (p : ℕ) % ℓ := by
      have h3 : ((p : ℕ) / ℓ + 1) * ℓ = ℓ * ((p : ℕ) / ℓ) + ℓ := by ring
      omega
    exact Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le hℓ).2 hstep)⟩⟩
  left_inv := by
    rintro ⟨⟨r, hr⟩, ⟨j, hj⟩⟩
    have h1 : (r + j * ℓ) % ℓ = r := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    have h2 : (r + j * ℓ) / ℓ = j := by
      rw [Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt hr, Nat.zero_add]
    refine Sigma.ext (Fin.ext h1) ?_
    rw [Fin.heq_ext_iff (by simp only [Fin.val_mk]; rw [h1])]
    exact h2
  right_inv := by
    intro p
    refine Fin.ext ?_
    simp only
    rw [Nat.mod_add_div']

/-! ### §4  Averaging the offset classes: every position of the window -/

namespace FinLaw
variable {Ω Ω' Ω'' : Type*} [Fintype Ω] [Fintype Ω'] [Fintype Ω'']

lemma prob_singleton_map [DecidableEq Ω'] (L : FinLaw Ω) (f : Ω → Ω') (w : Ω') :
    (L.map f).prob {w} = ∑ ω ∈ Finset.univ.filter (fun ω => f ω = w), L.p ω := by
  rw [FinLaw.prob, Finset.sum_singleton, FinLaw.map_p]

/-- `prob` of a singleton only sees the composite, so two-step pushforwards collapse. -/
lemma prob_singleton_map_map [DecidableEq Ω'] [DecidableEq Ω''] (L : FinLaw Ω) (g : Ω → Ω')
    (h : Ω' → Ω'') (w : Ω'') :
    ((L.map g).map h).prob {w} = (L.map (fun ω => h (g ω))).prob {w} := by
  classical
  rw [prob_singleton_map, prob_singleton_map]
  have hmaps : ∀ ω ∈ Finset.univ.filter (fun ω => h (g ω) = w), g ω ∈
      Finset.univ.filter (fun v => h v = w) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨Finset.mem_univ _, hω.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps L.p]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.mem_filter] at hv
  rw [FinLaw.map_p]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro rfl; exact ⟨hv.2, rfl⟩
  · rintro ⟨_, h2⟩; exact h2

end FinLaw

/-- The average, over all coordinates `α` and **all** window positions `p` admitting a full
`ℓ`-block, of the probability that the block at `p` spells `w`. -/
noncomputable def posAvg {A : Type*} [Fintype A] [DecidableEq A] (m ℓ : ℕ)
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ)) : ℝ :=
  (∑ c : A × Fin (m - ℓ + 1), (L.map (fun z => posAt m ℓ (c.2 : ℕ) (z c.1))).prob {w})
    / ((Fintype.card A : ℝ) * ((m - ℓ + 1 : ℕ) : ℝ))

/-- The offset classes' block probabilities are exactly the positions' block probabilities. -/
theorem sum_offset_eq_sum_pos {A : Type*} [Fintype A] [DecidableEq A] {m ℓ : ℕ} (hℓ : 0 < ℓ)
    (hℓm : ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ)) :
    ∑ r : Fin ℓ, ∑ c : A × Fin ((m - (r : ℕ)) / ℓ),
        ((L.map (lowTuple m (r : ℕ))).map (fullCoord (m - (r : ℕ)) ℓ c)).prob {w}
      = ∑ c : A × Fin (m - ℓ + 1), (L.map (fun z => posAt m ℓ (c.2 : ℕ) (z c.1))).prob {w} := by
  classical
  have hterm : ∀ (r : Fin ℓ) (α : A) (j : Fin ((m - (r : ℕ)) / ℓ)),
      ((L.map (lowTuple m (r : ℕ))).map (fullCoord (m - (r : ℕ)) ℓ (α, j))).prob {w}
        = (L.map (fun z => posAt m ℓ ((r : ℕ) + (j : ℕ) * ℓ) (z α))).prob {w} := by
    intro r α j
    rw [FinLaw.prob_singleton_map_map]
    have hb : (r : ℕ) + (j : ℕ) * ℓ + ℓ ≤ m := by
      have h1 : ((j : ℕ) + 1) * ℓ ≤ m - (r : ℕ) := (Nat.le_div_iff_mul_le hℓ).1 j.isLt
      have h2 : ((j : ℕ) + 1) * ℓ = (j : ℕ) * ℓ + ℓ := by ring
      have := r.isLt
      omega
    have hfun : (fun z : A → Fin (2 ^ m) =>
        fullCoord (m - (r : ℕ)) ℓ (α, j) (lowTuple m (r : ℕ) z))
        = (fun z : A → Fin (2 ^ m) => posAt m ℓ ((r : ℕ) + (j : ℕ) * ℓ) (z α)) :=
      funext fun z => fullCoord_lowTuple_eq hb α j rfl z
    rw [hfun]
  calc ∑ r : Fin ℓ, ∑ c : A × Fin ((m - (r : ℕ)) / ℓ),
        ((L.map (lowTuple m (r : ℕ))).map (fullCoord (m - (r : ℕ)) ℓ c)).prob {w}
      = ∑ r : Fin ℓ, ∑ α : A, ∑ j : Fin ((m - (r : ℕ)) / ℓ),
          (L.map (fun z => posAt m ℓ ((r : ℕ) + (j : ℕ) * ℓ) (z α))).prob {w} := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun j _ => hterm r α j
    _ = ∑ α : A, ∑ r : Fin ℓ, ∑ j : Fin ((m - (r : ℕ)) / ℓ),
          (L.map (fun z => posAt m ℓ ((r : ℕ) + (j : ℕ) * ℓ) (z α))).prob {w} :=
        Finset.sum_comm
    _ = ∑ α : A, ∑ q : (r : Fin ℓ) × Fin ((m - (r : ℕ)) / ℓ),
          (L.map (fun z => posAt m ℓ ((q.1 : ℕ) + (q.2 : ℕ) * ℓ) (z α))).prob {w} := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.sum_sigma', Finset.univ_sigma_univ]
    _ = ∑ α : A, ∑ p : Fin (m - ℓ + 1),
          (L.map (fun z => posAt m ℓ (p : ℕ) (z α))).prob {w} := by
        refine Finset.sum_congr rfl fun α _ => ?_
        exact Fintype.sum_equiv (posEquiv m ℓ hℓ hℓm) _ _ (fun q => by rfl)
    _ = ∑ c : A × Fin (m - ℓ + 1), (L.map (fun z => posAt m ℓ (c.2 : ℕ) (z c.1))).prob {w} := by
        rw [Fintype.sum_prod_type]

/-- **Every position of the window.**  A deficit of `δ` bits per coordinate controls the
frequency of every `ℓ`-block word over **all** `m − ℓ + 1` positions of the window — not just
one aligned tiling — to within `2√(log 2 · ℓδ/(m − ℓ + 1))`.

This is the shape normality is built from: a word counted at every position, averaged. -/
theorem abs_posAvg_sub_le {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {m ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ))
    {δ : ℝ} (hδ : 0 < δ) (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂) :
    |posAvg m ℓ L w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - ℓ + 1)) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hmℓ : (1 : ℝ) ≤ (m : ℝ) - ℓ + 1 := by
    have : (ℓ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hℓm
    linarith
  have hCA : (0 : ℝ) < (Fintype.card A : ℝ) := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this
  set cc : ℝ := 1 / (2 : ℝ) ^ ℓ with hcc
  set B : ℝ := 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - ℓ + 1)) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  -- per offset class
  set S : Fin ℓ → ℝ := fun r => ∑ c : A × Fin ((m - (r : ℕ)) / ℓ),
      ((L.map (lowTuple m (r : ℕ))).map (fullCoord (m - (r : ℕ)) ℓ c)).prob {w} with hS
  set N : Fin ℓ → ℝ := fun r => (Fintype.card (A × Fin ((m - (r : ℕ)) / ℓ)) : ℝ) with hN
  have hNval : ∀ r : Fin ℓ, N r = (Fintype.card A : ℝ) * (((m - (r : ℕ)) / ℓ : ℕ) : ℝ) := by
    intro r
    rw [hN]
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hN0 : ∀ r : Fin ℓ, 0 ≤ N r := by
    intro r; rw [hNval r]; positivity
  have hclaim : ∀ r : Fin ℓ, |S r - cc * N r| ≤ B * N r := by
    intro r
    rcases le_or_gt ((r : ℕ) + ℓ) m with hcase | hcase
    · -- a full block exists at this offset
      have hone : 1 ≤ (m - (r : ℕ)) / ℓ := (Nat.one_le_div_iff hℓ).2 (by omega)
      have hNpos : 0 < N r := by
        rw [hNval r]
        have : (1 : ℝ) ≤ (((m - (r : ℕ)) / ℓ : ℕ) : ℝ) := by exact_mod_cast hone
        nlinarith
      have hoff := abs_avg_block_prob_offset_le (A := A) (m := m) (ℓ := ℓ) (r := (r : ℕ))
        hℓ (by omega) L w hδ hdef
      have hBr : 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - (r : ℕ))) ≤ B := by
        rw [hB]
        have hrle : ((r : ℕ) : ℝ) ≤ (ℓ : ℝ) - 1 := by
          have := r.isLt
          have : ((r : ℕ) : ℝ) < (ℓ : ℝ) := by exact_mod_cast r.isLt
          have h2 : ((r : ℕ) : ℝ) + 1 ≤ (ℓ : ℝ) := by
            have : (r : ℕ) + 1 ≤ ℓ := r.isLt
            exact_mod_cast this
          linarith
        have hden : (m : ℝ) - ℓ + 1 ≤ (m : ℝ) - (r : ℕ) := by linarith
        have hd0 : (0 : ℝ) < (m : ℝ) - ℓ + 1 := by linarith
        have : Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - (r : ℕ))
            ≤ Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - ℓ + 1) := by
          apply div_le_div_of_nonneg_left (by positivity) hd0 hden
        have := Real.sqrt_le_sqrt this
        linarith
      have hSN : |S r / N r - cc| ≤ B := le_trans hoff hBr
      have h1 : S r - cc * N r = N r * (S r / N r - cc) := by
        field_simp
      have hkey : |S r - cc * N r| = N r * |S r / N r - cc| := by
        rw [h1, abs_mul, abs_of_nonneg hNpos.le]
      rw [hkey]
      calc N r * |S r / N r - cc| ≤ N r * B := by
            exact mul_le_mul_of_nonneg_left hSN hNpos.le
        _ = B * N r := by ring
    · -- no full block at this offset: both sides vanish
      have hzero : (m - (r : ℕ)) / ℓ = 0 := Nat.div_eq_of_lt (by omega)
      have hN0' : N r = 0 := by
        rw [hNval r, hzero]
        norm_num
      have hS0 : S r = 0 := by
        rw [hS]
        refine Finset.sum_eq_zero fun c _ => ?_
        have hemp : IsEmpty (Fin ((m - (r : ℕ)) / ℓ)) := by rw [hzero]; infer_instance
        exact hemp.elim c.2
      rw [hS0, hN0']
      norm_num
  -- the offset classes exhaust the positions
  have hcard : ∑ r : Fin ℓ, (((m - (r : ℕ)) / ℓ : ℕ) : ℝ) = ((m - ℓ + 1 : ℕ) : ℝ) := by
    have h := Fintype.card_congr (posEquiv m ℓ hℓ hℓm)
    rw [Fintype.card_sigma, Fintype.card_fin] at h
    have : ∑ r : Fin ℓ, Fintype.card (Fin ((m - (r : ℕ)) / ℓ)) = m - ℓ + 1 := by
      simpa using h
    calc ∑ r : Fin ℓ, (((m - (r : ℕ)) / ℓ : ℕ) : ℝ)
        = ((∑ r : Fin ℓ, ((m - (r : ℕ)) / ℓ) : ℕ) : ℝ) := by push_cast; ring
      _ = ((m - ℓ + 1 : ℕ) : ℝ) := by
          congr 1
          simpa using this
  have hNsum : ∑ r : Fin ℓ, N r = (Fintype.card A : ℝ) * ((m - ℓ + 1 : ℕ) : ℝ) := by
    simp_rw [hNval]
    rw [← Finset.mul_sum, hcard]
  have hSsum : ∑ r : Fin ℓ, S r
      = ∑ c : A × Fin (m - ℓ + 1), (L.map (fun z => posAt m ℓ (c.2 : ℕ) (z c.1))).prob {w} :=
    sum_offset_eq_sum_pos hℓ hℓm L w
  -- assemble
  have hsum : |(∑ r : Fin ℓ, S r) - cc * ∑ r : Fin ℓ, N r| ≤ B * ∑ r : Fin ℓ, N r := by
    have h1 : |(∑ r : Fin ℓ, S r) - cc * ∑ r : Fin ℓ, N r| ≤ ∑ r : Fin ℓ, |S r - cc * N r| := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ r : Fin ℓ, |S r - cc * N r| ≤ ∑ r : Fin ℓ, B * N r :=
      Finset.sum_le_sum fun r _ => hclaim r
    rw [← Finset.mul_sum] at h2
    linarith
  have hDpos : (0 : ℝ) < (Fintype.card A : ℝ) * ((m - ℓ + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((m - ℓ + 1 : ℕ) : ℝ) := by
      have : 1 ≤ m - ℓ + 1 := by omega
      exact_mod_cast this
    nlinarith
  have hsum' : |(∑ r : Fin ℓ, S r)
      - cc * ((Fintype.card A : ℝ) * ((m - ℓ + 1 : ℕ) : ℝ))|
      ≤ B * ((Fintype.card A : ℝ) * ((m - ℓ + 1 : ℕ) : ℝ)) := by
    rw [← hNsum]
    exact hsum
  simp only [posAvg]
  rw [← hSsum]
  have hdiv : (∑ r : Fin ℓ, S r) / ((Fintype.card A : ℝ) * ((m - ℓ + 1 : ℕ) : ℝ)) - cc
      = ((∑ r : Fin ℓ, S r) - cc * ((Fintype.card A : ℝ) * ((m - ℓ + 1 : ℕ) : ℝ)))
        / ((Fintype.card A : ℝ) * ((m - ℓ + 1 : ℕ) : ℝ)) := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
  exact hsum'

end NormalNumbers.G4Entropy




