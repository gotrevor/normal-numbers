/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyJointPos

/-!
# The uniform `t`-wise bound: every position vector, averaged

Lap 40 recorded a narrowing: the *uniform* average over all position vectors
`(p_1,…,p_t)` looked unreachable, because a jointly injective family of `(m/ℓ)^t` pattern
coordinates per block would have to carry `tℓ(m/ℓ)^t` bits against the `tm` its windows hold.

**That narrowing was too pessimistic, and this module corrects it.**  One never needs a single
injective family covering all position vectors.  Write each vector of aligned indices
`jj ∈ [0,J)^t` (with `J = ⌊m/ℓ⌋`) uniquely as `jj = d + j·1` with `min d = 0`; for each fixed
*diagonal* `d` the vectors `d + j·1` are exactly what `abs_avg_patPos_prob_opt` controls, at the
offset vector `pp s = d s · ℓ` and cut length `D_d = m − (max d)·ℓ`.  Its bound there is

    `2√(log 2 · ℓ · Δ / (|B| · D_d))`,

so the diagonal's *unnormalized* contribution is at most

    `(J − max d) · 2√(log 2 · Δ / (|B| · (J − max d)))  ≤  2√(log 2 · Δ · J / |B|)`,

uniformly in `d`.  There are at most `t·J^{t−1}` diagonals (at least one coordinate of `d` is
zero), so the average over all `J^t` vectors deviates by at most

    `(t·J^{t−1}/J^t) · 2√(log 2 · Δ · J/|B|)  =  2t√(log 2 · ℓ · Δ / (|B| · m))`

— the aligned bound of `abs_avg_patCoord_prob_opt`, times `t`.  The blow-up of the individual
diagonal bounds as `max d → J` is exactly cancelled by those diagonals' small weight.

Status: the statement and the two combinatorial steps are laid out; the decomposition
`sum_diag_decomp` and the diagonal count `card_diag_le` are the open leaves.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The pattern read at an arbitrary vector of aligned indices. -/
def jjPat (m ℓ t : ℕ) (blk : B → Fin t → A) (b : B) (jj : Fin t → ℕ)
    (z : A → Fin (2 ^ m)) : Fin (2 ^ (ℓ * t)) :=
  packFin t ℓ (fun s => posAt m ℓ (jj s * ℓ) (z (blk b s)))

/-- `patPos` at the offset vector `d·ℓ` **is** `jjPat` at the shifted index vector. -/
lemma patPos_eq_jjPat (m ℓ t D : ℕ) (d : Fin t → ℕ) (blk : B → Fin t → A)
    (c : B × Fin (D / ℓ)) (z : A → Fin (2 ^ m)) :
    patPos m ℓ t D (fun s => d s * ℓ) blk c z
      = jjPat m ℓ t blk c.1 (fun s => d s + (c.2 : ℕ)) z := by
  rw [patPos, jjPat]
  congr 1
  funext s
  congr 1
  ring

/-- **The uniform pattern frequency**: the average over blocks and over *all* vectors of
aligned indices in `[0, J)^t`. -/
noncomputable def uniPatFreq (m ℓ t J : ℕ) (blk : B → Fin t → A)
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) : ℝ :=
  (∑ b : B, ∑ jj : Fin t → Fin J,
      (L.map (jjPat m ℓ t blk b (fun s => (jj s : ℕ)))).prob {w})
    / ((Fintype.card B : ℝ) * (J : ℝ) ^ t)

/-- The diagonals: index vectors with at least one zero coordinate. -/
noncomputable def diagSet (t J : ℕ) : Finset (Fin t → Fin J) :=
  open Classical in
  Finset.univ.filter (fun d => ∃ s, (d s : ℕ) = 0)

/-- At most `t·J^{t−1}` index vectors have a zero coordinate. -/
theorem card_diagSet_le (t J : ℕ) : (diagSet t J).card ≤ t * J ^ (t - 1) := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : diagSet 0 J = ∅ := by
      rw [diagSet]
      refine Finset.eq_empty_of_forall_notMem fun d hd => ?_
      rw [Finset.mem_filter] at hd
      exact hd.2.elim fun s _ => s.elim0
    simp [this]
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hsub : diagSet (n + 1) J ⊆ Finset.univ.biUnion
      (fun s : Fin (n + 1) =>
        Finset.univ.filter (fun d : Fin (n + 1) → Fin J => (d s : ℕ) = 0)) := by
    intro d hd
    rw [diagSet, Finset.mem_filter] at hd
    obtain ⟨s, hs⟩ := hd.2
    exact Finset.mem_biUnion.2 ⟨s, Finset.mem_univ _,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  have hfib : ∀ s : Fin (n + 1),
      (Finset.univ.filter (fun d : Fin (n + 1) → Fin J => (d s : ℕ) = 0)).card ≤ J ^ n := by
    intro s
    have hinj : Set.InjOn (fun d : Fin (n + 1) → Fin J => fun i : Fin n => d (s.succAbove i))
        ↑(Finset.univ.filter (fun d : Fin (n + 1) → Fin J => (d s : ℕ) = 0)) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      funext i
      rcases eq_or_ne i s with rfl | hne
      · exact Fin.ext (by rw [ha.2, hb.2])
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hne
        exact congrFun hab k
    refine le_trans (Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj) ?_
    simp
  calc ∑ s : Fin (n + 1),
        (Finset.univ.filter (fun d : Fin (n + 1) → Fin J => (d s : ℕ) = 0)).card
      ≤ ∑ _s : Fin (n + 1), J ^ n := Finset.sum_le_sum fun s _ => hfib s
    _ = (n + 1) * J ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ = (n + 1) * J ^ (n + 1 - 1) := by norm_num

/-! ### The minimum coordinate, and the diagonal of an index vector -/

lemma univNE {t : ℕ} (ht : 0 < t) : (Finset.univ : Finset (Fin t)).Nonempty :=
  ⟨⟨0, ht⟩, Finset.mem_univ _⟩

/-- The least coordinate of an index vector. -/
noncomputable def minv {t J : ℕ} (ht : 0 < t) (jj : Fin t → Fin J) : ℕ :=
  (Finset.univ : Finset (Fin t)).inf' (univNE ht) (fun s => (jj s : ℕ))

lemma minv_le {t J : ℕ} (ht : 0 < t) (jj : Fin t → Fin J) (s : Fin t) :
    minv ht jj ≤ (jj s : ℕ) :=
  Finset.inf'_le _ (Finset.mem_univ s)

lemma exists_minv_eq {t J : ℕ} (ht : 0 < t) (jj : Fin t → Fin J) :
    ∃ s, (jj s : ℕ) = minv ht jj := by
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf' (univNE ht) (fun s => ((jj s : ℕ)))
  exact ⟨s, hs.symm⟩

/-- The diagonal of an index vector: translate it down so its least coordinate is `0`. -/
noncomputable def diagOf {t J : ℕ} (ht : 0 < t) (jj : Fin t → Fin J) : Fin t → Fin J :=
  fun s => ⟨(jj s : ℕ) - minv ht jj, lt_of_le_of_lt (Nat.sub_le _ _) (jj s).isLt⟩

lemma diagOf_mem {t J : ℕ} (ht : 0 < t) (jj : Fin t → Fin J) :
    diagOf ht jj ∈ diagSet t J := by
  classical
  rw [diagSet, Finset.mem_filter]
  obtain ⟨s, hs⟩ := exists_minv_eq ht jj
  exact ⟨Finset.mem_univ _, ⟨s, by simp only [diagOf]; omega⟩⟩

lemma diagOf_add_minv {t J : ℕ} (ht : 0 < t) (jj : Fin t → Fin J) (s : Fin t) :
    ((diagOf ht jj s : ℕ)) + minv ht jj = (jj s : ℕ) := by
  have := minv_le ht jj s
  simp only [diagOf]
  omega

lemma minv_lt {t J : ℕ} (ht : 0 < t) (jj : Fin t → Fin J) : minv ht jj < J :=
  lt_of_le_of_lt (minv_le ht jj ⟨0, ht⟩) (jj ⟨0, ht⟩).isLt

lemma minv_add_sup_lt {t J : ℕ} (ht : 0 < t) (jj : Fin t → Fin J) :
    minv ht jj + (Finset.univ.sup fun s => ((diagOf ht jj s : ℕ))) < J := by
  have hlt := minv_lt ht jj
  have hpos : 0 < J - minv ht jj := by omega
  have hbound : (Finset.univ.sup fun s => ((diagOf ht jj s : ℕ))) < J - minv ht jj :=
    (Finset.sup_lt_iff hpos).2 fun s _ => by
      have h1 := diagOf_add_minv ht jj s
      have h2 := (jj s).isLt
      omega
  omega

/-- On a diagonal the least coordinate is `0`, so translating by `k` gives least coordinate
`k`. -/
lemma minv_shift {t J : ℕ} (ht : 0 < t) {d : Fin t → Fin J} (hd : d ∈ diagSet t J)
    {k : ℕ} (e : Fin t → Fin J) (he : ∀ s, (e s : ℕ) = (d s : ℕ) + k) :
    minv ht e = k := by
  classical
  rw [diagSet, Finset.mem_filter] at hd
  obtain ⟨s₀, hs₀⟩ := hd.2
  refine le_antisymm ?_ ?_
  · have h1 : minv ht e ≤ (e s₀ : ℕ) := minv_le ht e s₀
    rw [he s₀, hs₀] at h1
    omega
  · simp only [minv]
    refine Finset.le_inf' (univNE ht) _ fun s _ => ?_
    rw [he s]
    omega

/-- **The reindexing.**  Every index vector is uniquely `d + j·1` with `d` a diagonal and
`j < J − max d`.  This is what turns the uniform average into a weighted sum of the
per-diagonal averages `abs_avg_patPos_prob_opt` controls. -/
theorem sum_diag_decomp {t J : ℕ} (ht : 0 < t) (g : (Fin t → ℕ) → ℝ) :
    ∑ jj : Fin t → Fin J, g (fun s => (jj s : ℕ))
      = ∑ d ∈ diagSet t J,
          ∑ j ∈ Finset.range (J - (Finset.univ.sup fun s => (d s : ℕ))),
            g (fun s => (d s : ℕ) + j) := by
  classical
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · haveI : IsEmpty (Fin t → Fin 0) := ⟨fun f => (f ⟨0, ht⟩).elim0⟩
    have hd : diagSet t 0 = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun d _ => ?_
      exact (d ⟨0, ht⟩).elim0
    rw [hd]
    simp
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun jj => diagOf ht jj)
    (fun jj _ => diagOf_mem ht jj) (fun jj => g (fun s => (jj s : ℕ)))]
  refine Finset.sum_congr rfl fun d hd => ?_
  set S := (Finset.univ.sup fun s => ((d s : ℕ))) with hS
  -- the clamped translate, total on `ℕ` and correct on the range
  set sh : ℕ → Fin t → Fin J := fun k s => ⟨((d s : ℕ) + k) % J, Nat.mod_lt _ hJ⟩ with hsh
  have hdle : ∀ s, (d s : ℕ) ≤ S := fun s =>
    Finset.le_sup (f := fun s => ((d s : ℕ))) (Finset.mem_univ s)
  have hshval : ∀ k ∈ Finset.range (J - S), ∀ s, ((sh k s : Fin J) : ℕ) = (d s : ℕ) + k := by
    intro k hk s
    rw [Finset.mem_range] at hk
    have := hdle s
    simp only [hsh]
    rw [Nat.mod_eq_of_lt (by omega)]
  refine (Finset.sum_nbij' (i := fun k => sh k) (j := fun jj => minv ht jj) ?_ ?_ ?_ ?_ ?_).symm
  · -- `sh k` lands in the fibre of `d`
    intro k hk
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hmin : minv ht (sh k) = k := minv_shift ht hd (sh k) (hshval k hk)
    funext s
    refine Fin.ext ?_
    simp only [diagOf, hmin]
    rw [hshval k hk s]
    omega
  · -- the minimum of a vector in the fibre is in range
    intro jj hjj
    rw [Finset.mem_filter] at hjj
    rw [Finset.mem_range, hS, ← hjj.2]
    have := minv_add_sup_lt ht jj
    omega
  · -- left inverse
    intro k hk
    exact minv_shift ht hd (sh k) (hshval k hk)
  · -- right inverse
    intro jj hjj
    rw [Finset.mem_filter] at hjj
    funext s
    refine Fin.ext ?_
    have h1 := diagOf_add_minv ht jj s
    have h2 := (jj s).isLt
    simp only [hsh, ← hjj.2]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · -- the summands agree
    intro k hk
    congr 1
    funext s
    rw [hshval k hk s]

end NormalNumbers.G4Entropy
