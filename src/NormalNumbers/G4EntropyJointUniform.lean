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

Status: **proved**.  `abs_uniPatFreq_sub_le` assembles the decomposition `sum_diag_decomp`, the
per-diagonal bound `abs_diagAgg_sum_sub_le` (an instance of `abs_avg_patPos_prob_opt`) and the
diagonal count `card_diagSet_le` into

    `|uniPatFreq − 2^{−ℓt}| ≤ 2t√(log 2 · Δ / (|B|·J))`,

valid whenever `Jℓ ≤ m` — the aligned bound of `abs_avg_patCoord_prob_opt` times `t`.
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

/-! ### Assembling the uniform bound -/

/-- `a·√(X/a) = √(aX)`. -/
lemma mul_sqrt_div_self {a X : ℝ} (ha : 0 < a) (hX : 0 ≤ X) :
    a * Real.sqrt (X / a) = Real.sqrt (a * X) := by
  have h : a * Real.sqrt (X / a) = Real.sqrt (a ^ 2) * Real.sqrt (X / a) := by
    rw [Real.sqrt_sq ha.le]
  rw [h, ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- The per-diagonal aggregate: the pattern mass summed over the blocks. -/
noncomputable def diagAgg (m ℓ t : ℕ) (blk : B → Fin t → A)
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) (jj : Fin t → ℕ) : ℝ :=
  ∑ b : B, (L.map (jjPat m ℓ t blk b jj)).prob {w}

lemma sup_coe_lt {t J : ℕ} (hJ : 0 < J) (d : Fin t → Fin J) :
    (Finset.univ.sup fun s => ((d s : ℕ))) < J :=
  (Finset.sup_lt_iff hJ).2 fun s _ => (d s).isLt

/-- **The bound along one diagonal.**  The `J − max d` index vectors `d + j·1` are exactly the
aligned indices of `abs_avg_patPos_prob_opt` at the offset vector `pp s = d s·ℓ` and cut length
`D = (J − max d)·ℓ`, so their unnormalized total deviates from `|B|(J − max d)2^{−ℓt}` by at
most `2√(|B|(J − max d)·log 2·Δ) ≤ 2√(|B|J·log 2·Δ)`. -/
theorem abs_diagAgg_sum_sub_le {m ℓ t J : ℕ} (hℓ : 0 < ℓ) (ht : 0 < t) (hJ : 0 < J)
    (hJm : J * ℓ ≤ m) [Nonempty B] (d : Fin t → Fin J)
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    |(∑ j ∈ Finset.range (J - (Finset.univ.sup fun s => ((d s : ℕ)))),
        diagAgg m ℓ t blk L w (fun s => (d s : ℕ) + j))
       - (Fintype.card B : ℝ) * ((J - (Finset.univ.sup fun s => ((d s : ℕ))) : ℕ) : ℝ)
           / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * ((Fintype.card B : ℝ) * (J : ℝ))
          * Real.sqrt (Real.log 2 * Δ / ((Fintype.card B : ℝ) * (J : ℝ))) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcB : (0 : ℝ) < (Fintype.card B : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := B)
  have hSJ : (Finset.univ.sup fun s => ((d s : ℕ))) < J := sup_coe_lt hJ d
  set S := (Finset.univ.sup fun s => ((d s : ℕ))) with hSdef
  set R := J - S with hRdef
  have hR0 : 0 < R := by omega
  have hRJ : R ≤ J := by omega
  have hdS : ∀ s, (d s : ℕ) ≤ S := fun s =>
    Finset.le_sup (f := fun s => ((d s : ℕ))) (Finset.mem_univ s)
  have hDl : R * ℓ / ℓ = R := Nat.mul_div_cancel _ hℓ
  have hℓD : ℓ ≤ R * ℓ := by
    have : 1 * ℓ ≤ R * ℓ := Nat.mul_le_mul_right ℓ hR0
    simpa using this
  have hDm : R * ℓ ≤ m := le_trans (Nat.mul_le_mul_right ℓ hRJ) hJm
  have hppD : ∀ s, (d s : ℕ) * ℓ + R * ℓ ≤ m := by
    intro s
    have h1 : ((d s : ℕ) + R) * ℓ ≤ J * ℓ := Nat.mul_le_mul_right ℓ (by have := hdS s; omega)
    have h2 : ((d s : ℕ) + R) * ℓ = (d s : ℕ) * ℓ + R * ℓ := add_mul _ _ _
    omega
  have key := abs_avg_patPos_prob_opt (A := A) (B := B) (m := m) (ℓ := ℓ) (t := t) (D := R * ℓ)
    hℓ hℓD ht hDm (fun s => (d s : ℕ) * ℓ) hppD blk hblk L w hΔ0 hΔ
  -- rewrite the sum over `B × Fin ((R*ℓ)/ℓ)` as `∑_{j < R} diagAgg`
  have hstep : ∀ b : B,
      (∑ j : Fin (R * ℓ / ℓ),
          (L.map (patPos m ℓ t (R * ℓ) (fun s => (d s : ℕ) * ℓ) blk (b, j))).prob {w})
        = ∑ j ∈ Finset.range R,
            (L.map (jjPat m ℓ t blk b (fun s => (d s : ℕ) + j))).prob {w} := by
    intro b
    have h1 : ∀ j : Fin (R * ℓ / ℓ),
        (L.map (patPos m ℓ t (R * ℓ) (fun s => (d s : ℕ) * ℓ) blk (b, j))).prob {w}
          = (fun k : ℕ => (L.map (jjPat m ℓ t blk b (fun s => (d s : ℕ) + k))).prob {w})
              ((j : ℕ)) := by
      intro j
      have hf : patPos m ℓ t (R * ℓ) (fun s => (d s : ℕ) * ℓ) blk (b, j)
          = jjPat m ℓ t blk b (fun s => (d s : ℕ) + (j : ℕ)) :=
        funext fun z =>
          patPos_eq_jjPat m ℓ t (R * ℓ) (fun s => ((d s : ℕ))) blk (b, j) z
      rw [hf]
    rw [Finset.sum_congr rfl (fun j _ => h1 j),
      Fin.sum_univ_eq_sum_range
        (fun k : ℕ => (L.map (jjPat m ℓ t blk b (fun s => (d s : ℕ) + k))).prob {w}),
      hDl]
  have hsum : (∑ c : B × Fin (R * ℓ / ℓ),
        (L.map (patPos m ℓ t (R * ℓ) (fun s => (d s : ℕ) * ℓ) blk c)).prob {w})
      = ∑ j ∈ Finset.range R, diagAgg m ℓ t blk L w (fun s => (d s : ℕ) + j) := by
    rw [Fintype.sum_prod_type]
    simp only [hstep, diagAgg]
    exact Finset.sum_comm
  have hcard : (Fintype.card (B × Fin (R * ℓ / ℓ)) : ℝ) = (Fintype.card B : ℝ) * (R : ℝ) := by
    simp [hDl]
  rw [hsum, hcard] at key
  -- clear the denominator
  set T := ∑ j ∈ Finset.range R, diagAgg m ℓ t blk L w (fun s => (d s : ℕ) + j) with hT
  have hcR : (0 : ℝ) < (Fintype.card B : ℝ) * (R : ℝ) := by
    have : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR0
    positivity
  have hid : T - (Fintype.card B : ℝ) * (R : ℝ) / (2 : ℝ) ^ (ℓ * t)
      = ((Fintype.card B : ℝ) * (R : ℝ))
          * (T / ((Fintype.card B : ℝ) * (R : ℝ)) - 1 / (2 : ℝ) ^ (ℓ * t)) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hcR]
  refine le_trans (mul_le_mul_of_nonneg_left key hcR.le) ?_
  -- arithmetic: `|B|R · 2√(log2·ℓΔ/(|B|·Rℓ)) = 2√(|B|R·log2·Δ) ≤ 2√(|B|J·log2·Δ)`
  have hXe : Real.log 2 * (ℓ : ℝ) * Δ / ((Fintype.card B : ℝ) * ((R * ℓ : ℕ) : ℝ))
      = (Real.log 2 * Δ) / ((Fintype.card B : ℝ) * (R : ℝ)) := by
    have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
    push_cast
    field_simp
  rw [hXe]
  have hX0 : (0 : ℝ) ≤ Real.log 2 * Δ := by positivity
  have e1 : (Fintype.card B : ℝ) * (R : ℝ)
      * (2 * Real.sqrt (Real.log 2 * Δ / ((Fintype.card B : ℝ) * (R : ℝ))))
      = 2 * Real.sqrt (((Fintype.card B : ℝ) * (R : ℝ)) * (Real.log 2 * Δ)) := by
    rw [← mul_sqrt_div_self hcR hX0]; ring
  have hcJ : (0 : ℝ) < (Fintype.card B : ℝ) * (J : ℝ) := by
    have : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
    positivity
  have e2 : 2 * ((Fintype.card B : ℝ) * (J : ℝ))
      * Real.sqrt (Real.log 2 * Δ / ((Fintype.card B : ℝ) * (J : ℝ)))
      = 2 * Real.sqrt (((Fintype.card B : ℝ) * (J : ℝ)) * (Real.log 2 * Δ)) := by
    rw [← mul_sqrt_div_self hcJ hX0]; ring
  rw [e1, e2]
  have hmono : ((Fintype.card B : ℝ) * (R : ℝ)) * (Real.log 2 * Δ)
      ≤ ((Fintype.card B : ℝ) * (J : ℝ)) * (Real.log 2 * Δ) := by
    have hRJR : (R : ℝ) ≤ (J : ℝ) := by exact_mod_cast hRJ
    have := mul_le_mul_of_nonneg_left hRJR hcB.le
    exact mul_le_mul_of_nonneg_right this hX0
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by norm_num)

/-- **The uniform `t`-wise bound.**  Averaged over *all* vectors of aligned positions in
`[0,J)^t`, the `ℓt`-bit pattern frequency deviates from `2^{−ℓt}` by at most `t` times the
aligned bound. -/
theorem abs_uniPatFreq_sub_le {m ℓ t J : ℕ} (hℓ : 0 < ℓ) (ht : 0 < t) (hJ : 0 < J)
    (hJm : J * ℓ ≤ m) [Nonempty B]
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    |uniPatFreq m ℓ t J blk L w - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * (t : ℝ) * Real.sqrt (Real.log 2 * Δ / ((Fintype.card B : ℝ) * (J : ℝ))) := by
  classical
  have hcB : (0 : ℝ) < (Fintype.card B : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := B)
  have hJR : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hden : (0 : ℝ) < (Fintype.card B : ℝ) * (J : ℝ) ^ t := by positivity
  set C := 2 * ((Fintype.card B : ℝ) * (J : ℝ))
      * Real.sqrt (Real.log 2 * Δ / ((Fintype.card B : ℝ) * (J : ℝ))) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]; positivity
  -- the numerator, decomposed over the diagonals
  have hN : (∑ b : B, ∑ jj : Fin t → Fin J,
        (L.map (jjPat m ℓ t blk b (fun s => ((jj s : ℕ))))).prob {w})
      = ∑ d ∈ diagSet t J,
          ∑ j ∈ Finset.range (J - (Finset.univ.sup fun s => ((d s : ℕ)))),
            diagAgg m ℓ t blk L w (fun s => (d s : ℕ) + j) := by
    rw [Finset.sum_comm]
    exact sum_diag_decomp ht (diagAgg m ℓ t blk L w)
  -- the diagonals' lengths total `J^t`
  have hcount : ∑ d ∈ diagSet t J,
      ((J - (Finset.univ.sup fun s => ((d s : ℕ))) : ℕ) : ℝ) = (J : ℝ) ^ t := by
    have h := sum_diag_decomp (t := t) (J := J) ht (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Finset.card_range] at h
    rw [← h]
    push_cast
    ring
  -- the deviation of the numerator
  have hdev : |(∑ b : B, ∑ jj : Fin t → Fin J,
        (L.map (jjPat m ℓ t blk b (fun s => ((jj s : ℕ))))).prob {w})
      - (Fintype.card B : ℝ) * (J : ℝ) ^ t / (2 : ℝ) ^ (ℓ * t)|
      ≤ ((diagSet t J).card : ℝ) * C := by
    have hsplit : (Fintype.card B : ℝ) * (J : ℝ) ^ t / (2 : ℝ) ^ (ℓ * t)
        = ∑ d ∈ diagSet t J, (Fintype.card B : ℝ)
            * ((J - (Finset.univ.sup fun s => ((d s : ℕ))) : ℕ) : ℝ) / (2 : ℝ) ^ (ℓ * t) := by
      rw [← hcount, Finset.mul_sum, Finset.sum_div]
    rw [hN, hsplit, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun d _ =>
      abs_diagAgg_sum_sub_le hℓ ht hJ hJm d blk hblk L w hΔ0 hΔ)) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  -- divide
  have huni : uniPatFreq m ℓ t J blk L w - 1 / (2 : ℝ) ^ (ℓ * t)
      = ((∑ b : B, ∑ jj : Fin t → Fin J,
            (L.map (jjPat m ℓ t blk b (fun s => ((jj s : ℕ))))).prob {w})
          - (Fintype.card B : ℝ) * (J : ℝ) ^ t / (2 : ℝ) ^ (ℓ * t))
        / ((Fintype.card B : ℝ) * (J : ℝ) ^ t) := by
    rw [uniPatFreq]
    field_simp
  rw [huni, abs_div, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  refine le_trans hdev ?_
  have hcardle : ((diagSet t J).card : ℝ) ≤ (t : ℝ) * (J : ℝ) ^ (t - 1) := by
    have := card_diagSet_le t J
    exact_mod_cast this
  have hstep1 : ((diagSet t J).card : ℝ) * C ≤ ((t : ℝ) * (J : ℝ) ^ (t - 1)) * C :=
    mul_le_mul_of_nonneg_right hcardle hC0
  refine le_trans hstep1 ?_
  -- `t·J^{t−1}·2|B|J·√(…) = (2t√(…))·(|B|J^t)`
  have hJt : (J : ℝ) ^ (t - 1) * (J : ℝ) = (J : ℝ) ^ t := by
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    simp [pow_succ]
  rw [hC]
  have : ((t : ℝ) * (J : ℝ) ^ (t - 1))
      * (2 * ((Fintype.card B : ℝ) * (J : ℝ))
          * Real.sqrt (Real.log 2 * Δ / ((Fintype.card B : ℝ) * (J : ℝ))))
      = 2 * (t : ℝ) * Real.sqrt (Real.log 2 * Δ / ((Fintype.card B : ℝ) * (J : ℝ)))
          * ((Fintype.card B : ℝ) * ((J : ℝ) ^ (t - 1) * (J : ℝ))) := by ring
  rw [this, hJt]

end NormalNumbers.G4Entropy
