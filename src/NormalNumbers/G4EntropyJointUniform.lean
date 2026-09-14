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

/-- **Open leaf (combinatorics).**  At most `t·J^{t−1}` index vectors have a zero coordinate. -/
theorem card_diagSet_le (t J : ℕ) : (diagSet t J).card ≤ t * J ^ (t - 1) := by
  sorry

/-- **Open leaf (combinatorics).**  Every index vector is uniquely `d + j·1` with `d` a diagonal
and `j < J − max d`.  This is the reindexing that turns the uniform average into a weighted sum
of the per-diagonal averages `abs_avg_patPos_prob_opt` controls. -/
theorem sum_diag_decomp {t J : ℕ} (g : (Fin t → ℕ) → ℝ) :
    ∑ jj : Fin t → Fin J, g (fun s => (jj s : ℕ))
      = ∑ d ∈ diagSet t J,
          ∑ j ∈ Finset.range (J - (Finset.univ.sup fun s => (d s : ℕ))),
            g (fun s => (d s : ℕ) + j) := by
  sorry

end NormalNumbers.G4Entropy
