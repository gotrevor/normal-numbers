/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropySample
import NormalNumbers.G4ScheduleGrid

/-!
# The multipliers are all equal to within `1 + 1/K`

Prefix control for the schedule-only read `fullPos` truncates the sample **per atom**: a position
cutoff `c` keeps the pair `(n, α)` exactly when `2·kIdx(n,α) = 2(n − t_α)/d_α ≤ c`, i.e. when
`n ≲ t_α + d_α·c/2`, and the threshold moves with `d_α`.  The last session flagged this as the
open caveat of the downward route: *either* (i) show the per-atom truncations are within a
bounded factor, *or* (ii) restate `entropy_E0_down` for an atom-indexed truncation vector.

**(i) holds, with the factor `1 + 1/K`.**  The schedule's grid takes

    `d_α = 1 + Q·(D₀ + u_α)`,  `D₀ = K·U`,  `0 ≤ u_α ≤ U`

(`gridOf`, `G4ScheduleGrid`), so every multiplier lies in `[1 + QKU, 1 + Q(K+1)U]` and

> `gridOf.mul_d_le_mul_d` — `K · d_α ≤ (K+1) · d_β` for **every** pair of atoms.

The consequence for the read, division-free:

> `kIdx_cross` — if `2·kIdx(n,β) ≤ c` for one atom `β`, then `K·(2·kIdx(n,α)) ≤ (K+1)·(c+4)`
> for **every** atom `α`.

So the atom-indexed truncation vector is squeezed between two honest outer scales whose ratio is
`(K+1)/K + O(1/c)`, and the sandwich costs a relative `≈ 1/K` — negligible against the
`O(K^{−1/4})` errors the capture inequality already carries.  Route (ii) is not needed.
-/

open Finset

namespace NormalNumbers.G4

namespace gridOf

variable {K N : ℕ} (hK : 1 ≤ K)

/-- The schedule grid's multiplier, unfolded. -/
lemma d_eq (α : (gridOf K N hK).Atom) :
    (gridOf K N hK).d α = 1 + gridQ K N * (gridD₀ K N + gridU (gridB K N) α) := rfl

/-- The multiplier's floor: `d_α ≥ 1 + Q·K·U`, attained when `u_α = 0`. -/
lemma d_ge (α : (gridOf K N hK).Atom) :
    1 + gridQ K N * (K * gridUmax K N) ≤ (gridOf K N hK).d α := by
  rw [d_eq hK α]
  have hD : gridD₀ K N = K * gridUmax K N := rfl
  have : K * gridUmax K N ≤ gridD₀ K N + gridU (gridB K N) α := by omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ this) 1

/-- The multiplier's ceiling: `d_α ≤ 1 + Q·(K+1)·U`. -/
lemma d_le' (α : (gridOf K N hK).Atom) :
    (gridOf K N hK).d α ≤ 1 + gridQ K N * ((K + 1) * gridUmax K N) := by
  rw [d_eq hK α]
  have hu : gridU (gridB K N) α ≤ gridUmax K N := (gridOf K N hK).hU α
  have hD : gridD₀ K N = K * gridUmax K N := rfl
  have hsum : gridD₀ K N + gridU (gridB K N) α ≤ (K + 1) * gridUmax K N := by
    rw [hD, Nat.succ_mul]
    omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hsum) 1

/-- **The multipliers agree to within `1 + 1/K`.**  For every pair of atoms,
`K·d_α ≤ (K+1)·d_β`.  This is the whole content of the per-atom truncation caveat: `D₀ = K·U`
dominates the atom-dependent part `u_α ≤ U` by a factor `K`. -/
theorem mul_d_le_mul_d (α β : (gridOf K N hK).Atom) :
    K * (gridOf K N hK).d α ≤ (K + 1) * (gridOf K N hK).d β := by
  have hα := d_le' hK α
  have hβ := d_ge hK β
  set Q := gridQ K N with hQ
  set U := gridUmax K N with hU
  have hmid : K * (1 + Q * ((K + 1) * U)) ≤ (K + 1) * (1 + Q * (K * U)) := by
    have hexp1 : K * (1 + Q * ((K + 1) * U)) = K + (K * (K + 1)) * (Q * U) := by ring
    have hexp2 : (K + 1) * (1 + Q * (K * U)) = (K + 1) + ((K + 1) * K) * (Q * U) := by ring
    rw [hexp1, hexp2]
    have heq : (K * (K + 1)) * (Q * U) = ((K + 1) * K) * (Q * U) := by ring
    omega
  calc K * (gridOf K N hK).d α ≤ K * (1 + Q * ((K + 1) * U)) := Nat.mul_le_mul_left _ hα
    _ ≤ (K + 1) * (1 + Q * (K * U)) := hmid
    _ ≤ (K + 1) * (gridOf K N hK).d β := Nat.mul_le_mul_left _ hβ

end gridOf

end NormalNumbers.G4

namespace NormalNumbers.G4Entropy

open NormalNumbers.G4

/-- `d_α · kIdx(n,α) ≤ n`: the orbit index never outruns the sample time. -/
lemma mul_kIdx_le (G : GridParams) (n : ℕ) (α : G.Atom) :
    G.d α * kIdx G n α ≤ n := by
  have h := Nat.div_mul_le_self (n - G.t α) (G.d α)
  have hle : G.d α * kIdx G n α ≤ n - G.t α := by
    rw [kIdx, mul_comm]; exact h
  omega

/-- If the cutoff keeps `(n, β)`, then `2n ≤ d_β·(c+4)`. -/
lemma two_mul_le_of_two_kIdx_le {G : GridParams} {n c : ℕ} (β : G.Atom)
    (hn : G.t β + G.d β * kIdx G n β = n) (h : 2 * kIdx G n β ≤ c) :
    2 * n ≤ G.d β * (c + 4) := by
  have ht : G.t β < G.d β := G.t_lt_d β
  have h3 : G.d β * (2 * kIdx G n β) ≤ G.d β * c := Nat.mul_le_mul_left _ h
  have h2 : 2 * (G.d β * kIdx G n β) = G.d β * (2 * kIdx G n β) := by ring
  have hexp : G.d β * (c + 4) = G.d β * c + 4 * G.d β := by ring
  omega

/-- **The per-atom truncations are within a factor `1 + 1/K`.**  If a position cutoff `c` keeps
the window of the sample time `n` at *some* atom `β`, then at *every* atom `α` the same sample
time sits below the cutoff `(K+1)(c+4)/K`.

So the atom-indexed truncation vector a position cutoff induces is sandwiched between two plain
outer scales whose ratio is `(K+1)/K + O(1/c)`: caveat (i) of the downward route holds, and the
restatement of `entropy_E0_down`/`entropy_E1_down` for a truncation vector — caveat (ii) — is not
needed. -/
theorem kIdx_cross {K N : ℕ} (hK : 1 ≤ K) {X n c : ℕ}
    (hn : n ∈ apSample X (gridOf K N hK).P₀ (gridOf K N hK).b₀)
    (α β : (gridOf K N hK).Atom) (h : 2 * kIdx (gridOf K N hK) n β ≤ c) :
    K * (2 * kIdx (gridOf K N hK) n α) ≤ (K + 1) * (c + 4) := by
  have hspecβ := (kIdx_spec (gridOf K N hK) hn β).1
  have hβ : 2 * n ≤ (gridOf K N hK).d β * (c + 4) :=
    two_mul_le_of_two_kIdx_le β hspecβ.symm h
  have hα : (gridOf K N hK).d α * (2 * kIdx (gridOf K N hK) n α) ≤ 2 * n := by
    have hml := mul_kIdx_le (gridOf K N hK) n α
    have heq : (gridOf K N hK).d α * (2 * kIdx (gridOf K N hK) n α)
        = 2 * ((gridOf K N hK).d α * kIdx (gridOf K N hK) n α) := by ring
    omega
  have hdpos : 0 < (gridOf K N hK).d α := (gridOf K N hK).d_pos α
  have hratio : K * (gridOf K N hK).d β ≤ (K + 1) * (gridOf K N hK).d α :=
    gridOf.mul_d_le_mul_d hK β α
  have hchain : (gridOf K N hK).d α * (K * (2 * kIdx (gridOf K N hK) n α))
      ≤ (gridOf K N hK).d α * ((K + 1) * (c + 4)) := by
    calc (gridOf K N hK).d α * (K * (2 * kIdx (gridOf K N hK) n α))
        = K * ((gridOf K N hK).d α * (2 * kIdx (gridOf K N hK) n α)) := by ring
      _ ≤ K * (2 * n) := Nat.mul_le_mul_left _ hα
      _ ≤ K * ((gridOf K N hK).d β * (c + 4)) := Nat.mul_le_mul_left _ hβ
      _ = (K * (gridOf K N hK).d β) * (c + 4) := by ring
      _ ≤ ((K + 1) * (gridOf K N hK).d α) * (c + 4) := Nat.mul_le_mul_right _ hratio
      _ = (gridOf K N hK).d α * ((K + 1) * (c + 4)) := by ring
  exact Nat.le_of_mul_le_mul_left hchain hdpos

end NormalNumbers.G4Entropy
