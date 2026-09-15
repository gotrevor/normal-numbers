/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Grid

/-!
# After the extraction, L2: **offset rigidity of the coordinatewise cancellation**

In the tensor grid the layer-`j = i₀ + 1` term cancels because the shift
`j·d_α − t_α` does not depend on coordinate `i₀` of the atom `α` (`G4Grid.proj_update_eq`; the
row sums of `D_s` then kill it, `sum_kronPow_diffZ_mul_eq_zero`).

**Scope.**  This module is about that specific *coordinatewise* mechanism only — pointwise
invariance of `j·d_α − t_α` under single-coordinate updates, for every coordinate — not about
every cancellation of the weighted sum, nor about other carry methods.

**Statement.**  Fix the multipliers `d`.  If new offsets `t'` preserve the same pointwise
coordinate-cancellation identities as `t` for every coordinate, then `t' − t` is invariant
under every single-coordinate update, hence constant on the product grid
(`const_of_update_invariant`): `t'_α = t_α + Δ` for one `Δ` (`offset_rigidity`).  A common
offset change only translates sample time: the physical index of `n + Δ` under `t'` is the
physical index of `n` under `t` (`physIdx_translate`), so no new orbit indices appear once the
sample is translated too, apart from finite cutoff effects.

The actual grid satisfies the hypothesis (`grid_cancel`), so the theorem applies to it verbatim.
-/

namespace NormalNumbers.G4.Rigidity

/-! ### A function invariant under every single-coordinate update is constant -/

/-- On the product grid `Fin K → X`, a function invariant under every single-coordinate update
is constant: walk from `α` to `β` one coordinate at a time. -/
theorem const_of_update_invariant {K : ℕ} {X R : Type*} [DecidableEq (Fin K)]
    (f : (Fin K → X) → R) (hf : ∀ α (i : Fin K) c, f (Function.update α i c) = f α)
    (α β : Fin K → X) : f α = f β := by
  let γ : ℕ → (Fin K → X) := fun j i => if (i : ℕ) < j then β i else α i
  have h0 : γ 0 = α := by funext i; simp [γ]
  have hK : γ K = β := by funext i; simp [γ, i.isLt]
  have hstep : ∀ j, j < K → f (γ (j + 1)) = f (γ j) := by
    intro j hj
    have hγ : γ (j + 1) = Function.update (γ j) ⟨j, hj⟩ (β ⟨j, hj⟩) := by
      funext i
      by_cases hij : i = ⟨j, hj⟩
      · subst hij; simp [γ]
      · rw [Function.update_of_ne hij]
        have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
        simp only [γ]
        by_cases h1 : (i : ℕ) < j
        · simp [h1, Nat.lt_succ_of_lt h1]
        · have h2 : ¬ (i : ℕ) < j + 1 := by omega
          simp [h1, h2]
    rw [hγ, hf]
  have hall : ∀ j, j ≤ K → f (γ j) = f α := by
    intro j
    induction j with
    | zero => intro _; rw [h0]
    | succ j ih => intro hj; rw [hstep j (by omega), ih (by omega)]
  rw [← hK, hall K le_rfl]

/-! ### The coordinatewise cancellation identities -/

/-- **Pointwise coordinate cancellation** of the offsets `t` against the multipliers `d`: at
every coordinate `i₀`, the layer-`(i₀+1)` shift `(i₀+1)·d_α − t_α` ignores coordinate `i₀`. -/
def CoordCancel {K s : ℕ} (d t : (Fin K → Fin (s + 1)) → ℤ) : Prop :=
  ∀ (i₀ : Fin K) (α : Fin K → Fin (s + 1)) (c : Fin (s + 1)),
    ((i₀ : ℕ) + 1 : ℤ) * d (Function.update α i₀ c) - t (Function.update α i₀ c)
      = ((i₀ : ℕ) + 1 : ℤ) * d α - t α

/-- **Offset rigidity.**  At fixed multipliers, offsets `t'` that preserve the coordinatewise
cancellation identities of `t` differ from `t` by a constant on the whole grid. -/
theorem offset_rigidity {K s : ℕ} (d t t' : (Fin K → Fin (s + 1)) → ℤ)
    (ht : CoordCancel d t) (ht' : CoordCancel d t') :
    ∃ Δ : ℤ, ∀ α, t' α = t α + Δ := by
  classical
  have hinv : ∀ α (i : Fin K) c, (t' - t) (Function.update α i c) = (t' - t) α := by
    intro α i c
    have h1 := ht i α c
    have h2 := ht' i α c
    simp only [Pi.sub_apply]
    linarith
  cases K with
  | zero =>
    refine ⟨t' (fun i => i.elim0) - t (fun i => i.elim0), fun α => ?_⟩
    have : α = fun i => i.elim0 := funext fun i => i.elim0
    rw [this]; ring
  | succ K =>
    let α₀ : Fin (K + 1) → Fin (s + 1) := fun _ => 0
    refine ⟨t' α₀ - t α₀, fun α => ?_⟩
    have := const_of_update_invariant (t' - t) hinv α α₀
    simp only [Pi.sub_apply] at this
    linarith

/-- A common offset change only translates sample time: the physical index of `n + Δ` under
`t + Δ` is the physical index of `n` under `t`. -/
theorem physIdx_translate (d t n Δ : ℤ) : (n + Δ - (t + Δ)) / d = (n - t) / d := by
  congr 1; ring

/-! ### The actual grid satisfies the hypothesis -/

/-- The tensor grid's `d = mult`, `t = offset` satisfy `CoordCancel`: the layer-`(i₀+1)` shift is
`(i₀+1)(1 + Q·D₀) + Q·proj B (i₀+1) α`, and `proj_update_eq` is exactly the cancellation. -/
theorem grid_cancel {K s : ℕ} (B Q D₀ : ℕ) :
    CoordCancel (fun α : Fin K → Fin (s + 1) => (mult B Q D₀ α : ℤ))
      (fun α => (offset B Q α : ℤ)) := by
  intro i₀ α c
  have key : ∀ β : Fin K → Fin (s + 1), ((i₀ : ℕ) + 1 : ℤ) * (mult B Q D₀ β : ℤ) - (offset B Q β : ℤ)
      = ((i₀ : ℕ) + 1 : ℤ) * (1 + (Q : ℤ) * D₀) + (Q : ℤ) * proj B ((i₀ : ℕ) + 1) β := by
    intro β
    rw [proj_eq]
    unfold mult offset
    push_cast
    ring
  rw [key, key, proj_update_eq]

end NormalNumbers.G4.Rigidity
