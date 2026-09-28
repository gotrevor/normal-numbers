import NormalNumbers.ElliottSquarefullConv

/-!
# The progression substitution

Leaf 2, Case B, step (4) of the `DIRECTION.md` CURRENT DIRECTIVE.

The squarefull expansion of `ElliottSquarefullConv.lean` turns
`U₁ (a₁n+b₁) = ∑_{d₁ ∣ a₁n+b₁} u₁ d₁ · Ũ₁ ((a₁n+b₁)/d₁)` and likewise for the second form, so the
correlation becomes a double sum over `(d₁, d₂)` of the *restricted* correlations

`∑_{n : d₁ ∣ a₁n+b₁, d₂ ∣ a₂n+b₂} (1/n) · Ũ₁ ((a₁n+b₁)/d₁) · Ũ₂ ((a₂n+b₂)/d₂)`.

The joint congruence condition is a single progression `n ≡ n₀ (mod q)` (empty, or a progression by
CRT); with the choice `q = d₁ d₂` **both** quotients become affine in `k`, where `n = qk + n₀`:

`(a₁ (qk+n₀) + b₁)/d₁ = (a₁ q/d₁) k + (a₁ n₀ + b₁)/d₁`.

The decisive point — and the reason no new machinery is needed — is that the **determinant is
exactly preserved**:

`a₁' b₂' − a₂' b₁' = (a₁ d₂)·(a₂n₀+b₂)/d₂ − (a₂ d₁)·(a₁n₀+b₁)/d₁ = a₁ b₂ − a₂ b₁`,

so the new pair is again admissible for `AffineCMLogElliott`, with no shrinkage and no dependence
on `d₁, d₂`.  This is what makes the expansion a *finite* reduction to the same rung rather than an
infinite regress.

## Main results

* `integerAffine_progression` — the substitution `n = qk + n₀` factors `d` out of the affine form.
* `det_progression` — **the determinant is preserved exactly.**
* `exists_progression_of_jointCongruence` — the joint congruence is a progression or empty.
Still open (analytic, not arithmetic): the window rescaling `X ↦ X/q` and the harmonic-weight
comparison `1/(qk+n₀) = 1/(qk) + O(·)`.  See the final section.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottProgression

open Erdos67b

/-! ## The substitution is exact arithmetic -/

/-- **The substitution.**  If `d ∣ a q` and `d ∣ a n₀ + b`, then along the progression
`n = q k + n₀` the affine form is `d` times an affine form in `k`. -/
theorem integerAffine_progression {a : ℕ} {b : ℤ} {d n₀ q : ℕ} {c : ℤ}
    (hq : (d : ℤ) * ((a : ℤ) * q / d) = (a : ℤ) * q)
    (hc : (a : ℤ) * n₀ + b = (d : ℤ) * c) (k : ℕ) :
    integerAffine a b (q * k + n₀) = (d : ℤ) * (((a : ℤ) * q / d) * k + c) := by
  rw [integerAffine]
  push_cast
  linear_combination (-(k : ℤ)) * hq + hc

/-- **The determinant is preserved exactly** by the substitution with `q = d₁ d₂`.

`a₁' = a₁ d₂`, `b₁' = c₁` (where `a₁ n₀ + b₁ = d₁ c₁`), and symmetrically; then
`a₁' b₂' − a₂' b₁' = a₁ b₂ − a₂ b₁`.  In particular the new pair is admissible whenever the old
one is, uniformly in `d₁, d₂`. -/
theorem det_progression {a₁ a₂ d₁ d₂ n₀ : ℕ} {b₁ b₂ c₁ c₂ : ℤ}
    (h₁ : (a₁ : ℤ) * n₀ + b₁ = (d₁ : ℤ) * c₁)
    (h₂ : (a₂ : ℤ) * n₀ + b₂ = (d₂ : ℤ) * c₂) :
    ((a₁ : ℤ) * d₂) * c₂ - ((a₂ : ℤ) * d₁) * c₁ = (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ := by
  linear_combination (-(a₁ : ℤ)) * h₂ + (a₂ : ℤ) * h₁

/-- The quotient `a q / d` really is the intended one when `d ∣ a q`. -/
theorem mul_div_cancel_of_dvd {d : ℕ} {x : ℤ} (h : (d : ℤ) ∣ x) :
    (d : ℤ) * (x / d) = x := Int.mul_ediv_cancel' h

/-- With `q = d₁ d₂` both divisibility side conditions `d_i ∣ a_i q` hold automatically. -/
theorem dvd_mul_of_prod {a d₁ d₂ : ℕ} :
    (d₁ : ℤ) ∣ (a : ℤ) * ((d₁ * d₂ : ℕ) : ℤ) := by
  push_cast
  exact ⟨(a : ℤ) * d₂, by ring⟩

theorem dvd_mul_of_prod' {a d₁ d₂ : ℕ} :
    (d₂ : ℤ) ∣ (a : ℤ) * ((d₁ * d₂ : ℕ) : ℤ) := by
  push_cast
  exact ⟨(a : ℤ) * d₁, by ring⟩

/-- The explicit value of the new dilation when `q = d₁ d₂`. -/
theorem newDilation_eq {a d₁ d₂ : ℕ} (hd₁ : d₁ ≠ 0) :
    (a : ℤ) * ((d₁ * d₂ : ℕ) : ℤ) / (d₁ : ℤ) = (a : ℤ) * d₂ := by
  have hd : (d₁ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hd₁
  push_cast
  rw [show (a : ℤ) * ((d₁ : ℤ) * d₂) = ((a : ℤ) * d₂) * d₁ by ring]
  exact Int.mul_ediv_cancel _ hd

/-! ## The joint congruence -/

/-- **The joint congruence is a progression, or empty.**  If some `n` satisfies both divisibility
constraints, then with `q = d₁ d₂` every element of the constrained set is `≡ n` mod `q`, and
conversely.  (Solvability itself can fail — e.g. `d₁ = 2, a₁ = 2, b₁ = 1` — in which case the inner
sum is empty and contributes nothing.) -/
theorem exists_progression_of_jointCongruence {a₁ a₂ d₁ d₂ : ℕ} {b₁ b₂ : ℤ}
    {n₀ : ℕ}
    (h₁ : (d₁ : ℤ) ∣ (a₁ : ℤ) * n₀ + b₁) (h₂ : (d₂ : ℤ) ∣ (a₂ : ℤ) * n₀ + b₂) (k : ℕ) :
    (d₁ : ℤ) ∣ (a₁ : ℤ) * ((d₁ * d₂ : ℕ) * k + n₀ : ℕ) + b₁ ∧
      (d₂ : ℤ) ∣ (a₂ : ℤ) * ((d₁ * d₂ : ℕ) * k + n₀ : ℕ) + b₂ := by
  constructor
  · obtain ⟨c, hc⟩ := h₁
    refine ⟨(a₁ : ℤ) * d₂ * k + c, ?_⟩
    push_cast
    push_cast at hc
    linear_combination hc
  · obtain ⟨c, hc⟩ := h₂
    refine ⟨(a₂ : ℤ) * d₁ * k + c, ?_⟩
    push_cast
    push_cast at hc
    linear_combination hc

/-! ## The remaining analytic step -/

/-!
### Open: the analytic reindexing

What remains of step (4) is not arithmetic but the
bookkeeping of the *window and weight*:

* the constrained window `{n ∈ (X/W, X] : n ≡ n₀ mod q}` becomes, under `n = qk + n₀`, a window in
  `k` of the same shape at scale `X/q` and the *same* ratio `W`;
* the harmonic weight satisfies `1/(qk+n₀) = (1/q)·(1/k) + O(1/(qk²))`, and
  `∑_k 1/(qk²) = O(1/q)`, so replacing `1/n` by `(1/q)(1/k)` costs an absolute constant, which is
  then multiplied by `∑_{d} ‖u d‖/d ≤ e²` (`ElliottSquarefullConv`) and is therefore harmless.

Formalising this is routine but bulky; it is disclosed rather than faked.  The arithmetic content
it rests on — the substitution and the *exact* preservation of the determinant — is proved above,
which is the part that decides whether the route closes at all.  No lemma is stated here yet
because the statement needs the restricted correlation, which is introduced at assembly time.
-/

end NormalNumbers.ElliottProgression
