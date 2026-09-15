/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyOffsetClass

/-!
# Window positions in a residue class mod `k`

`G4EntropyOffsetClass` showed that the capacity bound survives restriction to **any** sub-family
`R : Finset (Fin ℓ)` of the `ℓ` offset classes, at the *same* constant.  This module identifies
the sub-family that base-`2^k` normality needs.

A base-`2^k` digit of a number in `[0,1)` is a `k`-block of its binary digits at a position
`≡ 0 (mod k)`, so base-`2^k` normality asks for the frequency of a binary word of length
`ℓ = k·ℓ'` **restricted to positions in a fixed residue class mod `k`**.  Since `posEquiv` is
literally `(r, j) ↦ r + jℓ` and `k ∣ ℓ`, the position `r + jℓ` lies in the same class mod `k` as
`r` does: the positions `≡ c (mod k)` are exactly the union of the offset classes `r ≡ c (mod k)`.

* `resClasses`, `resPos` — the offset classes, resp. the window positions, in residue `c`.
* `sum_resClasses_eq_sum_resPos` — the tiling identity (step 2 of the base-`2^k` directive).
* `abs_posAvgRes_sub_le` — 🎯 the capacity bound for the residue-restricted average, at the
  *same* constant `2√(log2·ℓδ/(m − ℓ + 1))` as the unrestricted one.
-/

open Finset

namespace NormalNumbers.G4Entropy

/-! ### §1  The two index sets -/

/-- The offset classes `r < ℓ` with `r ≡ c (mod k)`. -/
def resClasses (ℓ k c : ℕ) : Finset (Fin ℓ) :=
  Finset.univ.filter (fun r : Fin ℓ => (r : ℕ) % k = c)

/-- The window positions `p < m − ℓ + 1` with `p ≡ c (mod k)`. -/
def resPos (m ℓ k c : ℕ) : Finset (Fin (m - ℓ + 1)) :=
  Finset.univ.filter (fun p : Fin (m - ℓ + 1) => (p : ℕ) % k = c)

lemma mem_resClasses {ℓ k c : ℕ} {r : Fin ℓ} : r ∈ resClasses ℓ k c ↔ (r : ℕ) % k = c := by
  simp [resClasses]

lemma mem_resPos {m ℓ k c : ℕ} {p : Fin (m - ℓ + 1)} :
    p ∈ resPos m ℓ k c ↔ (p : ℕ) % k = c := by
  simp [resPos]

/-- With `k ∣ ℓ`, sliding by a whole number of blocks does not change the class mod `k`. -/
lemma add_mul_mod_eq_of_dvd {k ℓ : ℕ} (hk : k ∣ ℓ) (r j : ℕ) : (r + j * ℓ) % k = r % k := by
  obtain ⟨d, rfl⟩ := hk
  have : r + j * (k * d) = r + k * (j * d) := by ring
  rw [this, Nat.add_mul_mod_self_left]

/-! ### §2  The tiling identity -/

/-- **Step 2 of the base-`2^k` directive.**  For `k ∣ ℓ` the positions `≡ c (mod k)` are exactly
the union of the offset classes `r ≡ c (mod k)`, via `posEquiv : (r, j) ↦ r + jℓ`. -/
theorem sum_resClasses_eq_sum_resPos {M : Type*} [AddCommMonoid M] {m ℓ k c : ℕ}
    (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (hk : k ∣ ℓ) (f : ℕ → M) :
    ∑ r ∈ resClasses ℓ k c, ∑ j : Fin ((m - (r : ℕ)) / ℓ), f ((r : ℕ) + (j : ℕ) * ℓ)
      = ∑ p ∈ resPos m ℓ k c, f (p : ℕ) := by
  classical
  set S : Finset ((r : Fin ℓ) × Fin ((m - (r : ℕ)) / ℓ)) :=
    (resClasses ℓ k c).sigma (fun _ => Finset.univ) with hS
  have hleft : ∑ r ∈ resClasses ℓ k c, ∑ j : Fin ((m - (r : ℕ)) / ℓ), f ((r : ℕ) + (j : ℕ) * ℓ)
      = ∑ q ∈ S, f ((q.1 : ℕ) + (q.2 : ℕ) * ℓ) := by
    rw [hS, Finset.sum_sigma]
  rw [hleft]
  refine Finset.sum_equiv (posEquiv m ℓ hℓ hℓm) ?_ ?_
  · intro q
    simp only [hS, Finset.mem_sigma, Finset.mem_univ, and_true, mem_resClasses, mem_resPos]
    have : ((posEquiv m ℓ hℓ hℓm) q : ℕ) = (q.1 : ℕ) + (q.2 : ℕ) * ℓ := rfl
    rw [this, add_mul_mod_eq_of_dvd hk]
  · intro q _
    rfl

/-! ### §3  The residue-restricted average -/

/-- The block-probability sum over the window positions `≡ c (mod k)`. -/
noncomputable def posSumRes {A : Type*} [Fintype A] [DecidableEq A] (m ℓ k c : ℕ)
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ)) : ℝ :=
  ∑ p ∈ resPos m ℓ k c, ∑ α : A, (L.map (fun z => posAt m ℓ (p : ℕ) (z α))).prob {w}

/-- The average of a word's block probability over the window positions `≡ c (mod k)`. -/
noncomputable def posAvgRes {A : Type*} [Fintype A] [DecidableEq A] (m ℓ k c : ℕ)
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ)) : ℝ :=
  posSumRes m ℓ k c L w / ((Fintype.card A : ℝ) * ((resPos m ℓ k c).card : ℝ))

/-- The offset class `r`'s block probabilities, position by position. -/
lemma classSum_eq {A : Type*} [Fintype A] [DecidableEq A] {m ℓ : ℕ} (hℓ : 0 < ℓ)
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ)) (r : Fin ℓ) :
    classSum m ℓ L w r
      = ∑ j : Fin ((m - (r : ℕ)) / ℓ), ∑ α : A,
          (L.map (fun z => posAt m ℓ ((r : ℕ) + (j : ℕ) * ℓ) (z α))).prob {w} := by
  classical
  rw [classSum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => ?_
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

/-- The numerator identity: the classes `≡ c` sum to the positions `≡ c`. -/
theorem sum_classSum_resClasses {A : Type*} [Fintype A] [DecidableEq A] {m ℓ k c : ℕ}
    (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (hk : k ∣ ℓ) (L : FinLaw (A → Fin (2 ^ m)))
    (w : Fin (2 ^ ℓ)) :
    ∑ r ∈ resClasses ℓ k c, classSum m ℓ L w r = posSumRes m ℓ k c L w := by
  classical
  have h1 : ∀ r : Fin ℓ, classSum m ℓ L w r
      = ∑ j : Fin ((m - (r : ℕ)) / ℓ),
          (fun p : ℕ => ∑ α : A, (L.map (fun z => posAt m ℓ p (z α))).prob {w})
            ((r : ℕ) + (j : ℕ) * ℓ) := fun r => classSum_eq hℓ L w r
  rw [Finset.sum_congr rfl (fun r _ => h1 r)]
  rw [sum_resClasses_eq_sum_resPos hℓ hℓm hk
    (fun p : ℕ => ∑ α : A, (L.map (fun z => posAt m ℓ p (z α))).prob {w})]
  rfl

/-- The denominator identity. -/
theorem sum_classCard_resClasses (A : Type*) [Fintype A] {m ℓ k c : ℕ}
    (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (hk : k ∣ ℓ) :
    ∑ r ∈ resClasses ℓ k c, classCard A m ℓ r
      = (Fintype.card A : ℝ) * ((resPos m ℓ k c).card : ℝ) := by
  classical
  have hcount : ∑ r ∈ resClasses ℓ k c, (((m - (r : ℕ)) / ℓ : ℕ) : ℝ)
      = ((resPos m ℓ k c).card : ℝ) := by
    have := sum_resClasses_eq_sum_resPos (M := ℝ) (m := m) (ℓ := ℓ) (k := k) (c := c)
      hℓ hℓm hk (fun _ => (1 : ℝ))
    simpa using this
  rw [← hcount, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [classCard]

/-- 🎯 **The capacity bound, restricted to a residue class of window positions.**  For `k ∣ ℓ`
the frequency of `w` among the window positions `≡ c (mod k)` obeys the *same* bound as the
frequency over all positions — no factor `√k`, not even a constant. -/
theorem abs_posAvgRes_sub_le {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {m ℓ k c : ℕ}
    (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (hk : k ∣ ℓ) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ))
    {δ : ℝ} (hδ : 0 < δ) (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂)
    (hne : (resPos m ℓ k c).Nonempty) :
    |posAvgRes m ℓ k c L w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - ℓ + 1)) := by
  classical
  have hCA : (0 : ℝ) < (Fintype.card A : ℝ) := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this
  have hcard : (0 : ℝ) < ((resPos m ℓ k c).card : ℝ) := by
    have : 0 < (resPos m ℓ k c).card := Finset.card_pos.2 hne
    exact_mod_cast this
  have hden := sum_classCard_resClasses A (m := m) (ℓ := ℓ) (k := k) (c := c) hℓ hℓm hk
  have hR : 0 < ∑ r ∈ resClasses ℓ k c, classCard A m ℓ r := by
    rw [hden]; positivity
  have hmain := abs_posAvgR_sub_le hℓ hℓm L w hδ hdef (resClasses ℓ k c) hR
  have heq : posAvgR m ℓ (resClasses ℓ k c) L w = posAvgRes m ℓ k c L w := by
    rw [posAvgR, posAvgRes, sum_classSum_resClasses hℓ hℓm hk L w, hden]
  rwa [heq] at hmain

end NormalNumbers.G4Entropy
