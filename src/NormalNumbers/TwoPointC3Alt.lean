/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TwoPointC3Budget

/-!
# TT2025 §5.2 in Lean: the alternating sum that kills the first `K` terms

`DIRECTION.md`'s rung 3 closes with the one technique the repo had no analogue of:
Tao–Teräväinen 2025 §5.2, *"taking an alternating sum to cancel terms"*, described there as
*"inspired by the theory of the Gowers uniformity norms"*.  It is the literature's way of reducing
a **growing-depth** linear combination `∑_h ω(n+h)b^{−h}` to **pairwise** correlations, and rungs 2
and 3 of this ladder proved that a growing depth is unavoidable — so this is the mechanism the
route needs.

## The trick, as the paper states it

Choose `p₀` and `v₁,…,v_K` so that `p_ε := p₀ + ε₁v₁ + ⋯ + ε_Kv_K` are distinct primes for all
`ε ∈ {0,1}^K`, and set (TT2025 (5.7))

    r_{ε,h} := p_ε·h − ∑_k k·ε_k·v_k = p₀·h + ∑_k (h − k)·ε_k·v_k .

**For `1 ≤ h ≤ K` the shift `r_{ε,h}` does not depend on `ε_h`**, because the coefficient `h − k`
vanishes at `k = h`.  Hence `∑_{ε_h ∈ {0,1}} (−1)^{ε_h} ω(n + r_{ε,h}) = 0`, so the alternating sum
over all of `{0,1}^K` annihilates every term with `1 ≤ h ≤ K`: the first `K` terms of the tail
cancel **identically**, at the cost of `2^K` terms.  That is TT2025 (5.8).

## What is formalised here

* `altToggle`, `altSum` — the alternating sum over `ε ∈ {0,1}^K`, realised as subsets
  `S : Finset (Fin K)` with sign `(−1)^{|S|}`.
* `altSum_eq_zero_of_indep` — **the abstract engine**: if the summand factors through a quantity
  that is invariant under toggling one coordinate `j`, the alternating sum vanishes.  A sign-
  reversing involution; no arithmetic.
* `altShift`, `altShift_toggle_eq` — the shift `r_{S,h}` and its independence of coordinate `h−1`
  (the repo's `Fin K` index `k` stands for the paper's `k+1`).
* `altSum_omegaLarge_eq_zero` — the cancellation for one `h`, for **any** function of the shifted
  argument, `ω_{>P}` included.
* `altSum_depthPeelShift_eq_zero` — **TT2025 (5.8)**: the whole depth-`K` head of the tail
  cancels, `∑_S (−1)^{|S|} ∑_{h=1}^{K} ω_{>P}(n + r_{S,h})·b^{−h} = 0`.

Only the *cancellation identity* is formalised, which is the combinatorial half; the analytic half
(that the `δ_{p_ε}` remainders are negligible, and that `p_ε` all prime is arrangeable) is the
paper's sieve input and is not touched here.  Note the identity is **unconditional on the
primality of the `p_ε`** — primality is needed only for the congruence (5.5) that produces the
`δ_p` form, not for the cancellation.
-/

open Filter Topology Finset

namespace NormalNumbers.CastingOut

/-! ### The abstract engine: a sign-reversing involution -/

variable {K : ℕ}

/-- Toggle the `j`-th coordinate of `ε ∈ {0,1}^K`, as a subset of `Fin K`. -/
def altToggle (j : Fin K) (S : Finset (Fin K)) : Finset (Fin K) :=
  open Classical in if j ∈ S then S.erase j else insert j S

lemma altToggle_involutive (j : Fin K) (S : Finset (Fin K)) :
    altToggle j (altToggle j S) = S := by
  classical
  by_cases hj : j ∈ S
  · have h1 : altToggle j S = S.erase j := by rw [altToggle, if_pos hj]
    rw [h1, altToggle, if_neg (Finset.notMem_erase j S), Finset.insert_erase hj]
  · have h1 : altToggle j S = insert j S := by rw [altToggle, if_neg hj]
    rw [h1, altToggle, if_pos (Finset.mem_insert_self j S), Finset.erase_insert hj]

lemma altToggle_ne (j : Fin K) (S : Finset (Fin K)) : altToggle j S ≠ S := by
  classical
  by_cases hj : j ∈ S
  · rw [altToggle, if_pos hj]
    exact fun hcon => (Finset.erase_eq_self.1 hcon) hj
  · rw [altToggle, if_neg hj]
    exact fun hcon => hj (Finset.insert_eq_self.1 hcon)

/-- Toggling flips the parity of `|ε|`. -/
lemma neg_one_pow_altToggle_card {R : Type*} [CommRing R] (j : Fin K) (S : Finset (Fin K)) :
    (-1 : R) ^ (altToggle j S).card = -((-1 : R) ^ S.card) := by
  classical
  by_cases hj : j ∈ S
  · have hc : S.card = (S.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have : 1 ≤ S.card := Finset.card_pos.2 ⟨j, hj⟩
      omega
    rw [altToggle, if_pos hj, hc, pow_succ]
    ring
  · have hc : (insert j S).card = S.card + 1 := Finset.card_insert_of_notMem hj
    rw [altToggle, if_neg hj, hc, pow_succ]
    ring

/-- **The engine.**  If the summand depends on `ε` only through a quantity invariant under
toggling the coordinate `j`, the alternating sum over `ε ∈ {0,1}^K` vanishes. -/
theorem altSum_eq_zero_of_indep {R : Type*} [CommRing R] {α : Type*} (j : Fin K)
    (shift : Finset (Fin K) → α) (g : α → R)
    (hind : ∀ S, shift (altToggle j S) = shift S) :
    ∑ S : Finset (Fin K), (-1 : R) ^ S.card * g (shift S) = 0 := by
  classical
  refine Finset.sum_ninvolution (altToggle j) (fun S => ?_) (fun S _ => altToggle_ne j S)
    (fun S => Finset.mem_univ _) (fun S => altToggle_involutive j S)
  have h1 : shift (altToggle j S) = shift S := hind S
  have h2 := neg_one_pow_altToggle_card (R := R) j S
  rw [h1, h2]
  ring

/-! ### The shift of TT2025 (5.7) -/

/-- `r_{S,h} = p₀·h + ∑_{k ∈ S} (h − (k+1))·v_k`.  The `Fin K` index `k` stands for the paper's
`k+1`, so the coefficient vanishes at `k + 1 = h`. -/
def altShift (p₀ : ℤ) (v : Fin K → ℤ) (h : ℕ) (S : Finset (Fin K)) : ℤ :=
  p₀ * h + ∑ k ∈ S, ((h : ℤ) - ((k : ℕ) + 1)) * v k

/-- **The point of the construction.**  For `1 ≤ h ≤ K` the shift is independent of the
`(h−1)`-st coordinate — the paper's "`r_{ε,h}` is independent of `ε_h`". -/
theorem altShift_toggle_eq (p₀ : ℤ) (v : Fin K → ℤ) {h : ℕ} (hh1 : 1 ≤ h) (hhK : h ≤ K)
    (S : Finset (Fin K)) :
    altShift p₀ v h (altToggle ⟨h - 1, by omega⟩ S) = altShift p₀ v h S := by
  classical
  set j : Fin K := ⟨h - 1, by omega⟩ with hj
  have hzero : ((h : ℤ) - (((j : ℕ) : ℤ) + 1)) * v j = 0 := by
    have hjv : (j : ℕ) = h - 1 := rfl
    have hcoef : ((h : ℤ) - (((j : ℕ) : ℤ) + 1)) = 0 := by omega
    rw [hcoef, zero_mul]
  rw [altShift, altShift]
  congr 1
  by_cases hjS : j ∈ S
  · rw [altToggle, if_pos hjS]
    rw [← Finset.add_sum_erase _ _ hjS, hzero, zero_add]
  · rw [altToggle, if_neg hjS]
    rw [Finset.sum_insert hjS, hzero, zero_add]

/-! ### The cancellation, for `ω_{>P}` and for the whole depth-`K` head -/

/-- One frequency `h` with `1 ≤ h ≤ K`: the alternating sum of **any** function of the shifted
argument vanishes.  With `g = fun m => (ω_{>P} m.toNat : ℝ)` this is the paper's
`∑_ε (−1)^{|ε|} ω(n + r_{ε,h}) = 0`. -/
theorem altSum_shift_eq_zero {R : Type*} [CommRing R] (p₀ : ℤ) (v : Fin K → ℤ) {h : ℕ}
    (hh1 : 1 ≤ h) (hhK : h ≤ K) (n : ℤ) (g : ℤ → R) :
    ∑ S : Finset (Fin K), (-1 : R) ^ S.card * g (n + altShift p₀ v h S) = 0 :=
  altSum_eq_zero_of_indep ⟨h - 1, by omega⟩ (fun S => n + altShift p₀ v h S) g
    (fun S => by rw [altShift_toggle_eq p₀ v hh1 hhK S])

/-- The `ω_{>P}` instance. -/
theorem altSum_omegaLarge_eq_zero (P : ℕ) (p₀ : ℤ) (v : Fin K → ℤ) {h : ℕ}
    (hh1 : 1 ≤ h) (hhK : h ≤ K) (n : ℤ) :
    ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
      * (omegaLarge P (n + altShift p₀ v h S).toNat : ℝ) = 0 :=
  altSum_shift_eq_zero p₀ v hh1 hhK n (fun m => (omegaLarge P m.toNat : ℝ))

/-- **TT2025 (5.8), the cancellation identity.**  The alternating sum annihilates the entire
depth-`K` head of the large-prime tail: every frequency `1 ≤ h ≤ K` drops out at once.  So the
alternating combination of the tails begins at depth `K+1` — which is exactly how a growing-depth
combination is traded for `2^K` shifted copies, the literature's route to pairwise correlations. -/
theorem altSum_depthHead_eq_zero (P b : ℕ) (p₀ : ℤ) (v : Fin K → ℤ) (n : ℤ) :
    ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
        * ∑ h ∈ Finset.Icc 1 K,
            (omegaLarge P (n + altShift p₀ v h S).toNat : ℝ) / (b : ℝ) ^ h = 0 := by
  classical
  have step1 : ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
        * ∑ h ∈ Finset.Icc 1 K,
            (omegaLarge P (n + altShift p₀ v h S).toNat : ℝ) / (b : ℝ) ^ h
      = ∑ S : Finset (Fin K), ∑ h ∈ Finset.Icc 1 K, (-1 : ℝ) ^ S.card
            * ((omegaLarge P (n + altShift p₀ v h S).toNat : ℝ) / (b : ℝ) ^ h) :=
    Finset.sum_congr rfl fun S _ => by rw [Finset.mul_sum]
  rw [step1, Finset.sum_comm]
  refine Finset.sum_eq_zero fun h hh => ?_
  rw [Finset.mem_Icc] at hh
  have hfac : ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
        * ((omegaLarge P (n + altShift p₀ v h S).toNat : ℝ) / (b : ℝ) ^ h)
      = (∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
          * (omegaLarge P (n + altShift p₀ v h S).toNat : ℝ)) / (b : ℝ) ^ h := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun S _ => by ring
  rw [hfac, altSum_omegaLarge_eq_zero P p₀ v hh.1 hh.2 n, zero_div]

end NormalNumbers.CastingOut
