/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TwoPointC3Trade
import NormalNumbers.G4Transport

/-!
# The link: TT2025 (5.5)+(5.7) is a dilation, and the repo already had the dilation identity

`TwoPointC3Alt`/`TwoPointC3Trade` gave the §5.2 cancellation and its price.  What was missing was
the bridge between the crux's single argument `n` and the `2^K` shifted arguments `n + r_{S,h}`.
The paper supplies it as a *congruence* (TT2025 (5.5)): `n ≡ ∑_k k·ε_k·v_k (mod p_ε)`.  This file
records what that congruence actually buys, and it is a **dilation**:

    altShift_eq_mul :  n − ∑_{k∈S}(k+1)v_k = p_S · m  →  n + r_{S,h} = p_S · (m + h)

with `p_S := p₀ + ∑_{k∈S} v_k` (the paper's `p_ε`).  So each of the `2^K` shifted tails is a
**dilated** tail — and the dilated tail identity is *already in this repo*, proved in the G4
entropy campaign for a general dilation `d` and never consumed by the C3 ladder:

    G4.dilatedTailB_eq :  ∑_{j≥1} b^{−j} ω(d(k+j)) = tailB b k + ω(d)/(b−1) − corrB b d k .

That **is** TT2025 (5.2), unconditionally and in general-`d` form: the paper's `δ_p(n)` is the
repo's `corrB b p`, and the paper's `q·∑1/2^h = q` term is the repo's `ω(d)/(b−1)`.  (The paper
states (5.2) mod 1 because it is arguing by contradiction from `q·G ∈ ℤ`; the repo's version is an
identity in `ℝ`, which is strictly more information.)

Landed here:

* `altPrime`, `altCong`, `altShift_eq_mul` — the link, pure `ℤ` algebra, no primality needed.
* `altSum_const_eq_zero` — the alternating sum of a constant vanishes as soon as `K ≥ 1`.
* `altSum_dilatedHead_eq_zero` — **(5.8) in the dilated vocabulary**: for any `p, m` the alternating
  sum of the depth-`K` heads of the dilated tails vanishes.
* `altSum_dilatedTail_eq` — **(5.8) in full**: for `p_S` all prime and `K ≥ 1`,

      ∑_S (−1)^{|S|} dilatedTailB b (p S) (m S)
        = ∑_S (−1)^{|S|} tailB b (m S) − ∑_S (−1)^{|S|} corrB b (p S) (m S) ,

  the `ω(p_S)/(b−1) = 1/(b−1)` term cancelling against the alternating sign.  This is exactly the
  paper's *"the alternating sum of the tails is the alternating sum of the `δ`s"*, with the integer
  part `tailB` kept explicit instead of being discarded mod 1.
-/

open Filter Topology Finset

namespace NormalNumbers.CastingOut

variable {K : ℕ}

/-! ### The link -/

/-- The paper's `p_ε = p₀ + ε₁v₁ + ⋯ + ε_Kv_K`. -/
def altPrime (p₀ : ℤ) (v : Fin K → ℤ) (S : Finset (Fin K)) : ℤ := p₀ + ∑ k ∈ S, v k

/-- The paper's congruence offset `∑_k k·ε_k·v_k` (the repo's `Fin K` index `k` is the paper's
`k+1`). -/
def altCong (v : Fin K → ℤ) (S : Finset (Fin K)) : ℤ := ∑ k ∈ S, (((k : ℕ) : ℤ) + 1) * v k

/-- **The link.**  TT2025 (5.5)'s congruence says exactly that the shifted argument `n + r_{S,h}`
is the dilation by `p_S` of a single sequence in `h`.  Pure algebra: no primality, no positivity. -/
theorem altShift_eq_mul (p₀ : ℤ) (v : Fin K → ℤ) (S : Finset (Fin K)) (n m : ℤ)
    (hm : n - altCong v S = altPrime p₀ v S * m) (h : ℕ) :
    n + altShift p₀ v h S = altPrime p₀ v S * (m + h) := by
  have hexp : altShift p₀ v h S = p₀ * h + ((h : ℤ) * ∑ k ∈ S, v k - altCong v S) := by
    rw [altShift, altCong, Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hexp, altPrime]
  have hm' : n = altPrime p₀ v S * m + altCong v S := by
    rw [← hm]; ring
  rw [hm', altPrime]
  ring

/-! ### The alternating sum of a constant -/

/-- As soon as `K ≥ 1` the signs `(−1)^{|S|}` cancel in pairs. -/
theorem altSum_const_eq_zero {R : Type*} [CommRing R] (hK : 1 ≤ K) (c : R) :
    ∑ S : Finset (Fin K), (-1 : R) ^ S.card * c = 0 :=
  altSum_eq_zero_of_indep (K := K) ⟨0, by omega⟩ (fun _ => (0 : ℕ)) (fun _ => c)
    (fun _ => rfl)

/-! ### TT2025 (5.8) in the dilated vocabulary -/

/-- **(5.8), head form.**  The alternating sum annihilates the depth-`K` head of the dilated
tails, for arbitrary dilations `p` and bases `m` — the composition of the §5.2 cancellation with
the link. -/
theorem altSum_dilatedHead_eq_zero (b : ℕ) (p₀ : ℤ) (v : Fin K → ℤ) (n : ℤ)
    (m : Finset (Fin K) → ℤ)
    (hm : ∀ S, n - altCong v S = altPrime p₀ v S * m S) :
    ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card
        * ∑ h ∈ Finset.Icc 1 K,
            (PrimeLambert.omegaR (altPrime p₀ v S * (m S + h)).toNat) / (b : ℝ) ^ h = 0 := by
  have hrw : ∀ (S : Finset (Fin K)) (h : ℕ),
      altPrime p₀ v S * (m S + h) = n + altShift p₀ v h S :=
    fun S h => (altShift_eq_mul p₀ v S n (m S) (hm S) h).symm
  have hcongr : ∀ S : Finset (Fin K),
      ∑ h ∈ Finset.Icc 1 K, (PrimeLambert.omegaR (altPrime p₀ v S * (m S + h)).toNat) / (b : ℝ) ^ h
        = ∑ h ∈ Finset.Icc 1 K,
            (PrimeLambert.omegaR (n + altShift p₀ v h S).toNat) / (b : ℝ) ^ h := by
    intro S
    exact Finset.sum_congr rfl fun h _ => by rw [hrw S h]
  rw [Finset.sum_congr rfl fun S _ => by rw [hcongr S]]
  exact altSum_head_eq_zero b p₀ v n (fun z => PrimeLambert.omegaR z.toNat)

/-- **(5.8) in full.**  The repo's exact transport identity plus the cancellation of the constant:
the alternating sum of the *dilated tails* is the alternating sum of the base tails minus the
alternating sum of the paper's `δ` terms.  `K ≥ 1` and primality of each `p S` are the only
hypotheses; note primality is used only to evaluate `ω(p S) = 1`. -/
theorem altSum_dilatedTail_eq {b : ℕ} (hb : 2 ≤ b) (hK : 1 ≤ K)
    (p m : Finset (Fin K) → ℕ) (hp : ∀ S, (p S).Prime) :
    ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card * G4.dilatedTailB b (p S) (m S)
      = (∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card * G4.tailB b (m S))
        - ∑ S : Finset (Fin K), (-1 : ℝ) ^ S.card * G4.corrB b (p S) (m S) := by
  have hone : ∀ S : Finset (Fin K), PrimeLambert.omegaR (p S) = 1 := by
    intro S
    rw [PrimeLambert.omegaR, ArithmeticFunction.cardDistinctFactors_apply_prime (hp S)]
    norm_num
  have hterm : ∀ S : Finset (Fin K), (-1 : ℝ) ^ S.card * G4.dilatedTailB b (p S) (m S)
      = (-1 : ℝ) ^ S.card * G4.tailB b (m S)
        + (-1 : ℝ) ^ S.card * (1 / ((b : ℝ) - 1))
        - (-1 : ℝ) ^ S.card * G4.corrB b (p S) (m S) := by
    intro S
    rw [G4.dilatedTailB_eq hb (p S) (m S) (hp S).pos.ne', hone S]
    ring
  rw [Finset.sum_congr rfl fun S _ => hterm S]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    altSum_const_eq_zero hK (1 / ((b : ℝ) - 1)), add_zero]

end NormalNumbers.CastingOut
