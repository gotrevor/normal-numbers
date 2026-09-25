/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtProductPhase

/-!
# The `K`-fold bridge expansion

`sum_pow_omega_offset_eq` (`C3MrtLinearForms`) expands ONE shift of `z^ω` over powerful moduli,
for an arbitrary index set `S` and offset `c` — it was written to be iterated.  This file
iterates it `K` times, giving the `K`-shift analogue of
`sum_pow_omega_two_shift_eq_coprime`:

    ∑_{n ∈ S} F(n) ∏_{i<K} z_i^{ω(n+i+1)}
      = ∑_{(d_0,…,d_{K-1}) ≤ B} (∏_i g_i(d_i)) ∑_{n ∈ S, ∀i d_i ∣ n+i+1}
            F(n) ∏_i z_i^{Ω((n+i+1)/d_i)} ,

with `g_i = sqfW z_i` supported on the powerful numbers.  The inner sum is a `K`-point
correlation of the **completely multiplicative** `z_i^Ω` along `K` linear forms in the
progression variable — the shape `ProductLogElliott K` / `KPointLogElliott K` is stated for.

The tuple sum is over `Fintype.piFinset (fun _ : Fin K => range (B+1))`; the induction peels the
LAST shift, which is why `sum_pow_omega_offset_eq`'s arbitrary-`S` generality is what makes the
iteration go through: the `i`-th application runs inside the congruences already imposed.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- Split a tuple sum over `Fin (K+1)` into its last coordinate and the rest. -/
theorem sum_piFinset_snoc {K : ℕ} {M : Type*} [AddCommMonoid M] (s : Finset ℕ)
    (f : (Fin (K + 1) → ℕ) → M) :
    ∑ d ∈ Fintype.piFinset (fun _ : Fin (K + 1) => s), f d
      = ∑ p ∈ s ×ˢ Fintype.piFinset (fun _ : Fin K => s), f (Fin.snoc p.2 p.1) := by
  classical
  refine Finset.sum_nbij' (fun d => (d (Fin.last K), fun i => d i.castSucc))
    (fun p => Fin.snoc p.2 p.1) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Fintype.mem_piFinset] at hd
    simp only [Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨hd _, fun i => hd _⟩
  · intro p hp
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hp
    rw [Fintype.mem_piFinset]
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]; exact hp.2 i'
    · rw [Fin.snoc_last]; exact hp.1
  · intro d _
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
    · rw [Fin.snoc_last]
  · intro p _
    simp
  · intro d _
    congr 1
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
    · rw [Fin.snoc_last]

/-- `∏_i z_i^{Ω(m)} = (∏_i z_i)^{Ω(m)}`: the product of the depth factors is the single factor
attached to the product phase.  This is what turns `ProductLogElliott`'s hypothesis into
`nonPretentious_prod_depthRoot` verbatim. -/
theorem prod_pow_cardFactors {K : ℕ} (z : ℕ → ℂ) (m : ℕ) :
    (∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors m)
      = (∏ i : Fin K, z i) ^ ArithmeticFunction.cardFactors m :=
  Finset.prod_pow _ _ _

/-- **The `K`-fold bridge expansion.**  Induction on `K`, peeling the last shift; the weight `F`
is quantified inside the induction because each peel absorbs one `z_K^Ω` factor into it. -/
theorem sum_pow_omega_multi_eq (z : ℕ → ℂ) :
    ∀ (K : ℕ) (F : ℕ → ℂ) (S : Finset ℕ) (B : ℕ), (∀ n ∈ S, n + K ≤ B) →
      ∑ n ∈ S, F n * ∏ i : Fin K, (z i) ^ omegaNat (n + i + 1)
        = ∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (B + 1)),
            (∏ i : Fin K, sqfW (z i) (d i)) *
              ∑ n ∈ S.filter (fun n => ∀ i : Fin K, d i ∣ n + i + 1),
                F n * ∏ i : Fin K,
                  (z i) ^ ArithmeticFunction.cardFactors ((n + i + 1) / d i) := by
  classical
  intro K
  induction K with
  | zero =>
      intro F S B _
      simp
  | succ K ih =>
      intro F S B hB
      -- peel the last shift
      have hstep : ∑ n ∈ S, F n * ∏ i : Fin (K + 1), (z i) ^ omegaNat (n + i + 1)
          = ∑ n ∈ S, (F n * ∏ i : Fin K, (z i) ^ omegaNat (n + i + 1))
              * (z K) ^ omegaNat (n + (K + 1)) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.coe_castSucc, Fin.val_last]
        ring_nf
      rw [hstep]
      rw [sum_pow_omega_offset_eq (z K) (fun n => F n * ∏ i : Fin K, (z i) ^ omegaNat (n + i + 1))
        S (K + 1) B (by omega) (by intro n hn; have := hB n hn; omega)]
      -- expand the remaining `K` shifts inside each congruence class
      have hinner : ∀ dK : ℕ,
          (∑ n ∈ S.filter (fun n => dK ∣ n + (K + 1)),
            (F n * ∏ i : Fin K, (z i) ^ omegaNat (n + i + 1))
              * (z K) ^ ArithmeticFunction.cardFactors ((n + (K + 1)) / dK))
          = ∑ d' ∈ Fintype.piFinset (fun _ : Fin K => range (B + 1)),
              (∏ i : Fin K, sqfW (z i) (d' i)) *
                ∑ n ∈ (S.filter (fun n => dK ∣ n + (K + 1))).filter
                    (fun n => ∀ i : Fin K, d' i ∣ n + i + 1),
                  (F n * (z K) ^ ArithmeticFunction.cardFactors ((n + (K + 1)) / dK))
                    * ∏ i : Fin K,
                        (z i) ^ ArithmeticFunction.cardFactors ((n + i + 1) / d' i) := by
        intro dK
        have hre : (∑ n ∈ S.filter (fun n => dK ∣ n + (K + 1)),
              (F n * ∏ i : Fin K, (z i) ^ omegaNat (n + i + 1))
                * (z K) ^ ArithmeticFunction.cardFactors ((n + (K + 1)) / dK))
            = ∑ n ∈ S.filter (fun n => dK ∣ n + (K + 1)),
                (F n * (z K) ^ ArithmeticFunction.cardFactors ((n + (K + 1)) / dK))
                  * ∏ i : Fin K, (z i) ^ omegaNat (n + i + 1) :=
          Finset.sum_congr rfl fun n _ => by ring
        rw [hre]
        exact ih (fun m => F m * (z K) ^ ArithmeticFunction.cardFactors ((m + (K + 1)) / dK))
          (S.filter (fun n => dK ∣ n + (K + 1))) B
          (by
            intro n hn
            have := hB n (Finset.mem_filter.1 hn).1
            omega)
      refine Eq.trans (Finset.sum_congr rfl (fun dK _ =>
        congrArg (fun y => sqfW (z K) dK * y) (hinner dK))) ?_
      -- reassemble: `(dK, d') ↦ Fin.snoc d' dK`
      rw [sum_piFinset_snoc, Finset.sum_product]
      refine Finset.sum_congr rfl fun dK _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d' _ => ?_
      -- the tuple product splits off its last factor
      have hprod : (∏ i : Fin (K + 1), sqfW (z i) ((Fin.snoc d' dK : Fin (K + 1) → ℕ) i))
          = (∏ i : Fin K, sqfW (z i) (d' i)) * sqfW (z K) dK := by
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.coe_castSucc, Fin.val_last, Fin.snoc_castSucc, Fin.snoc_last]
      -- and so do the two filters
      have hfilter : (S.filter (fun n => dK ∣ n + (K + 1))).filter
            (fun n => ∀ i : Fin K, d' i ∣ n + i + 1)
          = S.filter (fun n => ∀ i : Fin (K + 1), (Fin.snoc d' dK : Fin (K + 1) → ℕ) i ∣ n + i + 1) := by
        rw [Finset.filter_filter]
        refine Finset.filter_congr fun n _ => ?_
        constructor
        · intro hh i
          rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
          · rw [Fin.snoc_castSucc, Fin.coe_castSucc]
            exact hh.2 i'
          · rw [Fin.snoc_last, Fin.val_last]
            exact hh.1
        · intro hh
          refine ⟨?_, fun i => ?_⟩
          · have h := hh (Fin.last K)
            rw [Fin.snoc_last, Fin.val_last] at h
            exact h
          · have h := hh i.castSucc
            rw [Fin.snoc_castSucc, Fin.coe_castSucc] at h
            exact h
      rw [hprod, hfilter]
      have hsum : (∑ n ∈ S.filter (fun n => ∀ i : Fin (K + 1),
            (Fin.snoc d' dK : Fin (K + 1) → ℕ) i ∣ n + i + 1),
          (F n * (z K) ^ ArithmeticFunction.cardFactors ((n + (K + 1)) / dK))
            * ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((n + i + 1) / d' i))
          = ∑ n ∈ S.filter (fun n => ∀ i : Fin (K + 1),
              (Fin.snoc d' dK : Fin (K + 1) → ℕ) i ∣ n + i + 1),
            F n * ∏ i : Fin (K + 1), (z i) ^ ArithmeticFunction.cardFactors
              ((n + i + 1) / (Fin.snoc d' dK : Fin (K + 1) → ℕ) i) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.coe_castSucc, Fin.val_last, Fin.snoc_castSucc, Fin.snoc_last]
        ring
      rw [hsum]
      ring

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.sum_piFinset_snoc
#print axioms NormalNumbers.CastingOut.prod_pow_cardFactors
#print axioms NormalNumbers.CastingOut.sum_pow_omega_multi_eq
