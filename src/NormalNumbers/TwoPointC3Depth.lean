/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.DelangeSlot
import NormalNumbers.SwingC3AddChar

/-!
# C3's depth ladder, rung 1: the depth-`1` peel is a THEOREM

The C3 crux (`SwingC3Leaf.weylLambertTwist_holds`, equivalently `CastingOut.AddCharTail`) asks

    (1/N) ∑_{n<N} e(j n / Q) · e(h · tailLarge P b n)  →  0 ,

and `tailLarge P b n = ∑_{i≥1} ω_{>P}(n+i)·b^{−i}`, so the phase factors as

    e(h · tailLarge P b n) = ∏_{i≥1} z_i^{ω_{>P}(n+i)} ,   z_i = e(h / b^i) .

**Peeling one factor lands exactly on a theorem this repo already has.**
`DelangeSlot.twisted_omegaLarge_mean_tendsto_zero` (proved, `#print axioms`-clean, written for the
Leaf-B slot and never consumed outside its own namespace) is literally

    (1/N) ∑_{m≤N} e(j m / Q) · z^{ω_{>P}(m)}  →  0     for ‖z‖ = 1, z ≠ 1,

which after the re-index `m = n+1` is the depth-`1` truncation of the crux.  That is what this
file records: `addCharTail_depthOne`, unconditional, for **every** `j` (the depth-1 rung does not
need `j ≢ 0 (mod Q)`; the cancellation comes from `z ≠ 1` alone), for every `b ≥ 1` and every `h`
with `b ∤ h`.

## Where the ladder stops, and why depth must GROW

The depth-`K` truncation costs

    (1/N) ∑_{n<N} ‖e((h/b^K)·tailLarge P b (n+K)) − 1‖  ≤  2π|h|·b^{−K}·(1/N)∑_{n<N} tailLarge P b (n+K),

and `(1/N)∑_{n<N} tailLarge P b n → ∞` at rate `(log log N)/(b−1)` (Hardy–Ramanujan: the mean of
`ω` on `[1,N]` is `~ log log N`, and `∑_{i≥1} b^{−i} = 1/(b−1)`).  So **no fixed depth closes the
crux**: `K` must grow, at the very slow rate `K ≳ log_b log log N`.  Rung 2 of the ladder
(`DIRECTION.md`) is that divergence, as a kernel fact rather than a handoff claim.

Depth `2` is `(1/N)∑_n e(jn/Q)·z₁^{ω_{>P}(n+1)}·z₂^{ω_{>P}(n+2)} → 0`, which is **not** an open
conjecture outside a small set of scales: it is Tao–Teräväinen 2025, Theorem 3.1 (3.4) verbatim
(`h₁ = 1`, `h₂ = 2`, `W = Q`; text on disk at
`papers/tao-teravainen-2025-quantitative-correlations.txt`), built on Pilatte's 2025 decoupling
inequality.  See `PENDING_WORK.md`'s 2026-09-25 reflection and `papers/literature-review.md`'s
casting-out chapter.
-/

open Finset Filter Topology Complex

namespace NormalNumbers

/-- The two `omegaLarge`s in the tree — `SwingC3Split`'s (`¬ p ≤ P`) and `DelangeSlot`'s
(`P < p`) — are the same function.  Needed to consume the Delange slot from the C3 vocabulary. -/
theorem omegaLarge_eq_delangeSlot (P m : ℕ) : omegaLarge P m = DelangeSlot.omegaLarge P m := by
  classical
  rw [omegaLarge, DelangeSlot.omegaLarge]
  congr 1
  ext p
  simp [Finset.mem_filter]

/-- `e(k·x) = e(x)^k` for a natural exponent. -/
theorem ee_nat_mul (x : ℂ) (k : ℕ) : ee ((k : ℂ) * x) = (ee x) ^ k := by
  induction k with
  | zero => simp [ee]
  | succ n ih =>
      rw [pow_succ, ← ih, ← ee_add]
      congr 1
      push_cast
      ring

/-- The depth-`1` phase is a power of the root of unity `e(h/b)`. -/
theorem ee_depthOne_eq_pow (b : ℕ) (h : ℤ) (k : ℕ) :
    ee ((((h : ℝ) * (k : ℝ) / (b : ℝ) : ℝ)) : ℂ) = (ee ((((h : ℝ) / (b : ℝ) : ℝ)) : ℂ)) ^ k := by
  rw [← ee_nat_mul]
  congr 1
  push_cast
  ring

/-- `e(h/b) = 1` exactly when `b ∣ h`. -/
theorem ee_div_eq_one_iff {b : ℕ} (hb : 0 < b) (h : ℤ) :
    ee ((((h : ℝ) / (b : ℝ) : ℝ)) : ℂ) = 1 ↔ (b : ℤ) ∣ h := by
  have hbR : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  rw [ee_eq_one_iff_int]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have : (h : ℝ) = (b : ℝ) * (m : ℝ) := by
      field_simp at hm; linarith [hm]
    exact_mod_cast this
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; field_simp⟩

namespace CastingOut

/-- **RUNG 1 OF C3'S DEPTH LADDER — unconditional.**  The depth-`1` truncation of the twisted tail
phase has vanishing Cesàro mean, for every additive twist `e(jn/Q)` (including the trivial one)
and every frequency `h` not killed by the base.

This is `DelangeSlot.twisted_omegaLarge_mean_tendsto_zero` re-indexed by `m = n+1`; the point is
that the asset was already proved and unconsumed.  See the module docstring for why no FIXED depth
closes the crux. -/
theorem addCharTail_depthOne (b P Q j : ℕ) (h : ℤ) (hb : 0 < b) (hQ : 0 < Q)
    (hbh : ¬ ((b : ℤ) ∣ h)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ee ((((j : ℝ) * (n : ℝ) / (Q : ℝ) : ℝ)) : ℂ)
          * ee ((((h : ℝ) * (omegaLarge P (n + 1) : ℕ) / (b : ℝ) : ℝ)) : ℂ)) / (N : ℂ))
      atTop (𝓝 0) := by
  classical
  set z : ℂ := ee ((((h : ℝ) / (b : ℝ) : ℝ)) : ℂ) with hz
  have hznorm : ‖z‖ = 1 := norm_ee_real _
  have hz1 : z ≠ 1 := fun hc => hbh ((ee_div_eq_one_iff hb h).1 hc)
  have hQR : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hQ.ne'
  -- the Delange slot, in the `ee` vocabulary
  have hslot := DelangeSlot.twisted_omegaLarge_mean_tendsto_zero P Q hQ (j : ℤ) z hznorm hz1
  -- rewrite the slot's `exp (2πI j m / Q)` as `ee (j m / Q)`
  have hexp : ∀ m : ℕ, ee ((((j : ℝ) * (m : ℝ) / (Q : ℝ) : ℝ)) : ℂ)
      = Complex.exp (2 * Real.pi * Complex.I * ((j : ℤ) : ℂ) * (m : ℂ) / (Q : ℂ)) := by
    intro m
    rw [ee]
    congr 1
    push_cast
    field_simp
  -- the per-term identity, after the shift `m = n+1`
  have hterm : ∀ n : ℕ,
      ee ((((j : ℝ) * (n : ℝ) / (Q : ℝ) : ℝ)) : ℂ)
        * ee ((((h : ℝ) * (omegaLarge P (n + 1) : ℕ) / (b : ℝ) : ℝ)) : ℂ)
      = ee (((-((j : ℝ) / (Q : ℝ)) : ℝ)) : ℂ)
        * (Complex.exp (2 * Real.pi * Complex.I * ((j : ℤ) : ℂ) * ((n + 1 : ℕ) : ℂ) / (Q : ℂ))
            * z ^ DelangeSlot.omegaLarge P (n + 1)) := by
    intro n
    have hshift : ee ((((j : ℝ) * (n : ℝ) / (Q : ℝ) : ℝ)) : ℂ)
        = ee (((-((j : ℝ) / (Q : ℝ)) : ℝ)) : ℂ)
          * ee ((((j : ℝ) * ((n : ℕ) + 1 : ℕ) / (Q : ℝ) : ℝ)) : ℂ) := by
      rw [← ee_add]
      congr 1
      push_cast
      field_simp
      ring
    rw [hshift, ← hexp (n + 1), omegaLarge_eq_delangeSlot, ← ee_depthOne_eq_pow]
    push_cast
    ring
  -- the shift of the index set
  have hreindex : ∀ (N : ℕ) (f : ℕ → ℂ),
      ∑ n ∈ range N, f (n + 1) = ∑ m ∈ Icc 1 N, f m := by
    intro N f
    induction N with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
  have hid : ∀ N : ℕ,
      (∑ n ∈ range N, ee ((((j : ℝ) * (n : ℝ) / (Q : ℝ) : ℝ)) : ℂ)
          * ee ((((h : ℝ) * (omegaLarge P (n + 1) : ℕ) / (b : ℝ) : ℝ)) : ℂ)) / (N : ℂ)
      = ee (((-((j : ℝ) / (Q : ℝ)) : ℝ)) : ℂ)
        * ((∑ m ∈ Icc 1 N,
            Complex.exp (2 * Real.pi * Complex.I * ((j : ℤ) : ℂ) * (m : ℂ) / (Q : ℂ))
              * z ^ DelangeSlot.omegaLarge P m) / (N : ℂ)) := by
    intro N
    rw [Finset.sum_congr rfl (fun n _ => hterm n), ← Finset.mul_sum,
      hreindex N (fun m => Complex.exp (2 * Real.pi * Complex.I * ((j : ℤ) : ℂ) * (m : ℂ) / (Q : ℂ))
        * z ^ DelangeSlot.omegaLarge P m)]
    ring
  have := hslot.const_mul (ee (((-((j : ℝ) / (Q : ℝ)) : ℝ)) : ℂ))
  rw [mul_zero] at this
  exact Tendsto.congr (fun N => (hid N).symm) this

end CastingOut

end NormalNumbers
