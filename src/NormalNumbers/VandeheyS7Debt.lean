/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-DB: the current stall is a DEBIT on the ledger

S7-LG telescoped the height ledger (`∏ b ≤ C·∏(a+5)`, from `d ≥ √(|det Φ|/6)`).  S7-SA/S7-AG
showed that a stall of length `k` forces `d ≥ minDen · fib(k+1)`.  Putting the two together
strengthens the ledger by the *current* stall age — the height that the stall has built up and
not yet paid back:

    √(|det Φ|/6) · fib(stallAge + 1) · ∏_{i<n} b_i  ≤  d₂ · ∏_{i<n} (a_i + 5)

(`fib_stallAge_mul_prod_emitFac_le`), i.e. in log form

    log fib(stallAge n + 1) + Σ_{i<n} log b_i  ≤  ledgerConst + Σ_{i<n} log (a_i + 5)
                                                                  (`log_fib_stallAge_le`)

so **`stallAge n · log φ ≤ slack n`**, the ledger's running slack, up to an absolute constant.

Why this is the right shape for `WidthFreqBound`.  Summing the stall clock over a range is an
identity about the emission schedule:

    Σ_{n<p} stallAge n  =  Σ_{stalls} 1 + 2 + ⋯ + len  =  ½ Σ_{stalls} len(len+1) ,

so a bound `Σ_{n<p} stallAge n = O(p)` gives `Σ_{stalls} len² = O(p)`, and Chebyshev then gives
`Σ_{len > K} len = O(p/K) → 0`.  That is exactly `WidthFreqBound`, by S7-AG.  So the whole
obligation has collapsed to: **the running slack of the height ledger has bounded Cesàro
average** — equivalently, `(1/p)·Σ_{n<p} log d_n = O(1)`, positive recurrence of the height walk.
No geometry, no cells, no state space: one scalar walk, reflected at `√(|det Φ|/6)`.
-/
import NormalNumbers.VandeheyS7Age

namespace NormalNumbers.VandeheyS7

open Set Finset NormalNumbers

namespace MapState

lemma stallAge_le_self (Φ : MapState) (x : ℝ) : ∀ n, stallAge Φ x n ≤ n := by
  intro n
  induction n with
  | zero => simp [stallAge]
  | succ n ih =>
    rw [stallAge_succ]
    by_cases h : runWord Φ x n = [] <;> simp [h] <;> omega

/-- **The stall clock is a lower bound on the height.**  Capped at `n` so that the base time of
the stall is at least `2`, where the unconditional `minDen` floor is available. -/
theorem sqrt_mul_fib_stallAge_le_d (Φ : MapState) {x : ℝ}
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    Real.sqrt (|Φ.det| / 6) * (Nat.fib (min (stallAge Φ x (n + 2)) n + 1) : ℝ)
      ≤ (runState Φ x (n + 2)).d := by
  set k := stallAge Φ x (n + 2) with hk
  set k' := min k n with hk'
  have hkle : k ≤ n + 2 := stallAge_le_self Φ x (n + 2)
  have hk'le : k' ≤ k := min_le_left _ _
  have hk'n : k' ≤ n := min_le_right _ _
  set j := n - k' with hj
  have hjk : j + 2 + k' = n + 2 := by omega
  -- the full stall, from the clock
  have hfull : ∀ i, i < k → runWord Φ x ((n + 2 - k) + i) = [] := by
    refine stall_of_stallAge Φ x k (n + 2 - k) ?_
    have : n + 2 - k + k = n + 2 := by omega
    rw [this, ← hk]
  have hsuf : ∀ i, i < k' → runWord Φ x (j + 2 + i) = [] := by
    intro i hi
    have := hfull ((k - k') + i) (by omega)
    have heq : (n + 2 - k) + ((k - k') + i) = j + 2 + i := by omega
    rwa [heq] at this
  have hd := d_stall_ge' Φ hx (n₀ := j + 2) (k := k') hsuf
  have hmin : Real.sqrt (|Φ.det| / 6) ≤ (runState Φ x (j + 2)).minDen := runState_minDen_ge Φ x j
  have hfibpos : (0:ℝ) ≤ (Nat.fib (k' + 1) : ℝ) := by positivity
  calc Real.sqrt (|Φ.det| / 6) * (Nat.fib (k' + 1) : ℝ)
      ≤ (runState Φ x (j + 2)).minDen * (Nat.fib (k' + 1) : ℝ) :=
        mul_le_mul_of_nonneg_right hmin hfibpos
    _ ≤ (runState Φ x (j + 2 + k')).d := hd
    _ = (runState Φ x (n + 2)).d := by rw [hjk]

/-- **S7-DB.**  The ledger, with the current stall age charged to the emitted side. -/
theorem fib_stallAge_mul_prod_emitFac_le (Φ : MapState) {x : ℝ}
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    Real.sqrt (|Φ.det| / 6) * (Nat.fib (min (stallAge Φ x (n + 2)) n + 1) : ℝ) *
        ∏ i ∈ range n, emitFac Φ x (i + 2)
      ≤ (runState Φ x 2).d * ∏ i ∈ range n, (((inDigit x (i + 2) : ℕ) : ℝ) + 5) := by
  have hP : (0:ℝ) < ∏ i ∈ range n, emitFac Φ x (i + 2) :=
    Finset.prod_pos (fun i _ => emitFac_pos Φ x (i + 2))
  refine le_trans ?_ (d_mul_prod_emitFac_le Φ x n)
  exact mul_le_mul_of_nonneg_right (sqrt_mul_fib_stallAge_le_d Φ hx n) hP.le

/-- **The log form.**  The stall clock is charged against the ledger's running slack. -/
theorem log_fib_stallAge_le (Φ : MapState) {x : ℝ}
    (hx : ∀ j, gaussMap^[j] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    Real.log (Nat.fib (min (stallAge Φ x (n + 2)) n + 1) : ℝ)
      + ∑ i ∈ range n, Real.log (emitFac Φ x (i + 2))
      ≤ ledgerConst Φ x + ∑ i ∈ range n, Real.log ((((inDigit x (i + 2) : ℕ) : ℝ) + 5)) := by
  have hdet : (0:ℝ) < |Φ.det| := abs_pos.mpr Φ.hdet
  have hs : (0:ℝ) < Real.sqrt (|Φ.det| / 6) := Real.sqrt_pos.mpr (by positivity)
  have hd2 : (0:ℝ) < (runState Φ x 2).d := (runState Φ x 2).hd
  have hfib : (0:ℝ) < (Nat.fib (min (stallAge Φ x (n + 2)) n + 1) : ℝ) := by
    have : 0 < Nat.fib (min (stallAge Φ x (n + 2)) n + 1) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast this
  have hP : (0:ℝ) < ∏ i ∈ range n, emitFac Φ x (i + 2) :=
    Finset.prod_pos (fun i _ => emitFac_pos Φ x (i + 2))
  have hQ : (0:ℝ) < ∏ i ∈ range n, (((inDigit x (i + 2) : ℕ) : ℝ) + 5) := by
    refine Finset.prod_pos (fun i _ => ?_)
    have := one_le_inDigit_real x (i + 2); linarith
  have hmain := fib_stallAge_mul_prod_emitFac_le Φ hx n
  have hlog := Real.log_le_log (by positivity) hmain
  rw [Real.log_mul (by positivity) hP.ne', Real.log_mul hs.ne' hfib.ne',
    Real.log_mul hd2.ne' hQ.ne'] at hlog
  rw [Real.log_prod (fun i _ => (emitFac_pos Φ x (i + 2)).ne'),
    Real.log_prod (fun i _ => by
      have := one_le_inDigit_real x (i + 2)
      exact (by linarith : (0:ℝ) < (((inDigit x (i + 2) : ℕ) : ℝ) + 5)).ne')] at hlog
  rw [ledgerConst]
  linarith

end MapState

section Audit

#print axioms MapState.stallAge_le_self
#print axioms MapState.sqrt_mul_fib_stallAge_le_d
#print axioms MapState.fib_stallAge_mul_prod_emitFac_le
#print axioms MapState.log_fib_stallAge_le

end Audit

end NormalNumbers.VandeheyS7
