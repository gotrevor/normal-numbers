#!/usr/bin/env bash
# Axiom + exact-type audit for the joint-Lambert quantitative foundations
# (campaign of 2026-09-29: gcd divisor average and small prime pool).
# Expected: every #print axioms line lists exactly [propext, Classical.choice, Quot.sound].
set -euo pipefail
cd "$(dirname "$0")/.."
lake build NormalNumbers.JointLambertSmallPool
tmp=$(mktemp /tmp/jlsp-XXXX.lean)
cat > "$tmp" <<'LEAN'
import NormalNumbers.JointLambertSmallPool

open Finset NormalNumbers.SwingC2
namespace NormalNumbers.JointLambert

-- Exact headline types, compiler-enforced.
example : ∀ m n : ℕ, tau (m * n) ≤ tau m * tau n := tau_mul_le

example : ∀ {u A H M : ℕ}, 0 < u → 0 < A → 1 ≤ H → (∀ m, m < M → u + m * A ≤ H ^ 2) →
    (∑ m ∈ range M, (tau (u + m * A) : ℝ)) ≤
      (tau (Nat.gcd u A) : ℝ) * (2 * M * (1 + Real.log H) + 2 * H) :=
  fun {_ _ _ _} => sum_tau_progression_le_gcd

example : ∀ {u A H M : ℕ}, 0 < u → 0 < A → 1 ≤ H → (∀ m, m < M → u + m * A ≤ H ^ 2) →
    (∑ m ∈ range M, (tau (u + m * A) : ℝ)) ≤
      (tau A : ℝ) * (2 * M * (1 + Real.log H) + 2 * H) :=
  fun {_ _ _ _} => sum_tau_progression_le_noncoprime

example : ∀ {c a k r q : ℕ} {p : ℕ → ℕ → ℕ}, 2 ≤ c → 2 ≤ a → q.Prime →
    (∀ j t, j ∈ killedIdx k r → t < j + 1 → (p j t).Prime) →
    tau (jointA c a k r q p) ≤ (a + 1) * (c + 1) ^ (k ^ 2) :=
  fun {_ _ _ _ _ _} => jointA_tau_le

example : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ r : ℕ,
    1 + killPoolSize k r + 1 ≤ (((Ioo (k ^ 3) (2 * k ^ 3)).filter Nat.Prime).card) :=
  eventually_small_prime_pool

end NormalNumbers.JointLambert

#print axioms NormalNumbers.JointLambert.tau_mul_le
#print axioms NormalNumbers.JointLambert.tau_prod_le
#print axioms NormalNumbers.JointLambert.sum_tau_progression_le_gcd
#print axioms NormalNumbers.JointLambert.sum_tau_progression_le_noncoprime
#print axioms NormalNumbers.JointLambert.jointA_tau_le
#print axioms NormalNumbers.JointLambert.eventually_small_prime_pool
#print axioms NormalNumbers.JointLambert.exists_prime_allocation_small_pool
LEAN
lake env lean "$tmp"
rm -f "$tmp"
echo "joint-lambert small-pool audit OK"
