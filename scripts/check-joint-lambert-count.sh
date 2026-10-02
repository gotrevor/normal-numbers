#!/usr/bin/env bash
# Permanent audit for the joint-Lambert QUANTITATIVE COUNT (campaign of 2026-09-29).
#
#  * exact ratified headline types, compiler-enforced;
#  * the {2,4} specialization and the boundary controls;
#  * transitive axiom verification of BOTH headlines (no sorryAx anywhere in the chain);
#  * frozen-source diff of every pre-existing JointLambert*.lean against the baseline.
#
# Expected: every #print axioms line lists exactly [propext, Classical.choice, Quot.sound].
set -euo pipefail
cd "$(dirname "$0")/.."
BASE=${BASE:-e2828b32}

echo "== frozen sources unchanged since $BASE =="
for f in $(git ls-tree "$BASE" --name-only src/NormalNumbers/ | grep 'JointLambert.*\.lean$'); do
  if ! git diff --quiet "$BASE" -- "$f"; then
    echo "FROZEN SOURCE MODIFIED: $f" >&2
    exit 1
  fi
done
echo "ok"

echo "== full build =="
lake build

tmp=$(mktemp /tmp/jlcount-XXXX.lean)
cat > "$tmp" <<'LEAN'
import NormalNumbers.JointLambertQuantitative

open Finset NormalNumbers.SwingC2
namespace NormalNumbers.JointLambert

-- Ratified headline 1, exact type.
example : ∀ (S : Finset ℕ), (∀ b ∈ S, 2 ≤ b) → ∀ (lengths values : ℕ → ℕ),
    (∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b) →
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) * Real.exp (-C * (Real.log (Real.log (N : ℝ))) ^ 2
        * Real.log (Real.log (Real.log (N : ℝ))))
          ≤ (jointWordCount S lengths values N : ℝ) :=
  jointWords_quantitative

-- Ratified headline 2, exact type.
example : ∀ (S : Finset ℕ), (∀ b ∈ S, 2 ≤ b) → ∀ (lengths values : ℕ → ℕ),
    (∀ b ∈ S, 0 < lengths b ∧ values b < b ^ lengths b) →
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (N : ℝ) ^ (1 - ε) ≤ (jointWordCount S lengths values N : ℝ) :=
  jointWords_power_count

-- The {2,4} specialization, both headlines.
example : ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) * Real.exp (-C * (Real.log (Real.log (N : ℝ))) ^ 2
      * Real.log (Real.log (Real.log (N : ℝ))))
        ≤ (jointWordCount {2, 4} (fun _ => 1) (fun _ => 0) N : ℝ) :=
  jointWords_quantitative {2, 4} (by decide) _ _ (by decide)

example : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) ^ (1 - ε) ≤ (jointWordCount {2, 4} (fun _ => 1) (fun _ => 0) N : ℝ) :=
  fun ε hε => jointWords_power_count {2, 4} (by decide) _ _ (by decide) ε hε

-- Boundary controls on the count itself.
example (lengths values : ℕ → ℕ) (N : ℕ) : jointWordCount ∅ lengths values N = N :=
  jointWordCount_empty lengths values N
example (S : Finset ℕ) (lengths values : ℕ → ℕ) : jointWordCount S lengths values 0 = 0 :=
  jointWordCount_zero S lengths values
example (S : Finset ℕ) (lengths values : ℕ → ℕ) (N : ℕ) :
    jointWordCount S lengths values N ≤ N := jointWordCount_le S lengths values N

end NormalNumbers.JointLambert

#print axioms NormalNumbers.JointLambert.jointWords_quantitative
#print axioms NormalNumbers.JointLambert.jointWords_power_count
#print axioms NormalNumbers.JointLambert.exists_good_starts_at_height
#print axioms NormalNumbers.JointLambert.exists_joint_small_tail_count
#print axioms NormalNumbers.JointLambert.exists_candidate_data_at_height
#print axioms NormalNumbers.JointLambert.binTail_eq_three_range
#print axioms NormalNumbers.JointLambert.far_cost_le
#print axioms NormalNumbers.JointLambert.sqrt_window_mul_le
#print axioms NormalNumbers.JointLambert.eventually_countJ_le
LEAN
echo "== exact types + transitive axioms =="
out=$(lake env lean "$tmp")
echo "$out"
rm -f "$tmp"
if echo "$out" | grep -q 'sorryAx'; then
  echo "SORRY IN THE DEPENDENCY CHAIN" >&2
  exit 1
fi
echo "joint-lambert COUNT audit OK"
