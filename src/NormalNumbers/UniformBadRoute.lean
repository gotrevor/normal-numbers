/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadThreshold

/-!
# The route to `c⋆ ≤ 4`: perfect powers are free, and the small-base core

Two pieces of the `cStar_le_four` route (`UniformBadThreshold`).

**Proved here.**  A base-`m` guarantee is inherited by every power `mᵃ`
(`goodBase_pow`), so admissibility only has to be checked on bases that are not perfect powers
(`admissible_iff_nonPerfectPow`).  At `c = 4` this removes `4, 8, 9, 16, 25, 27, …`; bases `4`, `8`
and `9` are the costliest bases after `2, 3, 5, 6, 7`.

**The crux, as nodes.**  The 2026-10-07 probes (scratch models, recorded in `PENDING_WORK.md`)
say:
* every potential engine that charges base `2` (grid children `exists_avoid_powPot`, or children
  at a free real offset) fails its balance at `c = 4`, and in fact for all `c ≲ 7`;
* with base `2` exact (the limit point is forced into the base-2 set) and the obstacles averaged
  under a measure carried by the exact set, the remaining balance at `c = 4` is dominated by base
  `3` alone (about half the budget);
* with bases `2, 3, 5, 6, 7` exact, carried by a weighted tree of dimension `s ≈ 0.8` with
  cell-relative Frostman constant `C ≈ 1.5`, the averaged engine closes for all other bases with
  slack about `0.3`.
So the upper bound splits into `SmallBaseTreeCore` (a regular tree on the jointly-good set of the
small bases) and `TreeEngineSuffices` (the averaged potential engine on such a tree).  Both are
open nodes; `cStar_le_of_treeCore` wires them to the headline.
-/

namespace NormalNumbers.UniformBadThreshold

open NormalNumbers.UniformBad (dnear)

/-- `ξ` is good in base `b` at exponent `c`: `‖bⁿξ‖ > b^{−c}` for every `n`. -/
def GoodBase (c : ℝ) (b : ℕ) (ξ : ℝ) : Prop :=
  ∀ n : ℕ, (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ)

/-- `b` is a perfect power `mᵏ` with `k ≥ 2`. -/
def IsPerfPow (b : ℕ) : Prop := ∃ m k : ℕ, 2 ≤ k ∧ m ^ k = b

/-- Goodness in base `m` is inherited by every power `mᵃ`, `a ≥ 1` (for `c ≥ 0`). -/
theorem goodBase_pow {c : ℝ} (hc : 0 ≤ c) {m : ℕ} (hm : 1 ≤ m) {ξ : ℝ} (h : GoodBase c m ξ)
    {a : ℕ} (ha : 1 ≤ a) : GoodBase c (m ^ a) ξ := by
  intro n
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hle : ((m ^ a : ℕ) : ℝ) ^ (-c) ≤ (m : ℝ) ^ (-c) := by
    refine Real.rpow_le_rpow_of_nonpos (by linarith) ?_ (by linarith)
    push_cast
    calc (m : ℝ) = (m : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (m : ℝ) ^ a := pow_le_pow_right₀ hm' ha
  have := h (a * n)
  push_cast at hle ⊢
  rw [← pow_mul]
  exact lt_of_le_of_lt hle this

/-- Every `b ≥ 2` is a power `mᵃ` (`a ≥ 1`) of a base `m ≥ 2` that is not a perfect power. -/
theorem exists_nonPerfPow_root : ∀ b : ℕ, 2 ≤ b →
    ∃ m a : ℕ, 2 ≤ m ∧ 1 ≤ a ∧ ¬ IsPerfPow m ∧ m ^ a = b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb
    by_cases hp : IsPerfPow b
    · obtain ⟨m, k, hk, rfl⟩ := hp
      have hm2 : 2 ≤ m := by
        rcases Nat.lt_or_ge m 2 with h | h
        · interval_cases m
          · rw [zero_pow (by omega)] at hb; omega
          · rw [one_pow] at hb; omega
        · exact h
      have hlt : m < m ^ k := by
        calc m = m ^ 1 := (pow_one m).symm
          _ < m ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
      obtain ⟨m', a', h2, ha', hnp, rfl⟩ := ih m hlt hm2
      exact ⟨m', a' * k, h2, Nat.one_le_iff_ne_zero.2 (by positivity), hnp, by rw [pow_mul]⟩
    · exact ⟨b, 1, hb, le_rfl, hp, pow_one b⟩

/-- **Reduction to non-perfect-power bases.**  For `c ≥ 0`, `c` is admissible iff some `ξ` is good
in every base `b ≥ 2` that is not a perfect power. -/
theorem admissible_iff_nonPerfectPow {c : ℝ} (hc : 0 ≤ c) :
    Admissible c ↔ ∃ ξ : ℝ, ∀ b : ℕ, 2 ≤ b → ¬ IsPerfPow b → GoodBase c b ξ := by
  constructor
  · rintro ⟨ξ, hξ⟩
    exact ⟨ξ, fun b hb _ => hξ b hb⟩
  · rintro ⟨ξ, hξ⟩
    refine ⟨ξ, fun b hb => ?_⟩
    obtain ⟨m, a, hm, ha, hnp, rfl⟩ := exists_nonPerfPow_root b hb
    exact goodBase_pow hc (by omega) (hξ m hm hnp) ha

/-- **Crux node (small-base core).**  A weighted tree of closed cells `[q.1, q.2]` (level `k`
cells `T k`, a finite set) carried by the jointly-good set of the bases in `S`:
* cells are nondegenerate with positive weight, each level-`(k+1)` cell lies in a level-`k` cell
  and is at most `β` times as long, and a cell's weight is the sum of its children's weights;
* (**Frostman, cell-relative**) the level-`j` descendants of a level-`k` cell `q` that meet
  `[u, v]` carry weight at most `C · ((v − u)/|q| + β^{j−k})^s · w(q)`;
* every point lying in a cell of every level is good in every base of `S`.

Believed (with `S = {2, 3, 5, 6, 7}`, `c = 4`, `s = 4/5`, `C = 3/2`, some `β ≤ 2^{−9}`): 15%.
Probe 2026-10-07 (`scripts/cstar_models/fr.js`, `fr2.js`, depth 20): the survivor counting measure
has cell-relative constant `C ≈ 2.2` for base 2 alone (`s = 0.879`) but `C ≈ 9` once base 3 is
added (`s = 0.8`), from cells mostly eaten by one base-3 window; splitting cells at the windows
makes it worse (`≈ 30`, nearly dead components).  So a core with `C ≤ 3/2` must prune such cells,
and worst-case pruning (`t23.py`) keeps only `≈ 20%` of the children: neither works as is.  The
base-2 part alone is the binary run-free tree (no four equal consecutive digits) with Parry weights,
`s = log₂ 1.8393 ≈ 0.879`; the open part is the joint control of `3, 5, 6, 7` against it, whose
forbidden windows have relative size `≤ 2·3^{−4} ≈ 0.025`. -/
def SmallBaseTreeCore (c : ℝ) (S : Set ℕ) (s C β : ℝ) : Prop :=
  ∃ (T : ℕ → Finset (ℝ × ℝ)) (w : ℝ × ℝ → ℝ),
    (T 0).Nonempty ∧
    (∀ k, ∀ q ∈ T k, q.1 < q.2 ∧ 0 < w q) ∧
    (∀ k, ∀ q' ∈ T (k + 1), ∃ q ∈ T k, q.1 ≤ q'.1 ∧ q'.2 ≤ q.2 ∧ q'.2 - q'.1 ≤ β * (q.2 - q.1)) ∧
    (∀ k, ∀ q ∈ T k,
      w q = ∑ q' ∈ (T (k + 1)).filter (fun q' => q.1 ≤ q'.1 ∧ q'.2 ≤ q.2), w q') ∧
    (∀ k j, k ≤ j → ∀ q ∈ T k, ∀ u v : ℝ, u ≤ v →
      ∑ q' ∈ (T j).filter (fun q' => q.1 ≤ q'.1 ∧ q'.2 ≤ q.2 ∧ u ≤ q'.2 ∧ q'.1 ≤ v), w q' ≤
        C * ((v - u) / (q.2 - q.1) + β ^ (j - k)) ^ s * w q) ∧
    (∀ ξ : ℝ, (∀ k, ∃ q ∈ T k, q.1 ≤ ξ ∧ ξ ≤ q.2) → ∀ b ∈ S, GoodBase c b ξ)

/-- **Crux node (averaged engine).**  On a small-base tree core, the potential engine with
obstacle weights `(r/|q|)^α`, children averaged under the tree weights, and new obstacles charged
at their spacing scale, keeps the potential below threshold for every base outside `S` that is not
a perfect power; together with the core this gives admissibility.

Believed for `c = 4`, `S = {2, 3, 5, 6, 7}`, `s = 4/5`, `C = 3/2`, `β = 2^{−9}`: 50% (continuum
model slack `0.30`; the cell version loses up to `2^s` on the carried and proximity terms). -/
def TreeEngineSuffices (c : ℝ) (S : Set ℕ) (s C β : ℝ) : Prop :=
  SmallBaseTreeCore c S s C β → Admissible c

/-- The two crux nodes give the upper bound `c⋆ ≤ c`. -/
theorem cStar_le_of_treeCore {c : ℝ} {S : Set ℕ} {s C β : ℝ}
    (hcore : SmallBaseTreeCore c S s C β) (heng : TreeEngineSuffices c S s C β) : cStar ≤ c :=
  csInf_le bddBelow_admissible (heng hcore)

end NormalNumbers.UniformBadThreshold
