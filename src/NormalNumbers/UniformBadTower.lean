/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.UniformBadLowerBound

/-!
# Tightening the beam: where the finite systems stop, and rational towers for `c⋆`

**Lower side (host probe 2026-10-08, `scripts/uniformbad_cstar_probe_scaled.py`, exact
rationals).**  With all bases `b ≤ 10` and all `n` with `bⁿ ≤ 10¹¹`, the survivor set of
`‖bⁿξ‖ > b^{−c}` is empty at `c = 729/290 ≈ 2.513793`, with at most 18 live intervals at any stage.
With all bases `b ≤ 30` and `bⁿ ≤ 10¹²` it is empty below `c ≈ 2.5138155` and nonempty above.
The last survivors there are the family of `241/1365`: its binary orbit (period 12) stays
`239/1365` from `ℤ`, so it dies at `log₂(1365/239) ≈ 2.5138184`.  At `c = 2.514`, every base
`b < 1365` keeps `241/1365` good for every `n` (`goodBelow_241_1365`).  So a finite cover can pass
`2.514` only by using a multiple of `1365` as a base.  The earlier plateau at
`log₂(257/45) ≈ 2.513771`, the 16-cycle of `77/257`, was an artifact of short horizons: `3` is a
primitive root mod `257`, so base 3 kills `77/257`, but only at `n` near `128`.

**Upper side: self-good rationals and towers.**  A rational `p/q` is never admissible, since base
`q` kills it.  It can, however, be good for every base below `q`.  The extremal survivors all
have this shape, and their denominators have a small Carmichael exponent `λ(q)`.  When `λ(q)` is
small, every base has orbit length `≤ λ(q)` modulo `q`, so every window condition is a short
finite check.  Examples:

* `1365 = 3·5·7·13` has `λ = 12`.
* At `c = 3` there are 82 self-good rationals in `(0, 1/2]` with `q ≤ 8000`
  (`scripts/uniformbad_selfgood_rationals.py`).  Their denominators include `2730`, `6765` and
  `7735`, with `λ = 12, 40, 48`.
* At `c = 2.6`, only `241/1365` and `409/1365` have `17 < q ≤ 20000`.

Write `Q_L` for the product of the primes `p` with `(p − 1) ∣ L`, so that `λ(Q_L) ∣ L`.  Random
numerators mod `Q_L` (`scripts/uniformbad_carmichael_density.py`, 3000 samples) gave these
self-good densities:

* At `c = 4`: `153` for `Q_12 = 2730`, `12` for `Q_36 ≈ 1.9·10⁶`, and `8` for
  `Q_72 ≈ 1.4·10⁸`, out of 3000 each.
* At `c = 3`: `4` for `Q_12`, and none for `Q_36`, `Q_60` or `Q_72`.

`admissible_of_towerFamily` turns a family into an admissible `ξ`, provided each member can be
approximated arbitrarily well by members that are good below any base bound.  The point `ξ` is a
Cauchy limit that keeps the finitely many margins in force at each step.  For rational families
(`RationalTower`) this makes the upper bound a question about rationals with small-`λ`
denominators, each of whose finite checks is decidable.  This is a global mechanism: periodicity
handles every base at once, which is exactly what the local engines lack.  They are walled at
`9/2` (`not_nineHalvesBalance`, `not_perStageCert`).
-/

namespace NormalNumbers.UniformBadThreshold

open NormalNumbers.UniformBad (dnear)

/-- 95-window certificate at `c = 729/290` (`scripts/cstar_models/cert_exact.py 729 290 10 1e11 9`:
exact survivor sweep over bases `b ≤ 10`, `bⁿ ≤ 10¹¹`, then a chain of the windows it used;
bases `2, 3, 5, 6, 10`, `n ≤ 30`). -/
def cert729290 : List Win :=
  [(2, 0, 0, 21886831/125000000),
   (2, 16, 11475, 21886831/125000000),
   (3, 7, 383, 2527411/40000000),
   (2, 8, 45, 21886831/125000000),
   (2, 24, 2960595, 21886831/125000000),
   (5, 11, 8616466, 68343/3906250),
   (2, 16, 11565, 21886831/125000000),
   (3, 7, 386, 2527411/40000000),
   (2, 12, 723, 21886831/125000000),
   (3, 13, 281488, 2527411/40000000),
   (2, 20, 185133, 21886831/125000000),
   (2, 4, 3, 21886831/125000000),
   (5, 1, 1, 68343/3906250),
   (2, 6, 13, 21886831/125000000),
   (3, 5, 50, 2527411/40000000),
   (2, 10, 211, 21886831/125000000),
   (3, 7, 451, 2527411/40000000),
   (2, 2, 1, 21886831/125000000),
   (2, 18, 77011, 21886831/125000000),
   (6, 7, 82238, 11063403/1000000000),
   (2, 10, 301, 21886831/125000000),
   (3, 3, 8, 2527411/40000000),
   (2, 6, 19, 21886831/125000000),
   (2, 22, 1256659, 21886831/125000000),
   (3, 23, 28206322061, 2527411/40000000),
   (2, 30, 321704749, 21886831/125000000),
   (2, 14, 4909, 21886831/125000000),
   (3, 10, 17693, 2527411/40000000),
   (2, 18, 78547, 21886831/125000000),
   (3, 15, 4299416, 2527411/40000000),
   (2, 10, 307, 21886831/125000000),
   (10, 1, 3, 1531711/500000000),
   (2, 8, 77, 21886831/125000000),
   (3, 12, 160211, 2527411/40000000),
   (2, 16, 19757, 21886831/125000000),
   (3, 8, 1978, 2527411/40000000),
   (2, 12, 1235, 21886831/125000000),
   (3, 14, 1442335, 2527411/40000000),
   (2, 20, 316205, 21886831/125000000),
   (2, 4, 5, 21886831/125000000),
   (3, 1, 1, 2527411/40000000),
   (2, 3, 3, 21886831/125000000),
   (5, 1, 2, 68343/3906250),
   (2, 5, 13, 21886831/125000000),
   (3, 5, 100, 2527411/40000000),
   (2, 9, 211, 21886831/125000000),
   (3, 7, 902, 2527411/40000000),
   (2, 1, 1, 21886831/125000000),
   (3, 7, 1285, 2527411/40000000),
   (2, 9, 301, 21886831/125000000),
   (3, 5, 143, 2527411/40000000),
   (2, 5, 19, 21886831/125000000),
   (5, 1, 3, 68343/3906250),
   (2, 3, 5, 21886831/125000000),
   (3, 1, 2, 2527411/40000000),
   (2, 4, 11, 21886831/125000000),
   (2, 20, 732371, 21886831/125000000),
   (3, 14, 3340634, 2527411/40000000),
   (2, 12, 2861, 21886831/125000000),
   (3, 8, 4583, 2527411/40000000),
   (2, 16, 45779, 21886831/125000000),
   (3, 12, 371230, 2527411/40000000),
   (2, 8, 179, 21886831/125000000),
   (10, 1, 7, 1531711/500000000),
   (2, 10, 717, 21886831/125000000),
   (3, 15, 10049491, 2527411/40000000),
   (2, 18, 183597, 21886831/125000000),
   (3, 10, 41356, 2527411/40000000),
   (2, 14, 11475, 21886831/125000000),
   (2, 30, 752037075, 21886831/125000000),
   (3, 23, 65936856766, 2527411/40000000),
   (2, 22, 2937645, 21886831/125000000),
   (2, 6, 45, 21886831/125000000),
   (3, 3, 19, 2527411/40000000),
   (2, 10, 723, 21886831/125000000),
   (6, 7, 197698, 11063403/1000000000),
   (2, 18, 185133, 21886831/125000000),
   (2, 2, 3, 21886831/125000000),
   (3, 7, 1736, 2527411/40000000),
   (2, 10, 813, 21886831/125000000),
   (3, 5, 193, 2527411/40000000),
   (2, 6, 51, 21886831/125000000),
   (5, 1, 4, 68343/3906250),
   (2, 4, 13, 21886831/125000000),
   (2, 20, 863443, 21886831/125000000),
   (3, 13, 1312835, 2527411/40000000),
   (2, 12, 3373, 21886831/125000000),
   (3, 7, 1801, 2527411/40000000),
   (2, 16, 53971, 21886831/125000000),
   (5, 11, 40211659, 68343/3906250),
   (2, 24, 13816621, 21886831/125000000),
   (2, 8, 211, 21886831/125000000),
   (3, 7, 1804, 2527411/40000000),
   (2, 16, 54061, 21886831/125000000),
   (2, 0, 1, 21886831/125000000)]

/-- **Frozen gate (2026-10-08).**  Believed 95%.  A finite exact certificate at `c = 729/290`.
Host probe: bases `b ≤ 10`, all `n` with `bⁿ ≤ 10¹¹`, empty survivor set, at most 18 live
intervals.  Discharge it with `not_admissible_of_cert` and a window list generated by a script
in `scripts/cstar_models/`. -/
theorem not_admissible_729_290 : ¬ Admissible (729 / 290) := by
  have := not_admissible_of_cert 729 290 (by norm_num) cert729290 (by decide +kernel)
    (by decide +kernel)
  norm_num at this ⊢; exact this

/-- **Headline (lower bound, frozen 2026-10-08).**  `c⋆ ≥ 729/290 ≈ 2.513793`, within `2.6·10⁻⁵`
of the finite-system threshold `≈ 2.5138155` with bases `b ≤ 30`. -/
@[blueprint (title := "Bugeaud 10.36 optimal exponent: c⋆ ≥ 729/290, at the finite-system threshold")]
theorem le_cStar_729_290 : (729 : ℝ) / 290 ≤ cStar :=
  le_cStar_of_not_admissible not_admissible_729_290

/-- `x` is good at exponent `c` for every base below `B`, at every `n`. -/
def GoodBelow (c : ℝ) (B : ℕ) (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → b < B → ∀ n : ℕ, (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * x)

/-- **Frozen (2026-10-08).**  Believed 99%.  The extremal survivor `241/1365` is good at
`c = 2.514` for every base below `1365` and every `n`.  It is a finite computation: every orbit
mod `1365` has length dividing `λ(1365) = 12`, and for `b ≥ 18` the bound `1/1365 > b^{−2.514}`
is automatic, except when `1365 ∣ bⁿ·241`, which needs `1365 ∣ b`. -/
theorem goodBelow_241_1365 : GoodBelow (2514 / 1000) 1365 (241 / 1365) := by
  sorry

/-- A **tower family** at exponent `c`: a nonempty set, each of whose members is approximated
arbitrarily well by members that are good below any prescribed base bound. -/
def TowerFamily (c : ℝ) (F : Set ℝ) : Prop :=
  F.Nonempty ∧ ∀ x ∈ F, ∀ ε > 0, ∀ B : ℕ, ∃ y ∈ F, |y - x| < ε ∧ GoodBelow c B y

/-- **Frozen (2026-10-08).**  Believed 99%.  The tower lemma.

English proof.  Pick `y₀ ∈ F`.  Given `y_k`, which is good below `k + 2`, the finitely many
margins `m_k = min_{2 ≤ b ≤ k+1, n ≤ k} (dnear(bⁿ y_k) − b^{−c})` are positive.  Choose `y_{k+1} ∈ F`
good below `k + 3` with `|y_{k+1} − y_k| < ε_k`, where
`ε_k = min(ε_{k−1}/2, m_k / (4·(k+1)^k))`.  Then `y_k` is Cauchy with a limit `ξ` and
`|ξ − y_k| ≤ 2ε_k`.  Since `dnear` is `1`-Lipschitz,
`dnear(bⁿξ) ≥ dnear(bⁿy_k) − bⁿ·2ε_k > b^{−c}` whenever `b ≤ k+1` and `n ≤ k`.  Every `(b, n)`
is covered by some `k`. -/
theorem admissible_of_towerFamily {c : ℝ} {F : Set ℝ} (h : TowerFamily c F) : Admissible c := by
  sorry

/-- A tower family made of rationals.  Every `GoodBelow c B (p/q)` with `B ≤ q` is decidable
through the finitely many orbits mod `q`. -/
def RationalTower (c : ℝ) : Prop :=
  ∃ F : Set ℝ, F ⊆ Set.range ((↑) : ℚ → ℝ) ∧ TowerFamily c F

/-- **Headline (upper-bound route, frozen 2026-10-08).**  Believed 40% true, 15% provable soon.

A tower of rationals at exponent `4`.  With `cStar_le_of_rationalTower` this closes the frozen
wall `cStar_le_four` by a global mechanism, outside the local engines walled at `9/2`.

Proposed mechanism (Carmichael towers).  Take a chain of moduli `Q_{L₁} ∣ Q_{L₂} ∣ ⋯` with small
Carmichael exponent, e.g. `Lᵢ` highly composite and `Q_L = ∏_{(p−1) ∣ L} p`.  Inside each, take
numerators that are self-good at `c = 4`.  The host density (`153, 12, 8` per 3000 at
`L = 12, 36, 72`) must be turned into a proof that self-good numerators exist in every short
interval mod `Q_{L_{i+1}}`.  A natural count: a numerator `p` is bad iff for some base
`b ≤ Q^{1/4}`, some orbit point `p·bⁿ mod Q` lies in a window of size `2Q·b^{−4}`.  This bad set
is a union of cosets of `⟨b⟩`, which is a finite exact computation per `L` but not a uniform
proof.  A uniform proof needs the windows' cosets to overlap, or a structured choice of numerators
(e.g. shadowing the previous level's numerator).

Known-false siblings.  Rationals with a bounded denominator: they die at base `q`
(`uniformBad_base_two` is the base-2 floor).  The same tower at `c ≤ 93/37` must fail
(`ninety_three_thirty_sevenths_le_cStar`).  A proof must therefore use `c = 4` quantitatively,
not just periodicity. -/
theorem rationalTower_four : RationalTower 4 := by
  sorry

/-- A rational tower at `c` bounds `c⋆` by `c`. -/
theorem cStar_le_of_rationalTower {c : ℝ} (h : RationalTower c) : cStar ≤ c := by
  obtain ⟨F, -, hF⟩ := h
  exact csInf_le bddBelow_admissible (admissible_of_towerFamily hF)

/-- **Stretch node.**  Believed 25%.  A rational tower at exponent `3`.  Host density at
`c = 3` is `0/3000` at `Q_36`, `Q_60` and `Q_72`, so it needs structured numerators. -/
def RationalTowerThree : Prop := RationalTower 3

end NormalNumbers.UniformBadThreshold
