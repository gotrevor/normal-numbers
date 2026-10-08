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

open NormalNumbers.UniformBad (dnear dnear_le_abs_sub)

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

/-! ### `241/1365`: orbits mod `1365` have period dividing `12` -/

def m1365 (N : ℕ) : ℕ := min (N % 1365) (1365 - N % 1365)

theorem m1365_le (N : ℕ) (k : ℤ) : ((m1365 N : ℕ) : ℤ) ≤ |(N : ℤ) - 1365 * k| := by
  unfold m1365; rw [le_abs]; omega

theorem dnear_ge_m1365 (N : ℕ) : (m1365 N : ℝ) / 1365 ≤ dnear ((N : ℝ) / 1365) := by
  unfold dnear
  have h := m1365_le N (round ((N : ℝ) / 1365))
  have e : (N : ℝ) / 1365 - (round ((N : ℝ) / 1365) : ℝ) =
      (((N : ℤ) - 1365 * round ((N : ℝ) / 1365) : ℤ) : ℝ) / 1365 := by push_cast; ring
  rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 1365), div_le_div_iff_of_pos_right (by norm_num)]
  have : ((m1365 N : ℤ) : ℝ) ≤ ((|(N : ℤ) - 1365 * round ((N : ℝ) / 1365)| : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at this; simpa using this

theorem pow13_mod (r : ℕ) : r ^ 13 % 1365 = r % 1365 := by
  have h : ∀ r < 1365, r ^ 13 % 1365 = r % 1365 := by native_decide
  rw [Nat.pow_mod, h _ (Nat.mod_lt _ (by norm_num)), Nat.mod_mod]

theorem pow_mod_red (b n : ℕ) : ∃ n' ≤ 12, b ^ n % 1365 = b ^ n' % 1365 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ 12
    · exact ⟨n, hn, rfl⟩
    · obtain ⟨n', h1, h2⟩ := ih (n - 12) (by omega)
      refine ⟨n', h1, ?_⟩
      rw [← h2]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 13 := ⟨n - 13, by omega⟩
      rw [show k + 13 - 12 = k + 1 by omega, pow_add, Nat.mul_mod, pow13_mod, ← Nat.mul_mod,
        pow_succ]

theorem rpow_lt_of_pow (p q : ℕ) (hq : q ≠ 0) (b : ℕ) (hb : 1 ≤ b) (x : ℝ) (hx : 0 ≤ x)
    (h : 1 < x ^ q * (b : ℝ) ^ p) : (b : ℝ) ^ (-(p : ℝ) / q) < x := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hr : 0 < (b : ℝ) ^ (-(p : ℝ) / q) := Real.rpow_pos_of_pos hb0 _
  have h5 : ((b : ℝ) ^ (-(p : ℝ) / q)) ^ q = ((b : ℝ) ^ p)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, ← Real.rpow_natCast, ← Real.rpow_neg hb0.le]
    congr 1; field_simp
  by_contra hc
  have := pow_le_pow_left₀ hx (not_lt.1 hc) q
  rw [h5] at this
  have hb12 : (0:ℝ) < (b : ℝ) ^ p := by positivity
  have := mul_le_mul_of_nonneg_right this hb12.le
  rw [inv_mul_cancel₀ hb12.ne'] at this
  linarith

theorem check1365 : ∀ b < 1365, 2 ≤ b → ∀ n ≤ 12,
    1365 ^ 500 < m1365 (b ^ n * 241) ^ 500 * b ^ 1257 := by native_decide

/-- **Frozen (2026-10-08).**  Believed 99%.  The extremal survivor `241/1365` is good at
`c = 2.514` for every base below `1365` and every `n`.  It is a finite computation: every orbit
mod `1365` has length dividing `λ(1365) = 12`, and for `b ≥ 18` the bound `1/1365 > b^{−2.514}`
is automatic, except when `1365 ∣ bⁿ·241`, which needs `1365 ∣ b`. -/
theorem goodBelow_241_1365 : GoodBelow (2514 / 1000) 1365 (241 / 1365) := by
  intro b hb2 hb n
  obtain ⟨n', hn', hm⟩ := pow_mod_red b n
  have hmeq : m1365 (b ^ n * 241) = m1365 (b ^ n' * 241) := by
    unfold m1365; rw [Nat.mul_mod, hm, ← Nat.mul_mod]
  have hc := check1365 b hb hb2 n' hn'
  rw [← hmeq] at hc
  have hx := dnear_ge_m1365 (b ^ n * 241)
  have e : (b : ℝ) ^ n * (241 / 1365) = ((b ^ n * 241 : ℕ) : ℝ) / 1365 := by push_cast; ring
  rw [e]
  refine lt_of_lt_of_le ?_ hx
  generalize m1365 (b ^ n * 241) = M at hc hx ⊢
  have hc' : ((1365 : ℕ) : ℝ) ^ 500 < (M : ℝ) ^ 500 * (b : ℝ) ^ 1257 := by
    have := (Nat.cast_lt (α := ℝ)).2 hc
    simpa only [Nat.cast_pow, Nat.cast_mul] using this
  have := rpow_lt_of_pow 1257 500 (by norm_num) b (by omega) ((M : ℝ) / ((1365 : ℕ) : ℝ))
    (by positivity) (by
      rw [div_pow, div_mul_eq_mul_div, lt_div_iff₀ (by positivity), one_mul]
      exact hc')
  have e2 : (-(2514 / 1000 : ℝ)) = -((1257 : ℕ) : ℝ) / ((500 : ℕ) : ℝ) := by norm_num
  rw [e2]; simpa using this

/-- A **tower family** at exponent `c`: a nonempty set, each of whose members is approximated
arbitrarily well by members that are good below any prescribed base bound. -/
def TowerFamily (c : ℝ) (F : Set ℝ) : Prop :=
  F.Nonempty ∧ ∀ x ∈ F, ∀ ε > 0, ∀ B : ℕ, ∃ y ∈ F, |y - x| < ε ∧ GoodBelow c B y

theorem dnear_lipschitz : LipschitzWith 1 dnear := by
  refine LipschitzWith.of_le_add fun x y => ?_
  have h := dnear_le_abs_sub x (round y)
  have : |x - round y| ≤ dist x y + dnear y := by
    rw [Real.dist_eq]; unfold dnear
    calc |x - round y| = |(x - y) + (y - round y)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  linarith

/-- The finite good conditions at stage `k`: bases `2 ≤ b < k + 2`, exponents `n ≤ k`. -/
def stageGood (c : ℝ) (k : ℕ) : Set ℝ :=
  ⋂ b ∈ Finset.Ico 2 (k + 2), ⋂ n ∈ Finset.range (k + 1),
    {x | (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * x)}

theorem isOpen_stageGood (c : ℝ) (k : ℕ) : IsOpen (stageGood c k) := by
  refine isOpen_biInter_finset fun b _ => isOpen_biInter_finset fun n _ => ?_
  exact isOpen_lt continuous_const (dnear_lipschitz.continuous.comp (continuous_const.mul continuous_id))

/-- **Frozen (2026-10-08).**  Believed 99%.  The tower lemma.

English proof.  Pick `y₀ ∈ F`.  Given `y_k`, which is good below `k + 2`, the finitely many
margins `m_k = min_{2 ≤ b ≤ k+1, n ≤ k} (dnear(bⁿ y_k) − b^{−c})` are positive.  Choose `y_{k+1} ∈ F`
good below `k + 3` with `|y_{k+1} − y_k| < ε_k`, where
`ε_k = min(ε_{k−1}/2, m_k / (4·(k+1)^k))`.  Then `y_k` is Cauchy with a limit `ξ` and
`|ξ − y_k| ≤ 2ε_k`.  Since `dnear` is `1`-Lipschitz,
`dnear(bⁿξ) ≥ dnear(bⁿy_k) − bⁿ·2ε_k > b^{−c}` whenever `b ≤ k+1` and `n ≤ k`.  Every `(b, n)`
is covered by some `k`.  (The Lean proof packages this as Baire category in the complete space
`closure F`: each `stageGood c k` is open and dense there.) -/
theorem admissible_of_towerFamily {c : ℝ} {F : Set ℝ} (h : TowerFamily c F) : Admissible c := by
  obtain ⟨⟨y0, hy0⟩, hF⟩ := h
  let X := closure F
  have : CompleteSpace X := isClosed_closure.completeSpace_coe
  have : Nonempty X := ⟨⟨y0, subset_closure hy0⟩⟩
  let V : ℕ → Set X := fun k => (↑) ⁻¹' stageGood c k
  have hVo : ∀ k, IsOpen (V k) := fun k => (isOpen_stageGood c k).preimage continuous_subtype_val
  have hVd : ∀ k, Dense (V k) := by
    intro k
    rw [Metric.dense_iff]
    intro x r hr
    obtain ⟨x', hx'F, hx'⟩ := Metric.mem_closure_iff.1 x.2 (r / 2) (by positivity)
    obtain ⟨y, hyF, hyx, hyg⟩ := hF x' hx'F (r / 2) (by positivity) (k + 2)
    refine ⟨⟨y, subset_closure hyF⟩, ?_, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      rw [Real.dist_eq] at hx'
      calc |y - x| ≤ |y - x'| + |x' - x| := by
            have := abs_sub_le y x' x; exact this
        _ < r / 2 + r / 2 := by rw [abs_sub_comm x' x]; linarith
        _ = r := by ring
    · simp only [V, stageGood, Set.mem_preimage, Set.mem_iInter, Finset.mem_Ico, Set.mem_ofPred_eq]
      intro b hb n _
      exact hyg b hb.1 hb.2 n
  obtain ⟨ξ', hξ⟩ := (dense_iInter_of_isOpen hVo hVd).nonempty
  refine ⟨ξ'.1, fun b hb n => ?_⟩
  have := Set.mem_iInter.1 hξ (b + n)
  simp only [V, stageGood, Set.mem_preimage, Set.mem_iInter, Finset.mem_Ico, Finset.mem_range,
    Set.mem_ofPred_eq] at this
  exact this b ⟨hb, by omega⟩ n (by omega)

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

/-! ## Exact checker for rational goodness, and the Carmichael chain probe -/

/-- Distance of `N` to the nearest multiple of `q`, as a natural number. -/
def mDist (q N : ℕ) : ℕ := min (N % q) (q - N % q)

theorem dnear_ge_mDist (q N : ℕ) (hq : 0 < q) : (mDist q N : ℝ) / q ≤ dnear ((N : ℝ) / q) := by
  unfold dnear
  set k := round ((N : ℝ) / q)
  have h : ((mDist q N : ℕ) : ℤ) ≤ |(N : ℤ) - q * k| := by
    unfold mDist; rw [le_abs]
    have h5 : ((q - N % q : ℕ) : ℤ) = q - ((N % q : ℕ) : ℤ) :=
      Nat.cast_sub (Nat.mod_lt _ hq).le
    rcases le_or_gt k ((N : ℤ) / q) with hk | hk
    · left
      have h1 : (q : ℤ) * k ≤ q * ((N : ℤ) / q) := mul_le_mul_of_nonneg_left hk (by positivity)
      have h2 := Int.mul_ediv_add_emod (N : ℤ) q
      have h3 : ((N % q : ℕ) : ℤ) = (N : ℤ) % q := by push_cast; rfl
      omega
    · right
      have h1 : (q : ℤ) * ((N : ℤ) / q + 1) ≤ q * k := mul_le_mul_of_nonneg_left hk (by positivity)
      rw [mul_add, mul_one] at h1
      have h2 := Int.mul_ediv_add_emod (N : ℤ) q
      have h3 : ((N % q : ℕ) : ℤ) = (N : ℤ) % q := by push_cast; rfl
      have h4 : (N : ℤ) % q < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
      omega
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e : (N : ℝ) / q - (k : ℝ) = (((N : ℤ) - q * k : ℤ) : ℝ) / q := by
    push_cast; field_simp
  rw [e, abs_div, abs_of_pos hq', div_le_div_iff_of_pos_right hq']
  have : ((mDist q N : ℤ) : ℝ) ≤ ((|(N : ℤ) - q * k| : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at this; simpa using this

theorem pow_mod_red_gen (q n0 lam : ℕ) (hlam : 0 < lam)
    (hper : ∀ r, r ^ (n0 + lam) % q = r ^ n0 % q) (b n : ℕ) :
    ∃ n' < n0 + lam, b ^ n % q = b ^ n' % q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < n0 + lam
    · exact ⟨n, hn, rfl⟩
    · obtain ⟨n', h1, h2⟩ := ih (n - lam) (by omega)
      refine ⟨n', h1, ?_⟩
      rw [← h2]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + (n0 + lam) := ⟨n - (n0 + lam), by omega⟩
      rw [show k + (n0 + lam) - lam = k + n0 by omega, pow_add b k (n0 + lam), Nat.mul_mod, hper,
        ← Nat.mul_mod, ← pow_add]

/-- Every residue satisfies `r^(n0+lam) ≡ r^n0 (mod q)` (checked on residues). -/
def perCheck (q n0 lam : ℕ) : Bool := (List.range q).all fun r => r ^ (n0 + lam) % q == r ^ n0 % q

theorem perCheck_spec {q n0 lam : ℕ} (hq : 0 < q) (h : perCheck q n0 lam = true) (r : ℕ) :
    r ^ (n0 + lam) % q = r ^ n0 % q := by
  have := List.all_eq_true.1 h (r % q) (List.mem_range.2 (Nat.mod_lt _ hq))
  simp only [beq_iff_eq] at this
  rw [Nat.pow_mod, this, ← Nat.pow_mod]

/-- The finite window check: for every base `2 ≤ b < B` and every reduced exponent
`n < n0 + lam`, `q^R < mDist(bⁿp)^R · b^P`, i.e. `‖bⁿ p/q‖ > b^{−P/R}`. -/
def winCheck (P R q p B n0 lam : ℕ) : Bool :=
  (List.range B).all fun b => decide (b < 2) ||
    (List.range (n0 + lam)).all fun n => decide (q ^ R < mDist q (b ^ n % q * p) ^ R * b ^ P)

theorem goodBelow_of_check (P R q p B n0 lam : ℕ) (hR : R ≠ 0) (hq : 0 < q) (hlam : 0 < lam)
    (hper : perCheck q n0 lam = true) (hw : winCheck P R q p B n0 lam = true) :
    GoodBelow ((P : ℝ) / R) B ((p : ℝ) / q) := by
  intro b hb2 hb n
  obtain ⟨n', hn', hm⟩ := pow_mod_red_gen q n0 lam hlam (perCheck_spec hq hper) b n
  have hc := List.all_eq_true.1 hw b (List.mem_range.2 hb)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with hc | hc
  · omega
  have hc := List.all_eq_true.1 hc n' (List.mem_range.2 hn')
  simp only [decide_eq_true_eq] at hc
  have hmeq : mDist q (b ^ n' % q * p) = mDist q (b ^ n * p) := by
    unfold mDist; rw [← hm, Nat.mod_mul_mod]
  rw [hmeq] at hc
  have hx := dnear_ge_mDist q (b ^ n * p) hq
  have e : (b : ℝ) ^ n * ((p : ℝ) / q) = ((b ^ n * p : ℕ) : ℝ) / q := by push_cast; ring
  rw [e]
  refine lt_of_lt_of_le ?_ hx
  generalize mDist q (b ^ n * p) = M at hc hx ⊢
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hc' : (q : ℝ) ^ R < (M : ℝ) ^ R * (b : ℝ) ^ P := by exact_mod_cast hc
  have := rpow_lt_of_pow P R hR b (by omega) ((M : ℝ) / q) (by positivity) (by
      rw [div_pow, div_mul_eq_mul_div, lt_div_iff₀ (by positivity), one_mul]
      exact hc')
  rw [← neg_div]; exact this


/-- `Q_L = ∏_{(p − 1) ∣ L} p`: every unit mod `Q_L` has order dividing `L`. -/
def carmichaelQ (L : ℕ) : ℕ := ∏ d ∈ L.divisors.filter (fun d => (d + 1).Prime), (d + 1)

/-- The Carmichael moduli are small: `Q_L ≤ (L + 1)^{τ(L)}`, so `log Q_L ≤ τ(L)·log(L + 1) = L^{o(1)}`.
This is the rigorous half of `CarmichaelChainCollapse`: the orbit lengths of the bases grow like
`L`, the modulus only like `exp(L^{o(1)})`. -/
theorem carmichaelQ_le (L : ℕ) : carmichaelQ L ≤ (L + 1) ^ L.divisors.card := by
  unfold carmichaelQ
  calc _ ≤ (L + 1) ^ (L.divisors.filter (fun d => (d + 1).Prime)).card := by
        apply Finset.prod_le_pow_card
        intro d hd
        have := Nat.divisor_le (Finset.mem_filter.1 hd).1
        omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (Finset.card_filter_le _ _)

theorem carmichaelQ_12 : carmichaelQ 12 = 2730 := by decide +kernel

/-- Level-1 anchor: `529/2730` is self-good at `c = 4` (checked by `goodBelow_of_check`). -/
theorem goodBelow_529_2730 : GoodBelow 4 2730 (529 / 2730) := by
  have := goodBelow_of_check 4 1 2730 529 2730 1 12 (by norm_num) (by norm_num) (by norm_num)
    (by native_decide) (by native_decide)
  norm_num at this; exact this

/-- One tower step: `y = 529/2730 + 3/703 = 380077/1919190` (`Q_36 = 2730·19·37`) is self-good at
`c = 4`.  Found by `scripts/cstar_models/tower_local.py 4 12 36 400` (local density near
`529/2730` is about the global one, `≈ 0.3`–`3%` per numerator; no shadowing boost). -/
theorem per_1919190 : perCheck 1919190 1 36 = true := by native_decide
theorem win_tower_step : winCheck 4 1 1919190 380077 1919190 1 36 = true := by native_decide

set_option maxHeartbeats 1000000 in
theorem goodBelow_tower_step : GoodBelow 4 1919190 (380077 / 1919190) := by
  have := goodBelow_of_check 4 1 1919190 380077 1919190 1 36 (by norm_num) (by norm_num)
    (by norm_num) per_1919190 win_tower_step
  norm_num at this; exact this

/-- **Open conjecture (believed 85%): Carmichael chains collapse at `c = 4`.**  Only finitely many
Carmichael moduli `Q_L` carry a self-good numerator at `c = 4`.

Evidence (`scripts/cstar_models/tower_model.py`, `tower_local.py`, 2026-10-08).  A numerator `p` is
killed by base `b` iff its orbit `p·⟨b⟩` (length `ord_{Q_L}(b)`, typically `≍ L`) meets a window of
relative width `2b^{−4}`.  The independent-coset model predicts density `∏_b (1 − 2b^{−4})^{ord(b)}`;
the measured density is close to its square root (orbits are closed under `x ↦ −x` and the windows
are symmetric, which halves the independent events): `L = 36, 72, 120, 144` give measured
`2.5e-2, 1.8e-2, 6.7e-4, 2.7e-3` against model `2.3e-3, 1.9e-3, 7.3e-6, 5.4e-7`.  Then the expected
count is `Q_L · exp(−κ L)` with `κ ≈ 0.04`, while `log Q_L ≤ τ(L) log(L+1) = L^{o(1)}`
(`carmichaelQ_le`), so it tends to `0`.  The square-root model puts the crossover near `L ≈ 10³`;
`0/20000` were found at `L = 240, …, 1440` (no control there: too few samples to see the
predicted densities).  The same count applies to `GoodBelow 4 B` for any fixed `B ≥ 4`, and to
every finite `c` (only `κ` shrinks), so the chain alone cannot prove any upper bound on `c⋆`.

Implication: a proof of `rationalTower_four` must use denominators that are not Carmichael moduli
of growing `L`, i.e. moduli `q` with `Σ_b 2b^{−4} ord_q(b) ≲ log q` (`SmallOrderModuli`). -/
def CarmichaelChainCollapse : Prop :=
  ∃ N₀ : ℕ, ∀ L p : ℕ, N₀ ≤ carmichaelQ L →
    ¬ GoodBelow 4 (carmichaelQ L) ((p : ℝ) / carmichaelQ L)

/-- **Reopen condition (believed false, 85%).**  Infinitely many moduli on which bases `2` and `3`
both have order `O(log q)`: what a rational tower needs if the coset model is right (each base
costs a factor `exp(−κ_b ord_q(b))` in the count of good numerators, and `q` numerators are
available).  Expected false by the Corvaja–Zannier gcd bound for `S`-units (`gcd(u − 1, v − 1) ≤
max(|u|, |v|)^ε` for multiplicatively independent `u = 2^m`, `v = 3^n`, outside a finite set;
transcription not yet checked against the source). -/
def SmallOrderModuli : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, ∃ q ≥ N, Nat.Coprime 6 q ∧
    (orderOf (2 : ZMod q) : ℝ) ≤ C * Real.log q ∧ (orderOf (3 : ZMod q) : ℝ) ≤ C * Real.log q

/-- **Stretch node.**  Believed 25%.  A rational tower at exponent `3`.  Host density at
`c = 3` is `0/3000` at `Q_36`, `Q_60` and `Q_72`, so it needs structured numerators. -/
def RationalTowerThree : Prop := RationalTower 3

end NormalNumbers.UniformBadThreshold
