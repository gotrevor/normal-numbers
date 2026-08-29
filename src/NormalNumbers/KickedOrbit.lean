/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwoRuns

/-!
# The abstract kicked-orbit dichotomy (R2, the general lemma)

Companion to `docs/alien-review-2026-08-29.md` (transmission 2, move R2) and
`docs/lit-sweep-2026-08-29.md`.  The τ-floor/sliver mechanism proved for
`ln 2` (`LnTwoRuns.lean`) used nothing about `ln 2` except: the true orbit
is the surrogate perturbed by a tail trapped in `[lo, hi]` with `lo > 0`.
This file extracts the mechanism at that generality, for **any base `b` and
any BBP-type decomposition `x = s + tail`**:

* `orbit_eq_fract_add_tail`: the generic bracket
  `orbit b x n = fract (fract (bⁿ·s) + bⁿ·(x − s))`;
* `blockNatVal_replicate_max`: the max-digit run value `b^k − 1`
  (generalizing the base-2 `blockNatVal_replicate_one`);
* `occursAt_replicate_zero_iff'` / `occursAt_replicate_max_iff`: base-`b`
  run dictionary — a run of `k` zeros (max digits `b−1`) at position `n` is
  an orbit visit to `[0, b⁻ᵏ)` (`[1 − b⁻ᵏ, 1)`);
* **the dichotomy core** `top_sliver_of_fract_small` /
  `top_sliver_of_fract_large`: one-position real lemmas — if the perturbed
  point lands within `ε < lo` of the wrap and the perturbation is trapped
  in `[lo, hi]`, the base point sits in the top sliver;
* **the packaged dichotomy** `top_sliver_of_zeroRun_tail` /
  `top_sliver_of_maxRun_tail`: a digit run deeper than the tail floor
  forces the surrogate `fract (bⁿ·s)` into the top sliver.

🚨 **Lagarias guardrail** (sweep doc): a magnitude-only kick/tail floor can
never yield an equidistribution-or-finite conclusion — his adversarial
family `θ = Σ ε_n b^{−n}` survives any `ε_n ≥ c/n` floor.  Every conclusion
here is deliberately at the **forcing level** (run ⟹ sliver ride), which is
what survives that acid.

Instances: `ln 2` (base 2, kick `1/(n+1)`; the frozen statements stay in
`LnTwoRuns.lean` — an `example` below re-derives one from the abstract core
as a sanity anchor) and π (base 16, BBP kick, `PiBBP.lean`).  Sweep verdict
2026-08-29: kick-floor-as-resource and the run-forcing direction NOT FOUND
in the literature; Bailey–Borwein 2012 (Stoneham nonnormality) proves the
converse (easy, bottom-sliver) direction for an engineered constant and is
the compare-against citation.
-/

namespace NormalNumbers

/-! ### The dichotomy core: one-position real lemmas -/

/-- **Zero-side dichotomy core.**  If the perturbed point `u + τ` has
fractional part below `ε`, and the perturbation is trapped in
`[lo, hi] ⊆ (ε, 1]`, then `u` sits in the top sliver `[1 − hi, 1)`: the
no-wraparound branch is impossible because there `fract (u + τ) ≥ τ ≥ lo > ε`. -/
theorem top_sliver_of_fract_small {u τ lo hi ε : ℝ}
    (hu0 : 0 ≤ u) (hlo : lo ≤ τ) (hτhi : τ ≤ hi)
    (hε : ε < lo) (hfr : Int.fract (u + τ) < ε) :
    1 - hi ≤ u := by
  have h0 : (0 : ℝ) ≤ Int.fract (u + τ) := Int.fract_nonneg _
  have hτ0 : 0 ≤ τ := by linarith
  rcases lt_or_ge (u + τ) 1 with hlt | hge
  · exfalso
    rw [Int.fract_eq_self.mpr ⟨by linarith, hlt⟩] at hfr
    linarith
  · linarith

/-- **Max-side dichotomy core.**  If the perturbed point `u + τ` has
fractional part within `ε` of `1`, with the perturbation trapped in
`[lo, hi]`, `ε < lo`, and `hi, ε ≤ 1/2`, then `u ∈ [1 − hi − ε, 1)`: the
wraparound branch would force `u ≥ 2 − ε − τ ≥ 1`. -/
theorem top_sliver_of_fract_large {u τ lo hi ε : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hlo : lo ≤ τ) (hτhi : τ ≤ hi) (hhi : hi ≤ 1 / 2)
    (hε : ε < lo)
    (hfr : 1 - ε ≤ Int.fract (u + τ)) :
    1 - hi - ε ≤ u := by
  have h1 : Int.fract (u + τ) < 1 := Int.fract_lt_one _
  have hε0 : 0 < ε := by linarith
  have hτ0 : 0 ≤ τ := by linarith
  rcases lt_or_ge (u + τ) 1 with hlt | hge
  · rw [Int.fract_eq_self.mpr ⟨by linarith, hlt⟩] at hfr
    linarith
  · exfalso
    have hfr2 : Int.fract (u + τ) = u + τ - 1 := by
      have h2 : u + τ - 1 + ((1 : ℤ) : ℝ) = u + τ := by push_cast; ring
      rw [← h2, Int.fract_add_intCast,
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
      push_cast
      ring
    rw [hfr2] at hfr
    linarith

/-! ### The generic bracket -/

private lemma fract_fract_add' (y d : ℝ) :
    Int.fract (Int.fract y + d) = Int.fract (y + d) := by
  have h : Int.fract y + d = y + d - ((⌊y⌋ : ℤ) : ℝ) := by
    have h2 := Int.floor_add_fract y
    linarith
  rw [h, Int.fract_sub_intCast]

/-- **Generic bracket**: for any decomposition `x = s + (x − s)`, the true
orbit is the surrogate `fract (bⁿ·s)` perturbed by the scaled tail. -/
theorem orbit_eq_fract_add_tail (b : ℕ) (x s : ℝ) (n : ℕ) :
    orbit b x n
      = Int.fract (Int.fract ((b : ℝ) ^ n * s) + (b : ℝ) ^ n * (x - s)) := by
  rw [orbit, fract_fract_add']
  congr 1
  ring

/-! ### Base-`b` run dictionary -/

theorem blockNatVal_replicate_max (b k : ℕ) (hb : 1 ≤ b) :
    blockNatVal b (List.replicate k (b - 1)) = b ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, blockNatVal_cons, ih, List.length_replicate, pow_succ]
      have h1 : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
      have h3 : (b - 1) * b ^ k = b * b ^ k - 1 * b ^ k := Nat.sub_mul b 1 (b ^ k)
      have h5 : b ^ k ≤ b * b ^ k := Nat.le_mul_of_pos_left _ (by omega)
      rw [h3, one_mul, Nat.mul_comm (b ^ k) b]
      generalize hM : b * b ^ k = M at h5 ⊢
      generalize b ^ k = A at h1 h5 ⊢
      omega

/-- Base-`b` zero-run dictionary: a run of `k` zeros at position `n` is an
orbit visit to `[0, b⁻ᵏ)`. -/
theorem occursAt_replicate_zero_iff' (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (n k : ℕ) :
    OccursAt b x (List.replicate k 0) n ↔
      orbit b x n ∈ Set.Ico (0 : ℝ) (1 / (b : ℝ) ^ k) := by
  rw [occursAt_iff_orbit_mem b hb x _
      (fun e he => by rw [List.eq_of_mem_replicate he]; omega) n,
    blockNatVal_replicate_zero, List.length_replicate]
  norm_num

/-- Base-`b` max-digit run dictionary: a run of `k` copies of the top digit
`b − 1` at position `n` is an orbit visit to `[1 − b⁻ᵏ, 1)`. -/
theorem occursAt_replicate_max_iff (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (n k : ℕ) :
    OccursAt b x (List.replicate k (b - 1)) n ↔
      orbit b x n ∈ Set.Ico (1 - 1 / (b : ℝ) ^ k) 1 := by
  rw [occursAt_iff_orbit_mem b hb x _
      (fun e he => by rw [List.eq_of_mem_replicate he]; omega) n,
    blockNatVal_replicate_max b k (by omega), List.length_replicate]
  have h1 : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
  have hcast : ((b ^ k - 1 : ℕ) : ℝ) = (b : ℝ) ^ k - 1 := by
    push_cast [h1]
    ring
  have hbpos : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  rw [hcast]
  have e1 : ((b : ℝ) ^ k - 1) / (b : ℝ) ^ k = 1 - 1 / (b : ℝ) ^ k := by
    field_simp
  have e2 : (((b : ℝ) ^ k - 1) + 1) / (b : ℝ) ^ k = 1 := by
    rw [sub_add_cancel]
    exact div_self hbpos.ne'
  rw [e1, e2]

/-! ### The packaged dichotomy -/

/-- **Abstract zero-run dichotomy**: if `x = s + tail` with the scaled tail
`bⁿ·(x − s)` trapped in `[lo, hi] ⊆ (b⁻ᵏ, 1]`, then a run of `k` zeros at
position `n` in base `b` forces the surrogate `fract (bⁿ·s)` into the top
sliver `[1 − hi, 1)`. -/
theorem top_sliver_of_zeroRun_tail {b : ℕ} (hb : 2 ≤ b) {x s : ℝ} {n k : ℕ}
    {lo hi : ℝ} (hlo : lo ≤ (b : ℝ) ^ n * (x - s))
    (hhi : (b : ℝ) ^ n * (x - s) ≤ hi)
    (hε : (1 : ℝ) / (b : ℝ) ^ k < lo)
    (h : OccursAt b x (List.replicate k 0) n) :
    1 - hi ≤ Int.fract ((b : ℝ) ^ n * s) := by
  rw [occursAt_replicate_zero_iff' b hb, orbit_eq_fract_add_tail b x s n] at h
  exact top_sliver_of_fract_small (Int.fract_nonneg _) hlo hhi hε h.2

/-- **Abstract max-run dichotomy**: same decomposition, `hi, b⁻ᵏ ≤ 1/2` —
a run of `k` top digits `b − 1` at position `n` forces the surrogate into
`[1 − hi − b⁻ᵏ, 1)`. -/
theorem top_sliver_of_maxRun_tail {b : ℕ} (hb : 2 ≤ b) {x s : ℝ} {n k : ℕ}
    {lo hi : ℝ} (hlo : lo ≤ (b : ℝ) ^ n * (x - s))
    (hhi : (b : ℝ) ^ n * (x - s) ≤ hi) (hhi2 : hi ≤ 1 / 2)
    (hε : (1 : ℝ) / (b : ℝ) ^ k < lo)
    (h : OccursAt b x (List.replicate k (b - 1)) n) :
    1 - hi - 1 / (b : ℝ) ^ k ≤ Int.fract ((b : ℝ) ^ n * s) := by
  rw [occursAt_replicate_max_iff b hb, orbit_eq_fract_add_tail b x s n] at h
  exact top_sliver_of_fract_large (Int.fract_nonneg _) (Int.fract_lt_one _)
    hlo hhi hhi2 hε h.1

/-! ### The summed-kick machine (the classification node)

The packaged dichotomy above still wants the tail bracket `[lo, hi]` fed by
hand, per constant.  This section closes that gap: for any constant given
by a **kicked series** `x = Σ_{k≥1} r(k)/bᵏ` (Bailey–Crandall Def 4.1 is
the case `r = p/q`, `p, q` polynomials), a per-position floor/cap on the
kick sequence alone produces the bracket — `bⁿ·tail ∈ [L/b, A/(b−1)]` from
`r(n+1) ≥ L` and `0 ≤ r(m) ≤ A` for `m > n` — and hence both sliver
theorems.  Classifying a Def-4.1 constant reduces to (i) its series
identity (the CITED-class node) and (ii) elementary sign/size bounds on
`p/q`.  With `r(m) = 1/m`, `b = 2` the machine reproduces the ln-2
constants exactly (`example` below). -/

/-- Partial sums of the kicked series `Σ_{k≥1} r(k)/bᵏ`: the surrogate
generator for the constant `x` it converges to. -/
noncomputable def kickedPartial (b : ℕ) (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, r (k + 1) / (b : ℝ) ^ (k + 1)

/-- **Kicked tail floor**: kicks past `n` nonnegative and the first
omitted kick at least `L` put the scaled tail at or above `L/b`. -/
theorem kicked_tail_ge {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ} {x L : ℝ} (n : ℕ)
    (hsum : HasSum (fun k : ℕ => r (k + 1) / (b : ℝ) ^ (k + 1)) x)
    (hpos : ∀ m, n + 1 ≤ m → 0 ≤ r m)
    (hfloor : L ≤ r (n + 1)) :
    L / b ≤ (b : ℝ) ^ n * (x - kickedPartial b r n) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  set f : ℕ → ℝ := fun k => r (k + 1) / (b : ℝ) ^ (k + 1) with hf
  have hsummable : Summable f := hsum.summable
  have key := hsummable.sum_add_tsum_nat_add n
  have htail : x - kickedPartial b r n = ∑' i : ℕ, f (i + n) := by
    have hx : x = ∑' i, f i := hsum.tsum_eq.symm
    rw [kickedPartial, hx, ← key]
    ring
  have hs1 : Summable fun i : ℕ => f (i + n) := (summable_nat_add_iff n).mpr hsummable
  have hterm : f (0 + n) ≤ ∑' i, f (i + n) := by
    refine hs1.le_tsum 0 (fun i _ => ?_)
    simp only [hf]
    exact div_nonneg (hpos _ (by omega)) (by positivity)
  have hLval : L / (b : ℝ) ^ (n + 1) ≤ f (0 + n) := by
    have hval : f (0 + n) = r (n + 1) / (b : ℝ) ^ (n + 1) := by simp [hf]
    rw [hval]
    exact div_le_div_of_nonneg_right hfloor (by positivity)
  have heq : (b : ℝ) ^ n * (L / (b : ℝ) ^ (n + 1)) = L / b := by
    have hbn : ((b : ℝ) ^ n) ≠ 0 := by positivity
    field_simp
    ring
  rw [htail]
  calc L / b = (b : ℝ) ^ n * (L / (b : ℝ) ^ (n + 1)) := heq.symm
    _ ≤ (b : ℝ) ^ n * f (0 + n) :=
        mul_le_mul_of_nonneg_left hLval (by positivity)
    _ ≤ (b : ℝ) ^ n * ∑' i, f (i + n) :=
        mul_le_mul_of_nonneg_left hterm (by positivity)

/-- **Kicked tail cap**: kicks past `n` trapped in `[0, A]` put the scaled
tail at or below the geometric total `A/(b−1)`. -/
theorem kicked_tail_le {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ} {x A : ℝ} (n : ℕ)
    (hsum : HasSum (fun k : ℕ => r (k + 1) / (b : ℝ) ^ (k + 1)) x)
    (hpos : ∀ m, n + 1 ≤ m → 0 ≤ r m)
    (hcap : ∀ m, n + 1 ≤ m → r m ≤ A) :
    (b : ℝ) ^ n * (x - kickedPartial b r n) ≤ A / ((b : ℝ) - 1) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hA0 : 0 ≤ A := le_trans (hpos (n + 1) le_rfl) (hcap (n + 1) le_rfl)
  have hinv0 : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
  have hinv1 : (b : ℝ)⁻¹ < 1 := by
    rw [← one_div, div_lt_one hb0]
    linarith
  set f : ℕ → ℝ := fun k => r (k + 1) / (b : ℝ) ^ (k + 1) with hf
  have hsummable : Summable f := hsum.summable
  have key := hsummable.sum_add_tsum_nat_add n
  have htail : x - kickedPartial b r n = ∑' i : ℕ, f (i + n) := by
    have hx : x = ∑' i, f i := hsum.tsum_eq.symm
    rw [kickedPartial, hx, ← key]
    ring
  have hs1 : Summable fun i : ℕ => f (i + n) := (summable_nat_add_iff n).mpr hsummable
  -- per-term comparison against the geometric series `(A·b⁻¹)·(b⁻¹)^i`
  have hle : ∀ i : ℕ, (b : ℝ) ^ n * f (i + n) ≤ (A * (b : ℝ)⁻¹) * ((b : ℝ)⁻¹) ^ i := by
    intro i
    have hsplit : (b : ℝ) ^ (i + n + 1) = (b : ℝ) ^ n * (b : ℝ) ^ (i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have heq : (b : ℝ) ^ n * f (i + n) = r (i + n + 1) * ((b : ℝ) ^ (i + 1))⁻¹ := by
      show (b : ℝ) ^ n * (r (i + n + 1) / (b : ℝ) ^ (i + n + 1)) = _
      rw [hsplit]
      have hbn : ((b : ℝ) ^ n) ≠ 0 := by positivity
      have hbi : ((b : ℝ) ^ (i + 1)) ≠ 0 := by positivity
      field_simp
    have hgeq : (A * (b : ℝ)⁻¹) * ((b : ℝ)⁻¹) ^ i = A * ((b : ℝ) ^ (i + 1))⁻¹ := by
      rw [← inv_pow, pow_succ]
      ring
    rw [heq, hgeq]
    exact mul_le_mul_of_nonneg_right (hcap _ (by omega)) (by positivity)
  have hsg : Summable (fun i : ℕ => (A * (b : ℝ)⁻¹) * ((b : ℝ)⁻¹) ^ i) :=
    (summable_geometric_of_lt_one hinv0 hinv1).mul_left _
  have hsf : Summable (fun i : ℕ => (b : ℝ) ^ n * f (i + n)) := hs1.mul_left _
  have hkey : (1 - (b : ℝ)⁻¹) * b = (b : ℝ) - 1 := by
    rw [sub_mul, one_mul, inv_mul_cancel₀ hb0.ne']
  have hfin : (A * (b : ℝ)⁻¹) * (1 - (b : ℝ)⁻¹)⁻¹ = A / ((b : ℝ) - 1) := by
    rw [← hkey, div_eq_mul_inv, mul_inv]
    ring
  have hts2 : (b : ℝ) ^ n * ∑' i, f (i + n)
      ≤ (A * (b : ℝ)⁻¹) * (1 - (b : ℝ)⁻¹)⁻¹ := by
    rw [← tsum_mul_left]
    calc ∑' i, (b : ℝ) ^ n * f (i + n)
        ≤ ∑' i, (A * (b : ℝ)⁻¹) * ((b : ℝ)⁻¹) ^ i := hsf.tsum_le_tsum hle hsg
      _ = (A * (b : ℝ)⁻¹) * ∑' i, ((b : ℝ)⁻¹) ^ i := tsum_mul_left
      _ = (A * (b : ℝ)⁻¹) * (1 - (b : ℝ)⁻¹)⁻¹ := by
          rw [tsum_geometric_of_lt_one hinv0 hinv1]
  rw [htail]
  exact hts2.trans_eq hfin

/-- **The machine, zero-run side**: for a constant `x = Σ_{k≥1} r(k)/bᵏ`
whose kicks past `n` sit in `[0, A]` with first omitted kick `≥ L`, a run
of `k` zeros at position `n` with `b⁻ᵏ < L/b` forces the surrogate
`fract (bⁿ·(partial sum))` into the top sliver `[1 − A/(b−1), 1)`. -/
theorem top_sliver_of_zeroRun_kicked {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ}
    {x A L : ℝ} {n k : ℕ}
    (hsum : HasSum (fun m : ℕ => r (m + 1) / (b : ℝ) ^ (m + 1)) x)
    (hpos : ∀ m, n + 1 ≤ m → 0 ≤ r m)
    (hcap : ∀ m, n + 1 ≤ m → r m ≤ A)
    (hfloor : L ≤ r (n + 1))
    (hε : (1 : ℝ) / (b : ℝ) ^ k < L / b)
    (h : OccursAt b x (List.replicate k 0) n) :
    1 - A / ((b : ℝ) - 1) ≤ Int.fract ((b : ℝ) ^ n * kickedPartial b r n) :=
  top_sliver_of_zeroRun_tail hb (kicked_tail_ge hb n hsum hpos hfloor)
    (kicked_tail_le hb n hsum hpos hcap) hε h

/-- **The machine, max-run side**: same data with the sliver at most half,
for a run of `k` top digits `b − 1`. -/
theorem top_sliver_of_maxRun_kicked {b : ℕ} (hb : 2 ≤ b) {r : ℕ → ℝ}
    {x A L : ℝ} {n k : ℕ}
    (hsum : HasSum (fun m : ℕ => r (m + 1) / (b : ℝ) ^ (m + 1)) x)
    (hpos : ∀ m, n + 1 ≤ m → 0 ≤ r m)
    (hcap : ∀ m, n + 1 ≤ m → r m ≤ A)
    (hfloor : L ≤ r (n + 1))
    (hhalf : A / ((b : ℝ) - 1) ≤ 1 / 2)
    (hε : (1 : ℝ) / (b : ℝ) ^ k < L / b)
    (h : OccursAt b x (List.replicate k (b - 1)) n) :
    1 - A / ((b : ℝ) - 1) - 1 / (b : ℝ) ^ k
      ≤ Int.fract ((b : ℝ) ^ n * kickedPartial b r n) :=
  top_sliver_of_maxRun_tail hb (kicked_tail_ge hb n hsum hpos hfloor)
    (kicked_tail_le hb n hsum hpos hcap) hhalf hε h

/-- The machine reproduces the frozen ln-2 constants **exactly**:
`r(m) = 1/m`, `b = 2` gives floor `L/b = 1/(2(n+1))` and sliver
`A/(b−1) = 1/(n+1)` — the `lnTwoOrbit_top_sliver_of_zeroRun` statement. -/
example {n k : ℕ} (hk : 2 * ((n : ℝ) + 1) < 2 ^ k)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 0) n) :
    1 - 1 / ((n : ℝ) + 1) ≤ lnTwoOrbit n := by
  set r : ℕ → ℝ := fun m => 1 / (m : ℝ) with hr
  have hsum : HasSum (fun m : ℕ => r (m + 1) / ((2 : ℕ) : ℝ) ^ (m + 1)) (Real.log 2) := by
    have hfun : (fun m : ℕ => r (m + 1) / ((2 : ℕ) : ℝ) ^ (m + 1))
        = fun k : ℕ => 1 / ((k + 1 : ℝ) * 2 ^ (k + 1)) := by
      funext m
      simp only [hr]
      push_cast
      rw [div_div]
    rw [hfun]
    exact hasSum_lnTwoSeries
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcore := top_sliver_of_zeroRun_kicked (b := 2) le_rfl (x := Real.log 2)
    (A := 1 / ((n : ℝ) + 1)) (L := 1 / ((n : ℝ) + 1)) (n := n) (k := k) hsum
    (fun m _ => by simp only [hr]; positivity)
    (fun m hm => by
      simp only [hr]
      apply one_div_le_one_div_of_le hn1
      have : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
      linarith)
    (le_of_eq (by simp only [hr]; push_cast; ring))
    (by
      push_cast
      rw [div_div]
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith [hk]))
    h
  have hpart : kickedPartial 2 r n = lnTwoPartial n := by
    unfold kickedPartial lnTwoPartial
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hr]
    push_cast
    rw [div_div]
  rw [hpart] at hcore
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hcast] at hcore
  rw [lnTwoOrbit_eq_fract]
  calc 1 - 1 / ((n : ℝ) + 1)
      = 1 - (1 / ((n : ℝ) + 1)) / ((2 : ℝ) - 1) := by norm_num
    _ ≤ Int.fract ((2 : ℝ) ^ n * lnTwoPartial n) := hcore

/-! ### Sanity anchor: the ln-2 instance -/

/-! ### Sanity anchor: the ln-2 instance -/

/-- The frozen `lnTwoOrbit_top_sliver_of_zeroRun` conclusion re-derived from
the abstract core, confirming the abstraction subsumes the ln-2 case
(`lo = 1/(2(n+1))`, `hi = 1/(n+1)`). -/
example {n k : ℕ} (hk : 2 * ((n : ℝ) + 1) < 2 ^ k)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 0) n) :
    1 - 1 / ((n : ℝ) + 1) ≤ lnTwoOrbit n := by
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  have htail : ((2 : ℕ) : ℝ) ^ n * (Real.log 2 - lnTwoPartial n)
      = 2 ^ n * lnTwoTail n := by
    rw [hcast, lnTwoTail]
  have hlo : 1 / (2 * ((n : ℝ) + 1)) ≤ ((2 : ℕ) : ℝ) ^ n * (Real.log 2 - lnTwoPartial n) := by
    rw [htail]; exact lnTwoTail_ge n
  have hhi : ((2 : ℕ) : ℝ) ^ n * (Real.log 2 - lnTwoPartial n) ≤ 1 / ((n : ℝ) + 1) := by
    rw [htail]; exact lnTwoTail_le n
  have hε : (1 : ℝ) / ((2 : ℕ) : ℝ) ^ k < 1 / (2 * ((n : ℝ) + 1)) := by
    rw [hcast]
    exact one_div_lt_one_div_of_lt (by positivity) hk
  have hcore := top_sliver_of_zeroRun_tail (le_refl 2) hlo hhi hε h
  rw [lnTwoOrbit_eq_fract]
  rwa [hcast] at hcore

end NormalNumbers
