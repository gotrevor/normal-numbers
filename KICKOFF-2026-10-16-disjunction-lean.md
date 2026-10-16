# Kickoff 2026-10-16: discharge three disjunction-shelf sorries

Branch `proof/disjunction-lean`, worktree `~/src/nn-disjunction`.  The attended session ratified
the three statements below as they stand; prove them **without changing any statement**.

## Objectives, in order

1. **`IndependenceRelative.ternary_line`** (`src/NormalNumbers/IndependenceRelative.lean`).
   The English proof is in its docstring: assume all three avoidances past some position, track
   the borrow sequence `c ∈ {−1, 0}` of `Y − X` from deep to shallow, show a `0` borrow propagates
   upward, and conclude `Y − 2X` is rational in both cases.  Mind the digit convention: `DigitIO`
   reads the canonical expansion of the fractional part, so negative `Y − X` and dyadic-style
   double expansions need a lemma relating digits of `frac (Y − X)` to the borrow arithmetic.
   When this lands, `pi_e_disjunction` becomes sorry-free for free.
2. **`IndependenceRelative.exists_counterexample_on_line`**: `X = Σ 3^{-k!}`, `Y = 2X`.
3. **`QSpan.exists_pair_qSpan_not_normal`** (`src/NormalNumbers/QSpanNormal.lean`).  The English
   construction is in its docstring (supersparse disjoint supports `(2k)!`, `(2k+1)!`; between
   support points every span element's digits are those of a rational of denominator `q`, hence
   periodic with period `≤ q`; a block outside the periodic ones has frequency → 0 along the
   support times).  Reuse the repo's existing machinery: grep for factorial-support / Liouville
   constructions (`Barriers`, `CantorLiouville`, `CantorRepetition`) and `isNormal_rat_mul_add`
   before writing new digit lemmas.

**Out of scope:** `not_isRelativeBlock_small` (65%, may be false), `qSpanNormal_sqrt_two_sqrt_three`
(open problem), `span_dimension_budget`, `exists_pair_exponentTwo_qSpan_not_normal`.  Leave them
sorried.

## If a statement is false

Do not weaken it.  Prove the negation in a new theorem next to it (a counterexample is a result),
leave the original sorried with a docstring note, and `box stuck` with the witness.

## After objective 3: Maze promotion

- `Maze.lean` row "pair-universal mechanism for a normal element of a Q-span": tier `.frozen` →
  `.kernel`, add an `alias hall_… := QSpan.exists_pair_qSpan_not_normal` in §2, and drop
  "(sorry, 90%)" from its evidence string.
- `Barriers.lean` `liouville_pair_qSpan`: `.frozen` → `.proved` if that constructor's signature
  allows it (mirror `perStage_dead_not_enough`).
- `IndependenceRelative` row (dated 2026-10-05): drop nothing, but `ternary_line` is now proved,
  so note it in the evidence string.
- Update `#guard_msgs` counts in `MazeAudit.lean` if they move.

## Part 2 (added 2026-10-16, after Part 1): Stoneham sums

Source: the joint-orbit research report, `tmp/joint-bc-orbits/REPORT.md` in the **main** checkout
`~/src/normal-numbers` (read-only to you; copy what you need).  New file
`src/NormalNumbers/StonehamSums.lean`, imported from `NormalNumbers.lean`.  Ratified statements
(state them exactly; `stoneham23` is in `Stoneham.lean`):

```lean
/-- The Stoneham constant `α_{B,c} = Σ_{m≥1} 1/(c^m · B^(c^m))`. -/
noncomputable def stonehamAlpha (B c : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / ((c : ℝ) ^ (n + 1) * (B : ℝ) ^ (c ^ (n + 1)))

theorem stonehamAlpha_two_three : stonehamAlpha 2 3 = stoneham23

/-- `α₂,₃ + α₄,₃ = Σ_k ((2^(3^k)+1)/3^k)·4^(−3^k)` is a sum of disjoint integer blocks
(`3^(k+1) ∣ 2^(3^k) + 1`, lifting the exponent), so its binary digits vanish on
`[2·3^k, 3^(k+1))` (0-indexed `digitOf`). -/
theorem digitOf_stoneham_sum_eq_zero (k i : ℕ) (h₁ : 2 * 3 ^ k ≤ i) (h₂ : i < 3 ^ (k + 1)) :
    digitOf 2 (Int.fract (stonehamAlpha 2 3 + stonehamAlpha 4 3)) i = 0

/-- Hence the zero frequency is pushed toward `2/3` at `n = 3^(k+1)`. -/
theorem not_isSimplyNormal_stoneham_sum :
    ¬ IsSimplyNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 4 3)
```

Confidence 95% for the digit window (hand-checked; if an endpoint is off by one, fix the endpoint
and say so in the commit, never weaken the conclusion).  The proof of the corollary: if zeros had
frequency `1/2`, about `3^k` of the first `2·3^k` digits are zero, and the window adds `3^k` more by
`3^(k+1)`, so the frequency there is near `2/3`.

Stretch, in order (skip any that balloons):
1. `isNormal_two_stonehamAlpha_four_three` (α₄,₃ is 4-normal hence 2-normal), generalizing
   `Stoneham.lean` if that is cheap, so the docstring punchline "two 2-normal numbers whose sum is
   not simply normal" is a theorem.
2. Maze rows from the report's §3 (R1–R6), plus the **Rauzy row** (ratified 2026-10-16, do this one
   even if R1–R6 are trimmed).  Rauzy is not yet stated in Lean (only cited in a
   `DeterministicBD.lean` docstring), so in `DeterministicBD.lean`'s `Literature` namespace add the
   cited direction and the vacuity theorem:

   ```lean
   /-- **Rauzy 1976** (one direction): adding a deterministic real to a normal real gives a
   normal real.  Cited, not proved. -/
   def Rauzy1976 (b : ℕ) : Prop :=
     ∀ x y : ℝ, IsNormal b x → IsDeterministic b y → IsNormal b (x + y)

   /-- The Rauzy disjunction holds for **every** `y`, so it says nothing about `π` (or any
   particular constant): `.vacuous`. -/
   theorem rauzy_disjunction_universal (b : ℕ) (hR : Rauzy1976 b) (c : ℝ) (hc : IsNormal b c)
       (y : ℝ) : IsNormal b (c + y) ∨ ¬ IsDeterministic b y
   ```

   Maze row: name "Rauzy disjunction as information about pi", tried "Read 'pi + Champernowne is
   normal, or pi's digits are not deterministic' as a fact about pi", `.vacuous`, `.kernel`,
   mechanism "The disjunction holds for every real y (rauzy_disjunction_universal), so it carries
   no information about pi; the only informative branch, pi + Champernowne NOT normal, is believed
   false.  REOPEN IF: a proof that some explicit c + pi is non-normal", evidence
   "DeterministicBD.lean: rauzy_disjunction_universal, Literature.BergelsonDownarowicz.Rauzy1976",
   date 2026-10-16.  Link it in `MazeAudit.lean`.

   For R1–R6: each row needs a `MazeAudit` link per the Maze rules; R3 and R5 link
   `not_isSimplyNormal_stoneham_sum`.
3. T-C from the report (HypA ⇒ every nonzero rational combination of `ln 2`, `ln 3` is 4-normal)
   only if the repo already has a generic BBP ⇒ `bcOrbit` bridge.

## Done when

Part 1: all three named theorems print only `[propext, Classical.choice, Quot.sound]` under
`#print axioms` (use `lean-axiom-gate` if present in the box), `lake build` is green, and the Maze
edits compile.  Part 2: `not_isSimplyNormal_stoneham_sum` axiom-clean too.  Then `box done`.
