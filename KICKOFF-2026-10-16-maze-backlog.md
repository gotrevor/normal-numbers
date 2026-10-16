# Kickoff 2026-10-16 (queued): Maze backlog from the disjunction day

Launch after `proof/stoneham-sums-normal` merges (that run may touch `Maze.lean`; one writer).
Source: the joint-orbit report (`tmp/joint-bc-orbits/REPORT.md` §3, copied into
`docs/joint-bc-orbits-2026-10-16.md` as the lap's first act so the rows have a tracked pointer).

## 1. Closed routes still prose-only (each gets a Lean witness + Maze row + `MazeAudit` link)

- **R1** factor-map entropy seed for a BBP pair: `.restatement`.  Witness: a Lean lemma that a
  nonzero rational combination of two base-b BBP-type series is again BBP-type (same `bcOrbit`
  shape), so the seed needs a normal BBP constant (a HypA instance).  REOPEN IF a BBP constant is
  proved normal or of positive entropy.
- **R2** Stoneham sub-series pointing (ln 2 = α₂,₃ + R₃): `.vacuous`.  Witness: report T-D, the
  universal-in-x disagreement bound, or a frozen Prop of it if the borrow lemma balloons.
- **R4** Diophantine input for a disjunctive channel: `.refuted`.  Witness: the {0,1}-digit base-10
  Cantor pair has no disjunctive rational channel (10ⁿ(ax+cy) mod 1 ∈ aC + cC, dim ≤ 0.602); link
  the existing `exists_pair_exponentTwo_qSpan_not_normal` for the exponent-2 leg.
- **R6** joint orbit containing ln 2: `.wall`.  Witness: joint normality ⇒ each coordinate normal
  (a short Weyl lemma).  REOPEN IF ln 2 gets ε > 0 from any source.

## 2. Positive-frequency C2 (new frozen node + its universal refutation)

```lean
/-- Some multiplier in `S` puts every base-`g` digit at positive lower density. -/
def IsDensityProductBlock (g : ℕ) (S : Finset ℕ) (X : ℝ) : Prop :=
  ∃ m ∈ S, ∀ d < g, 0 < Filter.liminf (fun n : ℕ =>
    (countOccurrences [d] ((List.range n).map (digitOf g (Int.fract ((m : ℝ) * X)))) : ℝ) / n)
    Filter.atTop

/-- Universal version fails: a Liouville-sparse ternary `X` has every multiple mostly `0`s. -/
theorem not_forall_isDensityProductBlock (S : Finset ℕ) :
    ∃ X : ℝ, Irrational X ∧ ¬ IsDensityProductBlock 3 S X
```

Use `Mahler.bgLiouville 3 0 1` as the witness (as in `exists_counterexample_on_line`).  Then a
`.wall` Maze row "positive-frequency product block, universal": REOPEN IF a restricted class
(irrationality exponent 2, positive digit entropy, BBP-type) is proposed with a mechanism.

## 3. Bailey–Borwein boundary witnesses (refereed 2026-10-16, ACCEPT)

Source: `papers/2026-10-16-bailey-borwein-full-answer.md` (L1, L2), same template as
`StonehamSums.lean` (integer blocks ⇒ zero windows ⇒ not simply normal).  New file
`StonehamSumsBoundary.lean`.  Ratified statements:

```lean
/-- (L1) For every prime `p ∤ b`: `α_{b,p} − (p+1)·α_{b,p²}` is a sum of integer blocks
`N_j = (b^{(p−1)p^j} − 1)/p^j` (odd `j`) with base-`b` zeros on digits `p^{j+1}+1 .. p^{j+2}`. -/
theorem not_isSimplyNormal_stoneham_sub_succ_mul (b p : ℕ) (hb : 2 ≤ b) (hp : p.Prime)
    (hpb : ¬ p ∣ b) :
    ¬ IsSimplyNormal b (stonehamAlpha b p - (p + 1) * stonehamAlpha b (p ^ 2))

/-- (L2) Three pairwise jointly normal constants whose combination is not: blocks
`M_k = Φ₆(3^{7^k})/7^k`, zeros on `(3·7^k, 7^{k+1}]`. -/
theorem not_isSimplyNormal_three_seven_triple :
    ¬ IsSimplyNormal 3 (stonehamAlpha 3 7 - stonehamAlpha 9 7 + stonehamAlpha 27 7)
```

Then kernel Maze rows: "joint normality is pairwise" refuted (L2 is the triple witness), and
"same-c combinations are normal" falseAsStated (L1).

## Done when

All new rows link declarations, `#maze_audit` counts updated, build green, new theorems axiom-clean.
