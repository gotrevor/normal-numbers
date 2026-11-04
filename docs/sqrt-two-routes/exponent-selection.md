# Exponent selection: discovery-lap outcome

**No usable exponent-selection construction emerged from the two tested mechanisms.**  This lap targeted the missing step in [construction.md](construction.md), rather than improving coefficient bounds or collecting more digits.  All retained findings have Lean statements in `SqrtTwoRoutes/ExponentOrder.lean`, `ExponentLift.lean`, and `ExponentSelection.lean`.

The two selector rows are separate from the still-open general Pell route.  Apply [MAZE.md](../../MAZE.md) when reusing these ideas.  Namespace for the declarations below: `NormalNumbers.SqrtTwoRoutes`.

## 1. Select an exponent from a complete Pell residue period

**Proposed mechanism.**  At an odd Pell index, use the rational orbit `p_n·2^m mod q_n` to find a word, then transfer it to √2 using the Pell approximation.  A complete period may supply the rational word; the question is whether a usable hit occurs early enough.

Set `S=2^L` and `r=p·2^m mod q`.  `pellOrderMarginHit` requires the integer margins

\[
Aq<Sr,\qquad
S2^m<2q\bigl((A+1)q-Sr\bigr).
\]

The proved `pellOrderMarginHit_exponent_bound` gives the necessary horizon

\[
\boxed{S2^m<2q^2.}
\]

**Decisive Pell-specific control.**  `pell_order_full_cycle_misses_margin_control` uses `(p_5,q_5)=(41,29)`.  Multiplication by two has order 28 modulo 29.  At exponent seven its rational orbit point is `28/29`, inside the `111` cylinder.  Nevertheless, **no exponent** satisfies the stated margin test for this cylinder at that denominator.  The horizon forces `m<8`; the remaining cases are checked exactly in Lean.

This is not merely a conservative bound rejecting a correct visit.  `pell_order_q29_rational_hit_is_wrong_word` proves that the true √2 orbit at exponent seven lies in `(0,1/8)`, the `000` cylinder.  The rational prediction and the actual word differ.  The control at `(p_3,q_3)=(7,5)`, `pell_order_positive_controls`, passes the margin test for both one-letter words.

**Transfer status.**  `PellOrderMarginTransfer` is a formally stated, undischarged elementary bridge from the margin test to an actual word hit.  `PellEarlyOrderMarginSupply` is the hard, unproved uniform supply premise across changing odd Pell denominators.  The theorem `pellEarlyOrderSupply_implies_disjunctive` takes **both** premises.  It is not an unconditional disjunctivity proof.

**Disposition.**  The complete-period shortcut fails; the generic version was already retired, and Pell arithmetic does not rescue it in this control.  An independent estimate producing early margin hits across different denominators remains a possible route.  No such estimate or construction was found.  A larger order or another complete-period census alone does not address the missing timing bound.

## 2. Select an exponent by lifting a Pell index modulo powers of two

**Proposed mechanism.**  Impose `S=2^L`, `S | q_n`, and `S | Q`, with `Q=2^m`, hoping to steer the bounded coefficient representation toward a prescribed word.

The lift does have an exact effect.  `pell_index_lift_coeffV_divisible_for_every_numerator` proves `S | v`, and `pell_index_lift_coeffU_congruent_for_every_numerator` proves

\[
u\equiv(-1)^nPq_{n+1}\pmod S.
\]

But these statements hold for **every numerator `P`**.  They do not select its residue or its real signed error.  The separate generic divisibility theorem states explicitly the unit-modulus hypothesis needed when starting from an arbitrary denominator equation rather than the explicit synthesis coefficients.

**Size test.**  `pell_index_lift_size_lower_bound` proves that `n≥2^L` and the balanced condition `q_n²≤2^m` force

\[
2n\le m+2,\qquad 2^{L+1}\le m+2.
\]

For a nonzero coefficient divisible by `2^L`, `pell_index_lift_archimedean_cost` also forces `2^L≤4√Q`.  These are costs, **not an impossibility result**: the goal allows arbitrarily large exponents.

**Exact reachable controls.**  At `n=4,m=8`, the pair `(q_4,q_5)=(12,29)` and coefficients `(u,v)=(2,8)` give a valid `00` certificate with `4 | q_4` and `4 | v`.  The same data rejects `01`.  These are `exponent_lift_00_control`, `exponent_lift_00_values`, and `exponent_lift_neighbor_rejected`.

One might try to finish by freely prescribing a numerator residue.  `lifted_zero_residue_not_near` shows the accuracy cost of that step in the same real system:

\[
\nexists P\in\mathbb Z:\quad 4\mid P\quad\text{and}\quad
|P-256\sqrt2|\le1.
\]

The positive companion `lifted_near_positive_control` verifies that `P=362` is within one unit.  The negative result concerns this fixed exponent and residue; it does not prohibit a different exponent from realizing that residue.  A low residue of the numerator and the subsequent fractional word are distinct constraints, so this control is not presented as a refutation of all word steering by congruences.

**Disposition.**  Park the index-lift selector until it has a word-dependent constraint that survives the real accuracy requirement.  `PellLiftedWordSupply` records the stronger precise construction, including the lift, scale, and word-certificate conditions.  `pellLiftedWordSupply_implies_disjunctive` proves its implication to the goal.  The supply statement itself is unproved.

## What the lap changes

The complete-period selector now has an exact Pell example predicting the wrong word.  The index-lift selector has a quantified scale cost and a precise explanation of what its congruence does and does not constrain.  Neither supplies exponents for arbitrary words.  These findings do not refute disjunctivity or the general Pell route, and they give no reason to increase the prior subjective assessment of the chance of finishing the proof in the next bounded campaign.

Further work must introduce a relation connecting exponent choice to the signed word window.  Repeating these two selectors without such a relation would repeat their recorded gap.
