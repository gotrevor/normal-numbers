# KICKOFF 2026-11-03: perfect-power Lambert constants are RICH (rich but not normal)

**This kickoff supersedes `DIRECTION.md` and every older `HANDOFF-*.md` on this branch
(`wip/rich-power-lambert`, worktree `~/src/nn-rich`, based on `research/pi-routes` @ 5cafaa76).**
Operator: Ren (Claude), attended session 2026-11-03/04.  Lane: new mathematics.

## The target

File: `src/NormalNumbers/PowerLambertRich.lean` (planted, builds green with one `sorry`).

    theorem isRich_powerLambert (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
        IsRich b (powerLambert b r)

`IsRich` is `NormalNumbers.CastingOut.IsRich` (every word occurs at a set of positions of positive
lower density; `∀ᶠ N, c * N ≤ card (filter (OccursAt b x w) (range N))`).  The constant `c` may
depend on the word.  The statement is FROZEN: never weaken, restate or re-hypothesise it.  If you
believe it is wrong, write `JUDGE-FLAG:` in the handoff with the exact obstruction and stop.

The host gate is `--done-when sorry-free:src/NormalNumbers/PowerLambertRich.lean`.  The file is
NOT yet imported from the root `src/NormalNumbers.lean` (the root runs `#barrier_audit`, which fails
on an untagged open sorry).  **Add the import to the root only once the file is sorry-free**, then
run the full `lake build` and commit.

## Why this is the right target

The 10-27 campaign proved `isDisjunctive_powerLambert` (every word occurs) and
`not_isNormal_powerLambert` (`r ≥ 2`: frequencies are not uniform; small-mean obstruction).
Richness is the rung in between (`normal ⟹ rich ⟹ disjunctive`, see `isRich_of_isNormal`,
`isDisjunctive_of_isRich`), and the family `Σ_{n≥1} 1/(b^{n^r} − 1)` would be the first explicit
arithmetic constant placed exactly on it: rich AND nonnormal, with `r ≥ 2` essential in both halves.

## The proof (paper; execute it, splitting into named lemmas)

Read first: the module docstring of `PowerLambertRich.lean` (the five-step mechanism), then
`PowerLambertNonNormal.lean`, `PowerLambertTailExpansion.lean` (`exists_rat_powerLambert_tail`,
`tailPowerDivisorCount`), `SmallCoefficientMean.lean` (the orbit/coefficient identity
`lambertVal_mul_pow_eq`, `orbit = Int.fract (tail sum)`), `PowerLambertDisjunctivity.lean`,
`ArithmeticDisjunctivity.lean` (`floor_digit_of_coefficient_offset`), and `Disjunctive.lean`
(`isDisjunctive_iff_forall_occursAt`, `OccursAt`, `digitOf`, `blockNatVal`).

1. **Witness with guard digits.**  From `isDisjunctive_powerLambert`, for the word
   `w ++ [1] ++ replicate m 0` get `n₁` with `OccursAt`.  Translate `OccursAt` for a word of length
   `L'` into `orbit b x n₁ ∈ [W'/b^{L'}, (W'+1)/b^{L'})` (there is an equivalence in
   `Disjunctive.lean`; `blockNatVal`).  Conclude `orbit b x n₁` is in the `w`-cylinder with
   two-sided margin `δ > 0`.
2. **Orbit as a coefficient tail.**  With `x = q + Y`, `Y = coefficientValue c b`,
   `c = tailPowerDivisorCount r 8`: `orbit b x n = Int.fract (b^n q + Σ_{j≥1} c(n+j) b^{−j})`
   (reuse `lambertVal_mul_pow_eq` / the `hmaster` pattern in `SmallCoefficientMean.lean`).
   The rational part `b^n q mod 1` is periodic in `n` with period dividing `T = lcm(1..8)^r`.
3. **Periodic/non-periodic split of the coefficients.**  For a modulus `Q` define
   `c_Q m = #{d > 8 : d^r ∣ Q ∧ d^r ∣ m}` and `c_⊥ = c − c_Q`.  Prove `c_Q (m + Q) = c_Q m`.
4. **Choice of `J₀`, `D`, `Q`.**  `J₀` with `Σ_{j>J₀} c(n₁+j) b^{−j} · (1 + C_r) < δ/8`
   (the full sum is finite: `c m ≤ m`, geometric weights); `D ≥ 8` with `D ≥ d` for every `d` such
   that `d^r ∣ n₁ + j`, `j ≤ J₀`; `Q = (Finset.Icc 1 D).lcm id ^ (2r)` (a multiple of `T`).
5. **Averaging the non-periodic mass over the class.**  For `j ≤ J₀` and `K ≥ 1`:
   `Σ_{k<K} c_⊥(n₁ + kQ + j) ≤ K · a_r(n₁+j) · Σ_{p>D} p^{−r} + E(K)` with `E(K) = o(K)`, where the
   `o(K)` is the `+1` error of `#{k < K : d^r ∣ n₁ + kQ + j} ≤ K·gcd(d^r,Q)/d^r + 1` summed over
   `d ≤ (n₁ + KQ + j)^{1/r}`; this is `O((KQ)^{1/r}) = o(K)` since `r ≥ 2`.  Key arithmetic facts:
   (a) if `d^r ∤ Q` then some `p^a ∥ d` has `p^a > D`; (b) for `p ≤ D` the valuation
   `v_p(n₁ + j) < (⌊log_p D⌋ + 1) r ≤ 2⌊log_p D⌋ r` forces `#{k : d^r ∣ n₁+kQ+j} = 0`;
   (c) for `p > D` the density is `≤ p^{−r}`.  For `j > J₀` use the crude
   `Σ_{k<K} c(n₁+kQ+j) ≤ K (1 + C_r) a_r(n₁+j) + o(K)`, `C_r = Σ_p p^{−r}/(1 − p^{−r}) ≤ 1`.
   You may replace these with any cruder bound that still gives `Σ_j b^{−j} avg_k c_⊥(n₁+kQ+j) < δ/4`
   for `D` large: e.g. bound everything by `a_r` averages over the progression using only
   `Σ_{d>D} d^{−r} ≤ 1/(D−1)`-type tails, as long as the small-prime incompatibility (b) is used.
6. **Markov and the count.**  For `K ≥ K₀`, at least `K/2` indices `k < K` have
   `|orbit b x (n₁+kQ) − orbit b x n₁| < δ` (in the mod-1 sense; both tails are nonnegative so an
   absolute bound on the difference of the two tail sums suffices), hence are occurrences of `w`.
   Conclude `card (filter (OccursAt b x w) (range N)) ≥ (N − n₁)/(2Q) − 1`, so `c := 1/(4Q)` works.

Commit after each green lemma.  If a step needs a different decomposition, do it, but keep the
headline statement byte-identical.

## Rules

- No `native_decide`, no new axioms, no `maxHeartbeats` bumps without a `-- HEARTBEAT:` comment.
- Do not edit any other `.lean` file except to ADD lemmas (never change existing statements).
- Keep `src/NormalNumbers/PowerLambertFrequencies.lean` as is (a conjecture node, no sorry) unless
  the headline is done and time remains: then you may add a frozen `sorry` theorem there and attack
  it; that file is not the gate.
- Handoff: `HANDOFF-2026-11-03-rich-power-lambert.md`, with `#print axioms isRich_powerLambert`
  and `#print axioms powerLambert_rich_not_normal` recorded (expect only `propext`,
  `Classical.choice`, `Quot.sound`).
- Lines ≤ 100 chars; docstrings on every new theorem; `@[blueprint]` on the headline stays.
