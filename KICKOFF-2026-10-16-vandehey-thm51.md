# Kickoff 2026-10-16: prove Vandehey's Theorem 5.1 (make Theorem A unconditional)

Branch `proof/vandehey-thm51`, worktree `~/src/nn-vandehey`.  Target:
`VandeheyProof.vandeheyThm51_holds : Literature.VandeheyDiff.VandeheyThm51` in
`src/NormalNumbers/VandeheyProof.lean`.  The three unconditional corollaries below it are already
wired; they become axiom-clean the moment the target is.  **Do not edit `VandeheyThm51`'s
definition or the corollary statements.**  Put the machinery in new files
(`VandeheyKorobov*.lean`), imported by `VandeheyProof.lean`.

## Source

Vandehey, *Differencing methods for Korobov-type exponential sums*, J. Anal. Math. 138 (2019),
arXiv:1606.07911.  Text: `~/src/normal-numbers/tmp/joint-bc-orbits/lit-dl/vandehey/p.txt`
(Lemma 2.1 l.231, Lemma 2.2 l.279, Lemma 2.3 l.301, Prop 4.1 l.738 and its proof l.948,
Thm 5.1 and the recursion on p.14).  The repo's `docs/GROWING-PRIME-LOCALIZED-LOG-AUDIT-2026-10-02.md`
§1.1 re-derived the recursion and checked uniformity in `P`; `LiteratureVandeheyDifferencing.lean`
already defines `bigM`, `cP`, `alpha`, `expPair`, `constPair`.

## Ladder (state each rung as a sorried lemma first, then prove)

1. **Lemma 2.1 (orders).**  `m / M(P) ≤ ord(b, m)` for `m ∈ ℕ_P` (eq. 5), via lifting the exponent
   (`padicValNat.pow_sub_pow` and friends).  Only this inequality is consumed downstream; the exact
   order formula is optional.
2. **Twisted subgroup sums (the Parseval-orbit trick).**  For `H = ⟨b⟩ ≤ (ℤ/m)ˣ`, any character
   `ψ` of `H`, and `gcd(a, m) = 1`: `|Σ_{x∈H} ψ(x) e(ax/m)| ≤ √m`.  Proof: `T(ah) = ψ̄(h)·T(a)`
   for `h ∈ H`, so `|T|` is constant on the orbit `aH` of size `|H|`; Parseval
   `Σ_{t mod m} |T(t)|² = m·|H|` gives `|H|·|T(a)|² ≤ m|H|`.  No Gauss sums needed.
3. **Lemma 2.2, repaired `d = 1` case (Korobov).**  For `1 ≤ N ≤ τ = ord(b, m)` and
   `gcd(a, m) = 1`: `|Σ_{n=1}^N e(abⁿ/m)| < √m (1 + log m)`.  Proof by completion over `n mod τ`:
   `ψ_h(bⁿ) = e(hn/τ)` is a character of `H`, so each completed sum is rung 2, and
   `Σ_h |Σ_{n≤N} e(−hn/τ)| / τ ≤ 1 + log τ ≤ 1 + log m`.  Vandehey notes Korobov's printed
   statement is wrong in general; only `d = 1` is needed.  The independent referee of
   2026-10-16 confirmed this completion route (`tmp/referee-bb-full/` in the main checkout).
4. **Lemma 2.3** = the `k = 0` case of `VandeheyThm51`: full periods (rung 3 at `N = τ`) plus one
   partial period, with rung 1.
5. **Proposition 4.1 (the differencing step)**, exactly as in the paper, with its hypotheses on
   `α, γ, δ, A, B, r, ν`.  This is the long rung: a van der Corput-type differencing inequality
   (Cauchy–Schwarz over shifts `h`, with `b^h − 1` divisible by a large power of `m`'s primes,
   reducing the modulus).  Write the differencing inequality as its own lemma first.
6. **Theorem 5.1** by induction on `k` from rungs 4 and 5, matching `expPair`/`constPair`.

## If the transcription is wrong

`VandeheyThm51` was transcribed and audited at 90%.  If a constant or exponent in it is false as
stated (a counterexample, or Prop 4.1 delivering a different recursion), **do not edit it**.  Prove
the correct statement as `VandeheyThm51'`, prove `VandeheyThm51' → StonehamSumsNormal.VandeheyCor12`
(the only thing Theorem A consumes; see `vandeheyCor12_of_thm51` for the pattern), record the
discrepancy in the handoff, and `box stuck` so the attended session re-ratifies the target.

## Done when

`VandeheyProof.lean` is sorry-free (host gate), `lake build` is green, and **all four theorems in
it** print only `[propext, Classical.choice, Quot.sound]` under `#print axioms`.  The host gate is
a per-file grep, so a sorried helper in another file would pass it: the axiom print is the real
gate.  Remove the `BarrierAudit` waiver for `vandeheyThm51_holds` when it is proved.
