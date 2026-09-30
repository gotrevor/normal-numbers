# HEADLINES: normal-numbers 🧭

The wide questions this programme serves, one level above the campaigns.  [OVERVIEW.md](OVERVIEW.md)
maps one headline (G₄) in detail, [STATUS.md](STATUS.md) tracks campaigns, and
[DIRECTION.md](DIRECTION.md) binds laps.  Each headline below names the question, what is proved
on its ladder, the wall, and where the next rung could come from.  Written 2026-09-30 from a full
repo review.  Update a headline when one of its rungs moves.

## The ladder every headline shares 🪜

For the base-`b` digits of a real `x` (and, word for word, for its continued-fraction digits):

    normal ⟹ rich ⟹ disjunctive ⟹ complexity p(n)/n → ∞ ⟹ irrational
    normal ⟹ simply normal          (a side rung: independent of disjunctive)
    normal ⟹ abelian-normal         (a side rung: C4 and the binary example live here)

*Rich* means every word has positive lower frequency.  Most of this repo's wins landed one or two
rungs below normality.  Treat a rung as progress in its own right.

## H1. A number defined by arithmetic, not by its digits, is normal 🎯

**Question.**  Normality of a constant whose definition never mentions digits.  The family in play
is the Lambert ladder `c_f = Σ f(n)/(bⁿ−1) = Σ (f∗1)(m) b⁻ᵐ`: the prime constant
`G_b = Σ_p 1/(bᵖ−1) = Σ ω(n)/bⁿ`, and Erdős–Borwein `E_b = Σ 1/(bⁿ−1) = Σ d(n)/bⁿ`.

**Proved.**
- `G_b` disjunctive for `b ≥ 3` (`G4.isDisjunctive_base`); the same for prime subsets with a
  Mertens rate, for `Ω`, and for the master additive weight (`isDisjunctive_residueClass`,
  `SchedB.isDisjunctive_weightA_logLog`).
- **C′**: `Σ_{p∈P} 1/(4ᵖ−1)` is normal in base 4 whenever `Σ_{p∈P} 1/p = ∞` and the fresh mass
  `r_P(N) = Σ_{√N<p≤N, p∈P} 1/p → 0` (`isNormal_subsetLambert_of_sqrtFreshMassZero`).
- G₄ read along its schedule positions is normal (`isNormal_fullRealW`).
- `E_b`, finitely many bases at once: prescribed words at a common position, unconditional, with
  an `N^{1−ε}` occurrence count.  This lives on `proof/joint-lambert-unconditional` in the
  sibling checkout `normal-numbers-lambert` and is **not yet merged here**.

**The wall.**  Ordinary averages over all `n` of growing-depth carries: Chowla/Elliott strength
(C1–C3, Tao–Teräväinen arXiv:2512.01739).  Freezing primes along a designed progression reaches
disjunctivity and `N^{1−o(1)}` counts, and cannot reach positive density.  For all primes the fresh
mass tends to `log 2`, so C′ does not apply.

**Frontier.**
1. ⭐ **Quantitative C′: the normality defect is controlled by the fresh mass.**  The Astra paper
   (`papers/ROUND2-multicutoff-astra.md` §11.3) shows `r_P → 0` *characterizes the geometric
   consumer*.  It says nothing about `r_P` small but positive.  Conjecture shape, with
   `ρ = limsup r_P(N)`:

       limsup_N |freq_N(w) − 4^(−|w|)|  ≤  C_|w| · ρ^c        for some c > 0.

   **Payoff.**  Primes `≡ a (mod q)` have `ρ = log 2/φ(q)`.  So `Σ_{p≡a (q)} 1/(4ᵖ−1)` would carry
   every word of length `≤ L(q)` at nearly its fair frequency, with positive lower frequency
   below a length threshold that grows with `q`.  These would be the first *frequency*
   statements about a natural prime-Lambert constant.  At `q = 1` (G₄ itself) the bound is
   expected to go trivial.
   **Guard rule.**  The content locator is `ρ = 0`, which is C′.  The degenerate verdict is all
   primes, `ρ = log 2`: if the bound stayed nontrivial there, that would be near-normality of
   G₄, so distrust it.
   **Order of work.**
   - A probe first: synthetic `P` with controlled `ρ`, measuring block-frequency defect against
     `ρ`, with `ρ → 0` sets from C′ as the known-answer control.
   - Then audit §10 for where `u_N → ∞` is spent.  With `ρ` fixed the schedule `u_N ≈ ρ^(−1/2)`
     stays bounded, so the defect also carries a bounded-schedule term.
   Confidence that the shape holds for some `c > 0`: about 45%.  That it is new, if true: about 70%.
2. **Simple normality of `G_b`** is a rung below normality.  `SwingC1Log.castLawLog_one` is its
   log-density first step.  It is C1 territory, so count it with C1.
3. **Richness of `E_b`.**  Freezing tops out at `N·exp(−C(log log N)² log log log N)`.  Richness
   needs the same statistical mechanism as C3, so count it with C3.

## H2. Algebraic irrationals are normal (Borel 1950) √

**Question.**  Is `√2` normal in base 2?  Is every algebraic irrational normal in every base?

**Proved here.**  Nothing about the digits of an algebraic irrational beyond irrationality.
`docs/conditional-disjunctivity.md` does two things:
- it shows "`11` recurs in binary `√2`" is equivalent to a carry statement (Axiom C);
- it shows counting alone saturates at `√N` ones.

**Known unconditional rungs not yet in the repo.**
1. **Bailey–Borwein–Crandall–Pomerance 2004.**
   - An algebraic irrational of degree `D` has `≫ N^(1/D)` ones among its first `N` binary digits.
   - The proof is elementary: the ones-count is submultiplicative, pushed through the minimal
     polynomial.  The `D = 2` case is the counting saturation already derived in
     `conditional-disjunctivity.md`.
   - This would be the repo's first unconditional theorem about the digits of `√2`.
   - Confidence it fits in 1–3 laps: about 70%.
2. **Adamczewski–Bugeaud 2007.**
   - Complexity `p(n)/n → ∞`, so no algebraic irrational is automatic.
   - Ralf Stephan has formalized it in Lean (`rwst/Subspace-Theorems`, `AdamczewskiBugeaud2007/`).
   - Plan: enter it now as a `Literature` Prop, verbatim.  Discharge it by `require`-ing a fork
     once the toolchains meet (the lean-formalizations `Stephan2026Ridout` pattern).
3. **Borel's conjecture as a named hypothesis `Prop`**, with its consequence graph.  This is the
   parked proposal `docs/proposal-normality-master-conjectures-2026-09-29.md`.  Its trigger,
   "when §7 settles", fired on 2026-09-29.

## H3. The BBP constants: `ln 2`, `π` in base 16, and the exponent ε 📐

**Question.**  Is `ln 2` normal in base 2?  More generally, is each BBP-type constant normal in its
own base?

**Proved.**
- The Bailey–Crandall reduction: if the orbit is equidistributed, `ln 2` is normal.
- Run and sliver bounds for `ln 2` (`LnTwoRuns`).
- Stoneham `α₂,₃` normal in base 2 (`isNormal_two_stoneham23`), and not simply normal in base 6.
- Maze: Hypothesis A is a *restatement* for `ln 2`, not a weaker input.

**The organizing parameter** (KB leaf `normal-numbers-localized-log-growing-primes-2026-09-16`).
On an orbit segment of length `L` with denominator `q`, set `ε = log L / log q`.

| constant | `ε` | normality |
|---|---|---|
| Stoneham-type | fixed, `> 0` | proved |
| localized logarithm `Λ_P`, finite prime set `P` | `≈ 1/(|P|−1)` | proved on paper (CaptainSude, xi-normality) |
| `ln 2` | `0`, no segments at all | open |

Normality proofs exist exactly where `ε > 0`.

**Frontier.**
1. **The growing-prime localized logarithm.**
   - Candidate: `Σ_{P⁺(m) ≤ Y(m)} 1/(m·2ᵐ)` is normal when `π(Y(n)) ≤ (1−ε) log₂ log n`.  This
     is paper-level, about 70%.  It rests on Vandehey's differencing constants, which are
     explicit in `P`.
   - It is the honest approach toward `ln 2`: an explicit normal constant with unbounded prime
     support, plus a measured rate at which `ε` may go to zero.
   - Step 0 is the paper audit the 2026-09-25 review asked for, which has not happened.
   - Step 1 is the finite-`P` theorem in Lean, reusing the Korobov modules the Stoneham proof
     already built.
2. **Hypothesis A in its general Bailey–Crandall form** as a named `Prop`, with its consequence
   graph (`π` in base 16, `π²`, Catalan-type sums).  Same pass as H2.3.
3. **General Stoneham `α_{b,c}`, `gcd(b,c) = 1`** (Bailey–Crandall 2002), as a library side quest.

## H4. Which maps preserve normality? 🔁

**Question.**  For which `f` does "`x` normal ⟹ `f(x)` normal" hold, in base `b` and for continued
fractions?

**Proved.**
- Wall, extended to rational affine maps, in base `b` (`isNormal_rat_mul_add`).
- Vandehey 2017 Thm 1.1: integer Möbius maps preserve CF normality, by a new route
  (`vandehey_matrix_action_holds`).
- The Moshchevitin–Shkredov criterion, refuted in Lean.
- Base `b` ⟺ base `b^K` (`PowerBaseReal`).

**Open: Vandehey §7** (`φx`, `x+φ`).  The campaign closed 2026-09-29 unsolved; read
`docs/VANDEHEY-S7-FALSE-STARTS.md`.  The wall is joint equidistribution of (transducer state,
input point).  Stepping down to "`φx` is CF-disjunctive" does not help: it restates as the image
orbit avoiding an open set, which is the same joint problem.  Re-enter only with a mechanism a
Maze `reopenIf` names.

**Frontier (library, and a reframe).**
- **Rauzy 1976**, base `b`: `x + y` is normal for every normal `x` iff `y` is deterministic, in
  Rauzy's entropy-zero sense.
  - This is the additive answer in base `b`.
  - It recasts `x + φ` as the CF instance of the same question, with `φ = [1;1,1,…]` as the most
    deterministic input possible.
  - Verify the exact statement from the paper before planting (recall about 75%).
- **Agafonov 1968**: selecting digits along a finite-automaton rule preserves normality.  This is
  the selection side of H4, and it sits next to the transducer machinery §7 built.

## H5. Which statistical tests can hold independently? (spectra) 🌈

**Question.**  Take a family of tests: window lengths, bases, abelian versus ordered counts, CF
versus base `b`.  Which subsets of the family can be exactly the tests a number passes?

**Proved.**
- C4: the abelian length spectrum is completely classified (`Abelian.c4_realizable`).
- An abelian-normal, non-normal binary sequence (`exists_abelianNormal_not_normal`).
- B5′: one explicit `x` that is absolutely normal, CF-normal and Khinchin-typical
  (`exists_absolutely_normal_cf_normal_khinchin`).

**Frontier.**
- **The base spectrum.**
  - Schmidt 1960: normality in base `r` and base `s` coincide when `r, s` are multiplicatively
    dependent, and independent bases can be separated.
  - Becher–Bugeaud–Slaman characterize the same spectrum for simple normality.
  - The B5′ constructions are the machinery.  Verify both characterizations before planting.
- **C4 in base `b > 2`**, with multinomial counts.

## H6. The NN library: classical theorems proved, not cited 📚

Trevor's framing (2026-09-27): prove the basic literature facts as side quests, so the repo becomes
the NN library while the moonshots keep citing freely.

**Done.**  Wall, Pillai, Philipp ψ-mixing, Becher–Yuhjtman (B5′), Stoneham `α₂,₃`, Vandehey 1.1,
Wall-rational.

**Cheapest next.**  Champernowne's constant is normal *as a real number*.  OldMathematician's
sequence theorem plus our `Bridge` upgrade gives it.  Fork and `require` that repo; never vendor it.

**Then.**  Copeland–Erdős 1946, general Stoneham, Rauzy, Agafonov, Schmidt.

## Cross-cutting instruments 🔧

- **The analytic engine.**
  - Logarithmic two-point Elliott: proved.
  - `ZetaLogDerivExponent θ < 1`: parked.  Vinogradov–Korobov gives `θ = 2/3`; the repo owns `θ ≥ 9`.
  - AGP: no longer needed by joint Lambert.
  - Also: PNT in progressions, and the Korobov sums.
- **The two duals.**  Weyl's and Walsh's criteria are complete in every base (`WalshBase`).
- **`Maze.lean`.**  Read it before proposing a route.

## Ranked bets, 2026-09-30 🎲

| # | Bet | Headline | Kind | Confidence |
|---|---|---|---|---|
| 1 | Quantitative C′: probe, then audit of §10 | H1 | new math | ~45% that the shape holds |
| 2 | Master-conjectures pass: Borel + Hypothesis A as Props, consequence graph, Maze test | H2, H3 | conjecture graph | ~85% that it lands (the Schanuel pass proved 10 consequences in one lap) |
| 3 | BBCP `N^(1/D)` ones | H2 | known result; first digit theorem on `√2` | ~70% in 1–3 laps |
| 4 | Growing-prime localized log: paper audit, then finite-`P` in Lean | H3 | new math (paper) | ~70% on paper |
| 5 | Champernowne as a real, then Copeland–Erdős | H6 | library | high |
| 6 | Base spectrum (Schmidt, Becher–Bugeaud–Slaman) | H5 | library+ | unassessed |
| 7 | Harvest explicit open problems from 2024–26 normal-number papers | all | sweep | lean-formalizations answered Saito's Problem 1.8 this way in 2 laps |

**Don't fund:**
- a generic G₄ CLT, or a renamed full-Weyl hypothesis;
- §7 re-entry without a new mechanism;
- `E_b` richness by freezing;
- `θ < 1` for `ζ'/ζ`, which is a Vinogradov–Korobov-sized analytic project.

**Housekeeping:** merge `proof/joint-lambert-unconditional` into this checkout.
