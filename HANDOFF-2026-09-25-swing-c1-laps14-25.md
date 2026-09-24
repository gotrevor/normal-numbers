# Handoff — swing at C1, laps 14–25 (the crux reformulated, named, and localised)

**Branch** `wip/swing-c1` · **HEAD** `6915005` · tree clean, NOT pushed
**File** `src/NormalNumbers/SwingC1.lean` (~2200 lines)
**Build**: full `lake build` green, 9176 jobs.  **Sorries in the file: exactly two**, both named
leaves of the headline: `hDepthAll` (superseded route, kept on the record) and `hAutoCorrAll`
(THE leaf).  Everything else is `[propext, Classical.choice, Quot.sound]` — no `native_decide`,
no cited axiom, no `axiom` declaration.  `conjC1 : ConjC1` is still present and still open, per the
kickoff addendum.  Nothing outside `SwingC1.lean`, `probes/`, and this session's docs was touched.

## The crux now: SIX equivalent forms, all proved in BOTH directions

```
ConjC1  ⟺  HState        conjC1_iff_hState
        ⟺  HAutoCorr     conjC1_iff_hAutoCorr        ← the live leaf (hAutoCorrAll)
        ⟺  HFloorCorr    conjC1_iff_hFloorCorr
        ⟺  HOrbit        conjC1_iff_hOrbit
        ⟺  HFactorizes   conjC1_iff_hFactorizes      ← the literature-shaped form
```

With `T(n) := Σ_{m≤n} ω(m) + c_n` and `A_n := ⌊b^n·G4_b⌋` and `t_n := fract(b^n·G4_b)`:

1. **`castState b L n = T(n+L) − T(n)`** (`castState_eq_castSum_sub`).  So C1 is the
   AUTOCORRELATION SPECTRUM of one unimodular sequence at the FIXED modulus `b−1`:
   `mean_n ζ_{b−1}^{j(T(n+L)−T(n))} → b^{−L}`.  This replaced the old `HDepth` leaf, which lived at
   the growing modulus `b^{κ n}` (`κ n ≳ log_b log n`) and demanded equidistribution of the window
   word in `ZMod (b^L)` — i.e. block normality, STRICTLY STRONGER than `ConjC1`.
2. **`T(n) ≡ A_n (mod b−1)`** (`castSum_cast_eq_floor`): casting out nines kills every trace of `ω`
   and of the carry.  The leaf mentions no `ω`, no carry, no digits.
3. **`A_{n+L} − b^L A_n = ⌊b^L t_n⌋`** (`floor_sub_eq_floor_fract`): the leaf is weak
   equidistribution of the `×b`-orbit against the `b^L`-step test functions `t ↦ ζ_{b−1}^{j⌊b^L t⌋}`.
4. **`σ_L := (b^L−1)/(b−1) = 1+b+⋯+b^{L−1}` is an INTEGER** (`sub_one_mul_geomNat`), so
   (`zetaRoot_floor_diff_eq`)
   `ζ_{b−1}^{j(A_{n+L}−A_n)} = e(j·σ_L·b^n·x) · e(−j(t_{n+L}−t_n)/(b−1))`:
   a Weyl exponential at an **integer** frequency times a unimodular twist.
5. **The exact split (lap 24).**  Mod `b−1` the digit recursion loses its `b`:
   `d_{n+1} ≡ ω(n+1) + c_{n+1} − c_n`.  With `f_j(m) = ζ_{b−1}^{j·ω(m)}` (unimodular and
   MULTIPLICATIVE, `omegaChar_mul_of_coprime`) and `g_j(m) = ζ_{b−1}^{j·c_m}`, the carry factors
   TELESCOPE (`digitChar_eq`, `prod_digitChar_eq_omega_mul_boundary`, `corrSum_eq_elliott`):
   `∏_{i<L} D_j(n+i) = (∏_{i<L} f_j(n+1+i)) · g_j(n+L) · g_j(n)⁻¹`.
   `f_j(p) = ζ_{b−1}^j` is constant and `≠ 1`, so `f_j` is the `ω`-analogue of `λ(n) = (−1)^{Ω(n)}`:
   its one-point mean vanishes by Delange/Halász, and its shifted correlations ARE the Elliott
   correlations — known in LOGARITHMIC density for `L = 2` (Tao 2015) and odd `L`
   (Tao–Teräväinen), but NOT in natural density, which is what `ConjC1` needs.  The two factors are
   inseparable: by `not_hAutoCorr_of_carryNegligible` the `f`-part alone gives `0` while the leaf
   needs `b^{−L}`, and `g` is not independent of `f` (`c_n` is a function of `ω(n+1), ω(n+2), …`).
   **This is the sharpest localisation the leaf has: two named gaps to the known theorems — the
   inseparable carry boundary term, and natural vs logarithmic density.**

6. **Telescoping ⇒ the Elliott shape** (`prod_digitChar`, `corrSum_eq_mean_prod`): with
   `D_j(n) = ζ_{b−1}^{j·d_{n+1}}`,
   `ζ_{b−1}^{j(T(n+L)−T(n))} = ∏_{i<L} D_j(n+i)`, so C1 says exactly that the multiple correlations
   of the unimodular sequence `D_j` factorize as powers of its own mean `1/b`.

**Kickoff step 4, answered:** the leaf IS an Elliott/Chowla-type statement.  `L = 1` (the mean is
`1/b`) is the one-coordinate case Delange (1969) settles; every `L ≥ 2` is the open
independence-across-shifts assertion.  It is NOT a weaker classical statement.

**The constant `b^{−L}` is over-determined** — three independent derivations agree:
`fourier_normalCastLaw` (from `normalCastLaw_closed`, finite/combinatorial),
`mean_zetaRoot_block` (the test function's mean value over `[0,1)`, via
`sum_zetaRoot_range_pow : Σ_{v<b^L} ζ_{b−1}^{jv} = 1`), and the six `decide` anchors of lap 11.

## Four sub-approaches REFUTED (do not redo)

1. **Naive carry-independence** (`not_hAutoCorr_of_carryNegligible`, PROVED).  If the carry
   difference vanished mod `b−1` on a density-one set and the `ω`-only correlations vanished, the
   leaf would be FALSE (it needs `b^{−L} ≠ 0`).  The `ω`-only clause at `L=1` IS Delange, so the
   carry-negligibility fails.  Forced mechanistically: `c_n = ⌊(ω(n+1)+c_{n+1})/b⌋` is a function of
   `ω(n+1)`.  **The whole gap between the naive `0` and the true `b^{−L}` is that coupling — which
   is exactly why C1 is not a corollary of Delange.**
2. **Periodic rational approximants / CRT** (`OBSTRUCTION-2026-09-24-periodic-approximant.md`).
   `G4_b = Σ_p 1/(b^p−1)` truncated at `P` is `M_P/(b^{Λ}−1)`, `Λ = lcm{p≤P}`, hence purely periodic
   of period `Λ` — C1 for the approximant is an exact finite count over one period.  Dead: the tail
   `2b^{−P}` forces `P ≳ N` while `Λ(P) ≥ ∏_{p≤P}p = e^{(1+o(1))P}`, so the period is EXPONENTIALLY
   longer than the averaging range.  No repair.
3. **Sparse / finite block-frequency reduction** (`sum_zetaRoot_mixed_ne_zero`, PROVED).  ALL `b^L`
   coefficients of the mod-`(b−1)` statistic on the block alphabet are nonzero:
   `Σ_{v<b^L} ζ_{b−1}^{jv}ζ_{b^L}^{−av} = (ζ_{b−1}^j−1)/(w−1) ≠ 0`.  So the integer-frequency Weyl
   bridge (item 4 above) cannot be closed with finitely many Weyl sums.
4. **Kátai / BSZ** (lap 12, previous session) — dies on the shift in both directions.

## Numerics are USELESS here, and that is a theorem-shaped finding

`probes/swingc1_autocorr.py` (hand-computed known-answer check included).  For every `b ≥ 8` the
carry is IDENTICALLY ZERO at all feasible `N`: `ω(m) ≤ 7` below `9,699,690`, so
`Σ_k ω(n+k)b^{−k} < 1`.  The Lean content is `omegaCarry_eq_zero_of_omega_le` /
`omegaTail_le_of_bound`: `ω ≤ b−2` on the tail ⟹ `c_N = 0`.  Base-`b` carrying only switches on near
the `b`-th primorial (`b=10`: `m ≈ 6.5·10⁹`), so the `b=10` columns coincide EXACTLY with the
`ω`-only columns and measure Delange, not the leaf.  `b=3,4` do exercise the carry and give the right
order and `b^{−L}` decay (`b=3`: `0.224, 0.054, 0.016` vs `1/3, 1/9, 1/27`), off-constant by ~0.5–2×
as the `(log N)^{−c}` discrepancy of `ω` mod `q` predicts.  **No computation at feasible `N`
separates the leaf from its negation.**

## ⚠️ FALSE-ALARM GUARD: the `b=3` numerics look like a refutation and are NOT one

`probes/swingc1_autocorr.py::marginal_control`.  At `b=3` the digit frequencies of `G4_3` are nowhere
near `(1/3,1/3,1/3)` at reachable `N` — at `N=4·10⁶` they are `(0.325, 0.386, 0.289)` and
`mean_n (−1)^{d_{n+1}} ≈ 0.23` against the predicted `1/3`, STABLE over 2.5 decades.  Read naively
that refutes `ConjC1`.  It does not.

The control: block-shuffle `ω` within dyadic blocks (kills all arithmetic correlation, preserves the
local marginal), or resample iid from `ω`'s own marginal.  Both controls have uniform digits in the
limit (the resulting number is a.s. normal), so their column MUST tend to `1/3`.  It doesn't either —
it sits near `0.27`.  So ~3/4 of the apparent deficit is a finite-`N` artefact of `ω`'s MARGINAL
(mean `ω ≈ 2.95` at `m ≈ 4·10⁶`, far too small to spread evenly mod 3), not of arithmetic structure.
The genuine arithmetic residue is the real-minus-control gap, `≈ −0.040`, and both columns RISE
together past `N = 10⁶` (real `0.2233 → 0.2306`, shuffled `0.2620 → 0.2705`).

**Never compare C1 numerics against the uniform-digit model directly.**  Compare against the
same-marginal random model, which carries the identical finite-`N` bias.

## Exact next moves

1. The leaf `hAutoCorrAll` is an Elliott-type wall; expect to narrow, not clear.  Two live threads,
   in priority order:
   * **(a)** Attack the natural-vs-logarithmic gap in item 5.  The known Elliott results (Tao,
     Tao–Teräväinen) give the `f`-part in logarithmic density; `ConjC1` needs natural.  Formalising
     `HAutoCorrLog` and the (true, and standard) implication `HAutoCorr → HAutoCorrLog` would mark
     the gap precisely in Lean; upgrading log → natural is the genuinely hard half and is where a
     new idea is needed.
   * **(b)** The twist factor in item 4, `e(−j(t_{n+L}−t_n)/(b−1))`, is a function of `t_n` ALONE
     (since `t_{n+L} = fract(b^L t_n)`).  Quantifying its total variation against the repo's
     `WindowDecay` is the only route from the leaf to existing repo machinery — but refutation 3
     caps what that can give, so expect a partial result at best.
2. Do NOT re-attack via normality of `G4_b`: `conjC1_conjC3_of_normal` (in `CastingOut.lean`) already
   records that route, and normality is the repo's own open headline.  Item 3 above now makes the
   gap between C1 and normality precise: normality is equidistribution against ALL
   Riemann-integrable test functions, C1 only against the `b^L`-step functions of item 3.
3. `hDepthAll` is the superseded stronger route.  Keep it; do not try to close it (it implies block
   normality) and do not delete it.
4. `CastingOut.lean`, `CastingOutCount.lean`, `CastingOutLambert.lean`, `Maze.lean`, `papers/`,
   `agent-mail/` and the other KICKOFFs were NOT touched and must stay that way.
