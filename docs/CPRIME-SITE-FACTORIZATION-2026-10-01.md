# Site factorization: the frozen statement behind `RelativeFirstOrder`

Ren, 2026-10-01, attended.  Paper statement plus mechanism sketch, **not refereed**.  Frozen in Lean, compile-checked:
`src/NormalNumbers/CPrimeSiteFactorization.lean` (`SiteFactorization`, `PairSecondOrder`,
`CPrimeResidueQuad`, `Literature.GranvilleShaoCor71`, `MultBVResidue`).  Predecessor:
`docs/CPRIME-QUANTITATIVE-2026-09-30.md`, sections "`RelativeFirstOrder`, measured" and
"Analytic `G_h`".

## Verdict (after the referee pass, 2026-10-01)

**The reduction to known theorems does not survive as written.**  An independent referee, with
its main claims re-checked by me, found that the crux is uniformity in the growing window `J`.
That is the repo's wall "fixed-window conductor at depth" again.  Maze row: "site factorization
via log-power BV" (`wall`).

- **What holds:**
  - the identity `T1'_k = mean[Φ^{≠k}(n)·(F − F_y)(n+k)]`;
  - the main term `W_y·g(κ_k, s_k)`.  The `1/Γ(1+κ)` size budget is genuinely present, and the
    first order is `δ w_k log s_k`;
  - the Granville–Shao Corollary 7.1 transcription;
  - the parity sibling, which is type I.
- **What fails:**
  - The sieve that turns the other sites into progressions has modulus multiplicity about
    `(2J)^{ω(e)}`, a loss of `(log N)^{O(δJ²)}`.  BV saves only a fixed `(log N)^{−A}`.
  - Deep sites can be dropped only down to `J₁ ≳ log₄ log log N`, because each still carries
    phase `|w_j|·δ log log N`.
  - My `|w_j|`-weights argument for multiplicity `C_h^{ω(e)}` uses the weighted divisor
    expansion, which has **no level control**.  Withdrawn.
- **Needed to reopen:**
  - BV for `z^{Ω_{P,≤y}}` at moduli `≤ x^{3/8}` with a **super-polylog** saving.  Candidate:
    `Δ_A` with conductors up to `exp(c√log x)`, a Gallagher-style large-sieve bound, and an
    excised exceptional modulus.  For primes this is the FGKMT-type input the repo already has,
    `Erdos4.FGKMT.exists_exponential_prime_distribution`; the multiplicative-function version
    is not in the literature I found.
  - Or: a sieve whose `ℓ¹` mass stays polylog at growing depth.
- **Confidence:**
  - `SiteFactorization` is true (proof regime, residue classes): about 75%.
  - This assembly proves it: about 15–20% (referee: 15%; down from 60%).
  - `CPrimeResidueQuad`, corrected to `O(log⁵φ(q)/φ(q)²)`: about 45%, carried by the truth of
    the statement, not by this proof.
  - `PairSecondOrder`: about 75%.  Measured `|T2|/Fw² ∈ [0.007, 0.53]`, stable in N
    (`probes/data-2026-10-01-cprime-pair-second-order.md`).

### First-draft verdict (superseded; kept for the record)

- The one-site fresh term is a correlation of the other sites' frozen phase with `F − F_y`.  So
  the crux "is" BV for `F = z^{Ω_P}` and `F_y`, at moduli up to `N^{3/8}`, which is
  Granville–Shao.  The first draft cited their Thm 2.1; the faithful input is Cor 7.1, check (a).
- The previous doc's CRT/BV split by prime size is unnecessary.  That still holds.
- Confidence then: about 60% for the assembly.

## Setup

- `P` = primes `≡ a (mod q)`, `(a, q) = 1`, `q ≥ 3`, so `δ = 1/φ(q)` and `ρ = δ log 2`.
- Sites `k = 1..J`, `J = ⌊log₂log₂N⌋ + 1`, and `z_k = e(h/4^k)`, `w_k = z_k − 1`.
- Proof-regime cutoffs `y_k = N^{u⁻²2⁻ᵏ}`, with `u` fixed and large (C′ needs `u ≥ 66` for its
  sieve budget `R ≤ N^{1/8}`).
- Frozen phase `Φ(n) = ∏_j z_j^{ω_{P,≤y_j}(n+j)}`, so `W_y = mean Φ`.  `Φ^{≠k}` drops site `k`.
- `T1' = Σ_k T1'_k`, with `T1'_k = mean[ Φ(n)·(z_k^{ω_{P,>y_k}(n+k)} − 1) ]`.  This is the fresh
  primes at site `k` with every frozen part kept.  The probe's `T1` column **is** `T1'`, so its
  `T2 = W − W_y − T1'` is exactly `PairSecondOrder`'s left side.  The exact one-site term differs
  from `T1'` only on `n` with fresh primes at two sites.

The identity that drives everything:

    T1'_k = mean[ Φ^{≠k}(n) · (F_k − F_{k,y})(n+k) ],
    F_k = z_k^{ω_P},   F_{k,y} = z_k^{ω_{P,≤y_k}}.

The site-`k` frozen factor times the fresh factor is the full multiplicative function.  So `T1'_k`
is a correlation of one site's **multiplicative** function with the other sites' **frozen**
phase.  The frozen phase is a sieve-truncatable function of `n` modulo small moduli: a type-I
object.  No site ever sees fresh primes on both sides of a correlation.  That is `T2`'s job, and
`T2` is only upper-bounded.

## The statement

**`SiteFactorization`.**  There is `u₀` such that for each `h ≠ 0` there is `C_h`, uniform in `q`
and `u`, with

    limsup_N | T1'(N) − W_y(N)·G_h(u) |  ≤  C_h·( e^{−u/2} + δ/√u )      (u ≥ u₀),

    G_h(u) = Σ_k g(κ_k, s_k),   g(κ, s) = s^κ e^{−γκ}/Γ(1+κ) − 1,
    κ_k = δ w_k,   s_k = u²·2^k.

- `s^κ` is the limit of the fresh tail `∏_{y_k<p≤N, p∈P}(1 + w_k/p)` (Mertens in progressions).
- `e^{−γκ}/Γ(1+κ)` is the Selberg–Delange size budget.
- At a pole, `κ` a negative integer, `1/Γ = 0` and the factor is `−1`.  The Lean form gets
  this from Mathlib's `Γ(−n) = 0` convention.
- The Dickman factor `F_κ(s_k)` of the analytic-`G` section is `1 + O(s^{−s})` here.  It
  disappears into the error, and so do the unresolved complex-`κ` and pole cases of the probe
  regime.

**Content.**  The triangle bound on `T1'` is `≍ δ log u`, which grows with `u`, while the error
is fixed before `u`.  So the claim is genuine first-order cancellation.  In this regime
`|W_y| ≤ 4e^{−u} + o(1)` (C′ (5.3) plus model contraction (5.4)).  The main term `W_y G_h` is
therefore smaller than the error, and the usable content is:

> one-site fresh primes inherit the frozen mean's decay.

`G_h` matters at reachable `N` (`a = 1, 0.5`), where `W_y` is not small.  It is what the probe
measures, and there it converges for residue classes (2026-10-01 data).  The proof regime itself
is numerically unreachable.

**`PairSecondOrder`.**  With the weighted fresh mass `B_h(u) = Σ_k |w_k|·δ log(u²2^k)`, and an
absolute `C`:

    limsup_N | W − W_y − T1' |  ≤  C·B_h(u)².

This difference lives on `n` with fresh primes at two sites, `n+j = pm`, `n+j' = p′m′`.
Counting such `n` is an upper-bound sieve for two linear forms in `p`, with the primes restricted
to a progression (Halberstam–Richert).  The singular series is bounded on average.  The
probe's `|T2|/ρ² ∈ [0.2, 4.6]`, stable in `N`, is the numerical face of this.

## The chain to `O(ρ² polylog)`

- `|W| ≤ |W_y|(1 + |G_h|) + |T1' − W_y G_h| + |W − W_y − T1'|`.
- `|G_h(u)| ≤ C(k_h + δ log u)`, with `k_h = ⌈log₄|h|⌉`.  At sites `k ≤ k_h`,
  `|g| ≤ 1 + e^{O(δ)}`.  Beyond them, `|g| ≲ |κ_k| log s_k`, which is geometric in `k`.
- So `limsup|W_h| ≤ C[(k_h + log u)e^{−u} + e^{−u/2} + δ/√u + B_h(u)²]`.  Here
  `B_h(u) ≍ ρ(k_h log u + k_h² + log u)` (referee): the sites `k ≤ k_h` each carry `|w_k| ≍ 1`
  and fresh mass `δ log(u²2^k)`.
- Take `u = ⌈ρ⁻²⌉`.  Then `e^{−u/2}`, `δ/√u` and `e^{−u}log u` are all `≤ Cρ²`, and
  `log u ≍ log(1/ρ)`.  Also `u ≥ 66` for small `ρ`, and `u² ≤ L3 N` eventually.
- So `limsup|W_h| ≤ Cρ²L⁴`, with `L = log|h| + log(1/ρ)`.
- Erdős–Turán with `H = ⌈ρ⁻²⌉`: `D ≤ 6/H + (4/π)Σ_{h≤H}|W_h|/h ≤ Cρ² log⁵(1/ρ)`.
- `SiteFactorization`'s constant must be polylog in `h`, chosen before `h`, or this sum
  diverges.  The Lean form now has `C(1 + log|h|)^m`.
- `winJ ≈ log₂log₂N` puts `y_J < 2J`, outside C′'s hypotheses, so (5.3)–(5.4) need a
  deep-site truncation at `J₁ ≈ L3 N`.  That costs `4^{−J₁}δ log log N → 0`.

For residue classes this gives `D = O(log⁵φ(q)/φ(q)²)`, which is `CPrimeResidueQuad`.  (The
first draft said `log³`, an arithmetic slip the referee caught.)  The
modulus needed for every length-`L` word to have positive lower frequency drops to about the
square root of `CPrimeResidueRich`'s.  At `u ≍ ρ⁻²` the cutoff constant is
`c_u = 3 + 2log₂u ≍ log(1/ρ)`, which the `log⁵` absorbs.

## Mechanism (sketch)

1. **Sieve-truncate the other sites.**  C′ §5 approximates the frozen state by CRT atoms at
   moduli `Q·∏A·∏E ≤ Q·∏T_j·R`, which is at most `N^{1/4+1/8+o(1)} = N^{3/8+o(1)}` on its
   schedule (§6, `T_head^m T_tail^{J−m} ≤ N^{1/4}`).
   - C′ uses only a lower sieve and a TV transfer, (5.2)–(5.3).  The weight `(F − F_y)(n+k)` is
     complex, so positivity is lost.
   - Fix: sandwich each atom between fundamental-lemma upper and lower sieves `λ⁻ ≤ 1_atom ≤ λ⁺`.
     The sandwich gap is a positive count, controlled by CRT as in (5.1).  The `λ⁻` part is a
     linear combination of progressions.
   - Weighting by `|F − F_y| ≤ min(2, |w_k|·ω_{P,>y_k})` and Cauchy–Schwarz gives a per-site
     error `|w_k|·e^{−u/2}·δ log s_k`, which is summable over `k`.  **Open check (b).**
2. **BV for `F` and `F_y`.**  For each atom modulus `e` (coprime to `q`, since its primes lie in
   `P`), the progression sums of `F − F_y` follow from `MultBVResidue` (derived from GS Corollary 7.1).
   - The moduli are `≤ N^{3/8} < N^{1/2−ε}`, inside the BV range.
   - The savings are absolute, `N(log N)^{−A}`, and the main term is `≍ N` for fixed `u`.  So
     the AGP obstruction (`docs/JOINT-LAMBERT-AGP-GAP.md`: BV cannot give a *relative* lower
     bound) does not arise.
   - The multi-site weights carry `∏|w_j|` over the moduli's prime assignments.  So the divisor
     multiplicity is `C_h^{ω(e)}`, not `J^{ω(e)}`, and the `(log N)^{−A}` saving absorbs it.
     **Open check (c).**
   - The residues `c` need not be coprime to `e`; the standard gcd split handles that.
   - `ω` versus `Ω`: `z^{ω}` is not in class `C` when `|1 − z| > 1`.  Pass through
     `z^{ω} = z^{Ω} ∗ g`, with `g` supported on squarefull numbers.  Routine.
3. **Main terms.**  For `e` composed of frozen primes, the local factors of `F` and `F_y` agree
   at `p | e` with `p ≤ y_k`.
   - A prime `q′ ∈ (y_k, y_j]` is frozen at site `j` and fresh at site `k`.  It cannot divide both
     `n+j` and `n+k` (`q′ > J`), which costs `O(1/q′²)` per prime and `O(1/y_k)` in total.
   - So the main term is `W_y·(M[F]/M[F_y] − 1)`, the global mean ratio.  Selberg–Delange for
     `F` and the friable mean for `F_y` evaluate it as `g(κ_k, s_k)·(1 + O(|κ_k|/s_k))`.
   - Inside an atom the site-`k` frozen part `D_k` is fixed.  The fresh mean is then taken at
     `N/D_k`, a relative change of `|κ_k|·log D_k/log N`, typically `|κ_k|/s_k`.  Summed:
     `δ C_h/u²`.  The statement's `δ/√u` is deliberately looser.  **Open check (d).**

**Literature inputs** (Literature Props):
- **Granville–Shao 2018**, Corollary 7.1.  Frozen as `Literature.GranvilleShaoCor71`.  Classical
  BV is `BoundedGaps.Maynard.bombieriVinogradov`, already in the dependency tree.
- **Selberg–Delange for `z^{ω_P}`** (Tenenbaum II.5.2), frozen as
  `Literature.SelbergDelangeResidue`.  The instantiation of its hypotheses is ours.
- **Halberstam–Richert Thm 3.12**, the upper sieve for two linear forms, frozen weakened as
  `Literature.SelbergUpperTwoForms`.  The theorem number is recalled and has not been re-opened.
- **de la Bretèche–Tenenbaum**, *Friable averages of complex arithmetic functions*,
  arXiv:2305.06486: friable Selberg–Delange for complex `κ`.  It is needed **only in the probe
  regime**, as the authority for `F_κ` at complex `κ`.  In the proof regime, C′'s own proved
  model bound (5.3) gives the frozen single-site mean to `O(e^{−u})`, so no friable input
  enters the proof.
- **Tenenbaum–Wu**, *Moyennes de certaines fonctions multiplicatives sur les entiers friables*,
  J. reine angew. Math. 564 (2003).
- **The fundamental lemma of sieve theory**, upper and lower, and the **Selberg upper sieve**
  for two linear forms (Halberstam–Richert, *Sieve Methods*).
- **Siegel–Walfisz / Mertens in progressions** (`G4MertensAP` has the lower bound only).

Every input used by the proof now has a Lean statement.  The wiring is frozen as believed
`sorry` theorems, each with its confidence, an English proof and its evidence:
`twistedSiegelWalfisz`, `multBVResidue_of`, `siteFactorization_of`, `pairSecondOrder_of` and
`cprimeResidueQuad_of`.  Still owed: the fundamental lemma (upper and lower), for check (b).

## Negative-inventory check

Every row of `src/NormalNumbers/Maze.lean` (140 rows) was read.  These touch this statement:

| row | verdict | relation to `SiteFactorization` |
|---|---|---|
| (BL) bias-loss criterion | restatement | Not a per-band feedback ledger.  The error is fixed before `u` and comes from an external estimate (BV) |
| per-band contraction | refuted by the one-site control `z^{ω(n+1)}` | At `J = 1`, `SiteFactorization` is an identity (`T1' = M_f − M_y = M_y(M_f/M_y − 1)`).  The one-site control satisfies it exactly |
| late-band regeneration as feedback | refuted: it is the SD size budget `e^γ/\|Γ(i)\| = 3.41` | **Consistent, and a check.**  At `κ = i − 1` (all primes, `h = 1`), `\|e^{−γκ}/Γ(1+κ)\| = e^γ/\|Γ(i)\| = 3.41`.  `G_h` carries that budget as a deterministic factor, never as feedback |
| `OneSiteRatioBounded` (CRT form) | false as stated: `z = −1` zeroes the CRT prefix at `p = 2` | Avoided.  The statement is additive, `g` uses only the fresh product, and nothing divides by a CRT prefix.  The probe's `G_A` blow-up at `My₁ = 0` is this row |
| signed sum (7) | restatement | Not a restatement.  The proof route names an external estimate (Granville–Shao BV), and the consequence stops at `ρ²`: `T2` keeps `W ≠ 0` for all primes |
| absolute propagated budget B | refuted as universally necessary | Not used |
| full prime-incidence independence | refuted: TV → 1 at fixed-power cutoffs | Fresh primes are never modeled as independent.  The fresh side is the true multiplicative mean (SD).  Only the frozen side uses C′'s model, at TV `≤ 4e^{−u}`, and that is C′'s proved bound |
| fixed-window conductor at depth | wall: no uniformity at growing depth | **Hit.**  This is where the route stops (referee): the multi-site sieve multiplicity `(2J)^{ω(e)}` against BV's fixed log-power saving.  New Maze row "site factorization via log-power BV" |
| TT (3.3), K-point, Lebesgue scales | vacuous / false as stated: quantifier order | In the Lean Props, `C_h` comes before `q, u, N`, and the error is a fixed function of `u`.  The Literature Prop fixes `B, C` before `x, y` |
| peeling (12): dropping neighbors is the invalid shortcut | rule | Neighbors are kept: `Φ^{≠k}` stays in full.  The claim is their equidistribution along `F − F_y`, which is the BV content |
| peeling §6.4 parity test, phases (1/2, 1/2) | test | Run below |
| AGP hall (BV cannot give a relative lower bound) | wall | Absolute errors suffice here (main term `≍ N`) |

## Known-false siblings

1. **All primes (G₄).**  `3 ≤ q` excludes it in Lean.  On paper `ρ = log 2`, so `ρ²·log⁵` is
   trivial and nothing is claimed about G₄.  `SiteFactorization` at `δ = 1` is still plausible,
   and the probe's all-primes `G` converges toward `G_∞` (61 → 37%).
2. **Two-point parity** (§6.4 of the peeling audit): `J = 2`, `z₁ = z₂ = −1`, all primes.
   - Here `κ = −2` is a pole, so `g = −1`.  The statement then reduces to
     `mean[(−1)^{ω(n+1)}·(−1)^{ω_{≤y}(n+2)}] = O(e^{−u/2})`.
   - That is Liouville at one site against a **truncated** parity at the other.  After sieve
     truncation it is `λ` in progressions to small moduli: type I, BV-strength.
   - With `d_p ≤ 2`, the fundamental lemma plus BV for `(−1)^ω` handles it.  It does not reach
     Chowla, because the error does not vanish as `y → N^{1/2}`.  (The first draft called
     Mangerel's both-sides-truncated result "the harder case"; that is backwards.)
   - This sibling does **not** exercise growing `J`, which is where the real gap is.
   - The genuinely parity-forbidden correlation, full `ω` at both sites, sits in `T2`, which is
     only upper-bounded.  Not forbidden.
3. **One-site control** `z^{ω(n+1)}`: an exact identity (table above).
4. **Thinned / density-free `P`.**  Excluded: `G_h` needs a Selberg–Delange density, and the
   probe's golden-ratio thinned sets wander.  For general bounded-`ρ` sets, the linear
   `CPrimeQuant` stands.

## Open checks, before any lap

- **(a) Granville–Shao faithfulness: RESOLVED (2026-10-01, later).**  The first draft cited
  GS Theorem 2.1, whose Siegel–Walfisz hypothesis fails here.  `z^{Ω_P}` correlates with
  characters mod `q₀`.  The right citation is **GS Corollary 7.1** (§7).
  - It holds for every `f ∈ C`, stated with `Δ_A`: the characters of conductor `≤ (log x)^B` are
    subtracted.
  - Its only hypothesis is BV for `f·1_P`, which is classical BV at modulus `lcm(q, q₀)`.
  - At moduli `e` coprime to `q₀`, the gap `Δ − Δ_A` involves only characters of conductor
    coprime to `q₀`.  A twisted Siegel–Walfisz bound (`TwistedSiegelWalfisz`, believed ~80%,
    Selberg–Delange with characters plus Siegel) controls them, at a cost of `(log x)^{2B+1}`.
  - Lean: `Literature.GranvilleShaoCor71` (faithful transcription) and
    `multBVResidue_of : Cor71 → BV → TwistedSW → MultBVResidue := sorry`.
- **(b) Weighted two-sided transfer: FIXED.**  Cauchy–Schwarz needs `Σ(λ⁺−λ⁻)|G|²`, which is
  another equidistribution claim.  Use positivity instead: `λ⁺ − λ⁻ ≥ 0` pointwise,
  `|F − F_y| ≤ min(2, |w_k| s_k)`, and `Σ(λ⁺−λ⁻)` is exact by CRT.  Total `C_h u² e^{−u}`.
- **(c) Uniformity in `J`: FAILS.**  This is the wall in the Verdict above.
- **Atom modulus and `q₀`: disputed and settled.**  The referee read C′'s
  `Q = ∏_{p≤2J} p` literally: once `2J > q₀`, `q₀`'s primes divide every atom modulus, where
  plain-`Δ` BV fails.  But the frozen phase depends only on P-primes, and those never divide
  `q₀`.  So `Q` can be cut to `∏_{p≤2J, p∈P} p`, and the coprime-to-`q₀` claim stands.
- **(d) Restated (referee).**  In the identity form site `k` is not atomized, so "`D_k` fixed in
  an atom" does not apply.  The real check is uniformity of `Σ_{(m,e)=1} F(m)` over `e ≤ N^{3/8}`
  with many prime factors.
- **`TwistedSiegelWalfisz`.**  The uniform-in-`y` sketch was wrong: `Σ_{p≤y} p^{−σ}` blows up
  when `log y ≫ log T`.  A two-regime argument is owed; the statement is about 85%.
- Referee pass: done 2026-10-01.

**Not a lap target.**  The missing input is a super-polylog BV for multiplicative functions,
or a depth-uniform sieve.  That is a research question, not wiring.  A lap would wire `SiteFactorization + PairSecondOrder ⇒
CPrimeResidueQuad` from Literature Props.  That shares the six build gaps of the C′ doc
(Erdős–Turán, quantitative Weyl wiring, …).

## What it does not do

G₄ (all primes) stays where it was.  Its `ρ = log 2` makes the second-order term `O(1)`, and
the relative form of `T2` is a two-sided prime-pair correlation: the parity wall.  This statement
moves the wall from first order to second order in the fresh mass.  It does not thin the wall.
