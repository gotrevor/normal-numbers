# HANDOFF 2026-09-14 — prime Lambert irrationality (bounded campaign, laps 1–2 complete)

Branch `master`.  Lap 1: 3eb36d7 … d1a0fa4 (handoff f5e7175).  Lap 2: 5dfef3a, fbc93e2,
f90ae23, plus this commit.  Working tree clean after this commit.  Not pushed (host pushes).
Brief: `~/personal/claude/knowledge/core/projects/normal-numbers-prime-lambert-lean-brief-2026-09-14.md`
(with the 00:34/00:39 UTC addendum).  Footprint: `src/NormalNumbers/PrimeLambert*.lean`,
`docs/prime-lambert-irrationality.md`, this file.  Root module / lakefile / DIRECTION untouched.
Build: `lake build NormalNumbers.PrimeLambertMoments NormalNumbers.PrimeLambertLarge
NormalNumbers.PrimeLambertHexagonNegative` (targeted, green); full `lake build` green via
pre-commit (8888 jobs).  Every theorem below prints `[propext, Classical.choice, Quot.sound]`.

## Proved (lap 1)

`PrimeLambertDefs` (exact ω-transport, periodicity), `PrimeLambertConfig` (Theorem A
`phaseSum_sub_int`), `PrimeLambertGeometry` (hexagon tensor cancels at `1..6r`, coprime
transform), `PrimeLambertOscillation` (`PhaseOscillation → Irrational primeLambert`),
`PrimeLambertAnalytic` (exact prime split; four Props; `ChainExists → Irrational`),
`PrimeLambertTail` (`BadPrimeFrozen` from residue freezing; exact tail bound (20)),
`PrimeLambertHexagonCounterexample` (`¬ MeanRetention 7`).

## Proved (lap 2)

- `PrimeLambertHexagonNegative`: `¬ HexNonneg 19`, `¬ HexNonnegOfLargeMean 19`,
  `¬ MeanRetention 19` — the addendum's eighth-root witness, 6859 hexagon residue counts by
  kernel `decide` (~30 s), `η = (1+i)√2/2` exact, `6859 H = 469 − 450√2 < 0`, mean
  `(7+3√2)/19 > 1/2`.  Refutes even nonnegativity of the hexagon correlation.
- `PrimeLambertMoments`: sharp Taylor bound `‖e^{it} − ∑_{k<M}(it)^k/k!‖ ≤ |t|^M/M!`
  (`norm_expRem_le'`, integral induction); independent CRT model `indepAvg` (uniform residue
  mod `∏_{p small} p`), `smallSum_add_modulus` (periodicity); Props `IndepCharDecay`,
  `MomentComparison`, `IndepMomentSmall`; **proved transfer** `smallPrimeDecay_of_moments`
  (even `M_N`) and `MomentChain → SmallPrimeDecay`.  This is draft §5.4's centred even-moment
  step, machine-checked.
- `PrimeLambertLarge`: unconditional `|X_p(n)| ≤ ‖c‖₁ 2^{−K}`, class bound by active-prime
  count, `LargePrimeCountSmall → LargePrimeNegligible`.

## Open

Exactly one `sorry`: `phaseOscillation` (`PrimeLambertOscillation.lean`); the headline
`irrational_primeLambert` is sorry-gated and is NOT a proved theorem.  It is equivalent to
`ChainExists`, whose remaining unreduced content is exactly five Props with explicit
quantifiers (none is an opaque "good" hypothesis):

| Prop | module | what remains |
|---|---|---|
| `TailTruncation` | Tail | parameter arithmetic `H(log N + log d + J)/2^J → 0` |
| `LargePrimeCountSmall` | Large | `#{p > R : p ∣ n + jd_a − s_a} ≤ H(J−K) log(3N)/log R` |
| `IndepCharDecay` | Moments | local char.-function product `≤ exp(−c_q V_N)`, `V_N → ∞` |
| `MomentComparison` | Moments | `k`-fold products periodic with period `≤ R^k`, AP error `O(AR^k/N)`, CRT factorization of `indepAvg` |
| `IndepMomentSmall` | Moments | two-sided mgf (14) + `M_N ≫ V_N` |

Plus construction of the `Chain` itself (hexagon tensor `TConfig` from
`exists_tconfig_cancelling`, an AP sample frozen mod the bad primes, sieve data) with
`K ~ (6/5) log log log N`, `J = ⌈2 log₂ log N⌉`, `M ~ (log log N)^{1/12}` even, `R = N^{1/(20M)}`.
Geometry still lacking: distinct first coordinates for `B ≥ 7`, mass `6^{K/3}`, surviving
squared mass at site `K+1` (needed for `V_N → ∞`).

## Next attacks (if the campaign is extended)

1. `MomentComparison`, exact core: for `P = {n₀ + A t : t < L}` with `gcd(A, m) = 1` and
   `g` `m`-periodic with `|g| ≤ B`, `|avg_P g − avg_{range m} g| ≤ 2 m B / L` (residue counts
   differ from `L/m` by `≤ 1`).  Apply to `g = ∏_{i≤k} X_{p_i}` (period `∏ p_i ≤ R^k`,
   `B = (‖c‖₁2^{−K})^k`), expand `S^k` into `≤ |small|^k` tuples, and prove the CRT
   identity `avg_{range(∏ small)} ∏ X_{p_i} = avg_{range(∏ p_i)} ∏ X_{p_i}` (periodicity of
   the product mod `∏ p_i`, `smallSum_add_modulus` pattern).  That closes (16) modulo the AP
   shape of the sample, which must be added to `ProgressionFamily` or `SieveData`.
2. `IndepCharDecay`: CRT factorization `indepAvg (e(q·)) = ∏_p (1/p)∑_{r<p} e(q X_p(r))` (needs
   `ZMod.chineseRemainder` / `Nat.Coprime` product decomposition of `range (∏ p)`), then the
   local bound `|(1/p)∑_r e(qX_p(r))|² ≤ 1 − c σ²/p` from `1 − cos x ≫ x²` and `2^{−K} → 0`.
3. Do not touch the root module; host owns pointers.  No Aristotle, no outreach.

## Refutations on record

`¬ MeanRetention 7`, `¬ HexNonneg 19`, `¬ HexNonnegOfLargeMean 19`, `¬ MeanRetention 19`
(all kernel-checked).  Docs also record the IVT corollary (interpolant with `H = 0`, mean
`> 1/2`) and the paper iid base-four countermodel for disjunctivity — neither formalized.
