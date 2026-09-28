# ROUTE ESCALATION — C3/MRT, 2026-09-25 (deep-reflection lap 60)

**ROUTE VERDICT: ESCALATE.**  The destination is unchanged and still right.  The *input anchor*
the route was built on is wrong, and was chosen for availability rather than strength.  This
document re-costs the alternatives; the re-decision is executed in `DIRECTION.md` → CURRENT
DIRECTIVE the same lap (Trevor is asleep; autonomy charter says decide and proceed).

## 1. What fired

No 🚦 trigger was ever *registered* for the C3/MRT chapter — that is itself a defect, and this
document registers three.  What fired is diagnostic tell (b) of the reflection protocol:

| session wrap | laps | "leaf PROVABLE with known techniques" |
|---|---|---|
| first | 1–17 | 15 % |
| laps 33–39 | 33–39 | **28 %** (peak) |
| laps 40–42 | 40–42 | 22 % |
| laps 43–51 | 43–51 | 22 % |
| laps 52–59 | 52–59 | **20 %** |

The honest finishability estimate has declined for three consecutive session wraps while the
route was never re-decided.  Tell (a) — a recurring "the crux is almost cracked" with no
whole-lemma target closing — did **not** fire: laps 52–59 closed 33 real declarations, all
trust-triple clean.  The machinery is excellent.  It is aimed at the wrong input.

## 2. The independent ground (not another LLM's read of the same handoffs)

Two facts, both checked this lap against primary sources, neither previously acted on.

### 2a.  The dependency's Elliott `Prop` demands COMPLETE multiplicativity — Tao's theorem does not

`.lake/packages/lean-proofs-latest/src/latest/ErdosProblems/Erdos67b/LogElliott.lean:329`:

```lean
def IsMultiplicativeOnPositiveInt (g : ℤ → ℂ) : Prop :=
  g 1 = 1 ∧ ∀ m n : ℕ, 0 < m → 0 < n → g ((m * n : ℕ) : ℤ) = g m * g n
```

**No coprimality hypothesis.**  Despite the name this is *complete* multiplicativity, and
`NonasymptoticLogElliott` (line 411) is stated with it.  `ζ^ω` is not completely multiplicative
(`ω(p²) = 1`), so lap 4 correctly concluded the dependency's `Prop` cannot be applied to the
crux directly — and built `C3MrtOmegaBridge.lean`, the `z^ω = z^Ω ⋆ g` expansion over the
powerful numbers, to get around it.

Everything downstream of that bridge is a consequence of an artificial hypothesis:

* the `D`-fold tuple sum over powerful `d₀,…,d_{D−1}` (`C3MrtMultiForms/Mass/Trunc/Inner/…`);
* `prod_le_lcm_mul_pow`'s `K^{K²}` (lap 37);
* the whole budget repair of lap 40 (`QuantDepthElliottGen`, `budget_absorb_of_tIdx`);
* the "beat every power of `log log N` by a quasi-polynomial margin in `log log log N`" decay
  class, which `PENDING_WORK.md` records as "the sharpest characterisation the campaign has
  produced of the gap to the literature".

**That characterisation is a property of the bridge, not of the problem.**  Elliott's
conjecture, and Tao's Theorem 1.3 which the dependency is formalising, are stated for
1-bounded *multiplicative* functions.  With the literature's own hypothesis class the bridge is
unnecessary and `K^{K²}` never appears.

### 2b.  Tao–Teräväinen arXiv 2512.01739 is about THIS constant, and its Theorem 3.1 is a
strictly better anchor than the dependency's `Prop`

`primeLambertAtBase b = ∑' n, ω(n)/bⁿ` (`PrimeLambertFour.lean:38`) is *verbatim* the constant
of TT Theorem 1.3 (Erdős #69), which they prove irrational for `b = 2` and remark holds for every
integer base `b ≥ 2`, "the case `b > 2` … somewhat easier".  `ConjC3` asks for richness of the
same constant — strictly stronger, same object.

Their Theorem 3.1 (`papers/tao-teravainen-2025-quantitative-correlations.txt:1566`) reads, in the
non-pretentious case:

> Suppose that `g₁, g₂ : ℕ → ℂ` are 1-bounded **multiplicative** functions … `δ_N = 0` … and
> `exp(M(g₁; X², log^{1/125} X)) ≫ L`.  Then there is `E ⊂ [√X, X]` with
> `(1/log X)∫_E dt/t ≪ L^{-c}` such that for any `W ∈ [L^c]` and integers `b, h₁, h₂ = O(L^c)`
> with `h₁ ≠ h₂`,
> `(W/N) ∑_{N<n≤2N} (g₁(n+h₁) − δ_N) g₂(n+h₂) 1_{n≡b (W)} ≪ L^{-c}` for all `N ∈ [√X,X] \ E`.

Compared with `Erdos67b.NonasymptoticLogElliott`, this is better on **four** axes at once:

| axis | dependency `Prop` | TT Thm 3.1 |
|---|---|---|
| multiplicativity | **completely** multiplicative | multiplicative ✔ |
| averaging | logarithmic | **natural** (dyadic block) ✔ |
| saving | `ε · log W`, qualitative | `L^{-c}`, `L ≤ log X` — a **power of log** ✔ |
| progressions | via affine forms only | built in, `W ≤ (log X)^c` ✔ |
| price | — | an exceptional set `E` of scales, log-density `≪ L^{-c}` |

`ζ^{ω_{>P}}` satisfies the hypotheses: 1-bounded ✔; multiplicative ✔ (not completely —
irrelevant here); and `M(ζ^ω; ·)` is the same functional the repo already bounds, because the
pretentious distance depends on `g` **only through its values at primes**, where `ζ^ω` and
`ζ^Ω` agree — so `pretentiousDistSq_ge_class_sum` and the whole archimedean certificate
(`C3MrtArchimedean`, `C3MrtNonPretentious`, laps 18–21) transfer **verbatim**.  With
`D(ζ^ω, χ·n^{it})² ≍ (1 − Re ζ) log log X` one may take `L = (log X)^{c'}`, i.e. a genuine
power-of-log saving — **exactly `budget_absorb`'s hypothesis class `η N ≤ A (log N)^{-a}`**.

### 2c.  And TT say, in the same paper, that the input the current route needs is out of reach

`…:2997`:

> "However, to handle three-point equations such as `ω(n) = ω(n+1) = ω(n+2)` one would require …
> a version of Theorem 3.1 for triple correlations, **which does not appear to be within current
> technology**.  For similar reasons we are currently unable to remove the exceptional set."

The current route needs `KPointLogElliott K` for `K ≍ log log log N`, i.e. *unbounded* order.
The field's own experts flag order **3** as out of reach.  That is not a reason to abandon the
destination — the ratified success criterion is an equivalence, not a proof — but it is a
decisive reason to stop paying `K^{K²}` for it.

## 3. Alternatives, re-costed

**A. Status quo (finish brick 4b + the quantitative restatement).**  1–2 laps.  Yields a clean
ledger `ConjC3 ⟸ quantitative K-point log-Elliott + VK + log→natural`.  Value: *low*.  Every one
of the three inputs is 🔴, two of them are flagged out of reach by TT, and the decay class quoted
as "the distance to the literature" is an artefact of §2a.  **Rejected as the main line** (brick
4b is retained as cheap hygiene, not as the objective).

**B. Re-anchor on TT Theorem 3.1 (CHOSEN).**  State the merely-multiplicative correlation `Prop`
and TT Thm 3.1 faithfully in `src/NormalNumbers/C3Mrt*.lean`; derive the `D = 2` rung from it with
**no** `ω → Ω` bridge and **no** tuple sum.  Immediate consequences:
  * `K^{K²}` and the quasi-polynomial decay class leave the ledger (artefacts, §2a);
  * `LogToNaturalCorrelation` leaves the ledger at `K = 2` (TT Thm 3.1 is natural-density);
  * `Erdos67b.NonasymptoticLogElliott` (🔴 as used) is replaced by a **published** theorem (🟡);
  * the residual `K = 2` debt becomes exactly "remove the exceptional set of scales", which TT
    name and which is *far* smaller than the debt it replaces.
Cost: 3–6 laps.  Nothing is deleted; the K-fold stack stays in `src/`, sorry-free, as the
completely-multiplicative route.

**C. Hunt a two-point-only proof of the whole leaf (TT §5's architecture).**  *Assessed and
rejected this lap* — see `PENDING_WORK.md` "Reflection — 2026-09-25", item **R3**.  TT §5 reduces
the distribution of `∑_h ω(n+h)/2^h` to two-point correlations because their alternating sum over
`ε ∈ {0,1}^K` makes each prime-indexed variable `X_p` mean-zero *and* of variance `O(2^{-K}/p)`,
so the large-prime tail has total variance `O(2^{-K} log log N) = o(1)` and a second moment
suffices.  That variance shrinkage is bought with the *rationality hypothesis* (the dilation
identity `ω(n + ph) = ω(n/p + h) + 1 − 1_{p²|n+ph}` applied at `2^K` distinct primes `p_ε`), which
an unconditional Weyl bound does not have.  Van der Corput does not substitute: differencing
`Φ(n+u)\overline{Φ(n)}` makes `X_p` mean-zero but *doubles* the point count without shrinking the
per-prime variance.  Independently re-derived this lap: a direct moment expansion of `e(hR)` over
primes `> Y` fails at the level-of-distribution barrier (`∑_{p>Y} p·E[w_p] ≍ N/log N`).
**Do not re-chase.**

## 4. Triggers registered for the new route

* 🚦 **C3-T1.**  If `TwoPointNaturalCorrelation` (TT Thm 3.1) cannot be stated in Lean without
  a hypothesis `ζ^ω` provably fails, ESCALATE — the re-anchoring is void and route A returns.
* 🚦 **C3-T2.**  If the `D = 2` natural-density rung is not a theorem on the new anchor within
  **6** grind laps of 2026-09-25, ESCALATE: the bridge-free derivation is not as short as §2a
  predicts and the re-cost was wrong.
* 🚦 **C3-T3.**  If a lap needs `K ≥ 3` correlations *for a step that is not explicitly
  disclosed as the generational item*, that is drift back into route A — stop and re-read this
  file.
