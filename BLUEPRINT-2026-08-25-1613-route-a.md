# Blueprint: Route A -- Vandehey with a compact fiber

**Target** (Vandehey 2017, Compositio 153, Sec.7 problem 1; open):

> `x` CF-normal, `q, r` quadratic irrational, `q != 0`  =>  `qx + r` CF-normal.

Simplest instances `x -> phi*x`, `x -> x + phi`.  This blueprint is the lemma DAG,
written after the 2026-08-25 probe came back green
(`PROBE-2026-08-25-1235-route-a-transducer.md`).  It is a research blueprint, not a
Lean skeleton: several nodes need definitions that do not exist yet, and marking
them as `sorry`-bodied Lean today would be scaffolding around a hole.  Nodes A1 and
A8 are statable in Lean now and are the honest place to start.

## The one-line strategy

Vandehey proves the `q, r` RATIONAL case.  His whole argument rides on the
transducer's state set being **finite**: states are integer matrices with
`|det| = D`, so bounded implies finitely many.  Over `O_K = Z[phi]` that certificate
dies -- Dirichlet gives infinitely many units and `Z[phi]` is dense in `R`.

Route A's bet: **finiteness was a certificate, never part of the dynamics.**  The
emission rule reads only the REAL embedding of the state, which evolves
autonomously; the conjugate place was Vandehey's bookkeeping, not a variable the
transducer consults.  So replace *finite state set* by *compact state space* `W`,
and replace *finite-chain transitivity* by *Doeblin / cone contraction*.  Everything
else in his six sections is either algebraic (carries over verbatim) or a
Riemann-squeeze that was already written in a form tolerant of infinite families.

## The DAG

Status key: **free** = carries over with no new idea · **probe-green** = the
mechanism was measured and is present, proof still owed · **open** = real work ·
**owed-anyway** = a gap in the published proof of Theorem 1.1 itself.

| | node | replaces | status |
|---|---|---|---|
| A1 | transducer identity `Mx = R(w,M) . (U(w,M)(T^|w| x))` | Vandehey Lemma 2.1 + identity (9) | **free** |
| A2 | window lemma: `U(w,M)` lies in a compact `W` of bounded-distortion maps | "entries `<= D` => finite" | **probe-green** |
| A2a | burst bound: digits emitted per step uniformly bounded on `W` | Lemma 2.2 | **probe-green** |
| A2b | positive-cone normalisation | Lemma 2.3 (`[-1;1]`-cancellation) | free |
| A3 | Doeblin condition for the chain on `W` | Sec.4 sink-SCC transitivity, Lemma 4.1 | **probe-green**, and the wall |
| A4 | stationary `rho` on `W`, mutually a.c. with the natural measure | Theorem 3.1 | follows from A3 + compactness |
| A5 | hot-spot criterion **with tightness** | Lemma 3.2 (**false as stated**) | **open, owed-anyway** |
| A5a | empirical measures of a CF-normal point are tight | (absent from the paper) | **open, owed-anyway** |
| A6 | trigger WINDOWS `C_s x U`, `rho(dU) = 0`, Riemann squeeze by `f_j^±` | Lemma 4.3 countable-cylinder Cesaro counting | open, fiddly |
| A7 | `l(n) = c_1 n (1+o(1))`, trigger count `= c_s n (1+o(1))` | Lemmas 6.1, 6.2 | follows from A3-A6 |
| A8 | either-or endgame: `E_M ⊆ E` or `E_M ∩ E = ∅`, `E_M = M(co-null)` has positive measure | Sec.6 assembly | **free**, verbatim for any `M` |

**A8 is why this is worth doing.**  The endgame needs no limit identification: it is
enough that every string appears in `Mx` with *some* limiting frequency independent
of the CF-normal `x`.  That collapses the whole problem onto A2 + A3.

## What the probe settled, and what it did not

Settled, on Gauss-distributed CF input, exact `Z[phi]` arithmetic:

- **A2.** Real-place distortion median 1.038 (first half of a run) vs 0.976 (second
  half), 8 runs x 600 digits, no drift; worst 8.79.  Real-place entries stay `O(1)`
  while the conjugate place reaches `10^644` -- the compact-fiber thesis made
  directly visible.  `r = phi` behaves exactly like `r = 0`, so nothing depends on
  `det` being a unit.
- **A3.** Excursion tail exponential (`P(D > t)` ratio ~0.35 per unit, nothing past
  `t = 7` in 3000 samples), which answers the attack map's worry that excursion
  events are unbounded-rank.  State distribution KS-indistinguishable across four
  initial states from ~60 steps on.

Not settled, and this is the live risk: the probe samples **almost-every** input.
A3 is needed along **arbitrary CF-normal** input, and CF-normality controls
fixed-rank cylinder frequencies while excursions are unbounded-rank.  That gap is
exactly where the attack map put its 35% wall, and no simulation can close it --
it is what `f_j^±` (A6) exists to squeeze.

## The Lemma 3.2 hole, and why A5 is owed either way

Vandehey's Lemma 3.2 proves itself by "a simple consequence of Theorem 1 in [17]",
where [17] is Moshchevitin-Shkredov.  Airey-Mance (arXiv:1912.10265) show that
theorem is **incorrect as stated on non-compact spaces** -- a `lim sup` distributed
over an infinite sum -- and Vandehey applies it on `Omega x M` with a countably
infinite alphabet, where the counterexample lifts verbatim.

Theorem 1.1 is almost certainly still true: Lemma 3.2 is only ever applied at a
CF-normal `x`, and CF-normality forces the empirical measures to be tight, which is
precisely the hypothesis Airey-Mance add in their Theorem A.  But that argument is
**nowhere in the paper**.  So A5 + A5a are owed by anyone formalizing Sec.3 at all,
Route A or not -- including the "formalize Vandehey" target already on the shelf.

## Lean staging

- **Now.** A1 and A8 are statable against the existing `CFCylinder` / `CFDigitLaw`
  stack; A8 in particular is a clean measure-theoretic statement with no new
  definitions.  A5a sits directly on our `Pillai.lean` / digit-law machinery.
- **Needs new definitions.** A2 and A3 require a distortion functional on
  `PGL_2(R)`, the compact window `W`, and the Hilbert projective metric with
  Birkhoff-Hopf contraction.  A grep of the local mathlib clone (pin
  `leanprover/lean4:v4.33.1`) turned up no `Hilbert projective` / `Birkhoff-Hopf`
  hits, but that is one instrument on one pin -- verify against the current master
  and `docs/1000.yaml` before concluding it must be built here.
- **Sizing.** The attack map's estimate stands: months-scale, paper-sized.  The
  probe moves `P(program closes it)` up from ~50%, and moves the risk mass from
  "the mechanism is not there" onto A3-along-arbitrary-input.

## What would kill it

A3 failing for arbitrary CF-normal input while holding a.e. -- i.e. a CF-normal `x`
whose excursion structure defeats uniform merging.  That is a *constructible* target:
if someone wants to refute Route A cheaply, build such an `x` from a sparse sequence
of enormous partial quotients that is still CF-normal.  Worth one afternoon of
adversarial thought before committing months.
