# Handoff — swing at C1 (natural density), laps 1–6

**Date**: 2026-09-24 · **Branch**: `wip/swing-c1` · Kickoff: `KICKOFF-2026-09-24-swing-c1.md`
**File**: `src/NormalNumbers/SwingC1.lean` · full `lake build` green (9176 jobs)
**Open obligations in the file**: exactly two — `hTruncDecayAll` (Leaf A, the Elliott core) and
`hCarryOverflowAll` (Leaf B, carry overflow).  The count went 1 → 2 by DECOMPOSITION, which is the
kickoff's definition of progress.

## What the crux IS now

```
conjC1            (ratified statement, kept per the kickoff addendum)
 ← hState              HState            (digit-free density form)
 ← hWindowAll          HWindow b L       (equidistribution of the window value mod b^L)
 ← hWindowCharAll      HWindowChar b L   (Weyl form)
 ← hWindowChar_of_leaves:
      hTruncDecayAll       HTruncDecay b L     ← SORRY (Leaf A: FINITE-window joint
                                                 equidistribution of ω(n+1),…,ω(n+L+K))
      hCarryOverflowAll    HCarryOverflow b L  ← SORRY (Leaf B: SOME depth profile κ n → ∞
                                                 makes the truncation wrong on a null set)
```
`norm_windowCharSum_sub_trunc` is the glue: `‖charSum − charSumTrunc‖ ≤ 2·badCount/N`.

`HWindowChar b L`: for every `b ≥ 3`, `L`, and every `0 < a < b^L`,

    (1/N) Σ_{n<N} ζ^{ a·( Σ_{i<L} ω(n+1+i)·b^{L−1−i} + c_{n+L} ) }  →  0,     ζ = e^{2πi/b^L},

with `c_N = ⌊Σ_{k≥1} ω(N+k) b^{−k}⌋`.  No digits, no floor of `bᴺ·x`, no real number except the
carry.  Everything above this line is machine-checked with
`axioms = [propext, Classical.choice, Quot.sound]`.

## The five things proved, in dependency order

1. **`castFreq_eq_stateFreq` / `conjC1_iff_hState`** — the C1 counting function EQUALS (for every
   `N`, not asymptotically) the frequency of `n` with
   `Σ_{m∈(n,n+L]} ω(m) + c_{n+L} − c_n = r` in `ZMod (b−1)`.  Exact reduction, both directions.
2. **`omegaCarry_rec` / `omegaCarry_eq_windowVal_div`** — `c_n = (Σ_{i<L} ω(n+1+i) b^{L−1−i}
   + c_{n+L}) / b^L` (integer division).  The digit sequence of `G4_b` is the `ω` sequence run
   through ordinary right-to-left carrying.  `L = 1` is the plain recursion.
3. **`castState_eq_windowVal_emod`** — `castState b L n = (omegaWindowVal b L n mod b^L) mod (b−1)`.
   The unbounded part of the carry is `b^L·c_n`, and `b^L ≡ 1 (mod b−1)` annihilates it.
4. **`stateLaw_of_hWindow`** + **`normalCastLaw_eq_residue_count`** — the model lemma, with no
   error term.  The "normal" target law is just `#{v < b^L : v ≡ r (mod b−1)}/b^L`; casting out
   nines converts the word count into an interval count.
5. **`hWindow_of_hWindowChar`** + **`sum_zetaRoot_zpow`** — self-contained finite Fourier on
   `ZMod b^L` (orthogonality via `geom_sum_eq` + `Complex.exp_eq_one_iff`).

## Two findings that correct the kickoff

**(a) No growing truncation depth is needed for the mod-(b−1) reduction.**  The kickoff's step 1
worried that `ω ≈ log log N` unbounded forces `K = K(N) → ∞`.  For the reduction to `HState` that
is false: item 3 kills the whole unbounded part identically.  `K = L`, `Q = b^L` suffice, and the
conditioning is bounded.

**(b) It IS needed one level down, mod b^L, and the required depth is now explicit.**
`omegaCarry_eq_trunc_add`:  `c_N = H_K(N)/b^K + c_{N+K}/b^K + e`, `e ∈ {0,1}`,
`H_K(N) = Σ_{i<K} ω(N+1+i) b^{K−1−i}`.  Hence `omegaWindowVal_sub_trunc_le_one`: as soon as
`b^K > c_{n+L+K}` (size `≈ log log n/(b−1)`, so `K ≳ log_b log log n`), the window value equals its
FINITE-window truncation `windowValTrunc b L K n` — a function of `ω(n+1), …, ω(n+L+K)` alone —
up to a single unit.

## Literature status of the leaf (kickoff step 4)

* The **one-coordinate marginal is KNOWN**.  Delange (1969) characterises when an additive `g` is
  uniformly distributed mod `q`: it is iff `Σ_{p : d ∤ g(p)} 1/p = ∞` for every divisor `d > 1` of
  `q`.  For `g = ω` we have `g(p) = 1`, so every `d > 1` fails to divide it and the sum is
  `Σ_p 1/p = ∞`.  **`ω` is uniformly distributed mod `q` for every `q ≥ 2`.**
* The **joint version over the shifts `n+1, …, n+L+K` is the open part** — Elliott-type.  Note the
  relevant character is at a RATIONAL frequency `a/b^L`, so the Kátai-style results for
  `(αΩ(n), βΩ(n+1))` u.d. mod 1 (which need `α, β` irrational) do not apply; the rational case is
  exactly the residue-class case, where only Delange's one-coordinate theorem is available.
* Verdict: **open**, and specifically an asymptotic-independence statement, not a new estimate.

## REFUTATION (lap 8): the constant-depth truncation is FALSE

The first draft of Leaf B asked for a CONSTANT depth `K` with bad-set density `≤ ε`.  That is
false.  By `omegaWindowVal_eq_trunc_add` the depth-`K` truncation is off by
`c_{n+L+K}/b^K + e`, and `c_N ≈ log log N/(b−1) → ∞`; so for every fixed `K`, `c_{n+L+K}/b^K ≥ 1`
for almost all `n`, the truncation fails at almost every `n`, and the bad-set density tends to
**1**, not 0.  Both leaves are therefore stated with a DEPTH PROFILE `κ : ℕ → ℕ`, `κ → ∞`
(`κ n ≳ log_b log log n` is what the estimate asks for); `windowCharSumTrunc` and
`carryBadCount` now take `κ` rather than a constant.  The window at `n` is
`ω(n+1), …, ω(n+L+κ n)` — still local, but of slowly growing length.

## Exact next moves

1. The structural slack to exploit: `ω(n+L)` enters the exponent with coefficient `b^0 = 1`, while
   `c_{n+L}` depends only on `ω` at arguments `> n+L`.  So the `a`-th character sum is a twist by
   `ζ^{a·ω(n+L)}` against a factor measurable in disjoint arguments.  Formalise
   `HWindowChar b L ⟸ (Delange for ω mod b^L) + (asymptotic independence of ω(n+L) from the rest)`.
2. Make the finite-window reduction quantitative: bound
   `|windowCharSum − windowCharSumTrunc| ≤ 2·density{n : H_K(n+L) mod b^K ≥ b^K − c_{n+L+K}}`.
   The bad event is exactly where the `e ∈ {0,1}` of `omegaCarry_eq_trunc_add` equals 1, and its
   density is `≈ c_{n+L+K}/b^K → 0`.  That leaf is strictly more elementary than `hWindowCharAll`.
3. Do NOT re-attack `conjC1` via normality: `conjC1_conjC3_of_normal` in `CastingOut.lean` already
   records that route, and normality of `G4_b` is the repo's own open headline.
