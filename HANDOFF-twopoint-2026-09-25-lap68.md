# HANDOFF twopoint — lap 68, 2026-09-25: **the link — TT2025 (5.5) is a DILATION, and the repo already owned (5.2)**

Branch `wip/twopoint-avg`.  Full `lake build` green (**9306 jobs**).  All new declarations
`#print axioms`-clean.  **No `sorry`.**  New file `src/NormalNumbers/TwoPointC3Link.lean`;
no frozen file touched.

## The inventory hit (the standing rule earning its place)

Before writing any arithmetic I grepped `src/` for the §5.1 dilation identity, as the standing rule
demands.  **It was already there**, from the G4 entropy campaign, in *general dilation* form, and
nothing in the C3 ladder had ever consumed it:

    G4.dilatedTailB_eq (hb : 2 ≤ b) (d k) (hd : d ≠ 0) :
        dilatedTailB b d k = tailB b k + ω(d)/(b−1) − corrB b d k

**That is TT2025 (5.2).**  The dictionary: the paper's `δ_p(n)` is the repo's `corrB b p`; the
paper's `q·∑_h 2^{−h} = q` term is the repo's `ω(d)/(b−1)`; and the paper states (5.2) *mod 1*
(because it argues by contradiction from `q·G ∈ ℤ`) whereas the repo's is an identity in `ℝ` —
strictly more information, for a general `d` rather than a prime.  A fourth inventory near-miss
avoided; the rule is now three-for-three this session.

## The advance

The gap my lap-67 handoff named — the crux has one argument `n`, the §5.2 alternating sum has `2^K`
shifted arguments `n + r_{S,h}` — is closed, and the answer is that TT2025 (5.5)'s congruence *is*
a dilation:

    altShift_eq_mul :  n − ∑_{k∈S}(k+1)v_k = p_S·m  →  n + r_{S,h} = p_S·(m + h)

with `p_S := p₀ + ∑_{k∈S} v_k` (the paper's `p_ε`).  Pure `ℤ` algebra: **no primality, no
positivity**.  So each of the `2^K` shifted tails is a *dilated* tail, and `dilatedTailB_eq`
applies to each.  Then:

* `altSum_const_eq_zero` — the alternating sum of a constant vanishes once `K ≥ 1`
  (a one-line instance of lap 66's engine with a constant shift).
* **`altSum_dilatedHead_eq_zero`** — (5.8) in the dilated vocabulary: for arbitrary `p₀, v, m`
  satisfying the congruences, `∑_S (−1)^{|S|} ∑_{h=1}^{K} ω(p_S(m_S+h))·b^{−h} = 0`.
* **`altSum_dilatedTail_eq`** — (5.8) in full: for `p_S` all prime and `K ≥ 1`,

      ∑_S (−1)^{|S|} dilatedTailB b (p S) (m S)
        = ∑_S (−1)^{|S|} tailB b (m S)  −  ∑_S (−1)^{|S|} corrB b (p S) (m S) ,

  the `ω(p_S)/(b−1) = 1/(b−1)` term cancelling against the alternating sign.  This is the paper's
  *"the alternating sum of the tails is the alternating sum of the `δ`s"* — with the integer part
  `tailB` kept explicit instead of discarded mod 1.  Primality is used **only** to evaluate
  `ω(p_S) = 1`.

## Ladder state — the whole §5.2 mechanism is now in the kernel

| piece | statement | commit |
|---|---|---|
| rung 0 | `isRichSubpoly_of_weylTailAlmostAll` | `6978dd5` |
| rung 1 | `addCharTail_depthOne` | `29a4d7d` (lap 61) |
| rung 2 | `tendsto_mean_tailLarge_atTop` | `81606d2` |
| rung 3 | `addCharTail_iff_depthWeighted`, `no_constant_depth_budget`, `..._of_budget` | `f7f8d1c` |
| 3′ | `peelBudget_id`, `tailLarge_le_log` | `7021f54` |
| 3″ | `altSum_depthHead_eq_zero` (§5.2 cancellation) | `2e4ee6b` |
| 3‴ | `altSum_bound`, `altSum_bound_three` (the price; `b ≥ 3` earned) | `4e85afd` |
| link | `altShift_eq_mul`, `altSum_dilatedTail_eq` (§5.5 + §5.2 = (5.8)) | this lap |

## NEXT SESSION

1. **The sieve input, and it is the only remaining half of §5.2.**  Everything above holds for
   *arbitrary* `p₀, v`; the paper needs `p_ε = p₀ + ∑ε_kv_k` **simultaneously prime for all `2^K`
   values of `ε`**, plus the congruence (5.5) solvable — the latter is CRT once the `p_ε` are
   distinct primes, and `SwingC3Mean.lean`'s `primePeriod` is the right vocabulary.  Simultaneous
   primality of a `K`-dimensional affine cube of integers is a Brun/Selberg statement; check
   `master`'s `KICKOFF-brun-*` and `PairDecoupleBand.lean` before deriving anything.  **Do not
   assume it is hard: for a FIXED `K` it is a bounded-length prime constellation, so a sieve upper
   bound suffices to run the argument for infinitely many `p₀`.**
2. **The adjacent unconditional item** `SwingC3Signed.lean` names and nobody did:
   `∏_{P<p≤K} ‖primeFactor b p h‖ → 0` (one-term bound into `norm_primeFactor_sq_le`, then
   `mertens_lower`).
3. **Harden rung 0**: derive `ScalesDense` from a log-density hypothesis on the exceptional set.
4. **Cross-campaign audit, since this lap found another one.**  `G4Transport`/`G4RemainderW` hold a
   whole transport calculus (`tailB_eq : tailB b k = b^k·G_b − integer`, `corrB`, `dilatedTailB`,
   `overlap`) that the C3 ladder has now touched for the first time.  `tailB_eq` in particular says
   the tail IS `b^k G_b` mod integers — the exact object the irrationality route needs.  Read
   `G4Transport.lean` and `G4EntropyTransport.lean` end-to-end before the next new file.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3% (untouched, as ratified).
- `WeylTailHypothesis` TRUE 97%; provable at every scale with known techniques 8%.
- `WeylTailAlmostAll` from 2026 literature 70%; ⇒ `IsRichSubpoly` **in the kernel**.
- §5.2 mechanism (cancellation + price + link + (5.8)): **in the kernel**, sieve input excepted.
- The sieve input reachable in this repo: **40%** (new estimate; it is a fixed-`K` constellation
  count, not a growing-`K` one, which is much weaker than it first looks).
