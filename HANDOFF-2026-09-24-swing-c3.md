# HANDOFF 2026-09-24 — swing at C3 (branch `wip/swing-c3`)

Kickoff: `KICKOFF-2026-09-24-swing-c3.md`.  Target file `src/NormalNumbers/SwingC3.lean`
(+ helpers `SwingC3Digits.lean`, `SwingC3Carry.lean`, `SwingC3Split.lean`).
`lake build NormalNumbers.SwingC3` green throughout; **one** `sorry` in `src`.

## What the crux IS now

`largeTailLaw_holds` in `SwingC3.lean`.  Everything else on the path to `ConjC3` is proved.
The live attack is the **rotation route**, and its single open input is

> **`OmegaLargeDecouple`** — the limit law of `fract (tailLarge P b n)` along `n ≡ a (mod Q)`
> exists and is independent of the class `a`.

Status: **open, but sieve-grade, not Selberg–Delange-grade.**  It is a decoupling statement
(fundamental lemma of the sieve / Kubilius model), not a statement identifying any law.

## The chain in `src` (all proved except the last line)

| piece | where | status |
|---|---|---|
| `digitOf b (fract G_b) n = (ω(n+1) + omegaCarry b (n+1)) % b` | `SwingC3Digits` | proved |
| `omegaCarry_succ`: carry recursion `(ω(k+1) + c(k+1)) / b` | `SwingC3Carry` | proved |
| `tailB_le_log`, `omegaCarry_sandwich_log`: carry is an `O(log_b log k)`-window functional | `SwingC3Carry` | proved |
| `tailB_eq_small_add_large`, `tailSmall_congr`: tail splits, small half `Q`-periodic | `SwingC3Split` | proved |
| `orbit_eq_fract_tailB`, `orbit_eq_rotation`: orbit `= fract(θ(a) + tailLarge)` | `SwingC3Split` | proved |
| `exists_crt_pattern`: CRT steering of `θ(a)` | `SwingC3Split` | proved |
| `fract_add_mem_cylinder_iff`, `exists_shift_mem_cylinder`: rotations cover the circle | `SwingC3Split` | proved |
| `card_occ_ge_of_effDisj`, `isRich_of_effDisjRate` | `SwingC3` | proved (route refuted, see below) |
| `occursAt_primeLambertAtBase_iff`, `isRich_of_omegaCarryRich`, `omegaCarryRich_of_joint` | `SwingC3` | proved |
| `sum_rotate`, `isRich_of_largeTailLaw`: `LargeTailLaw b → IsRich b G_b` | `SwingC3` | proved |
| `largeTailLaw_holds` | `SwingC3` | **sorry** |

## The argument, end to end

A word `w` of length `ℓ` occurs at `n` iff the orbit point lies in `w`'s cylinder `I_w`
(length `b^{−ℓ}`).  Along `n ≡ a (mod Q)`, `Q = ∏_{p ≤ P} p`, the orbit point is
`fract(θ(a) + tailLarge P b n)` with `θ(a) = tailSmall P b a` constant on the class.  Let `μ` be
the limit law of `fract(tailLarge)`.  Then the density of occurrences of `w` is
`(1/Q) ∑_a μ(I_w − θ(a))`.  `exists_crt_pattern` makes `θ(a)` run over all `b^ℓ` multiples of
`b^{−ℓ}`; `exists_shift_mem_cylinder` says those translates COVER the circle; so the sum is
`≥ μ(circle) = 1` and the density is `≥ 1/Q > 0` — **for every `w`, with no knowledge of `μ`.**
Covering, not partition, is what is needed: a sum of masses dominates the mass of the union.

## Next lap

1. **The `θ` bookkeeping** (identified, not yet done).  `θ(a)` is steered only through the head
   `∑_{j ≤ ℓ} ω_{≤P}(a+j) b^{−j}`; slots `j > ℓ` contribute an uncontrolled `O(π(P) b^{−ℓ})`,
   comparable to the cylinder.  Fix: prescribe `ℓ' > ℓ` slots and fix `a` modulo `∏_{p ≤ ℓ'} p`
   so the primes too small to steer contribute a constant offset.  Then the uncontrolled
   remainder is `< b^{−ℓ}`.
2. **State `OmegaLargeDecouple` in Lean** as: for every `ℓ, w < b^ℓ, a`, the counting ratio
   `#{n < N : n ≡ a [MOD Q] ∧ fract(tailLarge P b n) ∈ I_{ℓ,w}} / N` converges to `μ ℓ w / Q`
   with `∑_{w < b^ℓ} μ ℓ w = 1`.  Genuine limits (not liminf) are required: with liminf only,
   mass can slosh between classes and `∑_k liminf` need not reach `1`.
3. `LargeTailLaw` is now STATED in Lean and `isRich_of_largeTailLaw` is PROVED, so `conjC3`
   routes through it and the only remaining obligation is `largeTailLaw_holds`.  Producing it
   means: build the classes with `exists_crt_pattern` (with the `θ` bookkeeping of item 1) and
   supply the limit law — the genuinely analytic step.

## Refuted routes (do not re-try)

- **Effective disjunctivity.**  `card_occ_ge_of_effDisj` is sharp: the amplification needs the
  de-Bruijn-like rate `N(b,L) = O_b(b^L)`; a rate `C·L·b^L` (what a random sequence has) gives
  occurrence density `≍ 1/L → 0`.  `probes/g4_first_occurrence.py`: `N(4,L)/4^L =
  7.2, 411, 288, 451, 747, 930, 952` for `L = 1..7` over `2·10⁷` digits — still climbing, two
  orders above the coupon-collector value `L·log 4`.  G₄ is not de-Bruijn-efficient.
- **Exact prescription of `ω` on a window.**  Landau: `#{n ≤ N : ω(n) = k} ∼
  N (log log N)^{k−1}/((k−1)! log N)`, so every exact value of `ω` has density zero.
- **A statement about `ω mod b` alone.**  The carry recursion `(ω + c)/b` reads `ω div b`.
- **Sharpening the §5 schedule.**  `isDisjunctive_base` is contradiction-from-total-omission
  (omission enters only via `exists_cover_of_omit`), so it certifies ONE occurrence, inside the
  window `Mx ≈ 2^{33856 ℓ² b^{2ℓ+2}}`.  `K` is forced large by `hbudget`/`hbig`.  No density is
  recoverable from it.

## Probes

- `probes/g4_word_density.py` — base-4 digit frequencies of G₄ drift `0.088 → 0.114 → 0.145`
  (digit 1) at `N = 2·10⁵, 10⁶, 5·10⁶`, i.e. toward `1/4` at the Erdős–Kac rate
  `(log N)^{−π²/8}`.
- `probes/g4_first_occurrence.py` — the horizon table above.
- `probes/g4_rotation_route.py` — **confirms the rotation mechanism**.  The globally rare word
  `(1,1,1,1)` has frequency `2.3·10⁻⁴` (uniform would be `3.9·10⁻³`) but reaches `7.5·10⁻³` in
  the best class mod `Q = 5005`, `33×` global and above uniform.  The boosting classes are
  exactly those with elevated `ω_{≤P}` at the FIRST TWO window positions — the `b^{−j}`
  weighting visible in the data.
