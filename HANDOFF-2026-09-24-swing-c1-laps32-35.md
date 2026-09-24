# Handoff — swing at C1, laps 32–35: the swing's conditional theorem is PROVED

**Branch** `wip/swing-c1` · **HEAD** `5310aed` · tree clean, NOT pushed
**Build**: full `lake build` green, **9186 jobs**.
**Objective**: `KICKOFF-2026-09-24-swing-c1.md` (supersedes `DIRECTION.md` and older handoffs).

## The headline of this session

```lean
theorem conjC1_of_delange_katai_decouple
    (hDK : KataiOrthogonality)                    -- KNOWN (Kátai 1986 / Daboussi–Delange 1974)
    (hD  : ∀ b ≥ 3, ∀ m ≠ 0 with b ∤ m, DelangeMean (m/b))   -- KNOWN (Delange 1969)
    (hDc : ∀ b ≥ 3, ∀ m ≠ 0 with b ∤ m, ∀ p ≠ q prime, PairDecouple b p q (m/b)) :
    ConjC1
```
Sorry-free, `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
This is the KICKOFF's stated main target: a conditional `conjC1_of_H` with `H` precise and
literature-checkable.  **`PairDecouple` is the only open input.**

`SwingC1.lean` still has exactly its two ratified `sorry`s (`hDepthAll` l. 920,
`hAutoCorrAll` l. 2201) per the kickoff addendum.  Nothing was deleted, renamed or weakened.

## New files (all additive, all sorry-free)

| file | content |
|---|---|
| `SwingC1Pair.lean` (completed) | `norm_pairLocalFactor_le` PROVED; `sum_pairTerm_period` |
| `SwingC1Katai.lean` | `KataiOrthogonality`, `PairDecorr`, `shiftIndep_of_pairDecorr` |
| `SwingC1Head.lean` | `weylMean_tendsto_zero_of_head` — the crux, route-independently |
| `SwingC1Weyl.lean` | the wiring: `conjC1_of_delange_katai` |
| `SwingC1Decouple.lean` | leaf (D) split: `conjC1_of_delange_katai_decouple` |

## Lap by lap

**lap 32 — `norm_pairLocalFactor_le` PROVED.**  Residue pigeonhole `exists_pair_residue`: for `r`
prime large, some `j ∈ [i, 2i+2]` has `q p⁻¹(r−1−j)` outside the top block `[r−i, r−1]` (window
`i+3`, bad set `≤ i`).  Corrects lap 31's count, which asked for `c_j ≤ r−2−J` and so had a bad
set growing with the window.  Separation is uniform in `r` because the `s = 0` summand is
EXACTLY `1`: `|arg| ∈ [A, B]` with `A = |t|/(2b^{1+J}) > 0`, `B = 2|t|/b^{1+i} ≤ 1/4` fixed, and
`‖e(x) − 1‖ ≥ |sin 2πx| ≥ sin 2πA =: δ`.  Hence `‖pairLocalFactor‖ ≤ 1 − (δ²/4)/r`, Mertens
finishes.  **The pair side is now unconditional.**

**lap 33 — `ShiftIndep` → `PairDecorr`.**  `KataiOrthogonality` and `DelangeMean` as named known
theorems; `phase_omegaNat_multiplicative`; `tendsto_fullMean_shift`.  Also `sum_pairTerm_period`:
the pair difference has EXACTLY zero drift over a full period (the single tail's drift is the
divergent Mertens sum).  **Refuted, with numbers**: prime truncation cannot close `PairDecorr`
(tail mean is `o(1)` only for cut `y = N^{1−o(1)}`, the primorial period needs `y ≤ log N`), and
zero drift does not rescue it (the variance still diverges like `log log N`).

**lap 34 — the wiring.**  Audit finding: `weylMean` appeared only in my own files, so the whole
chain was DANGLING.  Closed via `weylMean_eq_fourierMean` (integer frequency ⇒ the repo's
`fourierMean`), `weylMean_mul_b` (a frequency divisible by `b` peels off an INTEGER `ω`-digit, so
it merely shifts the orbit — this is why the hypotheses need only hold for `b ∤ m`, exactly where
Delange's theorem is true), and `hWindowChar_of_equidistributed` (the window character sum is a
step function of the orbit point; `Σ_{v<b^L} ζ_{b^L}^{av} = 0`).

**lap 35 — leaf (D) split.**  `pairDecorr_of_pairDecouple`: at cut `P`, `A` is exactly
primorial-periodic, `B` is the large-prime remainder, and `‖mean AB‖ ≤ ‖periodMean A Q‖ +
pairDefect`, the first term PROVED to vanish.  Ragged `N` via `norm_fullMean_le_of_mul`.
**Refuted**: `hAutoCorrAll` (fixed modulus `b−1`) is a weaker STATEMENT but not a cheaper TARGET
— casting out `b−1` makes `corrSum b j L N = mean_n ζ_{b−1}^{j⌊b^L u_n⌋}`, the Cesàro mean of a
step function of the orbit point, so any Fourier route needs all frequencies, as normality does.
(That also explains the `b^{−L}`: `b ≡ 1 mod b−1` makes the step function's integral `b^{−L}`.)

## THE next move (start here)

**`PairDecouple b p q t`** (`SwingC1Decouple.lean`) is the sole open input.  Probes, in order:

1. **Iterate the split.**  Expand `B` itself by the prime-periodic form and apply
   `norm_fullMean_mul_le_periodMean_add_defect` a second time at a higher cut `P'`.  That turns
   the defect at cut `P` into a defect at cut `P'` plus a product of local factors over
   `(P, P']`, which also → 0.  If the iteration telescopes, the defect is controlled by a limit
   of products over disjoint prime ranges.  **This is the one genuinely new idea available.**
2. Second moment / large sieve on `Σ_{c<Q} ‖progMean B Q R c − fullMean B‖²`; the frequencies are
   `a/Q` with `Q ≫ N`, which is where the obstruction bites — record the exact failure regime.
3. Do NOT attack Selberg–Delange or the Kátai criterion inside this swing; they are named known
   theorems and formalizing either is a separate mathlib-scale project.

## Standing constraints (unchanged)

* Do not edit `CastingOut.lean`, `CastingOutCount.lean`, `CastingOutLambert.lean`, `Maze.lean`,
  `papers/`, `agent-mail/`, other KICKOFFs.  Work in `src/NormalNumbers/SwingC1*.lean`.
* `hDepthAll` and `hAutoCorrAll` stay as `sorry`s in `SwingC1.lean` until proved.
* Never use `axiom`; named hypotheses are the sanctioned device.
* ⚠️ The `SwingC1Weyl` route proves NORMALITY of `G₄_b`, strictly stronger than `ConjC1`; lap 35
  showed the weaker leaf is not a cheaper target, so this costs nothing, but keep it recorded.
* Build note: system-wide fd exhaustion from OUTSIDE this container blocked `lake build` for
  ~45 min in lap 33 (`/proc/sys/fs/file-nr` above 300k with no local process over 100 fds).
  Environmental, not a code defect — see the reference corpus leaf
  `lean-box-fd-exhaustion-is-mmap-not-nofile.md`.  Retry; it clears.
* `PENDING_WORK.md` carries the per-lap record including all four refutations.
