# HANDOFF — entropy lap 21 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`, HEAD `543b6ed`.  `lake build` green, **8960 jobs**.  New module
`src/NormalNumbers/G4EntropyPrecision.lean`, sorry-free, trust triple.

## What was proved

`exists_qVal_eq_orbit_ne` — a quantized sampler whose windows have upper density `< 1`
determines **no** orbit value: for every time `r` there are `x, y ∈ [0,1)` with
`qVal W x = qVal W y` (identical sample at every index) and `{2^r x} ≠ {2^r y}`.

Witness: `x = 0`, `y = 2^{-(j+1)}` (the single-spike real `spikeReal j`) for an unread `j ≥ r`,
which exists by `exists_not_mem_of_density_eventually`.  The sample values agree because the
digits agree off `{j}` and `j` is unread; the orbit points differ because `digitOf_orbit` turns
digit `j - r` of `{2^r ·}` into digit `j` of the real, which is `0` versus `1`.

`Sched.exists_sample_eq_orbit_ne` is the instance at the implemented schedule (`≤ 1/4`).

## The three-way picture (laps 19–21)

1. one unquantized orbit value `{2^r x}` ⟹ forces normality (lap 19);
2. a quantized sampler forces normality **iff** its windows have density one (lap 20);
3. a quantized sampler of density `< 1` never determines any orbit value (lap 21).

Together: the entropy route did not fail because its statistic was too weak a hypothesis; it
failed because the quantizer discards precisely the object — a single orbit point — that the
transfer needed.  That is the sharpest form of the brief §6 answer the interface can carry.

**Honest scope.**  Lap 21 is about *exact* determination.  The two witnesses differ by
`2^{-(j+1)}`, so the sample does approximate `{2^r x}` when the windows are long; lap 20 is what
rules out the approximation route (only the density of the union of windows matters).

## Next bounded test

Candidates, none of which is a repair of this route:

1. **Quantitative precision at the implemented schedule.**  Strengthen lap 21 from `≠` to a
   lower bound: at the schedule the sampled positions near a given `r` are spaced `≥ 2·d_min`
   apart, so an unread `j` can be found within `O(1)` of `r`, giving `|{2^r x} − {2^r y}| ≥ 2^{-t}`
   for an explicit `t`.  Needs a "gap" lemma about `sampledPosAt` (positions are `≡ 0 mod 2 d_α`
   up to the window length), which `G4EntropyPositions` nearly has.
2. **A non-sampling route.**  Anything that reads `x` through an unbounded-precision functional;
   the `G4Jackson` / `G4SeparatingTest` layer is the repo's instance.  This is a new campaign,
   not a lap.
3. **Altitude.**  `DIRECTION.md`'s CURRENT DIRECTIVE and `STATUS.md` still describe `T_E` as the
   open objective and are four laps behind the mathematics (laps 16–21 are not reflected).  They
   are owned by review laps; a grind lap must not edit them.
