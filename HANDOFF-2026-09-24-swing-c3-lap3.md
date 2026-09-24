# HANDOFF 2026-09-24 (lap 3) — swing at C3, branch `wip/swing-c3`

**Checkpoint.**  `lake build` green, 9184 jobs.  `src/` holds **1** swing `sorry`
(`tailLargeDecouple_holds`, `SwingC3Rotation.lean`) plus the 2 designated-open off-campaign ones
(`PrimeLambertOscillation`, `MahlerDriftOne`) — do not touch those.

Obey `DIRECTION.md` → CURRENT DIRECTIVE (swing-c3), then
`KICKOFF-2026-09-24-swing-c3.md`.  Previous: `HANDOFF-2026-09-24-swing-c3-lap2.md`.

## This lap

### 1. Leaf A PROVED — `src/NormalNumbers/SwingC3Cover.lean` (new, sorry-free)

`exists_rotationCover` is discharged; `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
The assembly of the six `SwingC3Net` pieces:

* `sum_digits_eq` / `sum_digits_reflect` / `sum_digits_real` — base-`b` expansion in the
  most-significant-first slot order, both as a ℕ identity (used for injectivity mod `Q`) and as
  the real grid identity `∑_{i<L} d_i b^{−(i+1)} = k·b^{−L}`.
* `exists_L_growth` — `∃ L, b·L + 2 < len·b^L` (via `tendsto_pow_const_div_const_pow_of_one_lt`).
* `slotConst`, `exists_steered_class` — primes `≤ L+1` pinned by `a ≡ 0 [MOD R]` (`R` the
  primorial of `L+1`), primes in `(L+1,P]` distributed to window slots by
  `exists_slot_assignment`; gives `ω_{≤P}(a+j) = slotConst(L+1,j) + d_{j−1}` for `1 ≤ j ≤ L`.
* `exists_rotationCover_core` — `W = L+1`, `K = (b−1)L`, minimal `P` with exactly `K` primes in
  `(W,P]` so `π(P) ≤ bL+1`; head `= C + k·b^{−L}`, remainder `ρ_k ≤ π(P)b^{−L}/(b−1)`, and
  `1/b^L + ρ ≤ (bL+2)/b^L < len` makes the perturbed grid a `len`-net.  Distinctness mod `Q` is
  free from `Q`-periodicity of `ω_{≤P}`.

### 2. B5 REFUTED — `src/NormalNumbers/SwingC3B5.lean` (new, sorry-free)

`not_orbitDecouple_periodicWitness (hb : 2 ≤ b) (hQ : 2 ≤ Q) : ¬ OrbitDecouple b Q (1/(b^Q−1))`,
trust-triple clean, with `tailLargeDecouple_iff_orbitDecouple` anchoring `OrbitDecouple b Q (L_P)`
to Leaf B.

*The argument.*  `y_{n+1} = fract(b·y_n)` forces `ν^{(r+1)} = T_*ν^{(r)}` for the class-`r`
empirical measures, so any weak-`*` limit has `λ_r = T_*^r λ_0`, `λ_0` is `T^Q`-invariant, and
`∑_r λ_r` is automatically `T`-invariant.  Leaf B is *exactly* `λ_0` being `T`-invariant, which
`T^Q`-invariance does not give.  The gap is realised by a real orbit: for `x = 1/(b^Q−1)`,
`orbit b x n = x·b^{n mod Q}` (`orbit_periodicWitness`), the orbit is periodic of period `Q`, the
arc `[x, x·b)` is hit exactly on `n ≡ 0 (Q)`, and along `N = Q·m` the decoupling defect is the
constant `(1 − 1/Q)/Q ≠ 0`.

**Consequence for the route:** the orbit relation contributes nothing beyond `λ_r = T_*^r λ_0`.
Any proof of Leaf B *must* use arithmetic of `ω_{>P}`.  B5 is dead; B2/B3/B4 are live.

## What the crux IS now

**Leaf B, `tailLargeDecouple_holds`** — the sole remaining swing obligation, and `conjC3` rests
on it alone.  Equivalent forms now in `src/`:
`TailLargeDecouple b P Q` ⟺ `OrbitDecouple b Q (largeLambert P b)` ⟺ every weak-`*` limit of the
class-`0 (mod Q)` empirical measures of the `×b` orbit of `L_P` is `×b`-invariant.

### Attack list (updated; `PENDING_WORK.md` is authoritative)
- **B2 (one-sided suffices).**  `density_lower_of_decouple` only consumes `A_k ≥ B_k/Q − o(N)`.
  Weaken `TailLargeDecouple` to the liminf form and see whether the arc-boundary term vanishes.
- **B3 (bounded surrogate) — highest value.**  Replace `ω_{>P}` by a bounded read, prove
  decoupling exactly (finite-dimensional CRT), and price what the surrogate costs the covering.
- **B4 (refutation probe).**  Numeric class-dependence of `orbit L_P` histograms, `b = 4`,
  small `P`.  A visible persistent dependence REFUTES the route — first-class deliverable.
- **B5.**  ❌ refuted this lap, see above.  Do not retry.

### The obstruction, re-derived independently this lap
Truncating the primes at `K` makes the pattern exactly CRT-periodic only at modulus
`∏_{P<p≤K} p ≈ e^K`, so the fundamental lemma needs `K ≲ log N`; but the expected weight of the
discarded tail is `E[∑_j ω_{>K}(n+j)b^{−j}] ≈ log(log N/log K)/(b−1) → ∞` there.  It becomes
`o(1)` only at `K = N^{1−δ}`, where the modulus is hopeless.  **Truncate-and-CRT does not close**
— confirmed, not merely quoted.

## Pointers
`DIRECTION.md` (CURRENT DIRECTIVE — obey, do not edit) · `PENDING_WORK.md` (attack list) ·
`KICKOFF-2026-09-24-swing-c3.md` · `src/NormalNumbers/Maze.lean`.
