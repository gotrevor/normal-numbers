# HANDOFF 2026-09-24 (lap 2) — swing at C3, branch `wip/swing-c3`

**Checkpoint.**  HEAD `2116de1`, working tree CLEAN, nothing to push (host pushes).
`lake build` green, 9181 jobs.  `src/` holds **2** swing `sorry`s (both named leaves in
`src/NormalNumbers/SwingC3Rotation.lean`) plus the 2 pre-existing designated-open ones
(`PrimeLambertOscillation`, `MahlerDriftOne`) — do not touch those.

Kickoff `KICKOFF-2026-09-24-swing-c3.md`.  DIRECTION.md → CURRENT DIRECTIVE was re-sited to
this swing by this lap's review pass and OUTRANKS this handoff.

> ⚠️ **`src/NormalNumbers/SwingC3.lean` is now sorry-free, and that is NOT completion.**
> The crux was DECOMPOSED into two named leaves in `SwingC3Rotation.lean`, which `SwingC3.lean`
> imports; `#print axioms conjC3` still shows `sorryAx`.  A scoped gate reading
> `sorry-free:src/NormalNumbers/SwingC3.lean` will report met — it is not.  Do **not** take the
> `box done` exit on that basis.

## What the crux IS now

**Leaf B, `tailLargeDecouple_holds`** (`SwingC3Rotation.lean` l. ~271).  Everything else on the
path to `ConjC3` is either proved or (Leaf A) reduced to an assembly of six proved pieces.

## The structural re-siting (this lap's main finding)

`G_b = S_P + L_P` with `S_P = ∑_n ω_{≤P}(n)b^{−n}` **rational** (`smallLambert_rat`:
`(b^Q−1)S_P ∈ ℕ`, `Q = ∏_{p≤P} p`) and `L_P = ∑_n ω_{>P}(n)b^{−n}`.  The "tails" of
`SwingC3Split` are literally orbits:

| identity | where |
|---|---|
| `fract (tailSmall P b n) = orbit b (smallLambert P b) n` | `SwingC3Lambert` |
| `fract (tailLarge P b n) = orbit b (largeLambert P b) n` | `SwingC3Lambert` |
| `orbit b G_b n = fract (orbit b S_P n + orbit b L_P n)` | `SwingC3Lambert` |
| `orbit b x (n+1) = fract (b · orbit b x n)` | `SwingC3Lambert.orbit_succ_eq` |
| Leaf B restated on `orbit b (largeLambert P b)` | `SwingC3Rotation.tailLargeDecouple_iff_orbit` |

Consequence: class `r+1` is the `×b` image of class `r`, so **Leaf B ⟺ every weak limit of the
`×b^Q`-empirical measures of `L_P` is `×b`-invariant** ⟺ `μ̂(h) = μ̂(bh)` for all `h`.

## The hypothesis pair (replaced `LargeTailLaw`, which is strictly stronger)

`isRich_of_rotationRoute` is **sorry-free, trust triple**: `RotationCover` + `TailLargeDecouple`
⇒ `IsRich b G_b`.  Covering gives `∑_k B_k ≥ N`, decoupling gives
`∑_k A_k ≥ (∑_k B_k)/Q + o(N)`, classes are disjoint ⇒ density `≥ 1/(2Q)`.  Numerical core
extracted as `density_lower_of_decouple`.  Two things `LargeTailLaw` demanded and this does not:
genuine limits, and rotation constants on an exact `b^{−ℓ}` grid.

## Leaf B: PRICING CORRECTION (supersedes the previous handoff)

The previous handoff said "sieve-grade, not Selberg–Delange-grade".  **That is wrong for the
natural route.**  Expand the decoupling in additive characters mod `Q`: it holds iff
`(1/N)∑_{n<N} e(jn/Q)·e(h·tailLarge P b n) = o(1)` for `j ≢ 0 (Q)`, `h ≠ 0` (Erdős–Turán back to
arcs).  Keep only slot `j=1`: `e(h ω_{>P}(n+1)/b) = z^{ω_{>P}(n+1)}`, `z = e(h/b)` a `b`-th root
of unity, so the sum is `∑_{m≤N} e(jm/Q) z^{ω_{>P}(m)}` — a multiplicative function twisted by an
additive character.  Split `m = s·t` (P-smooth × P-rough): `t` is coprime to `Q` (Q is P-smooth),
so `e(jst/Q)` expands in **Dirichlet characters mod Q**, and the non-principal terms must beat
the main term — i.e. `∑_{t≤x} χ(t) z^{ω(t)}`, **Selberg–Delange with characters** (`L(s,χ)^z`).

What IS free: at the level of a finite divisibility pattern `p_i ∣ n+j_i` with all `p_i > P`, the
density inside a class mod `Q` is **exactly** `1/(Q∏p_i)` by CRT.  The obstruction is only that
`tailLarge` is not a function of finitely many such indicators:
`E_n[∑_{p>K} c_p(n)] ≍ (loglog N − loglog K)/(b−1) → ∞` for any `K ≤ N^{o(1)}`, while exact
periodicity of the truncation costs a modulus `≈ e^K` and so needs `K ≤ (1−ε)log N`.
**Truncate-and-CRT does not close.**  (Closed form worth formalising:
`tailLarge P b n = ∑_{p>P} b^{−j₀(n,p)}/(1−b^{−p})`, `j₀(n,p)` the least `j ≥ 1` with `p ∣ n+j`.)

Attack list (also in `PENDING_WORK.md`): **B3 is now highest value** — a bounded surrogate for
`ω_{>P}`, so the tail is uniformly small and decoupling is exactly finite-dimensional; then
measure what the surrogate costs in the covering step.  Mathlib has no Selberg–Delange, so any
route that identifies nothing is worth far more than one that does.  Also open: B2 (the glue
only uses the ONE-SIDED `A_k ≥ B_k/Q − o(N)` — does the arc-boundary term then vanish?), B4 (a
numeric probe for class-dependence, which would REFUTE the route and is a first-class result),
B5 (prove `×b`-invariance from `y_{n+1} = T y_n` plus a quantitative recurrence).

## Leaf A: six pieces proved, assembly left (`SwingC3Net.lean`, all sorry-free)

`exists_grid_mem_Ico` · `exists_perturbed_grid_mem_Ico` (a forward-`ε`-perturbed `1/m` grid meets
every arc of length `> 1/m + ε` — this is why the route wants a NET) · `piCount`,
`omegaSmall_le_piCount`, `tailSmall_head_rem` (head + remainder in `[0, π(P)b^{−L}/(b−1)]`) ·
`exists_crt_pattern_mod` (CRT steering with the primes `≤ L` pinned by `a ≡ a₀ [MOD R]`) ·
`omegaSmall_steered` (`ω_{≤P}(a+j) = #{p ≤ L : p ∣ j} + #{p ∈ S : f p = j}` for `j ∈ [1,L]`) ·
`exists_slot_assignment` (blocks of prescribed digit sizes) · `exists_prime_window` (exactly `K`
primes in `(L,P]`, hence `π(P) ≤ L + K`).

**Next lap, item 1 (mechanical, ~1 lap):**
1. Growth lemma: `∀ len > 0, ∃ L, (b·L + 2 : ℝ) < len · b^L`  (`b ≥ 2`, so `b^L` beats any linear
   function; induction or `tendsto` on `L/b^L`).
2. Assemble `exists_rotationCover`: given `α, len`, pick `L` by (1), `K = (b−1)L`, `P` by
   `exists_prime_window`, `Q = ∏_{p≤P} p` (a primorial — need `∀ p ≤ P, p.Prime → p ∣ Q` and its
   converse), `S =` primes in `(L,P]`, `R = ∏_{p≤L} p`, `a₀ = 0`; for `k < b^L` let
   `d i = (k / b^{L−1−i}) % b` and take `f` from `exists_slot_assignment`, `a k` from
   `exists_crt_pattern_mod`.  Then `omegaSmall_steered` gives the head
   `C + k·b^{−L}`, `tailSmall_head_rem` gives `ρ_k ≤ π(P)b^{−L}/(b−1) ≤ bL·b^{−L}/(b−1)`, and
   `exists_perturbed_grid_mem_Ico` finishes `RotationCover`.
   **Distinctness mod `Q` is free**: `ω_{≤P}` is `Q`-periodic, so `a k ≡ a k' (Q)` forces equal
   steered counts, hence equal digit vectors, hence `k = k'`.
3. Then `conjC3` rests on Leaf B alone.

## Refuted routes (do not re-try)

Effective disjunctivity (`N(4,L)/4^L` still climbing at `L=7`, `probes/g4_first_occurrence.py`);
exact prescription of `ω` on a window (Landau: density zero); any statement about `ω mod b` alone
(the carry recursion reads `ω div b`); sharpening the §5 schedule (`isDisjunctive_base` is
contradiction-from-total-omission: one occurrence, no density).  Also: the `OmegaCarryJoint`
route would need `ω(n), ω(n+1)` jointly mod `b`, i.e. Chowla-type correlations — the rotation
route deliberately avoids it.

## Pointers
`DIRECTION.md` (CURRENT DIRECTIVE — obey, do not edit) · `STATUS.md` (C3-swing section + axiom
ledger) · `PENDING_WORK.md` (attack list B1–B5, Leaf A missing pieces) ·
`KICKOFF-2026-09-24-swing-c3.md` · `src/NormalNumbers/Maze.lean`.
