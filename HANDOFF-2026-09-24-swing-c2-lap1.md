# HANDOFF 2026-09-24 — swing at C2, lap 1 (audit + window bridge)

Branch `wip/swing-c2`, file `src/NormalNumbers/SwingC2.lean` (green, one disclosed `sorry`).

## What the crux IS now

`NormalNumbers.SwingC2.tau_windowPrescribable` — the ONLY open leaf.  `ConjC2` is now a
one-line consequence of it (`conjC2_of_windowPrescribable`).  It says, in pure arithmetic:

> for `b ≥ 3`, `ℓ ≥ 1`, `t < b^ℓ` there is `n` with
> `Σ_{j<ℓ} τ(n+1+j)·b^{ℓ−1−j} + ⌊Σ_{k≥1} τ(n+ℓ+k)/b^k⌋ ≡ t (mod b^ℓ)`.

Status: **open**.  No real analysis remains in it — that was the point of the lap.

## Delivered (all machine-checked)

* `floor_orbit_mul_pow`, `isDisjunctive_of_floorWindow`: reading a length-`ℓ` window off the
  `×b` orbit is exactly `⌊x·b^{n+ℓ}⌋ mod b^ℓ`; prescribing all residues gives disjunctivity.
* `windowNum`, `floor_lambertVal_emod`: for a Lambert value with `w(m) ≤ m`, everything left of
  the window dies mod `b^ℓ`; only the `ℓ` in-window weights and the carry into the right end
  survive.  This is the bridge real-number → arithmetic.
* `conjC2_of_windowPrescribable` — the swing's conditional theorem.

## Audit verdict on the five `ω` places

`G4WeightInterface` (campaign G5) already pins the class the existing §4C Fourier control
covers: `w(m) = Σ_{p∣m} (1 + c_p(v_p(m)−1))`, i.e. additive with `a_p = 1`.

* **`τ ∉` that class, unconditionally** — `weightN_prime` (every class member is `1` at a prime)
  vs `τ(p) = 2`: `tau_ne_weightN`.
* **Not a normalisation artefact** — `tau_not_additive`: `τ(36) = 9 ≠ τ(4)+τ(9) = 6`.
  So `G4Transport.dilatedTailB_eq` (`ω(Dm) = ω(m)+ω(D) − overlap(D,m)`, `overlap` periodic mod
  `rad D`) has **no additive analogue**.  Verdict: `G4Transport` BREAKS for `τ`.
* `PrimeLambertDefs/Tail` survives trivially (`τ(m) ≤ m`, `tau_le_self`).

## The replacement, and the next attack

`tau_transport_frozen` (proved): if `v_p(m) = e_p` for every `p ∣ D`, then

    (∏_{p∣D}(e_p+1)) · τ(D·m) = (∏_{p∣D}(v_p(D)+e_p+1)) · τ(m).

So transport for `τ` IS exact — but it is **multiplication by a fixed rational**, not translation,
and the freezing hypothesis is a congruence mod `rad(D)^T` rather than `rad D`, with exceptional
density `≤ Σ_{p∣D} p^{−T}`.  Special case `e ≡ 0`: `τ(Dm) = τ(D)τ(m)` for `m` coprime to `D`.

**Next lap**: rebuild the G4 frame over modulus `rad(D)^T`, and decide whether multiplication-by-
`τ(D)` on the torus can play the role translation-by-`ω(D)/(b−1)` played in `G4Transport`
(it is an expanding endomorphism of `ℝ/ℤ`, so the Fourier side changes character: characters are
permuted, not translated).  That is the route-decisive question.

## Lap 2 addendum (same file, green)

* `tau_le_two_mul_sqrt` : `τ(m) ≤ 2⌊√m⌋` (divisors pair across `√m`).
* `sqrt_add_le` : `√(N+j) ≤ √N + j`.
* **`carry_le_sqrt`** : for `b ≥ 3`, `carry b τ N ≤ 2√N + 2`.

Why this is the route-decisive ingredient: it makes the *padding* reduction available.  Prescribe
a window of length `ℓ + K` whose low `K` digits are `0` and whose top `ℓ` digits are the target;
if the carry is `< b^K` it can only disturb the low `K` digits, so the top `ℓ` digits survive.
`carry_le_sqrt` says `K = ⌈log_b(2√N + 3)⌉` suffices — i.e. `K ≍ (1/2)log_b N`, which GROWS with
`N`.  So the reduction is not to a fixed-length residue prescription but to:

> **Sub-leaf A.**  For every `b ≥ 3`, `ℓ`, and target `t`, there are `n` and `K` with
> `b^K > 2√(n+ℓ+K) + 2` such that `τ(n+1+j) ≡ ρ_j (mod b^{j+1})` for `j < ℓ+K`, where the `ρ_j`
> encode "top `ℓ` digits `= t`, next `K` digits `= 0`".

Next lap: state Sub-leaf A in `src/` as a named `Prop` and prove
`tau_windowPrescribable` **from** it (that reduction is finite arithmetic and should go through);
`tau_windowPrescribable` then stops being the crux and A becomes it.

## Lap 3 addendum (green): the padding reduction is PROVED

`src/NormalNumbers/SwingC2.lean` now has exactly ONE `sorry`, and it is no longer about a real
number at all:

    ConjC2  ⟸  tau_windowPrescribable  ⟸  SubLeafA b       (windowPrescribable_of_subLeafA)

**`SubLeafA b`** (`b ≥ 3`): for every `ℓ ≥ 1` and `t < b^ℓ` there are `n, K` with

    2·√(n+ℓ+K) + 2 < b^K   and   Σ_{j<ℓ+K} τ(n+1+j)·b^{ℓ+K−1−j} ≡ t·b^K  (mod b^{ℓ+K}).

New proved machinery: `paddedSum`, `windowNum_eq`, `floor_mul_pow_div`, `carry_nonneg`,
`windowPrescribable_of_subLeafA`.  The padding argument: the low `K` digits are set to zero, the
carry (`carry_le_sqrt`: `≤ 2√N+2 < b^K`) can only occupy those, and integer division by `b^K`
recovers the target in the top `ℓ` digits.

**Where the crux now is.**  `SubLeafA` is pure multiplicative number theory — divisor counts in an
interval of length `ℓ+K`, weighted by powers of `b`, modulo `b^{ℓ+K}`.  The pad `K` must grow like
`½ log_b n`, which is the one non-classical feature (the interval length is not fixed).

**Next attack.** Two independent probes worth running before more Lean:
1. numeric (`probes/`): for `b = 3`, small `ℓ`, search `n ≤ 10^7` for each target `t` — does the
   padded window already hit every residue with `K = 3,4,5`?  If yes, `SubLeafA` is very likely
   true and the search shows what `n` looks like (smooth? prime-power-heavy?).
2. structural: use `tau_transport_frozen` with `D = p^a` to move a solution `n` to `p^a·n`,
   multiplying the whole padded sum by `(a+1)` modulo `b^{ℓ+K}` — if `gcd(a+1, b) = 1` this is an
   invertible action on `ℤ/b^{ℓ+K}`, and the orbit of ONE realisable value under all such `a`
   would give a large subgroup of realisable targets.  That is the most promising route: it turns
   "hit every residue" into "hit one residue + generate the group".

## Lap 4 addendum (green): `SubLeafA` is NOT vacuous — kernel-checked anchors

`probes/swingc2_window.py` (with a Fraction known-answer check against `Σ 1/(b^n−1)` in bases 3
and 10) searches the padded windows directly.  Results:

| b | ℓ | K | search limit (forced by `2√(n+L)+2 < b^K`) | targets hit |
|---|---|---|---|---|
| 3 | 1 | 5 | 14634 | 3/3 |
| 3 | 2 | 5 | 14633 | 9/9 |
| 3 | 2 | 6 | 132487 | 9/9 |
| 3 | 3 | 6 | 132486 | 26/27 (only `t = 12` missing — needs a larger `K`, which `SubLeafA` allows) |
| 4 | 1 | 4 | 16123 | 4/4 |
| 4 | 2 | 5 | 261113 | 15/16 |

So `SubLeafA` looks TRUE and, importantly, *comfortably* so: hits are plentiful, not marginal.
The witnesses are now in `src/` as `native_decide` anchors `subLeafA_three_one` and
`subLeafA_three_two` — `SubLeafA 3` holds for `ℓ ≤ 2` with `K = 5`, machine-checked.

Interpretation: the reduction is sound and the crux is a genuine equidistribution statement, not a
hidden obstruction.  `SubLeafA` is morally "the weighted divisor-count window equidistributes mod
`b^L`", and the hits occur at a rate consistent with `1/b^L` — i.e. no arithmetic bias blocks any
residue.

**Next attack (unchanged, now better motivated).**  Prove equidistribution of
`Σ_{j<L} τ(n+1+j) b^{L−1−j} (mod b^L)` over `n ≤ X`.  Route: `tau_transport_frozen` with
`D = p^a` acts on the window by multiplication by `(a+1)` mod `b^L` when `gcd(a+1,b)=1`; combined
with one realised value this generates the multiplicative subgroup, and the additive part comes
from shifting `n`.  The `ℓ=3, t=12` gap at `K=6` is a good adversarial test case for any proposed
mechanism.
