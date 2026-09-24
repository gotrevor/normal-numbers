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
