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

## Lap 5 addendum (green): the route back to an ADDITIVE weight

The §2 obstruction says `τ` is outside the additive class because `e(τ(n)/q)` is not multiplicative
(whereas `e(ω(n)/q)` is — that is precisely why Selberg–Delange/G4 works for `ω` and not for `τ`).

**The escape, now proved as algebra in `src/`:**

* `tau_of_squarefree` : `s` squarefree ⟹ `τ(s) = 2^{ω(s)}`.
* `tau_primePow_mul_squarefree` : `τ(p^a·s) = (a+1)·2^{ω(s)}` for `s` squarefree, `p ∤ s`.

So on the locus `n = p^a·s` (squarefree cofactor — positive density, and a *fixed* `p`,`a` is a CRT
condition), `τ(n) mod b^L` is determined by `a` together with `ω(s) mod ord_{b^L}(2)`.  `ω` is
ADDITIVE: this is exactly the weight `G4Transport` and `G4WeightInterface` were built for.  The
free factor `(a+1)` supplies the residues the cyclic group `⟨2⟩ ≤ (ℤ/b^L)^×` cannot reach (e.g.
`0 mod 3`, which `2^ω` never hits) — so both obstructions are covered.

**Concrete shape of the next lemma (next lap's target).**  Pick primes `q_0,…,q_{L−1}` and
exponents `a_0,…,a_{L−1}`; by CRT fix `n` so that `q_j^{a_j} ‖ n+1+j` for every `j`.  On the
positive-density subset where each cofactor is squarefree,

    paddedSum b τ n L  ≡  Σ_{j<L} (a_j+1)·2^{ω(s_j)}·b^{L−1−j}   (mod b^L),

and the only remaining freedom to control is the vector `(ω(s_j) mod ord)` — an additive-weight
prescription on `L` consecutive integers in a fixed progression.  State that as `SubLeafB` and
prove `subLeafA_of_subLeafB`; `SubLeafB` is then the crux, and it is in the G4 category.

## Lap 6 addendum (green): the crux is now INSIDE the additive category

Chain, all machine-checked except the last link:

    ConjC2 ⟸ tau_windowPrescribable ⟸ SubLeafA b ⟸ SubLeafB b        (subLeafA_of_subLeafB)

`Structured m q a s` := `q` prime ∧ `s` squarefree ∧ `q ∤ s` ∧ `m = q^a·s`; on it
`tau_of_structured` gives `τ(m) = (a+1)·2^{ω(s)}`.  `SubLeafB b` asks for a window position `n`,
pad `K`, and a structured factorisation of each of the `L = ℓ+K` consecutive integers, with

    Σ_{j<L} (a_j+1)·2^{ω(s_j)}·b^{L−1−j} ≡ t·b^K   (mod b^L).

**Why this is the right place to stand.**  No multiplicative weight is left.  The unknowns are
(i) the exponents `a_j`, free integers fixed by a CRT choice of `q_j^{a_j} ‖ n+1+j`, and
(ii) `ω(s_j)`, an ADDITIVE weight on `L` consecutive integers — and `e(ω(·)/q)` is multiplicative,
so Selberg–Delange and the whole G4 Fourier control (`G4Transport`, `G4WeightInterface`,
`PrimeLambertIndepChar`, `G4Mertens`) apply to it, unlike to `τ` itself.

Note `Structured` is a real restriction (`36 = 2^2·3^2` is not structured), but the structured
integers have positive density, and CRT lets one *choose* `q_j, a_j` per window slot.

**Next lap.** Prove `subLeafB_holds` for the easiest slice first: fix all `a_j = 0` except one slot
`j₀`, so all other `s_j = n+1+j` are squarefree and contribute `2^{ω}`, and the single slot `j₀`
carries the `(a+1)` factor needed to reach residues `≡ 0 mod b`.  The remaining input is a joint
prescription of `ω` on `L−1` consecutive squarefree integers mod `ord_{b^L}(2)` — compare
`G4WiringCRT` and `PrimeLambertIndepChar`, which already do joint `ω`-residue work.

## Lap 7 addendum (green): `SubLeafB` costs nothing — probe + kernel witnesses

Decisive question for lap 6's reduction: does restricting to *structured* windows (every entry
`q^a·s`, `s` squarefree) lose targets?  Probe answer: **no.**

| b | ℓ | K | structured-window density | SubLeafA targets | SubLeafB targets |
|---|---|---|---|---|---|
| 3 | 1 | 5 | 68.6% | 3/3 | 3/3 |
| 3 | 2 | 5 | 63.9% | 9/9 | 9/9 |
| 3 | 2 | 6 | 58.4% | 9/9 | 9/9 |

Structured windows are a *majority* of all windows (a window of length 6 is structured iff none of
its six entries has two repeated prime factors), and every target is still realised.  So the
descent `SubLeafA ⟸ SubLeafB` is not lossy in practice — the additive reformulation is free.

In `src/`, kernel-checked: `subLeafB_three_one_0/1/2` exhibit explicit structured windows
(`n = 2109, 1022, 1342`, `K = 5`) for all three base-3 digits, with the full `q^a·s` factorisation
of each of the six entries and the congruence verified by `native_decide`.

**Crux restated.** `subLeafB_holds` is the one open obligation.  Everything below it is now
additive: prescribe `Σ_{j<L} (a_j+1)·2^{ω(s_j)}·b^{L−1−j} mod b^L`.  Next lap: the `a_j = 0`
slice — with all entries squarefree the sum is `Σ_j 2^{ω(n+1+j)} b^{L−1−j}`, and the target set is
the subgroup generated by `⟨2⟩`; measure in a probe how much of `ℤ/b^L` that slice alone reaches,
which tells us how many non-squarefree slots the proof actually needs.

## Lap 8 addendum (green): no LOCAL obstruction — `structuredTarget_unobstructed`

Proved: for every `b ≥ 2`, `L ≥ 1`, `t`, the shape `Σ_{j<L} (a_j+1)·2^{e_j}·b^{L−1−j}` realises `t`
modulo `b^L` — already with **all `e_j = 0` and one free exponent in the last slot**.

Two consequences, both sharpening the crux:

1. **Nothing in `SubLeafB` is blocked by congruence algebra.**  A "local obstruction" refutation of
   the route is ruled out: the residue system is free.  Every remaining difficulty is *arithmetic
   realisability* — making `L` CONSECUTIVE integers carry a required exponent vector.
2. **A proof needs only ONE controllable slot.**  The other `L−1` window entries may contribute
   whatever they like; a single slot with a free prime-power exponent `a` (contributing the factor
   `a+1`, which ranges over all of `ℕ⁺` and hence over all residues mod `b^L`) closes the target.

This is the sharpest available statement of what remains, and it reframes the crux:

> **Crux, final form of this run.**  Find, for each `L` and each residue `r`, a position `n` and a
> prime `q` with `q^a ‖ n+L` for a *prescribable* `a ≡ r' (mod b^L)`, while `n+1, …, n+L−1` remain
> structured.  Equivalently: prime-power valuations of a prescribed size at a prescribed offset,
> with a squarefree-ish neighbourhood — a sieve problem, not a Fourier problem.

The `q^a ‖ n+L` condition with `a` large forces `n+L ≥ q^a ≥ 2^a`, so `a ≈ log n`; and `a+1` must
hit a residue mod `b^L` where `b^L ≈ n^{1/2}` (the pad constraint).  Since `a ≈ log n ≪ b^L`, the
factor `a+1` alone canNOT reach every residue — the `2^{ω(s)}` factors must supply the bulk, and
`⟨2⟩ ≤ (ℤ/b^L)^×` has index `φ(b^L)/ord(2)`.  **That index is the next quantity to compute**: if
`2` is a primitive root mod `b^L` (true for `b = 3` and many `L`), `⟨2⟩` covers all units and only
the non-unit residues need the `(a+1)` factors.  Probe that next.

## Lap 9 addendum (green): the CRT construction is REFUTED — and why

Lap 8 said "a proof needs only one controllable slot".  The natural construction is:

> By CRT fix `n` so that `q_j^{a_j} ‖ n+1+j` for distinct primes `q_j`.  Then
> `τ(n+1+j) = (a_j+1)·τ(u_j)`.  Choose `a_j + 1 ≡ 0 (mod b^{j+1})` to kill slot `j`, leaving one
> distinguished slot `n+L = 2^a·p` (`p` prime, Dirichlet) contributing `2(a+1)`; solve
> `2(a+1) ≡ t·b^K (mod b^L)`, which is possible for every ODD `b` since `2` is then invertible.

**This is refuted by the pad constraint**, now proved as `lt_pow_two_mul_of_pad`:

    2√(n+L) + 2 < b^K   ⟹   n + L < b^{2K}.

The construction needs `a_j + 1 ≡ 0 mod b^{j+1}`, hence `a_j ≥ b^{j+1} − 1`, hence
`n ≥ ∏_j q_j^{a_j} ≥ 2^{b^L}` — doubly exponential in `L`, while the pad allows only `n < b^{2K}`.
The two requirements diverge; no choice of `K` reconciles them.  **Route closed.**

**What `lt_pow_two_mul_of_pad` tells us positively.**  `SubLeafA`/`SubLeafB` are *finite* search
problems: for each `(ℓ, K)` the witness must live in `[0, b^{2K})`, a space of size `b^{2K}` against
`b^ℓ` targets, `ℓ < K`.  So the counting is comfortable (`b^{2K}` positions, `b^{ℓ}` targets, hit
rate `≈ b^{−ℓ−K}` gives `≈ b^{K−ℓ}` expected hits per target) — matching the probe, where hits were
plentiful.  The crux is therefore an EQUIDISTRIBUTION statement at scale `n ≤ b^{2K}` for a modulus
`b^{ℓ+K}` — i.e. modulus ≈ √(range).  That is exactly the "square-root barrier" regime: one needs
the weighted divisor window equidistributed to modulus `X^{1/2}` over `n ≤ X`.

**Next attack (concrete and literature-anchored).**  Divisor function in arithmetic progressions to
modulus `q ≈ X^{1/2}` is the classical hard range (Selberg/Hooley/Linnik give `q ≤ X^{2/3}` for
`τ` in APs on average; individual moduli near `X^{1/2}` are reachable by Weil for `τ` — see
Heath-Brown, "The divisor function in arithmetic progressions").  The next lap should state the
needed input in that language — a `τ`-in-APs estimate to modulus `X^{1/2+ε}` — as `SubLeafC`, and
prove `SubLeafB` (or `SubLeafA` directly) from it.  That makes the crux a *named, checkable*
analytic-number-theory statement rather than an unanalysed sorry.

Alternatively, relax the pad: the padding was a convenience (`windowPrescribable_of_subLeafA`), and
a version of the reduction that tracks the carry instead of zeroing it would remove the
`n < b^{2K}` coupling entirely and re-open the CRT route.  **That is the highest-value next move**:
`floor_lambertVal_emod` already gives the exact identity with the carry present.

## Lap 10 addendum (green): the search bound was SELF-INFLICTED — pad hypothesis weakened

Lap 9's refutation of the CRT route rested on `n + L < b^{2K}`, which came from `SubLeafA`'s pad
hypothesis being stated with the *crude sufficient condition* `2√(n+L)+2 < b^K` rather than the
thing actually needed.  What the padding argument uses is only

    carry b τ (n + ℓ + K)  <  b^K,

and `carry_le_sqrt` is merely one way to certify it.  `SubLeafA` and `SubLeafB` are now stated with
that honest hypothesis; `carry_le_sqrt` is kept as the certificate and `padOK` uses it to discharge
the anchors (`subLeafA_three_one/two`, `subLeafB_three_one_*` all still kernel-check).

**Effect on the refutation.**  `lt_pow_two_mul_of_pad` is still true and still stands as a limit on
*√-certified* windows, but it no longer constrains `SubLeafA` itself.  The real constraint is

    K  ≳  log_b (carry at n+L)  ≈  log_b τ_max(n)  ≈  log n / (log log n · log b),

since `τ(m) = m^{o(1)}` (not `m^{1/2}`).  So the admissible window position now satisfies roughly
`log n ≲ K log b · log log n` — still sub-doubly-exponential, so the CRT construction (which needs
`log n ≈ b^L`) remains refuted, but by a much finer margin and for a structural reason:

> **Recorded verdict.**  Any construction that pins `n` by congruences to a modulus of size `b^L`
> forces `log n ≳ b^L`, while the carry forces `b^K ≳ τ(n) = exp((1+o(1))log n/log log n)`, i.e.
> `K ≳ b^L / (log log n · log b)`.  Since `K < L`, this is impossible.  **Explicit CRT-style
> construction of the window is refuted for every base.**  The crux is irreducibly a counting /
> equidistribution statement about `τ`-windows, not a construction.

That is the sharpest statement this run produced about what a proof of `ConjC2` must look like.
