# HANDOFF 2026-09-02 (autonomous): `M(5,1) = 6` exact, prime lower side `Θ(g²)`, universal constant `≥ 0.840` 🧮

Branch `wip/adder-tower-c9`, HEAD `c237e8c`.  **Working tree clean; nothing
uncommitted.**  Every commit's pre-commit hook ran the full `lake build` green;
`src/` sorry-free; every new theorem audits `[propext, Classical.choice,
Quot.sound]`.  `CFScheduleA.lean` untouched (fenced), Comparator untouched.

Directive obeyed: `DIRECTION.md`'s objective is "pin the optimal universal
Mahler multiplier `M(g,k)`", with the prime-base upper bound as the mandated
crux.  All four commits are on that objective.

## What advanced

### 1. The prime-base LOWER side is `Θ(g²)` — the open half, settled (`45cf5ce`)

`MahlerLowerBoundBackground.lean` (new): the family
`α = a/(g−1) + B·Σ g^(−i!)` (`bgLiouville`), a two-parameter generalisation of
the file's existing pure-Liouville-multiple family.

* **`orbit_bg_mem` is the crux identity.**  For `n` late there is `d ≥ 1` with
  `orbit g (mα) n ∈ [ρ/g^d, (ρ+1)/g^d)`, where
  `ρ = bgResidue g a B m d = (b·S_d + mB) mod g^d`, `b = (m a) mod (g−1)`,
  `S_d` the repunit.  The orbit is *pinned to one order-`d` cell*, not merely
  bounded — that is what lets an arbitrary target block be excluded from
  either side (the old file could only push against the top cell).
* `mahler_lower_bound_bg` turns cell-disjointness into `M(g,k) > M`;
  `repunit_burst_lt` + `bgResidue_digit_stab` make the `k = 1` hypothesis a
  **finite `decide`-able certificate** (`mahler_lower_bound_bg_digit`).
* `MahlerPrimeLowerBound.lean` (new): `M(5,1) ≥ 6`, `M(7,1) ≥ 9`,
  `M(11,1) ≥ 24`, `M(13,1) ≥ 35`, **`M(23,1) ≥ 120`** — exact at `g = 5, 7,
  13, 23`.  `120/23² ≈ 0.227`, against Berend–Boshernitzan 1994 Thm 3.3's
  linear `(3/2)(g−1) = 33`.
* **Mechanism**: for odd `g` the background digit `2m mod (g−1)` is always even
  and `< g−1`, so `W = g−1` never arises from the background for any `m`; the
  whole multiplier budget goes to the burst, and `B` tunes it quadratic.  The
  `a = 0` family structurally cannot do this.

### 2. `M(5,1) = 6` — first exact Mahler constant at a prime base beyond `M(3,1) = 2` (`692c6a0`)

`MahlerBase5Exact.lean` (new).  `m5_mahler_upper`: five `decide +kernel`
certificates of `signed_engine_g_single` on the six-channel base-5 family
`x, 2x, …, 6x` (ambient `6! = 720`; only `6`–`11` live states survive pruning,
every surviving component a simple cycle).  `mahler_M_five_eq_six` conjoins the
two halves.  The general sandwich gave only `4 ≤ M(5,1) ≤ 25`.
Emitter + independent re-verifier: `experiments/mahler_collapse_cert.py`
(self-test: it reproduces `AdderTowerC1`'s base-3 shape, and correctly REFUSES
`M = 8` at base 7).

### 3. `M(10,k) ≥ 8(10ᵏ−1)` via a new power-divisor family (`53c85c0`)

`MahlerLowerBoundPower.lean` (new).  Replace `g = t·c` by `t·c = g^L` with an
`L`-digit guard block: if every `s·c` (`s < t`) avoids the digit `g−1` then
`M(g,k) ≥ t(gᵏ − 1)`.  `L = 1` recovers B–B Thm 3.1 exactly.  Reusable core:
**`window_lt_of_digit`** — one non-`(g−1)` digit anywhere in `[d−k, d)` gives
`N % g^d + g^(d−k) + 1 ≤ g^d`.  Base 10 (`8·125 = 10³`): `72 ≤ M(10,1) ≤ 100`.

### 4. The universal constant is `≥ 0.840`, was `1/2` (`c237e8c`)

`MahlerPowerInstances.lean` (new).  Scanning the power family over `L ≤ 5`, the
best admissible `t` **matches the exact `M(g,1)` at 13 of the 20 composite
bases `4 ≤ g ≤ 28`** — on composite bases it appears to be the extremal
construction.  Formalized: `g = 18, 20, 22, 24, 26` (all exact).
`mahler_universal_constant_ge`: `M(18,1) ≥ 272 = 0.840·18²`, so with
`mahler_multiplier_lt` the universal constant sits in `[0.840, 1]` (room cut
`1.19×`).

## The standing crux, and what is now KNOWN not to work

The prime-base **upper** side.  Recorded in `PENDING_WORK.md` §"structural
finding": `MahlerMultiplier.lean`'s covering method forces
`M ≥ g^(k+1) − q(g−2) − 1`, binding at the SMALLEST admissible shadow
denominator `q`.  `q = 1` is exactly the run branch, already settled with
`m ≤ gᵏ`, but excluding it buys only `2g − 4`; and `q ≥ 2` cannot be excluded
the same way (the `q=1` argument needs `A = ⌊gᵏx⌋` a *unit mod gᵏ*, which fails
once `gcd(A, q gᵏ) ≥ gᵏ`).  Since the empirical prime witnesses sit at
`q ≈ g/2`, even a perfect `q`-exclusion stops at `≈ g²/2`, a factor 2 above the
truth `≈ g²/4`.  **So the prime `Θ(g²)` upper side needs the Farey-hopping
analysis, not a sharper covering constant.**

## Next attack (PENDING_WORK.md top, in order)

1. **`M(7,1) = 9`** — mathematically settled, Lean-side only.  All seven digit
   certificates computed (`experiments/mahler_collapse_cert.py 7 9`): ambient
   `9! = 362880`, live `12/38/29/26/29/38/12`, omega-support `≤ 123`, every
   surviving component a simple cycle.  ⚠️ A single `decide +kernel` over that
   ambient ran **> 45 min without finishing** (probe this lap), so it needs the
   **chunked** `checkEdgesOnA` path of `AdderTowerC8/C9`
   (`experiments/emit_cert_lean.py` packs; `AdderCertSplit.lean` assembles).
   Estimate ~100 chunks/digit at C9's rate — measure one chunk first and size
   the split from that.  Recorded refutation: no subset of `{1,…,9}` with
   product `≤ 30000` collapses at base 7, so the ambient cannot be shrunk the
   way base 5's could (there `{1,2,3,4,6}`, ambient `144`, suffices).
2. **`M(g,k) ≤ g^(k+1) − 2g + 3` for prime `g`** — the `q = 1` exclusion above.
   Small but real, and the cheapest remaining upper-side item; surgery on
   `MahlerMultiplier.lean`'s sweep.
3. **A uniform `B(g)`** for a general prime `Θ(g²)` lower-bound theorem (not a
   table).  Probe data in `experiments/mahler_bg_burst_structure.py`: best `B`
   for `a = 2, W = g−1` is `5:781, 7:1123, 11:803, 13:1010, 17:1492, 19:1991,
   23:2641, 29:3893, 31:4398`, ratio `B/g² ≈ 4.6–6.6` throughout — no closed
   form spotted; `g = 17, 19, 29, 31` reach only `~0.6·((g−1)/2)²` at
   `B ≤ 40g²`, so either the range or the mechanism must change there.
4. Composite-`g` run theorem ("predecessor digit coprime to `g`"); B–B Thm 3.2.

## New files this lap

`src/NormalNumbers/`: `MahlerLowerBoundBackground.lean`,
`MahlerPrimeLowerBound.lean`, `MahlerBase5Exact.lean`,
`MahlerLowerBoundPower.lean`, `MahlerPowerInstances.lean` (all wired into
`NormalNumbers.lean`).
`experiments/`: `mahler_bg_burst_family.py`, `mahler_bg_burst_structure.py`,
`mahler_bg_cert.py`, `mahler_collapse_cert.py`, `mahler_subset_hunt.py`,
`mahler_power_family_scan.py`.
