# KICKOFF 2026-11-04: every word frequency of a perfect-power Lambert constant exists

**This kickoff supersedes `DIRECTION.md` and every older `HANDOFF-*.md` on this branch
(`wip/power-lambert-frequencies`, worktree `~/src/nn-freq`, based on `wip/rich-power-lambert` @
d2965847, which proved `isRich_powerLambert`).**  Operator: Ren (Claude), attended session
2026-11-04.  Lane: new mathematics.

## The target

File: `src/NormalNumbers/PowerLambertFrequenciesExist.lean` (planted, builds green with two
`sorry`s).  Host gate: `--done-when sorry-free:src/NormalNumbers/PowerLambertFrequenciesExist.lean`.

    theorem powerLambert_nearZero_density (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
        ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ᶠ N : ℕ in atTop,
          (((range N).filter fun n =>
            orbit b (powerLambert b r) n < 1 / (b : ℝ) ^ L ∨
              1 - 1 / (b : ℝ) ^ L ≤ orbit b (powerLambert b r) n).card : ℝ) ≤ ε * N

    theorem powerLambertFrequenciesExist (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
        PowerLambertFrequenciesExist b r

Both statements are FROZEN: never weaken, restate or re-hypothesise them.  If you believe one is
false, write `JUDGE-FLAG:` in the handoff with the exact obstruction and stop.  Build only what you
touch: `lake build NormalNumbers.PowerLambertFrequenciesExist` (every dependency is prebuilt; never
`lake update`).  The gate file is NOT imported from the root `src/NormalNumbers.lean` (the root runs
`#barrier_audit`, which fails on an untagged sorry); **add the import to the root only once the
file is sorry-free**, then run the full `lake build` and commit.

## Why this is the right target

`S = powerLambert b r = Σ_{n≥1} 1/(b^{n^r} − 1)` is disjunctive (10-27), rich and not normal
(11-03).  `PowerLambertFrequenciesExist b r` (conjecture node, `PowerLambertFrequencies.lean`,
85%) says every word has a limiting frequency; with `not_isNormal_powerLambert` this makes `S`
the first explicit arithmetic constant with a complete, non-uniform word-frequency law.  The
periodic/non-periodic split of the richness proof is the route; the one genuinely new input is
`powerLambert_nearZero_density` (no atom of the limiting law at `0`), which is why it is frozen
alongside the headline.

## Notation and facts already in the repo

`c m = powerDivisorCount r m = #{d ∣ m : d^r ∣ m}` (`c 0 = 0`, `c m ≥ 1` for `m ≥ 1` since
`d = 1` counts; `c m ≤ m`).  `S = coefficientValue c b = CastingOut.lambertVal b c`
(`powerLambert_eq_coefficientValue`).  Tail after position `n`:
`T n := Σ'_j c (n+1+j) / b^(j+1)` (this is `periodicTail b r 1 n`, and
`lambertVal_mul_pow_eq` gives `S · b^n = (integer) + T n`).  Orbit: `orbit b x n = Int.fract
(x · b^n)`, so `orbit b S n = Int.fract (T n)` (`orbit_powerLambert_eq` with `Q = 1`, or directly).
Words: `occursAt_iff_orbit_mem`: `OccursAt b S w n ↔ orbit b S n ∈ Ico (W / b^|w|) ((W+1) / b^|w|)`,
`W = blockNatVal b w < b^|w|`.  Periodic split (`PowerLambertRichCount/Orbit.lean`): for
`Q = (D !)^r` every `d ≤ D` has `d^r ∣ Q` (`hQD`); `c m = periodicPowerCount r Q m +
aperiodicPowerCount r Q m`; `periodicTail_add_mul` (exact `Q`-periodicity);
`orbit_powerLambert_eq : orbit b S n = Int.fract (periodicTail b r Q n + aperiodicTail b r Q n)`;
`aperiodicTail_nonneg`; `aperiodicPowerCount_le_card_Ioo` (a non-periodic root lies in
`(D, √m]`); `sum_Ioo_inv_sq_le : Σ_{d ∈ Ioo D X} 1/d² ≤ 2/(D+1)`; Markov
`card_le_two_mul_card_filter_lt`; `orbit_pow` (Disjunctive.lean) for the shift
`orbit b x (n + L) = Int.fract (b^L · orbit b x n)` (prove it if the form differs).

## The proof (paper; execute it, splitting into named lemmas; commit after each green lemma)

### A. `powerLambert_nearZero_density` (the arithmetic heart)

A1. **Tail split.**  For all `n L`: `b^L · T n = A L n + T (n + L)` with the natural number
    `A L n := Σ_{j<L} c (n+1+j) · b^(L-1-j)` (`sum_add_tsum_nat_add`-type split of the tsum).
A2. **Near zero is a congruence.**  Let `κ n := ⌊T n⌋ ∈ ℕ`.  From A1, `⌊b^L T n⌋ = A L n + κ (n+L)`,
    and `Int.fract (T n) < 1/b^L ↔ b^L ∣ A L n + κ (n+L)`,
    `1 − 1/b^L ≤ Int.fract (T n) ↔ (A L n + κ (n+L)) % b^L = b^L − 1`.  (Because
    `b^L T n = b^L ⌊T n⌋ + b^L fract(T n)` and `⌊b^L fract(T n)⌋ ∈ [0, b^L)` is `0` resp. `b^L − 1`
    exactly in the two cases.)  So the frozen event is: `(A L n + κ (n+L)) % b^L ∈ {0, b^L − 1}`.
A3. **Carry chain (pure ℕ).**  Statement: for `g : ℕ → ℕ`, `b ≥ 2`, `L ≥ P ≥ 1`, `κ : ℕ`, if
    `(Σ_{j<L} g (n+1+j) b^(L-1-j) + κ) % b^L ∈ {0, b^L − 1}` and every `P` consecutive positions in
    `[n+1, n+L]` contain one with `g ≥ 1`, then
        `(b − 1) · (L − P) ≤ Σ_{j<L} g (n+1+j) + κ`.
    Proof: define the carries `γ_0 = κ`, `γ_i = (g (n+L+1−i) + γ_{i−1}) / b` for `i = 1..L`
    (exact division when the residue is `0`; `(… − (b−1)) / b` when it is `b − 1`); the digit
    condition says `g (n+L+1−i) + γ_{i−1} = b γ_i + δ` with the same `δ ∈ {0, b−1}` for all `i`.
    Summing: `Σ g = δ L + (b−1) Σ_{i=1}^{L−1} γ_i + b γ_L − κ`.  For `δ = b − 1` this is
    `≥ (b−1) L − κ`.  For `δ = 0`: a carry `γ_{i−1} ≥ 1` forces `γ_i ≥ 1` (the sum is a positive
    multiple of `b`); a carry `γ_{i−1} = 0` forces `g (n+L+1−i) ≡ 0 (mod b)` and `γ_i = g/b`, which is
    `0` iff `g = 0`; so the zero carries form an initial segment `i < i₀` of the chain on which
    `g = 0`, of length `< P` by the run hypothesis, and from `i₀` on every carry is `≥ 1`:
    `Σ g ≥ (b−1)(L − P) − κ`.  (Induction on `L`, peeling the lowest position `n + L`, is the clean
    Lean shape; state the invariant with the carry explicit.)
A4. **Apply A3.**  Case `b ≥ 3`: `g = c`, `P = 1` (`c ≥ 1`): the event gives
    `Σ_{window} c ≥ (b−1)(L−1) − κ (n+L) ≥ 2(L−1) − κ (n+L)`.  Case `b = 2`: `T n ≥ Σ_j 2^{−j} = 1`,
    so `κ ≥ 1`; write `c = 1 + c'` (`c' m = powerDivisorCount r m − 1 = #{d ≥ 2 : d^r ∣ m}`),
    `A L n = (2^L − 1) + A' L n`, and the event becomes `(A' L n + (κ(n+L) − 1)) % 2^L ∈ {0, 2^L − 1}`
    for `g = c'`, `P = 2^r` (every `2^r` consecutive integers contain a multiple of `2^r`, where
    `c' ≥ 1`): `Σ_{window} c' ≥ L − 2^r − κ (n+L)`.
A5. **Window rigidity.**  For every window `(n, n+L]`:
    `Σ_{j<L} c' (n+1+j) ≤ (11/12) L + √L + B L n`, where
    `B L n := Σ_{j<L} #{d ∣ n+1+j : Nat.sqrt L < d ∧ d^r ∣ n+1+j}` (the big-root part), because for
    `2 ≤ d ≤ √L` the window has at most `L/d^r + 1 ≤ L/d² + 1` multiples of `d^r`, and
    `Σ_{2≤d} 1/d² ≤ 1/4 + 2/3` (`sum_Ioo_inv_sq_le` with `D = 2`, plus `d = 2`).  Any constant
    `< 1` in place of `11/12` is fine.  Also `Σ_{window} c = L + Σ_{window} c'`.
A6. **The big-root part is small on average.**  `Σ_{n<N} B L n ≤ L (N+L) Σ_{d > √L} 1/d² ≤
    2 L (N+L)/(Nat.sqrt L + 1) ≤ 2 (N+L) √L` (each `m ≤ N+L` lies in at most `L` windows; then swap
    the sums: `Σ_{m ≤ X} #{d > √L : d^r ∣ m} = Σ_{d > √L} #{m ≤ X : d^r ∣ m} ≤ X Σ_{d>√L} 1/d²`).
A7. **The carry is bounded on average.**  `Σ_{n<N} κ (n+L) ≤ Σ_{n<N} T (n+L) ≤ 2 (N + L) + 4`,
    from `Σ_{m ≤ X} c m = Σ_d ⌊X/d^r⌋ ≤ X Σ_d 1/d² ≤ 2X` and `Σ_j (j+1)/b^(j+1) ≤ 2`.
A8. **Assembly.**  On the frozen event, A4 + A5 give `B L n + κ (n+L) ≥ L/12 − 2^r − √L − 2`, so for
    `L ≥ L₀` one of `B L n ≥ L/26`, `κ (n+L) ≥ L/26` holds.  Markov with A6, A7:
    `#{n<N : event} ≤ (26/L)·2(N+L)√L + (26/L)·(2(N+L)+4) ≤ ε N` for `N ≥ N₀`, once
    `52/√L + 52/L < ε/2`.  Choose `L` accordingly (`L := max L₀ ⌈(200/ε)²⌉` or whatever the
    constants demand); `∀ᶠ N` is `Filter.eventually_atTop`.

### B. Transport to every `b`-adic rational

For `t = W / b^ℓ` and `η > 0`: `|orbit b S n − t| < η` (or the wrapped version near `t = 1 ≡ 0`)
implies `orbit b S (n + ℓ) < b^ℓ η ∨ 1 − b^ℓ η ≤ orbit b S (n + ℓ)`, since
`orbit b S (n+ℓ) = Int.fract (b^ℓ · orbit b S n)` and `b^ℓ t ∈ ℕ`.  Hence the upper density of
`{n : orbit n ∈ (t − η, t + η) mod 1}` is at most that of the near-zero event at radius `b^ℓ η`
(shift by `ℓ` costs `ℓ/N`).

### C. The periodic sandwich

Fix a word `w` (`ℓ = |w|`, `W`, `α = W/b^ℓ`, `β = (W+1)/b^ℓ`, cylinder `I = Ico α β`).  Fix
`η ∈ (0, 1/b^ℓ)`, `D ≥ 2`, `Q = (D !)^r`; `v n := Int.fract (periodicTail b r Q n)` (`Q`-periodic),
`R n := aperiodicTail b r Q n ≥ 0`, `u n := orbit b S n = Int.fract (v n + R n)`.
C1. **Periodic counts.**  For any set `J`, `|#{n<N : v n ∈ J} − N · G_J| ≤ Q` with
    `G_J := #{n<Q : v n ∈ J} / Q` (write `N = qQ + s`).
C2. **Sandwich.**  With `I⁻ := Ico α (β − η)` and `I⁺ := Ico (α − η) β ∪ Ico (1 − η) 1`:
    `v n ∈ I⁻ ∧ R n < η → u n ∈ I` (no wrap, `fract_add_mem_Ico_of_close`-style), and
    `u n ∈ I ∧ R n < η → v n ∈ I⁺` (if `v n + R n < 1` then `v n = u n − R n`; otherwise `u n < η ≤ α`
    unless `α = 0`, and then `v n ≥ 1 − η`).  So
    `#{v ∈ I⁻} − #{R ≥ η} ≤ #{u ∈ I} ≤ #{v ∈ I⁺} + #{R ≥ η}` (counts over `n < N`).
C3. **Markov for `R`.**  `Σ_{n<N} R n ≤ (2/(D+1)) (N + 2)`: swap the finite sum with the tsum,
    and `Σ_{m ≤ X} aperiodicPowerCount r Q m = Σ_{d^r ∤ Q} #{m ≤ X : d^r ∣ m} ≤ X Σ_{d > D} 1/d² ≤
    2X/(D+1)` (`d ≤ D → d^r ∣ Q` by `hQD`, so a non-periodic root is `> D`).  Hence
    `#{n<N : R n ≥ η} ≤ (2/(D+1)) (N + 2) / η`.
C4. **Boundary layer.**  `I⁺ \ I⁻ ⊆ Ico (α−η) α ∪ Ico (β−η) β ∪ Ico (1−η) 1`, and
    `v n ∈ Ico (t − η) t ∧ R n < η → u n ∈ (t − η, t + η) mod 1` for `t ∈ {α, β, 1}`, so by B the
    count `#{n<N : v n ∈ I⁺ \ I⁻}` is at most `#{R ≥ η}` plus three near-zero counts at radius
    `b^ℓ η` (shifted by `ℓ`).

### D. Cauchy

Let `a N := #{n<N : OccursAt b S w n} / N`.  Given `ε > 0`: take `L` from A for `ε/16`; set
`η := 1/b^(L+ℓ)` (so `b^ℓ η = 1/b^L`); take `D` with `2(N+2)/((D+1) η N) ≤ ε/16` for `N ≥ 1`;
then for `M, N ≥ N₀` (absorbing `Q/N`, `ℓ/N` and the `∀ᶠ` thresholds), C2–C4 give
`a N, a M ∈ [G_{I⁻} − ε/4, G_{I⁺} + ε/4]` and `G_{I⁺} − G_{I⁻} ≤ ε/4`, so `|a M − a N| ≤ ε`.
Conclude with `cauchySeq_tendsto_of_complete` (`Metric.cauchySeq_iff`), which yields the `∃ f`
of `PowerLambertFrequenciesExist` (unfold it: the counted predicate is exactly `OccursAt`).

A measure-theoretic route (weak limits on `UnitAddCircle`, portmanteau) is acceptable if you
find it shorter, but the elementary route above is complete as written.

## Rules

- No `native_decide`, no new axioms, no `maxHeartbeats` bumps without a `-- HEARTBEAT:` comment.
- Never edit statements in other files; new lemmas go in the gate file or in new files
  (suggested: `PowerLambertRuns.lean` for A, `PowerLambertPeriodicApprox.lean` for C), or ADDED to
  `PowerLambertRichCount/Orbit.lean`.  Do not touch `MAZE.md`, `Maze.lean`, `DIRECTION.md`; no
  `git add -A` (pathspec only).
- Handoff: `HANDOFF-2026-11-04-power-lambert-frequencies.md` with `#print axioms` of both frozen
  theorems (expect only `propext`, `Classical.choice`, `Quot.sound`).
- Lines ≤ 100 chars; docstrings on every new theorem; the `@[blueprint]` on the headline stays.
- Stretch (only after the gate; not the gate): state and prove that the frequency equals
  `lim_D G_D(w)` (computable from the `Q_D`-periodic model), and record the frequency of the digit
  `1` for `b = 10, r = 2` as a sanity table in the handoff.
