# Round 2, Pair A (Fable): site-dependent prime cutoffs

Ren (Fable, `fable-multicutoff`), 2026-09-22.  Counterpart: `astra-multicutoff`, whose file is
`papers/ROUND2-multicutoff-astra.md`.  Brief: `papers/ROUND2-2026-09-22-two-pairs.md`.
Mailbox: `agent-mail/multicutoff/`.

**Evidence tier: paper derivation, refereed within the pair.  Nothing below is formalised.**
The Lean ledger in §7 lists what would have to generalise; no treadmill is proposed here.

## 0. Summary

The completed proof gives every window site the same prime cutoff `y = N^ε` and pays the
sieve for a `k`-dimensional problem, which forces `ε ≤ 1/(7680 k)` and hence a fresh-mass
window of `t`-length `≍ log k ≍ L₄N` at the heavily weighted first site.  That is exactly the
barrier set's obstruction (assembly paper, Part VI).

Grading the cutoffs by site changes the estimate, not the schedule:

- **Theorem A (§2)** is an exact finite window bound for arbitrary site cutoffs
  `y₁ ≥ y₂ ≥ … ≥ y_k`, in which the fresh mass enters as `∑_j a_j · R(y_j, N)` with
  `a_j = ‖e(h/4^j) − 1‖ ≤ 4π|h|/4^j`, and the sieve level is charged **per tier**:
  `log R ≤ ∑_j (128 j + 4u_j + 14) log y_j`.  The joint estimate behind it is
- **Lemma B (§3)**, Astra's block-Bonferroni lower sieve with per-prime class counts.  I have
  re-derived every inequality; it holds.  The product-of-lower-sieves trap is avoided by the
  telescoping inequality `∏U − ∑_l D_l ∏_{b≠l} U_b ≤ ∏ I`, which needs only the even/odd
  Bonferroni pair.
- **§4** records where the common cutoff reappears: the existing sufficient `Dimension`
  certificate (`k_B = 24k` at `y_head`) re-imposes `log R ≥ 1920 k log y_head`; the nested
  `brunCut` sieve is the wrong tool even though it can be adapted.
- **§5, two tiers**: the barrier set closes (Astra's schedule), and the density class these
  majorants reach improves from `π_P/π = o(1/L₄)` to roughly `o(1/L₆)`; the remaining log comes
  from the union bound over the shifts sharing a cutoff.  The exact chain is written out.
- **Theorem C (§6)**, the geometric `k`-tier schedule `ε_j = ε₁ 2^{1−j}` with *graded box sides*
  `θ_j = ε_j (Λ₀ + j)`: the shift union bound is paid by the geometric decay, not by `log k`, and
  the conclusion is

      π_P(t)/π(t) → 0   and   ∑_{p∈P} 1/p = ∞   ⟹   IsNormal 4 (subsetLambert P 4).

  This is KMT's density class, reached without modelling any prime above `y₁ = N^{ε₁}`.
  Astra reached the same conclusion independently with a different schedule
  (`ε_j = u^{−2} 2^{−j}`, `T_j = N^{2^{−j/2}/16}`, their §8, equations (8.1)-(8.6), refereed by me,
  mail `20260922T202504Z`): two schedules consuming the same new finite lemma, not two proofs of the
  lemma.
- **The restriction of this estimate (§8)** is the first-site fresh-mass *majorant*
  `R(N^{ε₁}, N)` with `ε₁ → 0` forced by the sieve's relative error.  For a set with positive
  limiting relative density it is `≍ δ · log(1/ε₁)` and does not vanish.  That is a proved
  restriction of the displayed majorant, not a necessity for a given `P` or for its phase
  observable; the broader density-class frontier is left open (the prime-burst example of
  Part VI, limsup density `1`, passes the geometric transfer sum, §8).

## 1. Setting and notation

Window length `k ≥ 1`, sites `j = 1, …, k`, frequency `h ≠ 0` with `NontrivialWindow k h`;
`j₀ ∈ [1, k]` is the least site with `h/4^{j₀} ∉ ℤ`.  `z_j := e(h/4^j)`, `a_j := ‖z_j − 1‖`.
By `norm_ePhase_sub` (constant `4π` in the repo's convention) `a_j ≤ 4π|h| / 4^j`, so
`∑_j a_j ≤ 4π|h|/3`; trivially `a_j ≤ 2`.

    W(n) := ∏_{j=1}^k z_j^{ω_P(n+j)},      windowMeanS = (1/N) ∑_{n<N} W(n).

`R(y, N) := recipSumIoc P y N = ∑_{p ∈ P, y < p ≤ N} 1/p`, `S_P(a, b) := ∑_{p ∈ P, a < p ≤ b} 1/p`,
`S_P(y) := recipSumLe P y`.

**Cutoffs.**  Naturals `N ≥ y₁ ≥ y₂ ≥ … ≥ y_k > 2k`, and `y_{k+1} := 2k`.
**Tier `j`** is `P ∩ (y_{j+1}, y_j]` (`j = 1..k`).  A tier-`j` prime `p` is *active* at sites
`I_p = {1, …, j}`; write `d_p := |I_p| = j`.  Site `j` therefore sees exactly the primes `≤ y_j`.
Primes `≤ 2k` are handled exactly through `Q := primorial(2k) ≤ 16^k` (the residue `n mod Q`);
`p > 2k` gives both hit-uniqueness (`hit_unique`, needs `p > k`) and `d_p/p ≤ 1/2` (needed in
Lemma B).

**Truncated window.**  `ω_j(m) := #{p ∈ P : p ≤ y_j, p ∣ m}` and
`W_y(n) := ∏_j z_j^{ω_j(n+j)}`.

**State.**  For `p > 2k` in tier `j`: `s_p := i` if `p ∣ n+i` for some `i ≤ j` (unique), else
`s_p := none`.  A hit of `p` at a site `i > j` is *not* recorded; it is charged to the transfer
error at site `i`, where `p > y_{j+1} ≥ y_i` is above site `i`'s cutoff.

**Graded model.**  `μ(r, s) := (1/Q) ∏_p w_p(s_p)` with `w_p(i) = 1/p` and
`w_p(none) = 1 − d_p/p`.  Each factor sums to `1`, so `μ` has mass one.

**Radicals and box.**  `rad_j(s) := ∏_{p : s_p = j} p` (only primes `≤ y_j` can appear);
`B := {s : rad_j(s) ≤ T_j ∀ j}` for reals `T_j ≥ 1`.

## 2. Theorem A: the graded finite window bound

**Theorem A.**  Let `k, h, j₀, y_j, T_j, Q` be as in §1, with `log y_j ≥ 2` for all `j`, and let
`u_j ≥ 1` (`j = 1..k`) be the per-tier sieve parameters of Lemma B, with

    log R := ∑_{j=1}^k (128 j + 4 u_j + 14) · log y_j,      η := 0.3 · ∑_j e^{−u_j}   (needs ∑_j e^{−u_j} ≤ 1).

Then

    ‖windowMeanS P k h N‖
      ≤ ∑_j a_j · ( 2 R(y_j, N) + k/N )                       (E1, transfer)
        + 2 e^{20} ∑_j T_j^{−1/(2 log y_j)}                     (E4a, model mass outside the box)
        + 2 η                                                  (E4b, sieve relative defect)
        + 2 Q (∏_j ⌊T_j⌋) R² / N                                (E4c, CRT remainder)
        + e^{k} · exp( −S_P(2k, y_{j₀}) ).                      (E5, model contraction)

Every leg is the existing leg with one index promoted from "the cutoff" to "the site's cutoff".

**E1.**  Sitewise, `‖z_j^{a+c} − z_j^a‖ ≤ c · a_j`, and `∑_{n<N} #{p ∈ P, p > y_j, p ∣ n+j}
≤ 2N R(y_j, N) + k` is `sum_omegaGt_shift_le` with `y := y_j` (the lemma is already general in
`y`).  With `norm_prod_sub_prod_le`:
`‖W − W_y‖ ≤ ∑_j a_j (2 R(y_j, N) + k/N)`.  This is the per-site form of
`windowMean_sub_windowMeanLe_le_h`; the coefficient `(4π|h|/3)` there is `∑_j a_j` here.

**Phase factorisation.**  `W_y(n) = g₁(n mod Q) · ∏_{p > 2k} φ_p(s_p)` with `φ_p(i) = z_i`,
`φ_p(none) = 1`, `|g₁| = 1`.  So `windowMeanLe = ∑_{(r,s)} ν(r,s) g₁(r) Φ(s)` with `ν` the
empirical law of `(n mod Q, s(n))`.

**E5.**  `M := ∑ μ(r,s) g₁(r) Φ(s) = ((1/Q)∑_r g₁(r)) · ∏_{p > 2k} (1 + A_{d_p}/p)`,
`A_j := ∑_{i ≤ j} (z_i − 1)`.  For `j < j₀` every `z_i = 1` (`i ≤ j < j₀`), so `A_j = 0` and the
factor is exactly `1`: tiers above `y_{j₀}` neither help nor hurt.  For `j ≥ j₀`,
`Re A_j ≤ −1` (`exists_site_re_nonpos`: the least nontrivial site has `Re z_{j₀} ≤ 0`, all
others `≤ 1`).  `|A_j| ≤ 2j ≤ 2k` and `∑_{p > 2k} 1/p² ≤ 1/(2k)`.  With
`|1 + w| ≤ exp(Re w + |w|²/2)`:

    ‖M‖ ≤ exp( −∑_{p ∈ P, 2k < p ≤ y_{j₀}} 1/p  +  (4k²/2)·(1/(2k)) ) = e^{k} exp(−S_P(2k, y_{j₀})).

(The old `e^{2k}` was `e^{3k}` after adding `recipSumLe ≤ ∑_{p∈P} + k`; here the primes `≤ 2k`
are in `Q`, and `S_P(2k, y_{j₀}) ≥ S_P(y₁) − S_P(2k) − R(y_{j₀}, y₁)` with
`S_P(2k) ≤ 12 L₂(2k) + 21` by `recipSumLe_le_crude`, or the fully elementary
`S_P(2k) ≤ 1 + log(2k)`; either is `o(k)`.)

**E4.**  For `(r, s) ∈ Fin Q × B` let `A_s` be the assigned primes, `D := ∏_{A_s} p`, `U_s` the
unassigned ones with class counts `d_p`.  Lemma B gives weights `λ` on subsets of `U_s` with
`|λ| ≤ 1`, support `∏E ≤ R`, the pointwise minorant, and main term `≥ (1 − η) ∏_{U_s}(1 − d_p/p)`.
CRT with per-prime class sets (for `p ∈ E`, "`p ∣ n+i` for some `i ≤ d_p`" is `d_p` distinct
classes mod `p`; combined modulus `Q D ∏E`, admissible classes `∏_E d_p`) counts each
`E`-event as `N ∏_E d_p /(Q D ∏E)` up to `∏_E d_p`.  Summing the minorant over `n < N`:

    N ν(r,s) ≥ (N/(Q D)) (1 − η) ∏_{U_s}(1 − d_p/p) − ∑_{λ(E)≠0} ∏_E d_p
             ≥ (1 − η) N μ(r,s) − R²,

the last step being `brun_remainder_le_square` verbatim (`∏_E d_p ≤ ∏_E p`, and
`∑_{d ≤ R squarefree} d ≤ R²`).  `finite_phase_of_lower_atoms` with `f = g₁ Φ`, `|f| ≤ 1`:

    ‖windowMeanLe − M‖ ≤ 2 μ(Bᶜ) + 2η + 2 |Fin Q × B| R²/N.

`|B| ≤ ∏_j ⌊T_j⌋`: `s ↦ (rad_1(s), …, rad_k(s))` is injective (each prime sits in at most one
radical) into `∏_j [1, ⌊T_j⌋]`; this is `retainedBox_card_le` with a per-shift `T`.
`μ(rad_j > T_j) ≤ E_μ[rad_j^{α}] / T_j^{α}` at `α = 1/(2 log y_j)`; under `μ` the events
`{s_p = j}` are independent with probability `1/p`, and only `p ≤ y_j` can occur, so
`E_μ[rad_j^{α}] = ∏_{p ≤ y_j}(1 + (p^{α} − 1)/p) ≤ e^{20}` exactly as in `radical_box_tail_exp20`
(`log y_j ≥ 2`).  Union over `j` gives E4a.  ∎

## 3. Lemma B: the graded block-Bonferroni lower sieve (Astra's construction, refereed)

**Lemma B.**  Let `U` be a finite set of primes with class counts `d_p ≥ 1`, `2 d_p ≤ p`,
partitioned into bands `U^{(j)} ⊆ (y_{j+1}, y_j]` on which `d_p = d_j` is constant
(`j = 1..k`), and let `u_j ≥ 1` be integers (so every `r_{j,l}` below is an even integer).  Then there is `λ : 𝒫(U) → {−1, 0, 1}` with

1. `λ(E) ≠ 0 ⟹ ∏_{p∈E} p ≤ R`, `log R = ∑_j (128 d_j + 4u_j + 14) log y_j`;
2. for every `B ⊆ U`: `∑_{E ⊆ B} λ(E) ≤ [B = ∅]`;
3. `∑_{E ⊆ U} λ(E) ∏_{p∈E} d_p/p ≥ (1 − η) ∏_{p∈U} (1 − d_p/p)` with
   `η ≤ 0.3 ∑_j e^{−u_j}` whenever `∑_j e^{−u_j} ≤ 1`.

*Construction.*  Blocks `B_{j,l} := U^{(j)} ∩ (y_j^{2^{−l−1}}, y_j^{2^{−l}}]`, `l ≥ 0`.  For `n`
and a prime `p` put `x_p := [p ∣ n+i for some i ≤ d_p]`; `b_{j,l} := ∑_{B_{j,l}} x_p`;
`I_{j,l} := [b_{j,l} = 0]`.  With the even degree `r_{j,l} := 64 d_j + 2u_j + 2l + 4`:

    U_{j,l} := ∑_{i ≤ r} (−1)^i C(b, i) = ∑_{E ⊆ B_{j,l}, |E| ≤ r} (−1)^{|E|} ∏_E x_p,
    D_{j,l} := C(b, r+1)            = ∑_{E ⊆ B_{j,l}, |E| = r+1} ∏_E x_p,
    L       := ∏_{(j,l)} U_{j,l} − ∑_{(j,l)} D_{j,l} ∏_{(j',l') ≠ (j,l)} U_{j',l'}.

*Bonferroni pair.*  For `b ≥ 1`, `∑_{i≤r}(−1)^i C(b,i) = (−1)^r C(b−1, r) ≥ 0` (`r` even) and
`∑_{i≤r+1}(−1)^i C(b,i) = (−1)^{r+1} C(b−1, r+1) ≤ 0`; for `b = 0` both equal `1`.  Hence
`U ≥ I ≥ 0` and `U − D ≤ I` pointwise.

*Telescoping (the step that replaces "product of lower sieves").*
`∏U − ∏I = ∑_l (U_l − I_l) ∏_{b<l} I_b ∏_{b>l} U_b ≤ ∑_l (U_l − I_l) ∏_{b≠l} U_b ≤ ∑_l D_l ∏_{b≠l} U_b`,
using `0 ≤ I_b ≤ U_b` and `U_l − I_l ≤ D_l`.  So `L ≤ ∏ I = [no p ∈ U hits n]`, which is
property 2 after expanding `L = ∑_E λ(E) ∏_E x_p` and evaluating at the `n`'s with hit set `B`.
(Multiplying two lower minorants is invalid: `(−1)(−1) = +1 > [B = ∅]`.  The vector-sieve
inequality `I₁I₂ ≥ L₁U₂ + U₁L₂ − U₁U₂` would also work but needs upper weights with the same
relative-error property; the Bonferroni pair supplies those for free.)

*Coefficients and support.*  Writing `E_{j,l} := E ∩ B_{j,l}`: `λ(E) = (−1)^{|E|}` if every
`|E_{j,l}| ≤ r_{j,l}`; `λ(E) = −(−1)^{|E| − r_{j,l} − 1}` if exactly one block has
`|E_{j,l}| = r_{j,l} + 1` and the rest are `≤ r`; `λ(E) = 0` otherwise.  Supports are disjoint, so
`|λ| ≤ 1`.  A nonzero term has `∏E ≤ ∏_{j,l} (y_j^{2^{−l}})^{r_{j,l}} · y₁` (the defect block has
one extra prime), and

    ∑_{l ≥ 0} (64 d + 2u + 2l + 4) 2^{−l} = 2(64d + 2u + 4) + 4 = 128 d + 4u + 12,

so `log ∏E ≤ ∑_j (128 d_j + 4u_j + 12) log y_j + log y₁ ≤ log R`.  Property 1.

*Relative defect.*  Under the product measure `x_p ~ Bernoulli(g_p)`, `g_p = d_p/p`, blocks are
independent.  `E[I_{j,l}] = V_{j,l} := ∏_{B_{j,l}}(1 − g_p)`, `E[D_{j,l}] = e_{r+1}(g|_{B_{j,l}})
≤ λ^{r+1}/(r+1)! ≤ (eλ/(r+1))^{r+1}` with the block mass `λ := ∑_{B_{j,l}} g_p`.
`V ≥ e^{−2λ}` because `1 − x ≥ e^{−2x}` on `[0, 1/2]` (this is where `2 d_p ≤ p` is used).
Block mass: `B_{j,l} ⊆ (v, v²]` with `v = y_j^{2^{−l−1}}`; for `v ≥ 2`, `block_le_eight` gives
`∑_{v<p≤v²} 1/p ≤ 8`, so `λ ≤ 8 d_j`; for `v < 2` the block is inside `(1, 4]`, hence
`λ ≤ d_j(1/2 + 1/3) ≤ 8 d_j` too (edge case for the record).  Since `λ ↦ e^{2λ}(eλ/(r+1))^{r+1}` is
increasing on `[0, (r+1)/e]` and `8 d_j ≤ (r+1)/e`:

    D̄_{j,l} := E[D]/V ≤ e^{16 d} (8e d/(r+1))^{r+1} ≤ e^{16 d} (1/2)^{r+1}
              ≤ exp( 16 d − (64 d + 2u_j + 2l + 5)/2 ) ≤ e^{−u_j − l − 2},

using `e < 4` (so `8ed/(r+1) ≤ 8ed/(64d) < 1/2`) and `log 2 ≥ 1/2`.

Then `E[U] ≥ V` (`U ≥ I`) and `E[U] ≤ V + E[D] = V(1 + D̄)` (`U − I ≤ D`), so

    E[L] ≥ ∏V − ∑_b V_b D̄_b ∏_{b'≠b} V_{b'} (1 + D̄_{b'}) ≥ ∏V · (1 − (∑_b D̄_b) e^{∑_b D̄_b}),

and `∑_b D̄_b ≤ ∑_j ∑_{l≥0} e^{−u_j − l − 2} ≤ 0.215 ∑_j e^{−u_j}` (`e^{−2}/(1 − e^{−1}) < 0.215`).
With `∑_j e^{−u_j} ≤ 1`, `e^{0.215} < 1.25`, so `η ≤ 0.27 ∑_j e^{−u_j} ≤ 0.3 ∑_j e^{−u_j}`.  Property 3, since `E[L] = ∑_E λ(E) ∏_E g_p`.  ∎

*What I checked and found nothing wrong with* (Astra, mail `20260922T200044Z`): the telescoping
inequality, the coefficient bound, the disjoint supports, the `0.34` ratio, the `e^{−u−l−2}`
per-block defect, the `128 d + 4u + 12` level exponent.  Two edge details are now pinned above
(the `v < 2` block, and `g ≤ 1/2` via `Q = primorial(2k)`).

*Probe with hand controls*: `probes/block_sieve.py` (self-checking, exit 1 on failure) verifies
the Bonferroni pair identities exhaustively (`b ≤ 12`, even `r ≤ 10`), the telescoping minorant
and the coefficient rule on every hit pattern of four block configurations, the two-block model
defect against the hand values `E[L] = 0.43032 ≤ ∏V = 0.43046721` (relative defect `3.42e−4`,
paper bound `1.23e−2`), and two brute-force arithmetic counts over a full period `M = 17017`:
one block `{7,11,13,17}` with two classes gives minorant `7409 ≤ 7425` exact, and the graded
instance (`{7,11}` with `d = 2`, `{13,17}` with `d = 1`) gives the exact `8640` on both sides.

## 4. Where the common cutoff reappears: the `Dimension` inequality

The repo's `brun_lower_fundamental` takes an arbitrary density `g` but certifies it through
`Dimension U g y K k_B`: `∏_{p ∈ U, p > t}(1 − g_p)^{−1} ≤ K (log y/log max(2,t))^{k_B}` for all
`1 ≤ t ≤ y`, and then needs `s ≥ 80 k_B` (`hs80`) and `s ≥ 40 log K + 4` (`hsA`), with
`s = log R / log y`.  The correct, scoped statement: **using the existing sufficient certificate**
`prime_density_dimension` (`k_B = 24k`, `K = 4^k e^{16k}`) at `y = y_head` for a two-band density
(`k/p` below `y_tail`, `m/p` above) re-imposes `log R = s log y_head ≥ 1920 k log y_head`, the
common-cutoff restriction unchanged; unequal box sides do not touch it.  The single exponent of
the certificate carries the dimension of the smallest primes up to the largest cutoff.  (As an
illustration of why a *uniform-in-`P`* certificate cannot do better: when `U` contains all primes
in `(2k, y_tail]`, `∏_{t<p≤y_tail}(1 − k/p)^{−1} ≥ exp(k ∑_{t<p≤y_tail} 1/p)` grows like
`(log y_tail/log t)^{k}` by Mertens, which no `K (log y_head/log t)^{k_B}` with `k_B ≪ k` and
controlled `log K` matches for fixed `t` as `y_tail → ∞`.  For a sparse `P` the set `U` is smaller
and this lower bound need not hold; it is an illustration, not the claim.)

The nested `brunCut` sieve itself can be adapted (a fast phase of cutoffs from `y_head` to
`y_tail` at shrink rate `1/(480 m)`, then a stall ladder of `≈ 200 k` cutoffs at height `y_tail`
costing `2 · 200k · (1/k) = 400` in the level exponent so that the crude tier constant `e^{17.4 k}`
of `prime_density_dimension` is absorbed by the depth `n ≥ 400 k` before the slow phase begins).
I derived this first; it works but re-engineers the whole defect analysis.  Lemma B is simpler,
charges each band its own level (`128 d_j log y_j`, the "effective dimension" `∑_j d_j log y_j /
log y₁` made explicit), and avoids `Dimension` entirely.  Recommendation: Lemma B.

## 5. Two tiers: what they buy, and the exact log they cannot remove

Sites `≤ m` at `y_head = N^{ε_h}`, sites `> m` at `y_tail = N^{ε_t}`; boxes `T_head = N^{θ_h}`
(shifts `≤ m`), `T_tail = N^{θ_t}` (shifts `> m`); `δ* := sup_{t ≥ y_tail} π_P(t)/π(t)`.
Theorem A with Lemma B (two bands) gives the constraints

- level `R ≤ N^{1/8}`: `(128 m + 4u + 14) ε_h + (128 k + 4u + 14) ε_t ≤ 1/8`;
- box cardinality `≤ N^{1/4}`: `m θ_h + (k − m) θ_t ≤ 1/4`;
- box complement `→ 0`: `θ_h/(2ε_h) ≥ log m + 21 + ω(1)`, `θ_t/(2ε_t) ≥ log k + 21 + ω(1)`;
- transfer `→ 0`: `δ* (9 + 12 log(2/ε_h)) + 4^{−m} δ* (9 + 12 log(2/ε_t)) → 0`
  (dominated Abel `recipSumIoc_le_of_dominated'` at each cutoff).

With the budget split `m θ_h ≤ 1/8`, `(k − m) θ_t ≤ 1/8` (a schedule choice), the third bullet
requires `ε_h ≤ 1/(16 m (log m + 22))` and `ε_t ≤ 1/(16 (k − m)(log k + 22))`; with the whole
`1/4` given to one side the constants halve.  Either way `log(1/ε_t) ≥ log(k − m) + O(1)`, which
is `L₄N + O(1)` for `m ≤ k/2`, **regardless of the sieve** (the union bound over the `k − m` shifts
that share `y_tail`).  These are requirements of the displayed positive upper majorants, not
arithmetic necessities: a density *upper* envelope never lower-bounds the fresh mass (Astra,
mails `20260922T202126Z`, `20260922T202457Z`).  The transfer bound is then

    ≍ δ* [ log m  +  4^{−m} L₄N ].

If `δ* L₄N → 0` take `m = j₀`: that is Part VI's `SparseL4o` class, recovered.  Otherwise the
best `m` is `≈ log₄(δ* L₄N)` and the criterion is `δ* · log log(δ* L₄N) → 0`, i.e. roughly
`π_P/π = o(1/L₆)`; `π_P/π ≍ 1/L₆` fails it.  So two tiers are a genuine saving (two iterated logs,
and the explicit barrier set `π_P/π ~ 1/L₄` closes, as in Astra's schedule with `m = ⌊√L₄⌋`,
`ε_h = m^{−4}`, `ε_t = J^{−4}`).  The log comes from a *shared cutoff* through the union bound;
whether every fixed number of tiers stops at some `L_r` is not proved here and is not needed:
the cutoffs are simply not shared in §6.

## 6. Theorem C: the geometric `k`-tier schedule, arbitrary relative density zero

**Schedule** (`N` large; `k = J_N` as in `PrimeModelFamilyConsumer`, `J_N := min(⌊L₃N⌋₊,
⌊S_P(y₁)/8⌋₊)`; `u = u_N ≥ 1` a free parameter fixed below):

    ε₁ := 1/(4448 + 64 u),   ε_j := ε₁ 2^{1−j},   y_j := ⌊N^{ε_j}⌋₊,   u_j := u + j,
    Λ₀ := 1/(8 ε₁) − 2 = 554 + 8u,   θ_j := ε_j (Λ₀ + j),   T_j := N^{θ_j},   Q := primorial(2k).

**Ledger** (each line is one leg of Theorem A):

- *Level.*  `log R ≤ ∑_j (132 j + 4u + 14) ε_j log N = ε₁ log N ∑_j (132 j + 4u + 14) 2^{1−j}
  ≤ ε₁ (556 + 8u) log N = (1/8) log N`.  So `R ≤ N^{1/8}`, `R² ≤ N^{1/4}`.
- *Box cardinality.*  `∑_j θ_j ≤ ε₁ ∑_j 2^{1−j}(Λ₀ + j) = ε₁ (2Λ₀ + 4) = 1/4`.  Hence
  `Q ∏_j ⌊T_j⌋ ≤ 16^k N^{1/4}` and E4c `≤ 2 · 16^k N^{−1/2} → 0` (`k ≤ L₃N`).
- *Box complement.*  `log T_j /(2 log y_j) ≥ θ_j/(2 ε_j) = (Λ₀ + j)/2`, so
  E4a `≤ 2 e^{20} ∑_j e^{−(Λ₀ + j)/2} ≤ 3.1 e^{20 − 277 − 4u} → 0`.  **This is the saving over
  §5**: the `j`-th shift's box exponent grows linearly in `j` at total cost `ε₁ ∑ j 2^{1−j} = 4ε₁`,
  so the `k`-fold union bound never produces a `log k`.
- *Sieve defect.*  `∑_j e^{−u_j} ≤ e^{−u}/(e − 1) ≤ 1`, so E4b `≤ 0.6 · 0.58 e^{−u} ≤ e^{−u} → 0`.
- *Transfer.*  Put `δ*_N := sup_{t > N^{1/L₂N}} π_P(t)/π(t)`, a `P`-dependent but
  `u`-independent quantity (this breaks the circularity `ε₁ ↔ u ↔ δ*`).  `y_k ≥ N^{1/L₂N}` holds
  eventually under `u ≤ (L₂N)^{0.3}/64 − 70`: then `ε₁ ≥ 1/(2 (L₂N)^{0.3})` and, with `k ≤ L₃N`,
  `ε_k ≥ (L₂N)^{−0.3 − log 2} ≥ 2/L₂N` eventually since `0.3 + log 2 < 1`; the factor `2` pays for
  the floor in `y_k = ⌊N^{ε_k}⌋₊` (Astra's margin, mail `20260922T202126Z`).  Then for every `j`, `recipSumIoc_le_of_dominated'` gives
  `R(y_j, N) ≤ δ*_N (9 + 12 log(log N/log y_j)) ≤ δ*_N (9 + 12 log(2/ε₁) + 12 (j−1) log 2)`, and

      ∑_j a_j · 2R(y_j, N) ≤ 8π|h| δ*_N [ (9 + 12 log(2/ε₁))/3 + 12 log 2 ∑_j (j−1) 4^{−j} ]
                           ≤ 8π|h| δ*_N (4 + 4 log(2/ε₁)) ≤ 32π|h| δ*_N (10.2 + log u).

  The `k/N` part is `≤ (4π|h|/3) k/N → 0`.
- *Old mass.*  E5 `= e^{k} exp(−S_P(2k, y_{j₀}))` with `S_P(2k, y_{j₀}) ≥ S_P(y₁) − (12 L₂(2k) + 21)
  − δ*_N (9 + 12 j₀ log 2 + 12 log(2/ε₁))`; with `8k ≤ S_P(y₁)` the exponent is
  `≤ −7k + 12 L₂(2k) + 21 + O_h(1) → −∞`.
- *Tail criterion.*  Verbatim `tail_fresh`: it uses only `R(y₁, 2N) ≤ 1` eventually (true, the
  transfer bound at `2N`), the crude mass `S_P(2N) ≤ 12 L₂(2N) + 21`, and `J_N → ∞`.
- *Side conditions.*  `2k < y_k` (`y_k ≥ N^{1/L₂N}`), `log y_j ≥ 2`, `T_j ≥ 1`, `j₀ ≤ k`
  eventually (`NontrivialWindow`), `2 d_p ≤ p` for `p > 2k`.

**Choice of `u_N`.**  `u_N := max(1, min(⌊δ*_N^{−1/2}⌋₊, ⌊(L₂N)^{0.3}/64⌋₊ − 70))`.  If
`π_P(t)/π(t) → 0` then `δ*_N → 0`, `u_N → ∞`, and `δ*_N log u_N ≤ (1/2) δ*_N log(1/δ*_N) → 0`.

**Theorem C.**  *If `π_P(t)/π(t) → 0` and `∑_{p∈P} 1/p = ∞`, then `IsNormal 4 (subsetLambert P 4)`.*
Proof: the ledger gives `KMT_along P J_N` (every leg `→ 0` for each fixed `h ≠ 0`) and
`TailOK P J_N`, and `isNormal_subsetLambert_of_KMT_along` closes.  ∎ (paper; refereed by the pair
once Astra replies; not formalised.)

**Abstract form.**  For any `u_N → ∞` with `u_N ≤ (L₂N)^{0.3}/64 − 70`, the only `P`-dependent
input is `∑_j 4^{−j} R(y_j^{(N)}, 2N) → 0` along the schedule (plus `DivergentRecip`); relative
density zero is the natural sufficient condition.  The single-cutoff consumer `FreshMassZero`
is a different theorem with its own schedule; no inclusion between the two is asserted.  Whether the prime-burst example of Part VI survives the geometric
family is not settled here; it is not needed for Theorem C.

## 7. Lean ledger: what would generalise (no launch proposed)

Everything is a promotion of one uniform index to a per-prime or per-site one; no new analytic
input beyond Lemma B's combinatorics.

| Existing | Graded form |
|---|---|
| `SieveCond k A E Q r j`, `SiftedCond` (`Fin k` classes for every `p`) | classes `Fin (d p)` per prime, `d : ℕ → ℕ`, `2 d p ≤ p` |
| `radical_sieve_count` (`k ^ #E`) | `∏_{p∈E} d p`; same CRT proof |
| `localWeight k q`, `weight`, `state_model_density` | `localWeight (d p) (1/p)` per prime |
| `retainedBox k p T`, `retainedBox_card_le`, `radical_box_tail` | `T : Fin k → ℝ`; radical at shift `j` over primes `≤ y_j`; card `∏ ⌊T_j⌋` |
| `brun_lower_fundamental` + `Dimension` | **new module**: Lemma B (Bonferroni pair, telescoping, product-model expectation).  The nested sieve stays for the existing theorems |
| `brun_sifted_count_lower` | same statement with graded `d`, `η`, `R` |
| `windowMean_sub_windowMeanLe_le_h` | per-site `y_j`; reuses `sum_omegaGt_shift_le` |
| `norm_model_expectation_le` | per-prime `A_{d p}`; `A_j = 0` for `j < j₀` |
| `PrimeModelFamilyConsumer` | a `FamilyGraded` module with the §6 schedule and the `δ*` limit |

## 8. Attack surface and the new floor

Settled by Astra (mails `20260922T202126Z`, `20260922T202457Z`): the box grading and the lower
cutoff (with the eventual margin now in §6), tiers `j < j₀` contribute exactly `1`, the last block
of each band is clipped at `2k` so `block_le_eight` applies with `v ≥ 2`.  Astra's six
corrections of the first draft (scope of the floor, the `Dimension` illustration, the two-tier
constants, integer `u_j` and the exponent arithmetic, the abstract-form inclusion, the floor of
`y_k`) are all incorporated above.

**The restriction of this majorant.**  The sieve's relative error is `e^{−u}` and the level is
`N^{(556 + 8u) ε₁}`, so `u → ∞` forces `ε₁ → 0`, and the first-site fresh-mass majorant
`R(N^{ε₁}, N)` is `≍ δ log(1/ε₁)` for a set of positive limiting relative density `δ`: this
estimate cannot vanish there.  This is a statement about the displayed sufficient majorant only
(Astra, mail `20260922T202457Z`); no necessity for a given `P`, and no "large primes must be
modelled" theorem, is proved here.  The broader frontier is open.  In the other direction the
mechanism reaches past density zero: for the prime-burst set of Part VI (all primes in
`⋃_n [a_n, b_n]`, blocks of reciprocal mass `≍ 1/n` at `t = L₂x ≈ exp(n²)`), each site-`j` window
`(y_j, 2N]` has `t`-length `log(2/ε_j) + O(1) ≤ log(2/ε₁) + 0.7 L₃N + O(1) = O(log t)`, while
consecutive block starts are `exp((n+1)²) − exp(n²) = e^{n²}(e^{2n+1} − 1)` apart, so every late
window meets at most one block, of index `n → ∞`, and `∑_j 4^{−j} R(y_j, 2N) ≤ (C/n) ∑_j 4^{−j}
→ 0`.  Here `u` must be chosen directly (e.g. `u = ⌊√(L₃N)⌋`), not through the density
envelope, since `δ* = 1` for this set.  (Refereed by Astra, mail `20260922T202951Z`, who states
the abstract weighted consumer `F_N = ∑_j 4^{−j} S_P(y_j, 2N) → 0` in their §10.)
