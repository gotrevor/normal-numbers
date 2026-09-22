# Pair B Fable: the carry lift as a prescribed-orbit theorem, and what it says about G4

Ren / Fable 5.1 (`fable-shift-consistency`), 2026-09-22.  Paper mathematics; no Lean theorem is claimed.
Companion: `ROUND2-shift-consistency-astra.md`, which carries the complete every-M proof of the zero-orbit
countermodel (sections 2-8 there).  This file does not repeat that proof.  It records (1) an independent
derivation that reached the same lift from the other end, (2) my referee verdict on Astra's load-bearing
points, (3) the generalization to an arbitrary prescribed times-4 orbit, (4) an exact reformulation of the
repo's window formalism for `omega` itself, (5) a retraction of a claim in my own obstruction note, (6) the
remaining lemma stated so it cannot be mistaken for a reduction, and (7) the probe.  Mailbox:
`agent-mail/shift-consistency/`.  Probe: `probes/carry_lift.py` (`--selftest` asserts hand-computed values),
data `probes/data-2026-09-22-carry-lift.txt`.

**BLUF.**  Overlap and exact shift consistency do NOT repair the summary package.  There is one deterministic
nonnegative integer sequence `W`, with overlapping windows and ordinary averages at every sufficiently large
`M`, whose fixed-prefix laws are Poisson in total variation, whose centered second moments are `(1+o(1)) loglog M`
uniformly over the scheduled sites, and whose scheduled Fourier mean at `K = windowK M` converges to **1** at
every frequency.  More generally the scheduled Fourier means of such a `W` are the Weyl sums of an *arbitrary*
prescribed times-4 orbit, up to `O(|h| loglog M / 4^K)` at every `M` (Theorem 3.1).  Applied to `omega`
itself, the identity behind this shows that the repo's `WindowDecayK h` is *equivalent* to normality of the
G4 constant at frequency `h` (Proposition 4.1), so the window decomposition is a reformulation, not a
reduction, and the summary package discards exactly the carries.  My earlier claim that "shift consistency"
was the ingredient the Riesz countermodel lacked is withdrawn (section 5).  The only remaining distinction
from G4 is arithmetic: the actual joint law of the carries of `omega` with the leading residues, at
`J ~ (1/2) log_4 loglog M` sites (section 6).  Nothing here is evidence against G4 normality.

Notation.  `e(t) = exp(2 pi i t)`, `L = L_M = log log M`, `K = windowK M = Nat.log 2 (Nat.log 2 (Nat.log 2 M)) + 1`,
so `4^K` is between `a^2` and `4a^2` with `a = floor(log_2 floor(log_2 M))`, hence `4^K asymp L^2`.  For a sequence
`W` on the positive integers, `T_k(n) = sum_{j=1}^k W_{n+j}/4^j` (this is `truncTail k n` when `W = omega`),
`T_inf(n) = lim_k T_k(n)` when it exists, `{x}` is the fractional part.

## 1. Every nonnegative integer sequence is (orbit, carries)

**Lemma 1.1 (exact).**  Let `W_n >= 0` be integers with `W_n = O(n)` (any subexponential bound will do).  Put
`T_inf(n) = sum_{j>=1} W_{n+j}/4^j`, `C_n = floor T_inf(n)`, `X_n = {T_inf(n)}`, `d_n = floor(4 X_n)`.  Then for
every `n >= 0`:

    4 T_inf(n) = W_{n+1} + T_inf(n+1),                                      (1.1)
    X_{n+1} = {4 X_n},   d_n = 4 X_n - X_{n+1} in {0,1,2,3},                (1.2)
    W_{n+1} = 4 C_n - C_{n+1} + d_n,                                        (1.3)
    T_k(n) = C_n + X_n - 4^{-k} (C_{n+k} + X_{n+k})   for every k >= 1.     (1.4)

Conversely, given any `x_0 in [0,1)` with digits `d_n = floor(4 {4^n x_0})` and any integers `C_n >= 0` with
`C_{n+1} <= 4 C_n + d_n` and `C_n = O(n)`, the sequence (1.3) is nonnegative, satisfies `W_n = O(n)`, and has
`T_inf(n) = C_n + {4^n x_0}`; in particular its `X_n` is the times-4 orbit of `x_0`.

*Proof.*  (1.1) is the definition of `T_inf` after pulling out `j = 1`.  Taking fractional parts of (1.1) with
`W_{n+1}` an integer gives `X_{n+1} = {4 X_n}`; taking integer parts, `4 C_n + floor(4 X_n) = W_{n+1} + C_{n+1}`,
which is (1.3) with (1.2).  For (1.4), `T_k(n) = T_inf(n) - 4^{-k} T_inf(n+k)` by (1.1) iterated.  For the converse,
telescoping `sum_{j<=k} W_{n+j}/4^j = C_n - 4^{-k} C_{n+k} + sum_{j<=k} d_{n+j-1}/4^j`, and `C_{n+k}/4^k -> 0`,
`sum_{j>=1} d_{n+j-1}/4^j = {4^n x_0}`.  Nonnegativity is `C_{n+1} <= 4 C_n + d_n`.  QED.

So the design space is exactly a point `x_0` and a carry sequence `C`.  The infinite phases `X_n` of ANY such
sequence form a single times-4 orbit; this is not a property of `omega` but of the base-4 tail.  The
scheduled phase is, by (1.4),

    e(h T_K(n)) = e(h X_n) * e(-h 4^{-K} (C_{n+K} + X_{n+K})).                (1.5)

## 2. The lift: carries of a background, and the exact block law

Fix a "background" `A_n >= 3` (integers, `A_n = O(n)`) and set `C := ` the carries of `A`, i.e. `C_n = floor
sum_{j>=1} A_{n+j}/4^j`; write `X'_n`, `d'_n` for the background's own phase and digits.  Fix a prescribed
`x_0` with digits `d_n`.  Define

    W_{n+1} = 4 C_n - C_{n+1} + d_n.                                          (2.1)

Applying (1.3) to `A` gives `A_{n+1} = 4 C_n - C_{n+1} + d'_n`, so

    W = A + d - d',   |W - A| <= 3,   W >= A - 3 >= 0,   C^W = C,   X^W_n = {4^n x_0}.   (2.2)

This is Astra's carry lift with `U = T^A_inf`, and (2.2) is the note's identity.  The distributional content is
in the digit block `d'`:

**Lemma 2.1 (bijection).**  For `J >= 1`, the base-4 numeral `sum_{i=1}^J 4^{J-i} d'_{n+i-1}` equals
`(sum_{i=1}^J 4^{J-i} A_{n+i} + C_{n+J}) mod 4^J`.  For a fixed block `(A_{n+1},...,A_{n+J})` this is a bijection
between `C_{n+J} mod 4^J` and `{0,1,2,3}^J`.

*Proof.*  `4^J X'_n` has integer part `floor(4^J T^A_inf(n)) - 4^J C_n`, and `4^J T^A_inf(n) = sum_i 4^{J-i} A_{n+i}
+ T^A_inf(n+J)` by (1.1), whose integer part is `sum_i 4^{J-i} A_{n+i} + C_{n+J}`.  QED.

Solving (2.2) for `A` given `W = w` and the digits, `A_{n+i} = w_i - d_{n+i-1} + b_i` with `b_i = d'_{n+i-1}`, and
Lemma 2.1 forces `C_{n+J} = sum_i 4^{J-i}(d_{n+i-1} - w_i) mod 4^J`.  With `A_{n+1..n+J}` independent with laws
`p_i` and `C_{n+J}` independent of them with residue law `q`, this is exactly Astra's exact block formula

    P(W = w) = q(sum_i 4^{J-i}(d_{n+i-1} - w_i) mod 4^J) prod_i sum_{b=0}^3 p_i(w_i + b - d_{n+i-1}),   (2.3)

re-derived here from the other direction; the two derivations agree including the sign of the residue.  The
obstruction Astra names is visible in (2.3): if `q` is a point mass the block lies in one weighted congruence
class mod `4^J`, so `|W - A| <= 3` is not a total-variation statement.  What makes it one is that the carry
`C_{n+J} = floor((A_{n+J+1} + C_{n+J+1})/4)` is uniform mod `4^J` up to `eta_J(lambda) = (4^{J+1}-1)
exp(-lambda(1 - cos(2 pi/4^{J+1})))`, from the single site `A_{n+J+1}` alone and uniformly in the conditioned
later carry (Astra section 3).  I checked this and the rest of Astra's argument; verdict in section 7.

## 3. Theorem: the scheduled means are the Weyl sums of the prescribed orbit

**Fix `x_0 in [0,1)` FIRST.**  Then take Astra's background: `A_i = 3 + N_i`, `N_i ~ Pois(lambda_i)` independent,
`lambda_i = log log(i + e^e)`, and fix a realization in the probability-one set that Astra's sections 4-8 produce
for this `x_0` (the proof below runs with the digits `d` of `x_0` as a fixed deterministic input).  Let `W` be
(2.1).  The quantifier order matters: the theorem says *for every `x_0`, almost every background works*, not
that one background works for all `x_0`.  The stronger claim is false (Astra, 20:24Z): given a background,
choose `d_n in {0,1}` with `d_n = C_{n+1} mod 2`; then `W_{n+1} = 4C_n - C_{n+1} + d_n` is always even, which destroys
(P).  Those digits define a legitimate `x_0`, chosen after the background.

**Theorem 3.1.**  As `M -> infinity` through all integers:

(P) for every fixed `J`, the empirical law of `(W_{n+1},...,W_{n+J})`, `n < M`, is within `o(1)` total variation of
    `Pois(L_M)^{tensor J}`;

(V) uniformly for `1 <= j <= K(M)`, `(1/M) sum_{n<M} (W_{n+j} - L_M)^2 = (1 + o(1)) L_M`, hence the centered
    geometric-tail bound `(1+o(1)) sqrt(L_M) (4^{-a} - 4^{-K})/3` uniformly in `a < K`;

(F') for every fixed integer `h`,

        (1/M) sum_{n<M} e(h T_K(n)) = (1/M) sum_{n<M} e(h {4^n x_0}) + O(|h| L_M / 4^{K}),

    and `L_M/4^K = O(1/L_M)`.  The same holds on `M <= n < 2M`.

*Proof.*  (P) and (V): in (2.3) the prescribed digits enter only through the residue `r(w,d)` and through the
shifts `w_i + b - d_{n+i-1}` with `0 <= b - d <= 3` in absolute value; Astra's estimate (3.3) allowed shifts up to
6 already (the `+3` of the background), so the conditional TV bound `eta_J(lambda_{n+J+1})/2 + 6 sum_i
lambda_{n+i}^{-1/2}` holds verbatim with `d` present, uniformly in the conditioned tail, and sections 5-6 of
Astra's file go through unchanged: the filtration argument never used `d = 0`, and (V) uses only `|W - A| <= 3`.
(F'): by (1.5), `|e(h T_K(n)) - e(h X_n)| <= 2 pi |h| 4^{-K} (C_{n+K} + 1)`, and `(1/M) sum_{n<M} C_{n+K} = O(L_M)` is
Astra's (7.1).  QED.

**Corollaries.**

(a) `x_0 = 0`: `X_n = 0`, all scheduled means tend to 1.  This is Astra's theorem; it also has `T_inf(n) = C_n`,
    an integer at every `n`.

(b) `x_0 = 1/3 = 0.111..._4` (a fixed point of times-4): the scheduled mean tends to `e(h/3)`, of modulus 1 for
    EVERY `h`, including `h = 2`.  The Riesz countermodel had a vanishing `h = 2` mean, so "test `h = 2`" could
    not detect it; in the one-sequence model no frequency is exempt.  (`x_0 = 2/3` gives `e(2h/3)`.)

(c) A `mu`-generic `x_0` for a times-4-invariant ergodic probability `mu`: the scheduled mean tends to
    `mu-hat(h)`.  Astra's Riesz measure `mu = prod_{r>=0}(1 + delta cos(2 pi 4^r x)) dx` is times-4-invariant with
    `mu-hat(h) = (delta/2)^{s(h)}` (`s` = number of nonzero signed base-4 digits, zero if none).  It is also
    times-4-**mixing**, hence ergodic (Astra, 20:24Z): for fixed integers `u, v` and all large `n`,
    `mu-hat(u + 4^n v) = mu-hat(u) mu-hat(v)`, because signed-digit decoding of `u + 4^n v` reads off the digits
    of `u` below position `n` (terminating there if `u` is representable, hitting the forbidden residue 2 before
    `n` if not, in which case both sides vanish) and the digits of `v` above; so `int e(ux) e(v 4^n x) dmu ->
    mu-hat(u) mu-hat(v)`, and trigonometric-polynomial density gives mixing.  Birkhoff then supplies a point
    generic for all integer characters simultaneously.  Choosing that `x_0` first and an independent good
    background second embeds the exact Riesz table (`rho^{s(h)}`, zero at `h = 2`) into a one-sequence,
    overlapping-window, every-`M` model, unconditionally.

(d) A normal `x_0`: the scheduled means tend to 0 for every `h != 0`.  So a sequence with the identical summary
    package can equally well satisfy scheduled decay.  The package carries no information about which case
    holds.

The probe (section 8) runs (a), (b) and (d) at `L in {8, 64, 1000}`; in every row the scheduled mean sits within
the (F') bound of the orbit Weyl sum, and in the `L = 1000` rows the fixed `k = 1, 2` means are `< 0.005` while the
scheduled `K = 10` mean is `1.0000`, `e(h/3)`, or `0.000` respectively.

## 4. Exact reformulation for `omega` itself

Let `G = primeLambertAtBase 4 = sum_{n>=1} omega(n)/4^n` (`= sum_p 1/(4^p - 1)`), the number whose base-4
normality is the G4 target.  Apply Lemma 1.1 to `W = omega` (`omega(n) = O(log n)`):

    T_inf(n) = sum_{j>=1} omega(n+j)/4^j = 4^n G - sum_{m<=n} 4^{n-m} omega(m),   so   X_n = {4^n G}.   (4.1)

The infinite phase sequence of `omega` IS the times-4 orbit of the G4 constant, and `C^omega_n = floor T_inf(n)`.
With `truncTail K n = T_K(n)` and `fullWindowMean N K h = (1/N) sum_{N<=n<2N} e(h truncTail K n)`, (1.5) gives

**Proposition 4.1.**  For every `N, K, h`,

    | fullWindowMean N K h - (1/N) sum_{N<=n<2N} e(h {4^n G}) |
        <= 2 pi |h| 4^{-K} (1/N) sum_{N<=n<2N} (C^omega_{n+K} + 1)
        <= 2 pi |h| 4^{-K} ( (1/N) sum_{N<=n<2N} sum_{j>=1} omega(n+K+j)/4^j + 1 ).

At `K = windowK N` the right side is `O(|h| loglog N / 4^K) = O(|h| / loglog N)` by the first moment of `omega`
over shifted windows: the repo's `sum_window_omegaR_le` (G4WindowK.lean) gives `(1/N) sum_{N<=n<2N} omega(n+j+1)
<= log_2(4 (log 4N + 1)) = O(loglog N)` uniformly for `j + 1 <= 2N`; the `j > N` part of the geometric sum is
handled as in Astra's (7.1).  (Checked against the Lean statement, not just its docstring.)

Consequently **`WindowDecayK h` is equivalent to dyadic Weyl decay of the orbit `{4^n G}` at frequency `h`**,
which is equivalent to `(1/N) sum_{n<N} e(h 4^n G) -> 0`, i.e. to normality of `G` at frequency `h`: with
`S(N) = sum_{n<N} e(h 4^n G)` and `S(2m) - S(m) = o(m)`, take `m = floor(N/2)`, so `S(N) = S(m) + o(N) + O(1)`, iterate a
fixed number `r` of halvings and bound the last prefix by `N/2^r`; `N -> infinity` first, then `r -> infinity`
(Astra, 20:24Z; no exceptional-scale averaging enters).  The repo proves the direction `WindowDecayK -> IsNormal` (`isNormal_G4_of_windowDecayK`); the
proposition is the converse.  So the window ladder `PrefixDecay -> EventualPrefixDecay -> WindowDecayK ->
IsNormal` collapses at its last rung: the scheduled window mean is the Weyl sum of the target, rotated by a
deterministic unimodular factor and perturbed by `o(1)`.

Two consequences for how the crux should be read.

- **The schedule is immaterial beyond `4^K >> loglog N`.**  Any `K(N)` with `loglog N / 4^{K(N)} -> 0` gives the
  same equivalence; Candidate A of my obstruction note (half-log schedule, `4^K >> |h| sqrt(loglog N) A(N)`)
  is the sharp version of the same fact with the second moment in place of the first.  Below that threshold
  the window mean is a genuinely different object (section 6).

- **`EventualPrefixDecay h` splits at the threshold** into normality of `G` at `h` (the rungs `k >= a(M) :=
  (1/2) log_4 L + A`, by Candidate A's rotation) and a lower-range requirement: decay **uniformly over all
  `k_0 <= k < a(M)`**, for all large `M`.  The lower range is NOT "fixed-`k` decay": pointwise decay at each fixed
  `k` plus orbit normality does not supply uniformity over the growing intermediate range (Astra, 20:24Z).
  What Theorem 3.1 establishes is the one direction that matters here: pointwise fixed-`k` summaries, even
  in total variation and with every other summary added, do not imply the scheduled rung.  Whether orbit
  normality implies the uniform lower-range requirement is settled in the negative WITHOUT the second-moment
  summary, and open with it.  Witness (orbit fixed first, as the quantifier remark requires): let `x_0` be
  normal with digits `d`, let `a = a(n)` grow slowly, and write `r_n` for the `a`-digit block numeral
  `d_{n-a} ... d_{n-1}`, so `r_{n+1} = 4 r_n + d_n - 4^a d_{n-a}`.  Put `C_n = 4^a E_n + r_n` with `E` the carries of
  an independent Poisson background of mean `L/4^a` (at least 3).  Then

      W_{n+1} = 4 C_n - C_{n+1} + d_n = 4^a (4 E_n - E_{n+1} + d_{n-a}) = 4^a W'_{n+1},

  where `W'` is the lift of the orbit shifted by `a` with carries `E`, so `W >= 0`, mean `L`, orbit of `W`
  equal to the orbit of `x_0` (Lemma 1.1), hence scheduled decay at every `h != 0`; but `4^a` divides every
  `W_{n+j}`, so `T_k(n)` is an integer and `e(h T_k(n)) = 1` for every `k <= a(M)` in the bulk of `n < M`.  At an index
  where `a` steps up, `r_{n+1} = 4 r_n + d_n` still holds but the `4^a d_{n-a}` term is absent, so `W_{n+1} = 4^{a+1}
  (E_n - E_{n+1})`; restart the background there with `E_{n+1} = 0` to keep `W >= 0`.  Transitions are rare, so
  they and the windows crossing them cost `o(1)`.  The lower range fails at every `k` up to the threshold while the orbit is normal.
  The price is (V): `W` lives on the lattice `4^a Z` with `4^a = 4^A sqrt(L)`, so its variance is `asymp 4^a L`,
  not `(1+o(1)) L`, and no sequence on that lattice with mean `L` can have variance `(1+o(1)) L`.  So: with the
  summary package weakened by dropping (V), `EventualPrefixDecay h` is strictly stronger than normality at `h`;
  with (V) kept, whether it is strictly stronger remains open.

## 5. Retraction

My `OBSTRUCTION-2026-09-22-g4-lane-b-invention-round.md`, section 8 (late addition), named the missing input of
the Riesz countermodel as "the exact orbit relation `4 T_k(n) - T_{k-1}(n+1) = omega(n+1)` (shift consistency
across rows) and multiplicativity".  Lemma 1.1 shows the orbit relation holds for EVERY nonnegative integer
sequence, and Theorem 3.1 exhibits sequences satisfying it exactly, with all the summaries, and no scheduled
cancellation.  Shift consistency is therefore not an ingredient at all.  The sentence is withdrawn; a dated
correction is appended to that note.  What survives of section 8 is the sharpening of the sweep's item 2
(fixed-`k` decay plus tail summaries does not imply scheduled decay), now with a one-sequence witness.

## 6. The remaining lemma, and why it is not a reduction

Write `N_J(n) = floor(4^J T_inf(n)) = sum_{i=1}^J 4^{J-i} omega(n+i) + C^omega_{n+J}` (Lemma 2.1 applied to
`omega`).  Then `e(h N_J(n)/4^J) = e(h T_inf(n)) e(-h {4^J T_inf(n)}/4^J) = e(h X_n)(1 + O(|h|/4^J))`, so:

**The target at frequency `h` is the vanishing of the single Fourier coefficient `(1/M) sum_{n<M} e(h N_J(n)/4^J)`,
for `J = J(M) = (1/2) log_4 L_M + A(M)` with any `A -> infinity`, in ordinary average over `n < M` at every large
`M`.**  This is one frequency at a time, as the Weyl criterion demands; it is strictly weaker than
equidistribution of `N_J mod 4^J` in total variation, and the two are not to be identified (Astra's caution (b)).

This is equivalent to normality at `h` (up to `O(|h| 4^{-J})`), so it is not a reduction.  Its value is that it
names the object no summary reaches: `N_J mod 4^J` couples the leading residues `omega(n+1) mod 4`,
`omega(n+2) mod 16`, ... with the carry `C^omega_{n+J} mod 4^J`, where `4^J = 4^A sqrt(L)` is a slowly growing
multiple of the standard-deviation scale of the carry: `sqrt(L/15)` in the independent model, and for `omega`
itself of order `sqrt(L)` by Minkowski over the geometric weights with the shifted Turan-Kubilius bound
(`<= sqrt(L)/3`; the value `1/15` is the model's, not a proved arithmetic variance).  For fixed `J` the carry is spread over all of
`Z/4^J` (that is why fixed prefixes cancel in every model); at `J = (1/2) log_4 L + A` it is concentrated on a
`4^{-A}` fraction of the residues
and the leading residues have to do the work; above that the carry is frozen and nothing changes.
Theorem 3.1 is the witness that fixed-`J` laws, singleton laws, second moments, the whole-window Gaussian
limit, exact shift consistency, and (via (c)) any prescribed limiting phase law are jointly silent about
`N_J mod 4^J` at that `J`.

**Sharp version (Astra, sections 12-16 of the companion file, refereed by me 21:40Z, no defect).**  In the
zero-orbit model, for ANY schedule `1 <= J(M) <= K(M)` the empirical `J`-block TV to `Pois(L)^J` tends to 0 iff
`4^J/sqrt(L) -> 0`, tends to 1 if the ratio tends to infinity, and tends to `F(c) = (1/2) int_0^1 |g_c - 1|` (wrapped
Gaussian of variance `1/(15c^2)`) when `4^J/sqrt L -> c`; moreover the whole block TV equals the terminal carry's
residue TV to uniform, up to `o(1)` uniform in `J` (an exact finite isometry: each residue class carries exactly
`1/4^J` of the smoothed product mass).  So the threshold named above is exact, one realization serves every
schedule, and the transition is located at `4^A = c`.  Consistent with Candidate A's tail determinism: the
same scale `4^J asymp sqrt L` at which the block law separates from Poisson is the scale above which the
scheduled phase freezes.

What an arithmetic input would have to say: the distribution of the carry
`floor(sum_{j>=1} omega(n+J+j)/4^j)` modulo `q asymp sqrt(L)`, jointly with `omega(n+1) mod 4` and the next few
residues, at natural density on every scale.  The Kubilius model and joint Erdos-Kac at shifts give the joint
CLT at scale `sqrt(L)` (the obstruction note, section 4, already records that this reaches exactly the frozen
boundary and says nothing about `omega(n+1) mod 4`); a local version modulo `q asymp sqrt(L)` is a Fourier
coefficient at a frequency of size `1/q` in the carry, i.e. a frequency `h' = h 4^{-J}` in `T_inf(n+J)` -- which is
the original problem one window later.  I do not see an arithmetic statement about carries that is weaker
than the target, and I record that as an open requirement, not an impossibility.

## 7. Referee verdict on Astra's file

Load-bearing points (i)-(vi) of `ROUND2-shift-consistency-astra.md` section 9, checked independently (details in
`agent-mail/shift-consistency/20260922T200757Z-fable-…md`):

(i) preimages in (2.1): complete, with `A_i + C_i = 4 C_{i-1} + b_i` closing the forward/backward loop and the
mod-`4^J` residue condition implying integrality of every intermediate carry by reduction mod `4^{J-i}`.
(ii) residue uniformity from the single site `A_{J+1}` uniformly in the conditioned carry: correct, and better
than my own whole-tail Erdos-Turan route.  (iii) reverse filtration: `Y_n` is `F_{n+1}`-measurable,
`E(Z_n | F_{n+J+2}) = 0`, `Z_{n+J+1}` is `F_{n+J+2}`-measurable; iterated conditional Hoeffding gives Azuma; the
constant 32 is loose.  (iv) union over `2^{|S_M|}` subsets with `t = M^{-1/8}`: summable.  (v) recentering and
dyadic passage: correct.  (vi) infinite remainder of (7.1): correct.  Arithmetic spot checks: `Var((N - lambda)^2)
= lambda + 2 lambda^2`; `4^K in (a^2, 4a^2]`.  **No defect found.**  Astra's file is not modified.

## 8. Probe 15 (`probes/carry_lift.py`)

Hand-computed controls in `--selftest`: the `J = 1` block law for `p` uniform on `{3,4,5,6}` and uniform terminal
carry (`P(W=3) = 1/4`, `P(W=2) = 3/16`, `P(W=0) = 1/16`, enumerated by hand from the 16 pairs), the `J = 2` values
`P(W=(3,3)) = 1/16` and `P(W=(2,4)) = 9/256` from (2.3), the residue lock `W = -c mod 4`, the exact identities (1.4)
in integer arithmetic for `x_0 = 0` and `x_0 = 1/3`, and the Poisson(8) arithmetic behind (2.3).  The main run
(`M = 10^6`, backgrounds `3 + Pois(L)`, `L in {8, 64, 1000}`, orbits `0`, `1/3`, random digits) reports, per
frequency `h in {1,2,3}`: fixed `k = 1,2,3` means, the scheduled `K` mean, the orbit Weyl sum, and the (F')
bound.  Readings (`data-2026-09-22-carry-lift.txt`):

- The scheduled mean equals the orbit Weyl sum within the (F') bound in all 27 rows, and the bound is nearly
  attained: the difference is the deterministic rotation `e(-h C-bar/4^K)` of Candidate A, not noise.
- Fixed-prefix decay at `k` sites needs the carry uniform mod `4^k`, i.e. `L (1 - cos(2 pi/4^{k+1})) >> 1`: at
  `L = 64` only `k = 1` cancels (`0.006`), at `L = 1000` `k = 1, 2` cancel (`< 0.005`) and `k = 3` does not (`0.73`).
  This is Astra's `eta_J`, visible; `L = 8` is pre-asymptotic even at `k = 1` (carry mod 4 is `[0.27, 0.04, 0.18,
  0.51]`), and the printed `P(W = 11)` there is a control showing that the uniform-carry prediction is NOT met at
  small `L`, not a check of (2.3).
- Singleton law: at `L = 64` the empirical law is within sampling noise (`0.0045` vs `0.007`) of the exact 4-point
  smoothing of `Pois(64) + 3`, and its TV to `Pois(64)` is `0.075`, matching the shift-by-`1.5` estimate
  `1.5/sqrt(2 pi 64) = 0.075`.  At `L = 1000` the TV to `Pois(L)` is at noise level.
- The residue lock `W_{n+1} + C_{n+1} = 0 mod 4` holds at every `n` (fraction `1.0000`) while the singleton law is
  Poisson-smooth: the parity-locking obstruction and its resolution by carry uniformity, side by side.

## 9. Scope

Not an arithmetic sequence.  On the brief's stretch target, exact `omega` singleton marginals, two facts
(Astra, 20:11Z): (i) in the **empirical** reading - the histogram of `W_1..W_M` equals that of `omega(1)..omega(M)`
for every large `M` - subtracting the `M` and `M-1` histograms forces `W_M = omega(M)` eventually, so that reading
admits no alternative sequence at all; the Riesz note's exact marginals are probability marginals at each
scale, a different quantifier, and no correction mechanism for a one-sequence version has been established.
(ii) Replacing the Poisson background by independent copies of the `omega(U)`-law keeps the residue
uniformity (one-site root-of-unity decay at `4^{J+1}`-th roots) but the smoothing step needs small
**translation** TV for that lattice law, which root-of-unity decay plus a CLT do not give; a local limit
estimate would.  So "smoothed-`omega` singletons" is **conditional on translation smoothness of the
`omega(U)`-law**, not claimed.  The singleton law of `W` in the theorem is, asymptotically, the 4-point smoothing
of `Pois(L) + 3` (exactly: (2.3) with `J = 1`, whose carry-residue factor is only approximately uniform and whose
mean drifts), at TV distance `O(1/sqrt L)` from `Pois(L)`.  Nothing against G4
normality; the Riesz note and Astra's file are unchanged.  No formalization launch is warranted: the theorem
is a countermodel, not a node of the conjecture graph, and the exact reformulation of section 4 is a
one-line identity a future lap can state as a Lean lemma if a consumer wants the converse direction.
