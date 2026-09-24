# OBSTRUCTION 2026-09-24 — the periodic-rational-approximant (CRT) route to C1 is dead

**Status: REFUTED by a scale mismatch.  Do not re-attempt.**  Recorded because the repo's existing
CRT machinery (`G4WiringCRT.lean`, the `radical-crt` lemmas) makes this route very tempting.

## The route

`ω` is additive, so (already in the repo, `primeSumAtBase_eq_primeLambertAtBase`)

    G4_b  =  Σ_{p prime} 1/(b^p − 1).

Truncate at `P`: `G_P := Σ_{p ≤ P} 1/(b^p − 1)`.  Put `Λ(P) := lcm{p : p ≤ P}`.  Every `p ≤ P`
divides `Λ(P)`, so `(b^Λ − 1)/(b^p − 1) ∈ ℤ` and

    G_P = M_P / (b^{Λ(P)} − 1),      M_P = Σ_{p ≤ P} (b^{Λ}−1)/(b^p−1) ∈ ℕ.

A rational `M/(b^Λ − 1)` with `0 ≤ M < b^Λ` has a PURELY PERIODIC base-`b` expansion of period `Λ`,
whose period block is just the base-`b` word of `M`.  So for the approximant `G_P` the C1 statistic
is not a density at all: it is an EXACT finite count over `n ∈ [0, Λ(P))`, and casting-out-nines is
available on the period (the period digit sum is `≡ M_P mod (b−1)`, and
`(b^Λ−1)/(b^p−1) ≡ Λ/p`, so `M_P ≡ Σ_{p≤P} Λ/p (mod b−1)`).  Attractive: C1 would become a purely
finite/CRT equidistribution question about the words `M_P`, with no Elliott input at all.

## Why it cannot work

The tail is `0 < G4_b − G_P ≤ 2 b^{−P}`, so `G_P` only controls the digits of `G4_b` at positions
`≲ P` (and even there only off the long-run-of-`(b−1)`s set where the tail's carry propagates back).
To say anything about the window digit sums at positions `n < N` one therefore needs

    P ≳ N.

But `Λ(P) = lcm{p ≤ P}` is divisible by every prime `≤ P`, so `Λ(P) ≥ ∏_{p≤P} p = e^{(1+o(1))P}`.
Hence the period satisfies

    Λ(P) ≥ e^{(1+o(1))N}   ≫   N,

i.e. **the period is exponentially longer than the window of `n` we are averaging over.**  The
average of a `Λ`-periodic sequence over `n < N` with `Λ ≫ N` carries no information about the period
average — we would be looking at an exponentially small initial segment of one period.  The
periodicity is real but asymptotically inert.  Concretely: `Λ(P)` already exceeds `2·10^{11}` at
`P = 31`, while `P = 31` licenses statements only about `n ≲ 31`.

There is no repair by choosing `Λ` smaller: `Λ` must be divisible by every `p ≤ P` for `G_P` to be
a fraction with denominator `b^Λ − 1` at all, and any coarser common period fails to make the
individual `1/(b^p−1)` periodic.

## What survives

* The identity `G4_b = Σ_p 1/(b^p−1)` is still the right way to see that `G4_b` is a sum of
  periodic rationals, and the tail bound `≤ 2b^{−P}` is genuine.  It just cannot be used
  asymptotically in `n`.
* The correct statement of the obstruction is the same one the probe found from the other side: C1's
  content is asymptotic in a regime (`ω(m) ≳ b`, i.e. `m` past the `b`-th primorial) that no finite
  approximation reaches.  See `omegaCarry_eq_zero_of_omega_le` in `SwingC1.lean` and the VERDICT
  block of `probes/swingc1_autocorr.py`.

## Verdict

The live leaf stays `HAutoCorr` (`SwingC1.lean`), which is EXACTLY equivalent to `ConjC1`
(`conjC1_iff_hAutoCorr`).  It is an Elliott-type input and will not be reduced to a finite
computation.
