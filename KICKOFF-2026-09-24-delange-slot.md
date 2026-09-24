# KICKOFF 2026-09-24 — the Leaf-B slot (Delange-type twisted mean)

Worktree `~/src/nn-delange`, branch `wip/delange-slot`.  Opus/low.  Work in
`src/NormalNumbers/DelangeSlot.lean` plus new helper files `src/NormalNumbers/DelangeSlot*.lean`.
Never touch other files' statements, `papers/`, `agent-mail/`, `Maze.lean`, other KICKOFFs.

## Target

Two RATIFIED theorems (Ren, 2026-09-24).  Prove both without changing any statement, definition or
binder.  Never delete or rename them; a leaf that resists stays a named `sorry`.
1. `omegaLarge_mean_tendsto_zero` (untwisted).  First rung.
2. `twisted_omegaLarge_mean_tendsto_zero` (twist `e(jm/Q)`).

**Route: NOT full Halász** (Trevor: "let others do the legwork for general").  Use that `f(p) = z` is
CONSTANT on primes `> P`:
- (a) Selberg–Delange-lite: `Σ f(n)χ(n) n^{−s} = G(s)·L(s,χ)^z` near `s = 1`, with mathlib
  `LFunction_ne_zero_of_one_le_re`, `riemannZeta_residue_one`.  Then a Tauberian step (look in
  mathlib and `~/src/reservoir/AlexKontorovich/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/Wiener.lean`;
  that repo is readable, not a dependency; copy lemmas in if needed).
- (b) Elementary: Kubilius model / fundamental lemma.  For `y = N^{1/log log N}`, the law of
  `ω_{(P,y]}` is close to the independent model, so `E z^{ω_{(P,y]}} ≈ Π_{P<p≤y}(1 + (z−1)/p) → 0`.
  Primes `> y` number `≤ log log N`.  ⚠️ Maze row "full prime-incidence independence" (TV → 1 at
  FIXED-power cutoffs) says the cutoff must be `N^{o(1)}`.  The repo already has Brun lower-sieve
  pieces (`PrimeModelBrun*`), Mertens (`primeRecipSum_le`), and CRT counts; reuse them.
- For the twist: split `m = s·t` (`P`-smooth × `P`-rough), reduce to residue classes of `t`
  mod `Q' | Q`, and expand in Dirichlet characters.
**Probe before building:** in `probes/`, measure the twisted mean at `N = 10^6` for a few `z`, `P`,
`Q`, `j`, against the `Π(1 + (z−1)/p)` prediction.

Build: `lake build NormalNumbers.DelangeSlot` (warm tree; never run `lake exe cache get`).  Proof
tier: `native_decide`/boosts fine.  Commit each green step.  Each HANDOFF names the current crux.
