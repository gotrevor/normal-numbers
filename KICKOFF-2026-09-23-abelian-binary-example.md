# KICKOFF 2026-09-23 — an infinite binary sequence, abelian-normal but not normal

Branch `wip/g5-prime-subset`.  Engine Opus/low.  Work **only** in
`src/NormalNumbers/AbelianBinaryExample.lean` (new helpers `src/NormalNumbers/Abelian*.lean` are
fine).  Never edit other files' statements; never touch `papers/`, `agent-mail/`, other KICKOFFs.

## Target

The file is seeded (Ren, 2026-09-23) with **ratified statements** and three `sorry`s.  Prove all
three without changing any statement, definition or binder.  Done when the file is sorry-free.
Math: `DESIGN-2026-09-23-binary-abelian-nonnormal.md`; exact numbers:
`probes/abelian_hex_construction.py` (run it; uv shebang).

1. `not_isNormalSequence_xiBits` — likely easiest; do it first.  Show the frequency of the word
   `[0,0,1,1]` tends to `5/64 ≠ 1/16`.  Split positions by `n % 4`; each residue class is a
   function of at most two consecutive hex digits of `c`, whose joint frequencies tend to `1/256`
   by normality of `c` (`PowerBaseLimit.tendsto_winCount_wordOf` or the `IsNormalSequence`
   definition on length-2 words).  The offset-`r` limit is a finite sum over 256 hex pairs —
   `decide`/`native_decide`.  Per-offset limits (exact, offsets r = 0..3): `1/8, 1/16, 1/16, 1/16`; average `5/64`.
2. `isAbelianNormalTwo_xiBits` — the finite core: for every offset `r < 4` and length `L`,
   `#{v ∈ (Fin 16)^s : ones(bits r..r+L-1 of hexSwap-blocks v) = j} = 16^s · choose L j / 2^L`
   with `s` = blocks touched.  Prove it by: (a) the 10 in-block intervals are Binomial under the
   swapped block law (finite, `decide`); (b) windows = suffix + whole blocks + prefix, counts
   multiply, and the Binomial laws convolve (Vandermonde, `Nat.add_choose_eq`).  Then pass from
   hex-word frequencies of `c` (normal) to `onesFreq`, splitting positions by `n % 4`.
   Alternative: go through `isAbelianNormalTwo_iff_symParityMean` if the character side is easier.
3. `exists_abelianNormal_not_normal` — `c := digitOf 16 (Int.fract fullRealW)`: base-16 normal via
   `isNormal_pow (b := 2) (K := 4)` on `isNormal_fullRealW` (`IsNormal` unfolds to
   `IsNormalSequence b (digitOf b (Int.fract x))`), digits `< 16` by `digitOf_lt`, bits `< 2` by
   `Nat.mod_lt`.  Then 1 and 2.

## Tiers

Proof tier: `native_decide`, heartbeat boosts, deprecations fine.  Many small lemmas.  Build:
`lake build NormalNumbers.AbelianBinaryExample` (warm tree; never `lake exe cache get`).  Commit
each green step.
