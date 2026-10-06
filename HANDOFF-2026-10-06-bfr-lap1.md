# HANDOFF 2026-10-06 — BFR directive lap 1 (KICKOFF-2026-10-06-bfr.md)

Verdict: BFR-bet confidence < 1%; every candidate has a frozen statement and a verdict.

| # | Declaration (StretchBFR.lean) | Verdict |
|---|---|---|
| 2 | `card_cantor_hyperbola_le` | PROVED (axioms clean): ≤ 2^j when 2RQ < 3^j ≤ 3^b; the 3-adic covering bound. Maze "3-adic Farey separation as a BFR count" (vacuous, kernel) |
| 4 | `eq_of_hyperbola_low` | PROVED for any base B, only gcd(q,B)=1 used; composite base loses only the q = B^v q₀ reduction |
| 1,3 | `NKPowerSaving` (open def Prop) | Separation (either kind) returns the covering count Q δ^{-dim K}; a saving needs Fourier ℓ¹ dimension = Chow–Varjú–Yu arXiv:2402.18395. Maze "power saving for N_K(Q, delta) from separation" (priorArt) |

Not done: CVY's theorem not transcribed as a Literature Prop (paper not read past abstract; no fabrication).
`card_near_cantor_le`, `windowCount_of_inverseSum` remain sorry (pre-existing, off-bet).
Root `lake build` green; MazeAudit count 167/60.
