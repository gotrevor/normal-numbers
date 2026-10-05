# He–Liao 2026 — pin note (added 2026-10-05)

Y. He, L. Liao, *Jarník-type theorem for self-similar sets*, arXiv:2602.01307.  PDF alongside
(gitignored).  Companion: *Hausdorff dimension of τ-approximable points on self-similar sets in
ℝ^d*, arXiv:2608.15686 (`he-liao-2026-tau-approximable-self-similar.pdf`).

## Coverage

Read: abstract, Thm 1.2 (local counting property ⇒ dimension bounds), §6.1 (Thm 6.1 of
Bénard–He–Zhang, Cor. 6.2, Lemma 6.3 of Khalil–Luethi, Prop. 6.4 of Chen, Cor. 6.5).
2608.15686: abstract only.

## What it says

`A_Q(η) = {x : ‖qx‖ < η for some Q ≤ q < 2Q}`.  For a strongly irreducible self-similar measure
with OSC, Prop. 6.4 bounds `μ_ω(A_Q(η))` for every branch, main term `Qη^d` plus an error
`ρ_ω^{−1−dκ/(d+1)} (η/Q)^{dκ/(d+1)}`.  Cor. 6.5: the main term dominates on balls of radius
`≥ Q^{−β}` for `η ∈ [Q^{−α}, Q^{−1/d}]`, with `α − 1/d > 0` small (`κ` not explicit).
2608.15686 proves the Bugeaud–Durand formula for `K` only for `τ ∈ (1, 1 + ε_K)`.

## Use here

Lean: `CantorExactExponentStretch.Literature.HeLiao2026Cor65` (upper half, cylinders).  Verdict:
does not transfer to the stretch range of the exact-exponent triple (Stretch module doc; Maze
row "He-Liao local count on the forced-run measure").
