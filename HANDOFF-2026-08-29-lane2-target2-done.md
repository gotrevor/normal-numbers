# HANDOFF 2026-08-29: lane-2 target 2 done (scoped run complete)

Scoped objective `sorry-free:src/NormalNumbers/KickDynamicsOneRun.lean` is MET at
commit e602c40, full build green (8778 jobs).

- `oneRun_le_of_sliverEscape` proved, trust triple `[propext, Classical.choice, Quot.sound]`.
- Width mismatch resolved honestly: the one-run dichotomy only certifies the WIDE sliver
  `1 − 2/(n+j+1)` (tail bound only `τ ≤ 1/(n+1)`), so the frozen narrow `SliverEscape`
  cannot serve. Froze the wide variant node `SliverEscapeWide` in the same file with a
  provenance docstring; the edge takes that hypothesis; constant tightened +3 → +2.
- Bonus edge `sliverEscape_of_wide : SliverEscapeWide → SliverEscape` (wide is the
  stronger node). Frozen `SliverEscape` and all landed modules untouched.
- Decision recorded in PENDING_WORK.md (2026-08-29 lane-2 lap entry).

Next per operator brief (if a new run is scoped): target 3, the Glaisher/Sun congruence
(`LnTwoPrimeWindow.lean` docstring; probe `experiments/lntwo_fermat_bridge.py`).
