# On-line requests

## 2026-08-23 — install Lean toolchain v4.33.1 on the box

The read-only elan mount (`/home/lean/.elan/toolchains`) has only v4.29.1 and
v4.31.0.  This repo (and its prebuilt 4.33.1 mathlib oleans in `.lake/`) needs
`leanprover/lean4:v4.33.1`; `elan` can't fetch it (no egress) and hangs.  Every
`lake build` / `lake env lean` here is blocked on this.

**Request**: make `leanprover/lean4:v4.33.1` available to the box — either add
it to the toolchains mount, or `elan toolchain install leanprover/lean4:v4.33.1`
host-side into the shared elan home.

Meanwhile I am developing this lap's proofs against the built v4.31.0 mathlib in
`~/src/goodstein-ab-med` (scratch harness, ported back verbatim), so nothing
else is needed — but final in-repo verification waits on the toolchain.
