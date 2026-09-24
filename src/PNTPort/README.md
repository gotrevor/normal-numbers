# PNTPort — vendored quantitative PNT

Ported 2026-09-24 from **AlexKontorovich/PrimeNumberTheoremAnd** (Apache-2.0), upstream toolchain
`v4.32.2`, into our `v4.33.1` tree.  Import closure of `PNTPort.MediumPNT` only (14 files,
~12k lines).  Upstream is sorry-free; the port needed **no mathematical edits**:

* `import Architect`, `@[blueprint …]` attributes and `blueprint_comment …` blocks stripped
  (they are the upstream blueprint tooling, not mathematics);
* `PrimeNumberTheoremAnd.*` module prefixes rewritten to `PNTPort.*`;
* two one-line tactic repairs in `Fourier.lean` (`‖(z : Circle) : ℂ‖ = 1` now needs
  `Circle.norm_coe`, and `1 + 1 ≤ 2` needs `norm_num`).

Headline, verified axiom-clean in `Check.lean`:

    theorem MediumPNT : ∃ c > 0, (ψ - id) =O[atTop] fun x ↦ x * Real.exp (-c * (Real.log x) ^ (1/10 : ℝ))

`PNTPort` is a separate `lean_lib` and is **not** in `defaultTargets`; it enters the build only
through the modules that import it.  Do not edit these files except to repair toolchain drift.
