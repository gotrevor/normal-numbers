#!/usr/bin/env python3
"""Emit a Lean certificate block (sorted-Array tables + native_decide) from an
`adder_cert_<name>.json` produced by `adder_baseg_emit.py`.

Usage: emit_hitting_sparse.py <certname> <leanPrefix> <chansExpr> <g> <A>
  e.g. emit_hitting_sparse.py h32_w00 h32w00 "h32Chans 0 0" 3 3
Prints the Lean text to stdout.
"""
import json, sys
from pathlib import Path

CERTS = Path(__file__).parent / "certs"


def arr(xs):
    return "#[" + ", ".join(str(x) for x in xs) + "]"


def emit(name, pre, chans, g, A):
    c = json.loads((CERTS / f"adder_cert_{name}.json").read_text())
    S = c["ambient"]
    live = c["live"]; rho = c["rho"]; omega = c["omega"]
    fsig = c["forced_sig"]; fdst = c["forced_dst"]
    lk = [s for s in range(S) if live[s]]
    rk = [s for s in range(S) if rho[s] != 0]
    ok = [s for s in range(S) if omega[s] != 0]
    fk = [s for s in range(S) if fsig[s] >= 0]
    step = f"(fun σ s' => gfamPred {g} ({chans}) (σ % {g}) (σ / {g}) s')"
    L = []
    L.append(f"/-- Certificate `{name}` (`experiments/certs/adder_cert_{name}.json`): "
             f"ambient `{S}`, `{len(lk)}` live states, `{len(ok)}` ranked dead states. -/")
    L.append(f"def {pre}liveK : Array ℕ := {arr(lk)}")
    L.append(f"def {pre}rhoK : Array ℕ := {arr(rk)}")
    L.append(f"def {pre}rhoV : Array ℕ := {arr([rho[s] for s in rk])}")
    L.append(f"def {pre}omegaK : Array ℕ := {arr(ok)}")
    L.append(f"def {pre}omegaV : Array ℕ := {arr([omega[s] for s in ok])}")
    L.append(f"def {pre}forcedK : Array ℕ := {arr(fk)}")
    L.append(f"def {pre}forcedS : Array ℕ := {arr([fsig[s] for s in fk])}")
    L.append(f"def {pre}forcedD : Array ℕ := {arr([fdst[s] for s in fk])}")
    L.append("")
    L.append(f"def {pre}live : ℕ → Bool := fun s => tmem {pre}liveK s")
    L.append(f"def {pre}rho : ℕ → ℕ := fun s => tget {pre}rhoK {pre}rhoV s")
    L.append(f"def {pre}omega : ℕ → ℕ := fun s => tget {pre}omegaK {pre}omegaV s")
    L.append(f"def {pre}forced : ℕ → Option (ℕ × ℕ) := fun s => "
             f"tforced {pre}forcedK {pre}forcedS {pre}forcedD s")
    L.append("")
    L.append(f"theorem {pre}_cert : checkCertA {step}")
    L.append(f"    {A} {S} {pre}live {pre}rho {pre}omega {pre}forced = true := by")
    L.append("  native_decide")
    L.append("")
    return "\n".join(L)


if __name__ == "__main__":
    name, pre, chans, g, A = sys.argv[1:6]
    print(emit(name, pre, chans, int(g), int(A)))
