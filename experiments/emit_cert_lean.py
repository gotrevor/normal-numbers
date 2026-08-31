#!/usr/bin/env python3
"""Emit the Lean KData + chunk files for a signed-adder certificate JSON.

Reproduces the packed-table encoding that `AdderTowerC8KData.lean`'s
`c8OmegaK` decode expects, so a family certified in Python by
`adder_signed_emit.py` can be handed to the kernel `checkCertP` path
(`signed_engine`).  Faithfulness is self-checked: run with `--check c8`
to regenerate the committed C8 tables and diff.

Omega packing (must match the Lean decode exactly):
  c<X>OmegaK s = ((table.getD (s/2048) []).getD (s%2048/64) 0)
                  / 8 ^ (s%64) % 8
so  table[outer][mid] = sum_{i<64} omega[outer*2048 + mid*64 + i] * 8^i,
with dims (ambient/2048) outer lists of 32 mids each.  Requires
ambient % 2048 == 0 (padded via getD-default 0 otherwise, but we assert).

Usage:
  emit_cert_lean.py <jsonname> <PascalTag> <chunkSize>
    e.g. emit_cert_lean.py secondset C9 6144
  emit_cert_lean.py --check c8    # regenerate C8 tables to stdout for diff
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).parent
CERTS = HERE / "certs"


def load(name):
    return json.loads((CERTS / f"adder_cert_{name}.json").read_text())


def pack_omega(omega, ambient):
    assert ambient % 2048 == 0, f"ambient {ambient} not a multiple of 2048"
    outers = ambient // 2048
    table = []
    for o in range(outers):
        row = []
        for m in range(32):
            base = o * 2048 + m * 64
            v = 0
            for i in range(64):
                v += omega[base + i] * (8 ** i)
            row.append(v)
        table.append(row)
    return table


def gen_kdata(cert, tag):
    """Return the body (family + live/rho/omega/forced defs) as Lean text."""
    ambient = cert["ambient"]
    live = cert["live"]
    rho = cert["rho"]
    omega = cert["omega"]
    fsig = cert["forced_sig"]
    fdst = cert["forced_dst"]
    chans = cert["channels"]

    fam = ", ".join(
        f"⟨{c['a']}, {c['b']}, {c['word']}⟩".replace(" ", " ")
        for c in chans)
    fam = ", ".join(
        "⟨%d, %d, [%s]⟩" % (c["a"], c["b"],
                                      ", ".join(str(x) for x in c["word"]))
        for c in chans)

    live_list = [s for s in range(ambient) if live[s]]
    rho_list = [(s, rho[s]) for s in live_list if rho[s] != 0]
    forced = [(s, fsig[s], fdst[s]) for s in range(ambient) if fsig[s] >= 0]
    table = pack_omega(omega, ambient)

    L = []
    L.append(f"def {tag}Family : List ZChannel :=")
    L.append(f"  [{fam}]")
    L.append("")
    L.append(f"def {tag}Live_list : List ℕ := "
             + "[" + ", ".join(str(s) for s in live_list) + "]")
    L.append(f"def {tag}LiveK : ℕ → Bool := "
             f"fun s => {tag}Live_list.contains s")
    L.append("")
    L.append(f"def {tag}RhoK_list : List (ℕ × ℕ) := "
             + "[" + ", ".join(f"({s}, {r})" for s, r in rho_list) + "]")
    L.append(f"def {tag}RhoK : ℕ → ℕ := "
             f"fun s => ({tag}RhoK_list.lookup s).getD 0")
    L.append("")
    tbl = ",\n   ".join(
        "[" + ", ".join(str(x) for x in row) + "]" for row in table)
    L.append(f"def {tag}OmegaTable : List (List ℕ) :=")
    L.append(f"  [{tbl}]")
    L.append("")
    L.append(f"def {tag}OmegaK : ℕ → ℕ := fun s =>")
    L.append(f"  (({tag}OmegaTable.getD (s / 2048) []).getD "
             f"(s % 2048 / 64) 0) / 8 ^ (s % 64) % 8")
    L.append("")
    L.append(f"def {tag}ForcedK : ℕ → Option (ℕ × ℕ)")
    for s, g, d in forced:
        L.append(f"  | {s} => some ({g}, {d})")
    L.append("  | _ => none")
    return "\n".join(L)


def check_c8():
    cert = load("flagshipC")
    print(gen_kdata(cert, "c8gen"))


if __name__ == "__main__":
    if sys.argv[1] == "--check":
        check_c8()
        sys.exit(0)
    name, tag, chunk = sys.argv[1], sys.argv[2], int(sys.argv[3])
    cert = load(name)
    ambient = cert["ambient"]
    print(gen_kdata(cert, tag))
    print(f"\n-- ambient {ambient}, chunkSize {chunk}, "
          f"nchunks {-(-ambient // chunk)}")
