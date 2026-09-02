"""Emit Lean certificate data for a PER-DIGIT choice of channel subsets:
`subs[w]` is the multiplier set used for digit `w`.  Same encoding as
`mahler_collapse_cert.py` (which fixes one subset for all digits)."""
import sys
from mahler_collapse_cert import certificate

def emit(g, subs, tag):
    out = []
    for w, mults in enumerate(subs):
        c = certificate(g, list(mults), w)
        L = ", ".join(str(s) for s in c['live'])
        R = ", ".join(f"({s}, {v})" for s, v in sorted(c['rho'].items()))
        O = ", ".join(f"({s}, {v})" for s, v in sorted(c['omega'].items()))
        F = ", ".join(f"({s}, ({x}, {sp}))" for s, (x, sp) in sorted(c['forced'].items()))
        ch = ", ".join(f"⟨{a}, 0, [w]⟩" for a in mults)
        out.append(f"""/-- Digit `{w}`: channels {list(mults)}, ambient `{c['S']}`, {c['nlive']} live. -/
def {tag}Chans{w} (w : ℕ) : List ZChannel := [{ch}]

def {tag}live{w} : ℕ → Bool := fun s => [{L}].contains s

def {tag}rho{w} : ℕ → ℕ := fun s =>
  (([{R}] : List (ℕ × ℕ)).lookup s).getD 0

def {tag}omega{w} : ℕ → ℕ := fun s =>
  (([{O}] : List (ℕ × ℕ)).lookup s).getD 0

def {tag}forced{w} : ℕ → Option (ℕ × ℕ) := fun s =>
  ([{F}] : List (ℕ × ℕ × ℕ)).lookup s

theorem {tag}_cert{w} : checkCertA (fun σ s' => gfamPred {g} ({tag}Chans{w} {w}) (σ % {g}) (σ / {g}) s')
    {g} {c['S']} {tag}live{w} {tag}rho{w} {tag}omega{w} {tag}forced{w} = true := by
  decide +kernel
""")
        print(f"-- w={w}: mults {list(mults)} ambient {c['S']} live {c['nlive']} "
              f"rho_nz {len(c['rho'])} omega_nz {len(c['omega'])} forced {len(c['forced'])}",
              file=sys.stderr)
    return "\n".join(out)

if __name__ == "__main__":
    g = 7
    subs = [(1,2,3,4,5,6,8), (1,3,4,5,6,9), (1,2,3,4,5,6), (1,2,3,4,5,6,8),
            (1,2,3,4,5,6), (1,3,4,5,6,9), (1,2,3,4,5,6,8)]
    print(emit(g, subs, "m7"))
