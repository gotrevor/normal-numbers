"""Run ./exact3-review test.  Checks the real C CLI and exact entry script.

The sanitizer regression is an expected failure at dfde6d34, not a passing
soundness check.  Passing the other tests does not prove the enclosure algorithm.
"""
import gzip
import json
import os
import random
import re
import shlex
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent


def run(argv, **kwargs):
    return subprocess.run(argv, text=True, capture_output=True, timeout=45, **kwargs)


@pytest.fixture(scope="module")
def candidate(tmp_path_factory):
    directory = tmp_path_factory.mktemp("exact3-review")
    weights = directory / "weights.txt"
    weights.write_bytes(gzip.decompress((HERE / "W449_N128_M24_D6.txt.gz").read_bytes()))
    values = [int(line) for line in weights.read_text().splitlines()]
    assert len(values) == 25 * 128 * 24
    assert all(0 <= value <= 2**40 for value in values)
    return directory, weights, values


def compile_kernel(directory, sanitize=False):
    binary = directory / ("exact3-ubsan" if sanitize else "exact3")
    command = [*shlex.split(os.environ.get("CC", "cc")), "-O2"]
    if sanitize:
        command += ["-fsanitize=undefined", "-fno-sanitize-recover=undefined"]
    command += [str(HERE / "exact3.c"), "-o", str(binary)]
    if sys.platform != "darwin":
        command.append("-lm")
    result = run(command)
    assert result.returncode == 0, result.stderr
    return binary


@pytest.fixture(scope="module")
def checked(candidate):
    directory, weights, values = candidate
    binary = compile_kernel(directory)
    before = weights.read_bytes()
    result = run([str(binary), "128", "24", "6", "16", "check", str(weights)])
    assert weights.read_bytes() == before, "read-only mode changed the weights"
    return binary, result


def test_frozen_weights_pass_read_only_mode(checked):
    _, result = checked
    assert result.returncode == 0, result.stdout + result.stderr
    assert "CHECK PASSED: positive 74431/76800, failures 0" in result.stdout


def test_lean_embedding_matches_the_frozen_weights(candidate):
    _, _, values = candidate
    source = (HERE.parents[1] / "src" / "CertData" / "Gate4.lean").read_text()
    block = source.split("def wString : String :=", 1)[1].split("def W : Array Int", 1)[0]
    literal = block[block.index('"') + 1:block.rindex('"')]
    assert [int(value) for value in re.findall(r"\d+", literal)] == values


def test_actual_cli_geometry_matches_entry_artifact_and_exact_radius_bound(checked):
    _, result = checked
    rows = [line for line in result.stdout.splitlines()
            if line.startswith(("edge ", "dlo ", "dhi "))]
    assert rows == (HERE / "exact3_edges449.txt").read_text().splitlines()
    edges = [int(line.split()[1]) for line in rows if line.startswith("edge ")]
    bounds = {line.split()[0]: int(line.split()[1]) for line in rows
              if not line.startswith("edge ")}
    lo, hi = bounds["dlo"], bounds["dhi"]
    assert lo**100 * 3**449 < 2**9000 < hi**100 * 3**449
    assert edges[0] == 2 * lo and edges[-1] == 6 * hi
    assert all(a < b for a, b in zip(edges, edges[1:]))


def test_mutated_parent_weight_is_rejected(candidate, checked):
    directory, _, values = candidate
    binary, _ = checked
    mutation = directory / "mutation.txt"
    values = values.copy()
    values[0] = 10**14
    mutation.write_text("".join(f"{value}\n" for value in values))
    result = run([str(binary), "128", "24", "6", "16", "check", str(mutation)])
    assert result.returncode != 0
    assert "FAIL bin 0" in result.stdout


def test_exact_entry_reports_positive_root(candidate):
    _, weights, _ = candidate
    result = run([sys.executable, str(HERE / "entry_exact.py"), str(weights),
                  str(HERE / "exact3_edges449.txt")], cwd=HERE)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "root weight 1 1.0" in result.stdout


def test_kernel_lower_bounds_against_independent_rational_points(candidate):
    """A bounded falsification test, not a proof for all rectangles or phases."""
    directory, weights, values = candidate
    geometry = (HERE / "exact3_edges449.txt").read_text().splitlines()
    edges = [Fraction(int(line.split()[1]), 2**90) for line in geometry
             if line.startswith("edge ")]
    bounds = {line.split()[0]: Fraction(int(line.split()[1]), 2**90)
              for line in geometry if not line.startswith("edge ")}
    delta = (bounds["dlo"] + bounds["dhi"]) / 2
    transitions = json.loads((HERE / "sft449.json").read_text())["T"]

    def oracle(s, x, rho):
        total = 0
        for path in range(64):
            state = s
            for bit in range(5, -1, -1):
                state = transitions[state][(path >> bit) & 1]
                if state < 0:
                    break
            if state < 0:
                continue
            left, width = x + path * rho / 64, rho / 64
            good = True
            # Directly test the final interval against each resolved stage;
            # no zone-carrying recursion or C enclosure code is reused.
            while width <= 2 * delta:
                right = left + width
                for center in range(left.__floor__() - 1, right.__ceil__() + 2):
                    if not (right < center - delta or left > center + delta):
                        good = False
                        break
                if not good:
                    break
                left *= 3
                width *= 3
            if good:
                left -= left.__floor__()
                i = (128 * left).__floor__()
                js = [j for j in range(24) if edges[j] <= width <= edges[j + 1]]
                assert js
                total += min(values[state * 128 * 24 + i * 24 + j] for j in js)
        return total

    rng = random.Random(449)
    cases, expected = [], []
    for case in range(64):
        s = rng.randrange(25)
        xn = rng.randrange(1, 2**20 - 1) * 2**40
        rn = rng.randrange((2 * delta * 2**60).__ceil__() + 2,
                           (6 * delta * 2**60).__floor__() - 2)
        if case < 4:
            # Child width lies inside the ambiguous resolution enclosure.
            rn = int(4 * delta * 2**60) + case - 2
        radius = case % 2  # both point boxes and positive-width boxes
        cases.append(f"{s} {xn-radius} {xn+radius} {rn-radius} {rn+radius}\n")
        expected.append(oracle(s, Fraction(xn, 2**60), Fraction(rn, 2**60)))
    queries = directory / "queries.txt"
    queries.write_text("".join(cases))
    driver, binary = directory / "point-driver.c", directory / "point-driver"
    driver.write_text(f'''#define main kernel_main
#include {json.dumps(str(HERE / "exact3.c"))}
#undef main
static Z parse_z(char *p) {{ Z z=0; while(*p>='0' && *p<='9') {{ z=z*10+*p-'0'; p++; }} return z; }}
int main(int argc, char **argv) {{
  N=128; M=24; D=6;
  W=calloc(25*128*24,sizeof(long long));
  FILE *f=fopen(argv[1],"r"); char line[256]; long q=0;
  while(fgets(line,256,f)) W[q++]=strtol(line,0,10); fclose(f);
  f=fopen(argv[2],"r"); int j=0;
  while(fgets(line,256,f)) {{
    if(line[0]=='e') redge[j++]=parse_z(line+5);
    else if(line[1]=='l') dlo=parse_z(line+4);
    else dhi=parse_z(line+4);
  }} fclose(f);
  f=fopen(argv[3],"r");
  while(fgets(line,256,f)) {{
    char *p=line; int s=strtol(p,&p,10);
    Z xl=(Z)strtol(p,&p,10)<<30, xh=(Z)strtol(p,&p,10)<<30;
    Z rl=(Z)strtol(p,&p,10)<<30, rh=(Z)strtol(p,&p,10)<<30;
    needx=needr=0;
    printf("BOUND %lld\\n",go(s,xl,xh,rl,rh,0,-1,-1));
  }} fclose(f); return 0;
}}
''')
    command = [*shlex.split(os.environ.get("CC", "cc")), "-O2", str(driver), "-o", str(binary)]
    if sys.platform != "darwin":
        command.append("-lm")
    compiled = run(command)
    assert compiled.returncode == 0, compiled.stderr
    result = run([str(binary), str(weights), str(HERE / "exact3_edges449.txt"), str(queries)])
    assert result.returncode == 0, result.stderr
    actual = [int(line.split()[1]) for line in result.stdout.splitlines() if line.startswith("BOUND ")]
    assert len(actual) == len(expected)
    assert any(value > 0 for value in actual)
    for case, (lower, point_value) in enumerate(zip(actual, expected)):
        assert 0 <= lower <= point_value, (case, lower, point_value)


@pytest.mark.xfail(strict=True, reason="dfde6d34 shifts a negative window index left in child()")
def test_read_only_checker_has_no_undefined_integer_arithmetic(candidate):
    directory, weights, _ = candidate
    binary = compile_kernel(directory, sanitize=True)
    result = run([str(binary), "128", "24", "6", "0", "check", str(weights)])
    assert "runtime error:" not in result.stderr, result.stderr
