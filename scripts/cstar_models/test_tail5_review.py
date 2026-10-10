"""Review controls for the tail probes, independent of the expensive search.

The DFS controls use the actual probe function with a one-path toy tree.  They
test accounting semantics, not whether the toy weights occur in gate 4.
The zero-weight and unchargeable-profile cases reproduced defects in the initial
draft; both were repaired in d47bc1d6.  Keep these assertions as regression tests.
"""
import ast
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).parent


def function_from_file(filename, name, environment):
    """Load the real function without executing a probe's top-level search."""
    tree = ast.parse((HERE / filename).read_text())
    function = next(node for node in tree.body
                    if isinstance(node, ast.FunctionDef) and node.name == name)
    module = ast.Module(body=[function], type_ignores=[])
    exec(compile(module, str(HERE / filename), "exec"), environment)
    return environment[name]


def run_single_path(parent_weight):
    # One reachable cell a=0 at each level.  It is Good throughout.  At k=6
    # its weight is parent_weight.  The tail first kills it at k=7.  Its sole
    # k=12 descendant has weight 1.  Thus L_1=1 for BOTH choices of weight.
    environment = {
        "Fraction": Fraction, "MMAX": 1,
        "mass": [Fraction(1), Fraction(0), Fraction(0)],
        "loss": [Fraction(0), Fraction(0)],
        "pmax": [Fraction(0), Fraction(0)],
        "ZW": [0], "ZWL": [Fraction(0)],
        "weight": lambda k, a: Fraction(parent_weight if k == 6 else 1),
        "good": lambda k, a: True,
        "sft": lambda k, a: 0 if a == 0 else 99,
        "bad": lambda k, a: k == 7,
    }
    dfs = function_from_file("tail5_totals.py", "dfs", environment)
    dfs(1, 0, True, 0, Fraction(1), [Fraction(0)])
    return environment


def test_positive_parent_loss_control():
    result = run_single_path(1)
    assert result["loss"] == [0, 1]
    assert result["mass"] == [1, 1, 0]


def test_zero_weight_good_parent_still_contributes_child_loss():
    result = run_single_path(0)
    assert result["loss"] == [0, 1]
    assert result["mass"] == [1, 0, 0]


def test_uncharged_positive_loss_cannot_pass(capsys):
    environment = {"Fraction": Fraction, "GAMMA": Fraction(2),
                   "BUDGET": Fraction(1), "AMBIG": [0], "CLIMB": [0]}
    report = function_from_file("tail5_measure.py", "report", environment)
    try:
        report({(6, 0): (Fraction(0), [Fraction(1)])}, 1, "review control")
    except (ValueError, AssertionError):
        return  # An explicit rejection is also a correct interface.
    output = capsys.readouterr().out
    assert "PASS" not in output


def test_restricting_tail_does_not_order_parent_conditioned_loss():
    # A single parent has two unit-weight children.  Loss is counted only
    # while the parent survives.  An added base can remove that parent.
    def loss(parents, children):
        return sum(1 for p in parents for j in range(2)
                   if 2 * p + j not in children)

    assert loss({0}, {1}) == 1
    assert loss(set(), set()) == 0  # More deletion can decrease loss.
    assert loss({0}, set()) == 2  # Or increase it if the parent remains.


def test_radius_enclosures_used_by_finite_base_measurements():
    # Independent integer comparison certifies the Decimal-generated brackets:
    # lo < b^(-449/100) * SCALE < hi iff lo^100 b^449 < SCALE^100 < hi^100 b^449.
    scale = 10 ** 60
    rad = function_from_file("tail5_measure.py", "rad",
                             {"Decimal": Decimal, "SCALE": scale})
    with localcontext() as context:
        context.prec = 80
        for base in range(2, 41):
            lo, hi = rad(base)
            assert lo ** 100 * base ** 449 < scale ** 100 < hi ** 100 * base ** 449
