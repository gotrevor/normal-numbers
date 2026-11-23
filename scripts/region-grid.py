#!/usr/bin/env -S uv run --quiet python3
"""Insert (or refresh) the region grid section in how-irregular-is-a-number.html.

Lean links are resolved to line numbers in src/NormalNumbers/LandscapeGrid.lean at run time.
"""
import re
import sys
from pathlib import Path

ROOT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent
HTML = ROOT / "docs/how-irregular-is-a-number.html"
LEAN = ROOT / "src/NormalNumbers/LandscapeGrid.lean"
GH = "https://github.com/gotrevor/normal-numbers/blob/master/src/NormalNumbers/"

lean_lines = LEAN.read_text(encoding="utf-8").splitlines()


def line_of(name: str) -> int:
    pat = re.compile(rf"^(theorem|def|lemma) {re.escape(name)}\b")
    for i, ln in enumerate(lean_lines, 1):
        if pat.match(ln):
            return i
    raise SystemExit(f"declaration not found: {name}")


def L(name: str, file: str = "LandscapeGrid.lean") -> str:
    if file == "LandscapeGrid.lean":
        href = f"{GH}{file}#L{line_of(name)}"
    else:
        href = f"{GH}{file}"
    return f'<a class="st st-lean" href="{href}" title="{name}">Lean</a>'


Y = '<span class="mg mg-y">&#10003;</span>'
E = '<span class="mg mg-n">&#8709;</span>'
Q = '<span class="mg mg-q">?</span>'
C = '<span class="st st-cite">cited</span> '


def cell(mark, body, lean):
    return f'<td><div class="gc">{mark}<span>{body}</span></div><div class="gl-row">{lean}</div></td>'


rows = [
    ("not disjunctive in base <span class=\"mono\">b</span>", "some block never appears", [
        cell(Y, "every rational: eventually periodic", L("rat_not_isDisjunctive")),
        cell(Q, "open; Borel says empty", L("algebraic_notDisjunctive_open")),
        cell(Y, "Liouville&#8217;s <span class=\"mono\">&#955;<sub>b</sub> = &#931; b<sup>&#8722;n!</sup></span>; every positive multiple <span class=\"mono\">m&#955;<sub>b</sub></span> too",
             L("liouvilleNumber_cell_notDisjunctive") + " " + L("natMul_liouvilleNumber_not_isDisjunctive")),
        cell(Y, "uncountable: a Cantor set of digit-restricted reals, minus countably many computable ones",
             L("uncountable_transcendental_notDisjunctive") + ' <span class="st st-sorry">sorry, 99%</span>'),
    ]),
    ("disjunctive, not normal in base <span class=\"mono\">b</span>", "every block, wrong frequencies", [
        cell(E, "disjunctive implies irrational", L("rat_not_isDisjunctive")),
        cell(Q, "open; Borel says empty", L("algebraic_disjunctive_notNormal_open")),
        cell(Y, "<span class=\"mono\">b = 6</span>: Stoneham <span class=\"mono\">&#945;<sub>2,3</sub></span>, disjunctive (proved here), not 6-normal (Bailey&#8211;Borwein 2012), transcendental (Coons 2014). Any <span class=\"mono\">b</span>: an effective construction, unformalized (~80%)",
             C + L("stoneham23_cell_base6")),
        cell(Y, "uncountable: the set is residual, and has Liouville members", L("uncountable_liouville_absDisj_nowhereNormal") + " " + L("exists_liouville_absDisj_nowhereNormal")),
    ]),
    ("normal in base <span class=\"mono\">b</span>, not absolutely normal", "right frequencies in one base family", [
        cell(E, "normal implies disjunctive", L("rat_not_isNormal")),
        cell(Q, "open; Borel says empty", L("algebraic_normal_notAbsolutelyNormal_open")),
        cell(Y, "<span class=\"mono\">b = 2</span>: Stoneham <span class=\"mono\">&#945;<sub>2,3</sub></span>, normal (Bailey&#8211;Crandall 2002, proved here), not 6-normal, transcendental. Any <span class=\"mono\">b</span>: <span class=\"mono\">&#945;<sub>b,c</sub></span>, same sources",
             C + L("stoneham23_cell_base2")),
        cell(Y, "uncountable: Schmidt 1960, continuum many normal to <span class=\"mono\">r</span> and not to <span class=\"mono\">s</span>",
             C + L("schmidt1960_uncountable")),
    ]),
    ("absolutely normal", "right frequencies in every base", [
        cell(E, "normal implies disjunctive", L("rat_not_isNormal")),
        cell(Q, "open; Borel says <em>every</em> algebraic irrational is here", L("borel_algebraic_conjecture")),
        cell(Y, "Becher&#8211;Heiber&#8211;Slaman 2015: a computable absolutely normal Liouville number",
             C + L("becherHeiberSlaman_liouville_absNormal")),
        cell(Y, "Chaitin&#8217;s <span class=\"mono\">&#937;</span>, and almost every real (Borel 1909)",
             C + L("borel1909")),
    ]),
]

strip = [
    ("disjunctive in no base", "misses a block in every base", [
        cell(Y, "every rational", L("rat_not_isDisjunctive")),
        cell(Q, "open; Borel says empty", L("exists_irrational_disjunctive_in_no_base")),
        cell(Q, "<strong>open whether anything is here at all.</strong> <span class=\"mono\">&#955;</span> and Thue&#8211;Morse are not known members", L("exists_irrational_disjunctive_in_no_base")),
        cell(Q, "same question", L("exists_irrational_disjunctive_in_no_base")),
    ]),
    ("disjunctive in every base, normal in none", "every block everywhere, right frequencies nowhere", [
        cell(E, "disjunctive implies irrational", L("rat_not_isDisjunctive")),
        cell(Q, "open; Borel says empty", L("algebraic_disjunctive_notNormal_open")),
        cell(Y, "the effective nested-interval construction, with fast zero runs to make it Liouville; unpublished and unformalized (~80%)",
             ""),
        cell(Y, "uncountable: the set is residual, and has Liouville members", L("uncountable_liouville_absDisj_nowhereNormal") + " " + L("exists_liouville_absDisj_nowhereNormal")),
    ]),
]

HEAD = ('<thead><tr><th>Expansion</th><th><span class="mono">&#8474;</span></th><th>algebraic irrational</th>'
        '<th>transcendental, computable</th><th>transcendental, uncomputable</th></tr></thead>')


def render(rs, group):
    out = [f'<tr><td colspan="5" class="grp">{group}</td></tr>']
    for name, gloss, cells in rs:
        out.append(f'<tr><th scope="row" class="rowh">{name}<span class="rowg">{gloss}</span></th>{"".join(cells)}</tr>')
    return "\n".join(out)


section = f'''<!-- region-grid:start (generated; see src/NormalNumbers/LandscapeGrid.lean) -->
<h2>Every region, filled or named</h2>
<p>The Venn crosses two chains, so the same information fits a grid: four arithmetic columns against four expansion rows. Each cell holds a member with a source, an emptiness proof, or the word <em>open</em>. Every cell but one has a Lean statement in <a href="{GH}LandscapeGrid.lean"><span class="mono">LandscapeGrid.lean</span></a>.</p>
<p>The rows are read in a <strong>fixed base <span class="mono">b</span></strong>. Whether &#8220;disjunctive&#8221; means in one base, in some base, or in every base is a third axis, and it is exactly what the Venn left unsaid. It only creates new regions in two rows, so they get a strip below the grid instead of three copies of it.</p>
<div class="key"><span>{Y}a member, with its source</span><span>{E}empty, by proof</span><span>{Q}open</span><span><span class="st st-cite">cited</span> a literature result, stated in Lean but not proved here</span><span><span class="st st-lean">Lean</span> links to the statement</span></div>
<div class="tablewrap full regiongrid">
<table>
<colgroup><col style="width:19%"><col style="width:14%"><col style="width:15%"><col style="width:29%"><col style="width:23%"></colgroup>
{HEAD}
<tbody>
{render(rows, 'In a fixed base <span class="mono">b</span>')}
{render(strip, "Once the base is quantified")}
</tbody>
</table>
</div>
<p>Two things the grid makes visible that the Venn hid. The algebraic column is open from top to bottom: no algebraic irrational is known to be even disjunctive, and none is known not to be. And the top strip row is open in a stronger sense than any other cell, since nobody knows whether it has <em>any</em> member.</p>
<p>That second fact closes off one tempting route to the algebraic column. Mahler showed that for any irrational <span class="mono">&#945;</span> and any single block, some small multiple <span class="mono">m&#945;</span> contains the block infinitely often, which suggests &#8220;one of <span class="mono">&#945;, 2&#945;, &#8230;, M&#945;</span> must be disjunctive.&#8221; It cannot hold for irrationals in general: no positive multiple of Liouville&#8217;s <span class="mono">&#955;<sub>b</sub></span> is disjunctive in base <span class="mono">b</span> ({L("exists_transcendental_no_multiple_disjunctive")}). Any such theorem for algebraic numbers would need an input that only algebraic numbers have.</p>
<p style="font-size:.86rem; color:var(--muted)">Computability is not formalized here, because <span class="mono">&#8477;</span> is not an encodable type. So the Lean content of each uncomputable cell is that the cell is <em>uncountable</em>; since there are only countably many programs, an uncountable cell has uncomputable members.</p>
<!-- region-grid:end -->
'''

CSS = '''/* region grid */
.regiongrid table{min-width:52rem; font-size:.84rem}
.regiongrid th.rowh{font-family:var(--sans); font-weight:600; font-size:.86rem; text-transform:none; letter-spacing:0; color:var(--ink); background:var(--paper)}
.regiongrid .rowg{display:block; font-family:var(--serif); font-weight:400; font-style:italic; font-size:.8rem; color:var(--muted); margin-top:.2rem}
.regiongrid .gc{display:flex; gap:.35rem; align-items:baseline}
.regiongrid .gl-row{margin-top:.35rem; font-size:.74rem; line-height:1.5}
.st-lean{color:var(--digit); background:var(--digit-soft)}
a.st-lean{text-decoration:none}
.st-cite{color:var(--arith); background:var(--arith-soft)}
.st-sorry{color:var(--open); background:var(--open-soft)}
/* region grid end */
'''

s = HTML.read_text(encoding="utf-8")
s = re.sub(r"<!-- region-grid:start.*?<!-- region-grid:end -->\n", "", s, flags=re.S)
s = re.sub(r"/\* region grid \*/.*?/\* region grid end \*/\n", "", s, flags=re.S)
anchor = "<h2>Why the third one is hopeless</h2>"
assert s.count(anchor) == 1
s = s.replace(anchor, section + "\n" + anchor)
css_anchor = "td.stat{white-space:nowrap}\n"
assert s.count(css_anchor) == 1
s = s.replace(css_anchor, css_anchor + CSS)
HTML.write_text(s, encoding="utf-8")
print("ok")
