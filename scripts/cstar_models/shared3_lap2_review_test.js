// Independent lap-2 review checks, including one known C enclosure failure.
// Run: node --test scripts/cstar_models/shared3_lap2_review_test.js
const { test } = require('node:test');
const assert = require('node:assert/strict');
const { execFileSync } = require('node:child_process');
const fs = require('node:fs');
const path = require('node:path');
const os = require('node:os');
const vm = require('node:vm');
const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'shared3-lap2-review-'));

function generate(c) {
  const out = path.join(dir, `sft-${c}.json`);
  execFileSync(process.execPath, [path.join(__dirname, 'gen_sft.js'), String(c), '13', out]);
  return JSON.parse(fs.readFileSync(out));
}
function accepts(sft, n, length) {
  let s = 0;
  for (let k = length - 1; k >= 0; k--) {
    s = sft.T[s][(n >> k) & 1];
    if (s < 0) return false;
  }
  return true;
}

test('4.49 binary cutoff has an exact integer bracket and tightens 4.5', () => {
  // 8192 * 2^(-449/100) = 2^(851/100), strictly between 364 and 365.
  assert.ok(364n ** 100n < 2n ** 851n);
  assert.ok(365n ** 100n > 2n ** 851n);
  const a = generate(4.5), b = generate(4.49);
  assert.ok(accepts(a, 363, 13));
  assert.ok(!accepts(b, 363, 13));
  let survivors = 0;
  for (let n = 0; n < 8192; n++) if (accepts(b, n, 13)) {
    survivors++;
    assert.ok(n >= 365 && n < 8192 - 365);
    assert.ok(accepts(a, n, 13));
  }
  assert.ok(survivors > 0);
});

test('containment-screen leaves avoid all resolved ternary windows on a fixed grid', () => {
  // Execute the actual recursion, stopping before its expensive whole-state iteration.
  const source = fs.readFileSync(path.join(__dirname, 'shared3.js'), 'utf8');
  const prefix = source.slice(0, source.indexOf('// precompute sample leaves'));
  const ctx = { require, __dirname, console,
    process: { argv: ['node', 'shared3.js', '16', '6', '4', '1', '4.49', '1', '1', 'shared'],
      env: { CONT: '1', SFT: path.join(dir, 'sft-4.49.json') } } };
  // Keep this test independent of execution order.
  generate(4.49);
  vm.runInNewContext(prefix + '\nglobalThis.api = { descend, delta, rhoOf, L3, D };', ctx);
  const { descend, delta, rhoOf, L3, D } = ctx.api;
  let count = 0;
  for (let i = 0; i < 17; i++) for (const u of [1.1, 1.4, 1.8, 2.2, 2.5]) {
    const x = (i + 0.5) / 17, out = [];
    descend(0, x, u, 0, 0, 1, out);
    const rho = rhoOf(u);
    let phase = u, resolved = 0;
    for (let depth = 1; depth <= D; depth++) {
      phase--;
      if (phase <= 1 + 1e-12) { resolved++; phase += L3; }
      for (const [leaf] of out) {
        const ancestor = Math.floor(leaf / 2 ** (D - depth));
        const left = x + ancestor * rho / 2 ** depth, right = left + rho / 2 ** depth;
        for (let n = 0; n < resolved; n++) {
          const lo = left * 3 ** n, hi = right * 3 ** n;
          for (let k = Math.floor(lo) - 1; k <= Math.ceil(hi) + 1; k++)
            assert.ok(!(lo >= k - delta && hi <= k + delta), 'retained ancestor lies in a resolved window');
        }
      }
    }
    count += out.length;
  }
  assert.ok(count > 0);
});

// fixed (lap 4): outward bin ownership, an edge point belongs to both adjacent bins, so ja <= jb always
test('C enclosures at a leaf u-bin boundary must be finite', () => {
  const source = path.join(__dirname, 'shared3cert.c');
  const driver = path.join(dir, 'boundary.c'), exe = path.join(dir, 'boundary');
  fs.writeFileSync(driver, `#define main probe_main
#include ${JSON.stringify(source)}
#undef main
int main(void) {
  N=16; M=6; D=1; NO3=1; NB=N*M;
  delta=pow(3,-4.5)*1.0001; L3=log2(3); U=log2(6);
  for(int j=0;j<=4;j++) edges[j]=1+j/4.0;
  for(int j=1;j<=2;j++) edges[4+j]=2+(U-2)*j/2.0;
  for(int s=0;s<S;s++) for(int d=0;d<2;d++) P[s][d]=T[s][d]<0?0:R[T[s][d]]/(LAM*R[s]);
  V=malloc(S*NB*sizeof(double)); for(int q=0;q<S*NB;q++) V[q]=1;
  printf("%g\\n",evalbox(0,0.3,0.3,3-L3,3-L3));
  printf("%g\\n",evalbox(0,0.3,0.3+1e-14,3-L3-1e-14,3-L3+1e-14));
  return 0;
}
`);
  execFileSync(process.env.CC || 'cc', ['-O0', driver, '-o', exe], { timeout: 15000 });
  const result = execFileSync(exe, [], { encoding: 'utf8', timeout: 5000 }).trim();
  for (const value of result.split(/\s+/))
    assert.ok(Number.isFinite(Number(value)), `non-finite enclosure: ${result}`);
});
