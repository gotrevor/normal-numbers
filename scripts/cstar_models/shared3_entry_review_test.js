// Review of the Lean Good449 binary predicate and the numerical entry bridge.
// Run: node --test scripts/cstar_models/shared3_entry_review_test.js
const { test } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const os = require('node:os');
const zlib = require('node:zlib');
const vm = require('node:vm');
const sft = JSON.parse(fs.readFileSync(path.join(__dirname, 'sft449.json')));

function forbidden(length, value) {
  // Exact integer arithmetic for the rational Forb2 inequalities.
  const scale = 2 ** length;
  return (value + 1) * 100000 < 4451 * scale ||
    95549 * scale < value * 100000 ||
    (length === 13 && (value * 100000 < 4451 * scale ||
      95549 * scale < (value + 1) * 100000));
}
function acc(k, a) {
  for (let n = 0; n < k; n++) for (let m = n + 1; m <= k; m++) {
    const value = Math.floor(a / 2 ** (k - m)) % 2 ** (m - n);
    if (forbidden(m - n, value)) return false;
  }
  return true;
}
function state(k, a) {
  let s = 0;
  for (let i = k - 1; i >= 0; i--) {
    s = sft.T[s][(a >> i) & 1];
    if (s < 0) break;
  }
  return s;
}
test('stored 4.49 automaton agrees with rational Acc2 on every word of length <=13', () => {
  for (let k = 0; k <= 13; k++) for (let a = 0; a < 2 ** k; a++)
    assert.equal(state(k, a) >= 0, acc(k, a), `k=${k}, a=${a}`);
});

test('entry weights include the state factor used by normalized transition weights', {
  todo: '4c1a9e93 wReg returns V; the unnormalized weight is r_state * V',
}, () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'shared3-entry-review-'));
  const dump = path.join(dir, 'weights.txt');
  fs.writeFileSync(dump, zlib.gunzipSync(fs.readFileSync(path.join(__dirname, 'v449_N128_M24_D6.txt.gz'))));
  const source = fs.readFileSync(path.join(__dirname, 'entry.js'), 'utf8');
  const ctx = { require, console: { log() {} }, process: { argv: [
    'node', 'entry.js', dump, '128', '24', '6', '4.49', '1.8', path.join(__dirname, 'sft449.json'),
  ] } };
  vm.runInNewContext(source + '\nglobalThis.api = { wReg, sftState, clean, regular, ubin, V };', ctx);
  for (let k = 5; k <= 10; k++) for (let a = 0; a < 2 ** k; a++) {
    const s = ctx.api.sftState(k, a), value = ctx.api.wReg(k, a);
    if (s >= 0 && value > 0 && sft.r[s] < 0.99) {
      const { n, u } = ctx.api.regular(k);
      const i = Math.min(127, Math.floor(((3 ** n * a / 2 ** k) % 1) * 128));
      const raw = ctx.api.V[s * 128 * 24 + i * 24 + ctx.api.ubin(u)];
      assert.equal(value, sft.r[s] * raw,
        `entry weight=${value}, raw V=${raw} at k=${k}, a=${a}, s=${s}; required factor r=${sft.r[s]}`);
      return;
    }
  }
  assert.fail('no positive nontrivial state found in the stored candidate');
});
