// Reviewer controls for the real shared3.js CLI.
// Run: node --test scripts/cstar_models/shared3_review_test.js
// The binary SFT is rebuilt per C by gen_sft.js (fixes the c93704d6 hardcoded-sft45 defect).
const { test } = require('node:test');
const assert = require('node:assert/strict');
const { execFileSync } = require('node:child_process');
const path = require('node:path');

function run(c, mode, no3 = false) {
  return execFileSync(process.execPath, [path.join(__dirname, 'shared3.js'),
    '16', '6', '2', '3', String(c), '1', '1', mode,
    ...(no3 ? ['no3'] : [])], { encoding: 'utf8', timeout: 10000 });
}

function metrics(output) {
  return output.slice(output.indexOf(':') + 1).trim();
}

test('base 3 disabled recovers the supplied binary SFT rate', () => {
  assert.match(run(4.5, 'shared', true), /per-level growth 1\.890252/);
});

test('one parent phase gives identical shared and separate values', () => {
  assert.equal(metrics(run(4.5, 'shared')), metrics(run(4.5, 'separate')));
});

test('the joint control (C = 3, binary alive) is affected by the ternary kills', () => {
  assert.notEqual(metrics(run(3, 'shared')), metrics(run(3, 'shared', true)));
});

test('the low-exponent BINARY control must die with base 3 disabled', {
}, () => {
  assert.match(run(1.5, 'shared', true), /tree DEAD/);
});
