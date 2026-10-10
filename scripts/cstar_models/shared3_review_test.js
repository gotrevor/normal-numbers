// Reviewer controls for the real shared3.js CLI.
// Run: node --test scripts/cstar_models/shared3_review_test.js
// The TODO is a demonstrated defect at c93704d6, not a passing binary control.
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

test('the low-exponent joint control is affected by the ternary kills', () => {
  assert.notEqual(metrics(run(1.5, 'shared')), metrics(run(1.5, 'shared', true)));
});

test('the low-exponent BINARY control must die with base 3 disabled', {
  todo: 'c93704d6 hardcodes sft45.json; C changes only the ternary threshold',
}, () => {
  assert.match(run(1.5, 'shared', true), /tree DEAD/);
});
