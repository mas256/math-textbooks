import test from 'node:test';
import assert from 'node:assert/strict';
import { apiEndpoint } from '../regeneration.mjs';

test('only a HTTPS API origin is accepted', () => {
  assert.equal(apiEndpoint(''), null);
  assert.equal(apiEndpoint(undefined), null);
  assert.equal(apiEndpoint(' https://example.workers.dev/ '), 'https://example.workers.dev');
  for (const url of ['http://example.workers.dev', 'https://user:secret@example.workers.dev',
    'https://example.workers.dev/?token=secret', 'https://example.workers.dev/#secret', 'https://example.workers.dev/path', 'invalid']) {
    assert.throws(() => apiEndpoint(url));
  }
});
