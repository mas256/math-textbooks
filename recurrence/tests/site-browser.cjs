// Checks the assembled site, and after deployment the public URL: the deployed
// revision, the published bank, all six levels and the links shared before the
// two exercise pages were merged.
const { chromium } = require('playwright');
const assert = require('node:assert/strict');
const { createHash } = require('node:crypto');
const base = process.env.RECURRENCE_BASE_URL ||
  (process.env.RECURRENCE_TEST_ORIGIN || 'http://127.0.0.1:8787') + '/recurrence/';
const expected = process.env.RECURRENCE_EXPECT_SITE_REVISION;

// Query strings bypass CDN copies of an earlier deployment.
function url(path) {
  const target = new URL(path, base);
  if (expected) target.searchParams.set('deployment', expected);
  return target.href;
}

(async () => {
  const fetchJson = async path => {
    const response = await fetch(url(path), {cache: 'no-store'});
    assert.equal(response.ok, true, path);
    return Buffer.from(await response.arrayBuffer());
  };
  const manifest = JSON.parse(await fetchJson('data/manifest.json'));
  const bankBytes = await fetchJson('data/problems.json');
  assert.equal(createHash('sha256').update(bankBytes).digest('hex'), manifest.bank_sha256);
  const bank = JSON.parse(bankBytes);
  assert.equal(manifest.status, 'lean-verified');
  assert.equal(bank.problems.length, manifest.count);
  const browser = await chromium.launch({
    executablePath: process.env.CHROMIUM_PATH || process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH,
  });
  try {
    const page = await browser.newPage({viewport: {width: 1440, height: 1000}});
    page.setDefaultTimeout(30000);
    const errors = [];
    page.on('pageerror', error => errors.push(error.message));
    await page.goto(url('./'));
    if (expected) {
      assert.equal(await page.locator('meta[name="recurrence-site-revision"]').getAttribute('content'), expected);
    }
    await page.locator('#bank-status').filter({hasText: 'Lean検証済み'}).waitFor();
    await page.waitForFunction(() => !document.getElementById('level-six').disabled);
    for (let level = 1; level <= 6; level++) {
      await page.locator(`[data-level="${level}"]`).click();
      await page.locator('#generate').click();
      assert.equal(await page.locator('#problem-level').textContent(), `Lv.${level}`);
      await page.waitForFunction(() => document.querySelector('#problem-content mjx-container'));
    }
    const generated = bank.problems[0];
    await page.goto(url('./?problem=' + generated.id));
    await page.waitForFunction(id => document.getElementById('problem-id').textContent === id, generated.id.toUpperCase());
    // Links shared from the former textbook page keep working after the merge.
    await page.goto(url('./textbook.html?problem=L6-N03'));
    await page.waitForURL(/\/recurrence\/\?(?:.*&)?problem=L6-N03/);
    await page.waitForFunction(() => document.getElementById('problem-id').textContent === 'L6-N03');
    assert.match(await page.locator('#problem-level').textContent(), /6/);
    await page.goto(url('./?problem=removed-problem'));
    await page.locator('#action-status').filter({hasText: '指定された問題がない'}).waitFor();
    for (const width of [390, 320]) {
      await page.setViewportSize({width, height: 900});
      assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), `Overflow at ${width}px`);
    }
    assert.deepEqual(errors, []);
    console.log(`Site checks passed: bank seed ${manifest.seed} (${manifest.count} problems), Lv1-6, shared and legacy links, mobile widths`);
  } finally {
    await browser.close();
  }
})().catch(error => { console.error(error); process.exit(1); });
