const { chromium } = require('playwright');
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const { createHash } = require('node:crypto');
const lock = require('../engine-lock.json');
const base = process.env.RECURRENCE_LAB_BASE_URL ||
  (process.env.RECURRENCE_TEST_ORIGIN || 'http://127.0.0.1:8787') + '/recurrence/';

async function verifyAssets() {
  const root = new URL(`engine/${lock.revision}/`, base);
  const response = await fetch(new URL('provenance.json', root));
  assert.equal(response.ok, true, 'Published engine provenance');
  const manifest = await response.json();
  assert.equal(manifest.revision, lock.revision);
  assert.equal(manifest.version, lock.version);
  for (const [name, expected] of Object.entries(manifest.assets)) {
    const response = await fetch(new URL(name, root));
    assert.equal(response.ok, true, name);
    const actual = createHash('sha256').update(Buffer.from(await response.arrayBuffer())).digest('hex');
    assert.equal(actual, expected, 'Unchanged engine asset: ' + name);
  }
}

(async () => {
  await verifyAssets();
  const browser = await chromium.launch({
    executablePath: process.env.CHROMIUM_PATH || process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH,
    args: ['--no-sandbox'],
  });
  try {
    const context = await browser.newContext({viewport: {width: 1440, height: 1000}, acceptDownloads: true});
    context.setDefaultTimeout(30000);
    const page = await context.newPage();
    const errors = [], apiRequests = [], externalRequests = [];
    page.on('pageerror', error => errors.push(error.message));
    page.on('request', request => {
      const url = new URL(request.url());
      if (url.pathname.startsWith('/api/')) apiRequests.push(url.href);
      if (/^https?:$/.test(url.protocol) && url.origin !== new URL(base).origin) externalRequests.push(url.href);
    });
    await page.goto(base);
    await page.waitForFunction(() => !document.getElementById('generate').disabled);
    assert.equal(await page.locator('meta[name="recurrence-engine-revision"]').getAttribute('content'), lock.revision);
    const catalog = await page.evaluate(() => window.RecurrenceBrowser.request('/api/status'));
    assert.equal(catalog.application_version, lock.version);
    assert.equal(catalog.families.length, 42);
    assert.equal(catalog.variants.length, 123);
    assert.equal(catalog.verification.formal_verification, false);
    const ids = new Set();
    async function generate(level, mode = 'standard') {
      await page.locator(`[data-level="${level}"]`).click();
      await page.selectOption('#practice-mode', mode);
      const before = await page.locator('#problem-label').textContent();
      await page.locator('#generate').click();
      await page.waitForFunction(previous => {
        return document.getElementById('problem-label').textContent !== previous &&
          document.getElementById('job-progress').hidden &&
          document.getElementById('download-tex').href.startsWith('blob:');
      }, before, {timeout: 20000});
      assert.equal(await page.locator('#problem-level').textContent(), `Lv. ${level}`);
      assert.equal(await page.locator('#problem-family').isVisible(), false, 'Mixed practice must hide the method');
      assert.equal(await page.locator('#statement .katex').count() > 0, true);
      const id = await page.locator('#problem-label').textContent();
      assert.equal(ids.has(id), false); ids.add(id);
      return page.evaluate(async () => JSON.parse(await (await fetch(document.getElementById('download-recipe').href)).text()));
    }
    for (let level = 1; level <= 5; level++) await generate(level);
    await generate(2, 'method_choice');
    assert.equal(await page.locator('#method-exercise').isVisible(), true);
    await page.selectOption('#method-choice', 'custom');
    await page.locator('#check-method').click();
    assert.match(await page.locator('#method-feedback').textContent(), /自分の方針/);
    const recipe = await generate(3, 'alternatives');
    await page.locator('#solution-panel summary').click();
    await page.waitForFunction(() => document.getElementById('alternatives-exercise').hidden === false);
    assert.equal(await page.locator('.alternative-solution').count() >= 1, true);
    assert.equal(await page.locator('.alternative-solution[open]').count(), 0);
    await page.locator('.alternative-solution summary').first().click();
    assert.equal(await page.locator('.alternative-solution[open]').count(), 1);
    await page.waitForFunction(() => document.getElementById('download-tex').getAttribute('aria-disabled') !== 'true');
    const [download] = await Promise.all([page.waitForEvent('download'), page.locator('#download-tex').click()]);
    assert.match(await fs.readFile(await download.path(), 'utf8'), /別解/);
    // The same hosted worker must operate without a generation server or network.
    await context.setOffline(true);
    const replay = await page.evaluate(async recipe => {
      const runtime = window.RecurrenceBrowser;
      const {id} = await runtime.request('/api/replay', {method: 'POST', body: {recipe}});
      for (let i = 0; i < 600; i++) {
        const result = await runtime.request('/api/jobs/' + id);
        if (['succeeded', 'failed', 'timeout', 'cancelled'].includes(result.status)) return result;
        await new Promise(resolve => setTimeout(resolve, 20));
      }
      throw new Error('Replay timeout');
    }, recipe);
    assert.equal(replay.status, 'succeeded', replay.message);
    assert.equal(replay.problem.classification.level, 3);
    assert.equal(replay.verification.formal_verification, false);
    assert.equal(replay.verification.lean_executed, false);
    await context.setOffline(false);
    for (const width of [390, 320]) {
      await page.setViewportSize({width, height: 900});
      assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true, `Overflow at ${width}px`);
    }
    assert.deepEqual(errors, []);
    assert.deepEqual(apiRequests, [], 'The generator must not send API requests to Pages');
    assert.deepEqual(externalRequests, [], 'All dynamic practice assets are served locally');
    // Preserve the exact public URL supplied by the user, including its problem ID.
    await page.goto(new URL('?problem=L6-N03', base).href);
    await page.waitForURL(/\/recurrence\/textbook\.html\?problem=L6-N03/);
    await page.waitForFunction(() => document.getElementById('problem-id').textContent === 'L6-N03');
    assert.match(await page.locator('#problem-level').textContent(), /6/);
    const back = page.locator('header a[href="./"]');
    assert.equal(await back.count(), 1);
    assert.deepEqual(errors, []);
    console.log(`Hosted engine ${lock.version} @ ${lock.revision}: assets, 5 levels, 3 modes, alternatives, TeX, offline replay, mobile widths, L6-N03 link passed`);
  } finally {
    await browser.close();
  }
})().catch(error => { console.error(error); process.exit(1); });
