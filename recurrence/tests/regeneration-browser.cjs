const { chromium } = require('playwright');
const assert = require('node:assert/strict');

(async () => {
  const browser = await chromium.launch({ ...(process.env.CHROMIUM_PATH ? { executablePath: process.env.CHROMIUM_PATH } : {}) });
  const page = await browser.newPage({ viewport: { width: 375, height: 900 } });
  await page.clock.install();
  const errors = [];
  page.on('pageerror', error => errors.push(error.message));
  let endpoint = '', posts = 0;
  let status = { run: null, pending: false, nextAllowedAt: 0 };
  let mode = 'accept';
  await page.route('**/recurrence/regeneration-config.json', route => route.fulfill({ json: { endpoint } }));
  await page.route('https://regeneration-test.example/**', async route => {
    const headers = { 'Access-Control-Allow-Origin': '*' };
    if (route.request().method() === 'POST') {
      posts++;
      assert.equal(route.request().postData(), null);
      if (mode === 'fail') return route.fulfill({ status: 503, headers, json: { error: 'temporarily_unavailable' } });
      const now = await page.evaluate(() => Date.now());
      status = { pending: true, nextAllowedAt: now + 3600000, run: null };
      if (mode === 'cooldown') {
        status.pending = false;
        return route.fulfill({ status: 429, headers, json: { error: 'cooldown', nextAllowedAt: status.nextAllowedAt } });
      }
      return route.fulfill({ status: 202, headers, json: { ...status, accepted: true } });
    }
    await route.fulfill({ headers, json: status });
  });

  const open = () => page.goto('http://127.0.0.1:8787/recurrence/');
  await open();
  await page.getByText('再生成の受付は準備中です。', { exact: true }).waitFor();
  assert.equal(await page.locator('#regenerate-bank').isDisabled(), true);
  assert.equal(posts, 0);

  endpoint = 'https://regeneration-test.example';
  await open();
  await page.waitForFunction(() => !document.getElementById('regenerate-bank').disabled);
  await page.locator('#regenerate-bank').click();
  await page.evaluate(() => document.getElementById('regenerate-bank').click());
  await page.getByText('再生成を受け付けました。実行の開始を待っています。', { exact: true }).waitFor();
  assert.equal(posts, 1);
  assert.equal(await page.locator('#regenerate-bank').isDisabled(), true);

  status = { ...status, pending: false, run: { status: 'in_progress', url: 'https://github.com/mas256/math-textbooks/actions/runs/99' } };
  await page.clock.fastForward(30001);
  await page.locator('#regeneration-status').filter({ hasText: '再生成・検証しています' }).waitFor();
  assert.equal(await page.locator('#regeneration-run').getAttribute('href'), status.run.url);
  status.run = { ...status.run, status: 'completed', conclusion: 'success' };
  await page.clock.fastForward(30001);
  await page.locator('#regeneration-status').filter({ hasText: '公開が完了しました' }).waitFor();
  assert.equal(await page.locator('#regenerate-bank').isDisabled(), true);
  assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth));
  await page.screenshot({ path: 'recurrence/build/regeneration-mobile.png', fullPage: true });

  status = { run: null, pending: false, nextAllowedAt: 0 };
  mode = 'cooldown';
  await open();
  await page.waitForFunction(() => !document.getElementById('regenerate-bank').disabled);
  await page.locator('#regenerate-bank').click();
  await page.locator('#regeneration-status').filter({ hasText: '次の依頼は' }).waitFor();
  assert.equal(await page.locator('#regenerate-bank').isDisabled(), true);

  status = { pending: false, nextAllowedAt: 0, run: { status: 'completed', conclusion: 'failure', url: 'https://evil.example' } };
  await open();
  await page.locator('#regeneration-status').filter({ hasText: '完了しませんでした' }).waitFor();
  assert.equal(await page.locator('#regeneration-run').getAttribute('href'), 'https://github.com/mas256/math-textbooks/actions/workflows/pages.yml');

  mode = 'fail';
  status = { pending: false, nextAllowedAt: 0, run: { status: 'completed', conclusion: 'success' } };
  await open();
  await page.waitForFunction(() => !document.getElementById('regenerate-bank').disabled);
  await page.locator('#regenerate-bank').click();
  await page.locator('#regeneration-status').filter({ hasText: '今回の依頼の受付結果を確認できません' }).waitFor();
  assert.equal(await page.locator('#regenerate-bank').isDisabled(), false);
  assert.deepEqual(errors, []);
  await browser.close();
  console.log('Regeneration browser checks passed: setup, dispatch, double clicks, polling, cooldown, failures and mobile layout.');
})().catch(error => { console.error(error); process.exit(1); });
