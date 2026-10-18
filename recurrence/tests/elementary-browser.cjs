// Offline textbook UI integration checks. Certification metadata and MathJax are
// in-memory test doubles: this does not certify candidates or test typesetting.
const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const fs = require('node:fs');
const path = require('node:path');
const { chromium } = require('playwright');

(async () => {
  const root = path.resolve(__dirname, '..');
  const bank = JSON.parse(fs.readFileSync(path.join(root, 'build/candidates.json'), 'utf8'));
  const verification = {status:'lean-verified', commit:'offline-ui-test-fixture', count:bank.problems.length};
  bank.verification = verification;
  for (const p of bank.problems) p.verification = {status:'lean-verified'};
  const bytes = JSON.stringify(bank);
  const manifest = {...verification, proof_source_sha256:bank.proof_source_sha256,
    bank_sha256:crypto.createHash('sha256').update(bytes).digest('hex')};
  const browser = await chromium.launch({
    ...(process.env.CHROMIUM_PATH ? {executablePath:process.env.CHROMIUM_PATH} : {}),
    args:['--no-sandbox'],
  });
  try {
    const page = await browser.newPage({viewport:{width:375,height:900}});
    const errors = [];
    page.on('pageerror', error => errors.push(error.message));
    await page.route('**/*', async route => {
      const url = new URL(route.request().url());
      if (url.hostname === 'cdn.jsdelivr.net') {
        return route.fulfill({contentType:'text/javascript', body:
          'window.MathJax={startup:{promise:Promise.resolve()},typesetPromise:async()=>{},typesetClear:()=>{}};'});
      }
      if (url.hostname !== 'localhost') return route.abort();
      if (url.pathname.endsWith('/data/problems.json'))
        return route.fulfill({contentType:'application/json',body:bytes});
      if (url.pathname.endsWith('/data/manifest.json'))
        return route.fulfill({contentType:'application/json',body:JSON.stringify(manifest)});
      const name = url.pathname.split('/').pop() || 'textbook.html';
      if (!['textbook.html','app.js','model.mjs','styles.css','mathjax-config.js'].includes(name))
        return route.fulfill({status:404,body:''});
      const contentType = name.endsWith('.html') ? 'text/html' : name.endsWith('.css') ? 'text/css' : 'text/javascript';
      return route.fulfill({contentType,body:fs.readFileSync(path.join(root,name))});
    });
    await page.goto('http://localhost/recurrence/textbook.html');
    await page.waitForFunction(() => !document.querySelector('#family').disabled);
    await page.evaluate(() => {
      document.querySelector('#bank-status').textContent = 'UIテスト用データ（Lean未実行・数式描画は代替）';
    });
    await page.locator('#all-levels').click();
    for (const family of ['logarithmic','shifted_logarithmic','exponential_forcing']) {
      await page.locator('#family').selectOption(family);
      const seen = new Set();
      for (let i=0; i<12; i++) {
        await page.locator('#generate').click();
        const id = new URL(page.url()).searchParams.get('problem');
        const p = bank.problems.find(p => p.id===id);
        assert.equal(p.family,family);
        assert.ok(!seen.has(id), `duplicate ${id}`);
        seen.add(id);
        assert.equal(await page.locator('#answer').isVisible(),false);
        await page.locator('#hint-button').click();
        assert.equal(await page.locator('.hint').count(),1);
        await page.locator('#answer-button').click();
        assert.equal(await page.locator('#answer').isVisible(),true);
        assert.ok((await page.locator('#answer-formula').textContent()).includes(p.answer_tex));
        assert.equal(await page.locator('#solution-steps li').count(),p.routes[0].steps.length);
      }
      const downloadEvent = page.waitForEvent('download');
      await page.locator('#download-tex').click();
      const download = await downloadEvent;
      const tex = fs.readFileSync(await download.path(),'utf8');
      assert.ok(tex.includes('\\section*{解答}'));
      assert.ok(!tex.includes('\f') && !tex.includes('\r'));
      assert.ok(await page.evaluate(() => document.documentElement.scrollWidth<=window.innerWidth));
    }
    assert.deepEqual(errors,[]);
    console.log('Offline UI checks passed: all 36 new problems, family filters, no repeats, hints, answers and TeX downloads. MathJax and Lean certification were not tested.');
  } finally {
    await browser.close();
  }
})().catch(error => {console.error(error);process.exit(1);});
