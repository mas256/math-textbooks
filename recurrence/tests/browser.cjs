const { chromium } = require('playwright');
const assert = require('node:assert/strict');
const fs = require('node:fs');

(async () => {
  const browser = await chromium.launch();
  const page = await browser.newPage({viewport:{width:1440,height:1050},deviceScaleFactor:1});
  const bank=JSON.parse(fs.readFileSync('recurrence/build/problems.json','utf8'));
  const first=bank.problems.find(p=>p.family==='shifted_scaled');
  const errors=[];
  page.on('pageerror',e=>errors.push(e.message));
  await page.goto('http://127.0.0.1:8787/recurrence/?problem='+first.id);
  await page.locator('#bank-status').filter({hasText:'Lean検証済み'}).waitFor();
  await page.waitForFunction(()=>document.querySelectorAll('#problem-content mjx-container').length===2);
  assert.equal(await page.locator('#answer').isVisible(),false);
  assert.equal(await page.locator('#problem-content').textContent().then(t=>t.includes('階比型')),false);
  await page.screenshot({path:'recurrence/build/desktop.png',fullPage:true});
  await page.locator('#hint-button').click();
  assert.equal(await page.locator('.hint').count(),1);
  await page.locator('#answer-button').click();
  await page.waitForFunction(()=>document.querySelector('#answer-formula mjx-container'));
  assert.equal(await page.locator('#answer').isVisible(),true);
  assert.equal(await page.locator('#method-observation').textContent(), '着眼点：'+first.routes[0].hint);
  assert.ok((await page.locator('#method-choice').textContent()).includes('登録済みの候補'));
  for (const alternate of await page.locator('.alternate').all()) {
    await alternate.locator('summary').click();
    assert.ok((await alternate.textContent()).includes('主解法との比較：'));
    assert.ok((await alternate.textContent()).includes('着眼点：'));
  }
  await page.locator('#answer-button').click();
  assert.equal(await page.locator('#answer').isVisible(),false);
  assert.ok((await page.locator('#bank-status').textContent()).includes(`${bank.problems.length} 問・${Object.keys(bank.families).length}系統`));
  await page.locator('#family').selectOption('reciprocal_forcing');
  await page.locator('[data-level="1"]').click();
  assert.equal(await page.locator('#generate').isDisabled(),true);
  await page.locator('[data-level="4"]').click();
  await page.locator('#generate').click();
  assert.ok((await page.locator('#problem-level').textContent()).includes('4'));
  await page.locator('#answer-button').click();
  await page.waitForFunction(()=>document.querySelector('#answer-formula mjx-container'));
  const downloadPromise=page.waitForEvent('download');
  await page.locator('#download-tex').click();
  const download=await downloadPromise;
  await download.saveAs('recurrence/build/example.tex');
  assert.ok(fs.readFileSync('recurrence/build/example.tex','utf8').includes('\\section*{解答}'));
  await page.locator('#all-levels').click();
  await page.locator('#family').selectOption('all');
  for(const family of Object.keys(bank.families)) {
    await page.locator('#family').selectOption(family);
    await page.locator('#generate').click();
    await page.locator('#answer-button').click();
    await page.waitForFunction(()=>document.querySelector('#answer-formula mjx-container'));
    assert.equal(await page.locator('mjx-merror,[data-mml-node="merror"]').count(),0,family);
  }
  const formulas=bank.problems.flatMap(p=>[...p.statement.initials_tex,p.statement.recurrence_tex,p.answer_tex,
    ...p.routes.flatMap(r=>r.steps.flatMap(s=>[...s.matchAll(/\\\((.*?)\\\)/gs)].map(m=>m[1]))) ]);
  const renderingErrors=await page.evaluate(async formulas=>{
    const errors=[];
    for(const tex of formulas) {
      try {
        const result=await MathJax.tex2svgPromise(tex,{display:true});
        if(result.querySelector('[data-mml-node="merror"],[data-mjx-error]')) errors.push(tex);
      } catch(e) { errors.push(tex+': '+e.message); }
    }
    return errors;
  },formulas);
  assert.deepEqual(renderingErrors,[],'Every statement, answer and registered route must render.');
  await page.locator('#generation-details summary').click();
  await page.waitForFunction(()=>document.querySelector('#function-catalog mjx-container'));
  assert.ok((await page.locator('#generation-summary').textContent()).includes(`${bank.problems.length} 問`));
  assert.ok((await page.locator('#diversity-summary').textContent()).includes(`${bank.comparison.diversity.after.coefficient_patterns} 種類`));
  assert.equal(await page.locator('#diversity-summary tbody tr').count(),3);
  await page.setViewportSize({width:375,height:900});
  const widest=bank.problems.reduce((a,b)=>a.quality.metrics.nodes>b.quality.metrics.nodes?a:b);
  await page.goto('http://127.0.0.1:8787/recurrence/?problem='+widest.id);
  await page.waitForFunction(()=>document.querySelectorAll('#problem-content mjx-container').length===2);
  assert.ok(await page.evaluate(()=>document.documentElement.scrollWidth<=window.innerWidth));
  await page.screenshot({path:'recurrence/build/mobile.png',fullPage:true});
  await page.locator('#answer-button').click();
  await page.waitForFunction(()=>document.querySelector('#answer-formula mjx-container'));
  await page.screenshot({path:'recurrence/build/mobile-answer.png',fullPage:true});
  assert.ok(await page.evaluate(()=>document.documentElement.scrollWidth<=window.innerWidth));
  // Expanded explanations introduce longer equations than the statements.
  // Exercise the longest main explanation in every family on a phone.
  for (const family of Object.keys(bank.families)) {
    const examples=bank.problems.filter(p=>p.family===family);
    const longest=examples.reduce((a,b)=>a.routes[0].steps.join('').length>b.routes[0].steps.join('').length?a:b);
    await page.goto('http://127.0.0.1:8787/recurrence/?problem='+longest.id);
    await page.locator('#answer-button').waitFor({state:'visible'});
    await page.waitForFunction(()=>!document.querySelector('#answer-button').disabled);
    await page.locator('#answer-button').click();
    await page.waitForFunction(()=>document.querySelector('#answer-formula mjx-container'));
    assert.equal(await page.locator('mjx-merror,[data-mml-node="merror"]').count(),0,family);
    assert.ok(await page.evaluate(()=>document.documentElement.scrollWidth<=window.innerWidth),'mobile '+family);
  }
  assert.deepEqual(errors,[]);
  console.log(`Browser checks passed: ${formulas.length} formulas, every family, hints, filters, exports, comparison and mobile layout.`);
  await browser.close();
})().catch(e=>{console.error(e);process.exit(1);});
