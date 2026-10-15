const { chromium } = require('playwright');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const baseURL = process.env.RECURRENCE_BASE_URL || (process.env.RECURRENCE_TEST_ORIGIN || 'http://127.0.0.1:8787') + '/recurrence/';

(async () => {
  const {textbookText, mathTextParts, equashareSource} = await import('../model.mjs');
  const browser = await chromium.launch({executablePath:process.env.CHROMIUM_PATH || process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH});
  const page = await browser.newPage({viewport:{width:1440,height:1050},deviceScaleFactor:1});
  const bank=JSON.parse(fs.readFileSync('recurrence/build/problems.json','utf8'));
  const authored=JSON.parse(fs.readFileSync('recurrence/authored/level6.json','utf8'));
  const first=bank.problems.find(p=>p.family==='shifted_scaled');
  const errors=[];
  page.on('pageerror',e=>errors.push(e.message));
  await page.goto(baseURL+'?problem='+first.id);
  await page.locator('#bank-status').filter({hasText:'Lean検証済み'}).waitFor();
  await page.waitForFunction(()=>document.querySelectorAll('#problem-content mjx-container').length===2);
  assert.equal(await page.locator('#answer').isVisible(),false);
  assert.equal(await page.locator('#problem-content').textContent().then(t=>t.includes('階比型')),false);
  assert.equal(await page.locator('#single-actions button').count(),4);
  async function checkEquasharePreview(editor,problem) {
    await editor.evaluate(source=>new Promise((resolve,reject)=>{
      const preview=document.querySelector('#preview');
      const timeout=setTimeout(()=>{observer.disconnect();reject(new Error('Equashare preview did not update'));},10000);
      const observer=new MutationObserver(()=>{
        observer.disconnect(); clearTimeout(timeout); resolve();
      });
      observer.observe(preview,{childList:true});
      const input=document.querySelector('#input');
      input.value=source; input.dispatchEvent(new Event('input',{bubbles:true}));
    }),equashareSource(problem));
    if (/フォント|[Ff]ont/.test(await editor.locator('#status').textContent())) {
      await editor.waitForFunction(()=>document.querySelector('#status').textContent==='');
    }
    assert.equal(await editor.locator('#status').textContent(),'','Equashare '+problem.id);
    assert.equal(await editor.locator('#preview [data-mml-node="merror"],#preview [data-mjx-error]').count(),0,problem.id);
  }
  async function openInEquashare(problem, button = page.locator('#open-equashare')) {
    const popup=page.waitForEvent('popup');
    await button.click();
    const editor=await popup;
    editor.on('pageerror',e=>errors.push(e.message));
    await editor.waitForFunction(source=>document.querySelector('#input')?.value===source,equashareSource(problem));
    await checkEquasharePreview(editor,problem);
    assert.equal(new URL(editor.url()).pathname,new URL('../equashare/',page.url()).pathname);
    assert.equal(new URL(editor.url()).search,'');
    assert.equal(await editor.evaluate(()=>window.opener),null);
    return editor;
  }
  const editor=await openInEquashare(first);
  // Render every exported problem using the distributed Equashare parser, including
  // cases environments, partial-sum definitions, fractions and positivity conditions.
  for (const problem of [...bank.problems, ...authored.problems]) {
    await checkEquasharePreview(editor,problem);
  }
  await editor.close();
  await page.screenshot({path:'recurrence/build/desktop.png',fullPage:true});
  await page.locator('#hint-button').click();
  assert.equal(await page.locator('.hint').count(),1);
  assert.equal(await page.locator('.hint span').textContent(), textbookText(first.routes[0].hint));
  assert.equal(await page.locator('#hint-button').isDisabled(),true);
  assert.equal(await page.locator('#answer').isVisible(),false);
  await page.locator('#answer-button').click();
  await page.waitForFunction(()=>document.querySelector('#answer-formula mjx-container'));
  assert.equal(await page.locator('#answer').isVisible(),true);
  assert.equal(await page.locator('#method-observation').textContent(), '方針：'+textbookText(first.routes[0].hint));
  assert.equal(await page.locator('#method-choice').isVisible(),false);
  assert.ok((await page.locator('#score-info').textContent()).includes('登録済みの候補'));
  for (const alternate of await page.locator('.alternate').all()) {
    await alternate.locator('summary').click();
    assert.ok(!(await alternate.textContent()).includes('スコア')); 
    assert.ok((await alternate.textContent()).includes('方針：'));
  }
  await page.locator('#answer-button').click();
  assert.equal(await page.locator('#answer').isVisible(),false);
  assert.ok((await page.locator('#bank-status').textContent()).includes(`${bank.problems.length} 問・${Object.keys(bank.families).length}系統`));
  await page.locator('#family').selectOption('reciprocal_forcing');
  await page.locator('[data-level="1"]').click();
  assert.equal(await page.locator('#generate').isDisabled(),true);
  await page.locator('[data-level="5"]').click();
  await page.locator('#generate').click();
  assert.ok((await page.locator('#problem-level').textContent()).includes('5'));
  assert.equal(await page.locator('.exercise').count(),1);
  assert.equal(await page.locator('#answer').isVisible(),false);
  assert.equal(await page.locator('.hint').count(),0);
  const previousId=new URL(page.url()).searchParams.get('problem');
  await page.locator('#generate').click();
  assert.notEqual(new URL(page.url()).searchParams.get('problem'),previousId);
  assert.equal(await page.locator('.exercise').count(),1);
  await page.locator('#answer-button').click();
  await page.waitForFunction(()=>document.querySelector('#answer-formula mjx-container'));
  const downloadPromise=page.waitForEvent('download');
  await page.locator('#download-tex').click();
  const download=await downloadPromise;
  await download.saveAs('recurrence/build/example.tex');
  const exported=fs.readFileSync('recurrence/build/example.tex','utf8');
  assert.ok(exported.includes('\\section*{解答}'));
  assert.ok(exported.includes('{jsbook}'));
  assert.ok(exported.includes('\\begin{multicols*}{2}'));
  assert.ok(!exported.includes('スコア'));
  const current=bank.problems.find(p=>p.id===new URL(page.url()).searchParams.get('problem'));
  const answerEditor=await openInEquashare(current);
  assert.equal(await answerEditor.locator('#input').inputValue(),equashareSource(current));
  await answerEditor.close();
  await page.locator('#all-levels').click();
  await page.locator('#family').selectOption('all');
  for(const family of Object.keys(bank.families)) {
    await page.locator('#family').selectOption(family);
    await page.locator('#generate').click();
    await page.locator('#answer-button').click();
    await page.waitForFunction(()=>document.querySelector('#answer-formula mjx-container'));
    assert.equal(await page.locator('mjx-merror,[data-mml-node="merror"]').count(),0,family);
  }
  const multiple=bank.problems.find(p=>p.routes.length>1);
  assert.ok(multiple,'The bank must exercise alternative-method comparisons.');
  await page.goto(baseURL+'?problem='+multiple.id);
  await page.waitForFunction(()=>!document.querySelector('#answer-button').disabled);
  await page.locator('#answer-button').click();
  assert.equal(await page.locator('.alternate').count(),Math.min(2,multiple.routes.length-1));
  for (const alternate of await page.locator('.alternate').all()) {
    await alternate.locator('summary').click();
    assert.ok(!(await alternate.textContent()).includes('スコア')); 
    assert.ok((await alternate.textContent()).includes('方針：'));
  }
  const formulas=[...new Set([...bank.problems.flatMap(p=>[...p.statement.initials_tex,p.statement.recurrence_tex,p.answer_tex,
    ...p.routes.flatMap(r=>r.steps.flatMap(s=>[...s.matchAll(/\\\((.*?)\\\)/gs)].map(m=>m[1]))) ]),
    ...authored.problems.flatMap(p => [p.statement,p.hint,p.answer,...p.solution]
      .flatMap(text => mathTextParts(text).filter(part => part.type !== 'text').map(part => part.text)))])];
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
  assert.equal(await page.locator('#level-diversity tbody tr').count(),3);
  assert.ok((await page.locator('#level-diversity').textContent()).includes('対数と二重の階差'));
  for (const family of ['scaled_second_order','difference_scaled','weighted_sum','multiplicative_second']) {
    assert.ok(bank.problems.some(p=>p.family===family && p.scores.level>=3),family);
  }
  await page.setViewportSize({width:375,height:900});
  const widest=bank.problems.reduce((a,b)=>a.quality.metrics.nodes>b.quality.metrics.nodes?a:b);
  await page.goto(baseURL+'?problem='+widest.id);
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
    await page.goto(baseURL+'?problem='+longest.id);
    await page.locator('#answer-button').waitFor({state:'visible'});
    await page.waitForFunction(()=>!document.querySelector('#answer-button').disabled);
    await page.locator('#answer-button').click();
    await page.waitForFunction(()=>document.querySelector('#answer-formula mjx-container'));
    assert.equal(await page.locator('mjx-merror,[data-mml-node="merror"]').count(),0,family);
    assert.ok(await page.evaluate(()=>document.documentElement.scrollWidth<=window.innerWidth),'mobile '+family);
  }
  await checkAuthored(page, authored, openInEquashare);
  await checkBatch(page, [...bank.problems, ...authored.problems], openInEquashare);
  assert.deepEqual(errors,[]);
  console.log(`Browser checks passed: ${formulas.length} formulas, ${bank.problems.length + authored.problems.length} Equashare problems, every family, hints, filters, exports, comparison, mobile layout and 14-question batches.`);
  await browser.close();
})().catch(e=>{console.error(e);process.exit(1);});

async function checkAuthored(page, authored, openInEquashare) {
  await page.locator('#family').selectOption('all');
  await page.locator('#level-six').click();
  assert.ok((await page.locator('#selection-count').textContent()).includes('60 問'));
  await page.locator('#generate').click();
  assert.equal(await page.locator('#problem-level').textContent(), 'Lv.6');
  assert.ok(!(await page.locator('#bank-status').textContent()).includes('Lean検証済み'));
  assert.equal(await page.locator('#recipe-details').isVisible(), false);
  assert.equal(await page.locator('#authored-details').isVisible(), true);
  for (const category of authored.categories) {
    await page.locator('#family').selectOption('authored:' + category.id);
    await page.locator('#generate').click();
    const id = new URL(page.url()).searchParams.get('problem');
    assert.equal(authored.problems.find(p => p.id === id).category, category.id);
    await page.locator('#hint-button').click();
    assert.equal(await page.locator('.hint').count(), 1);
    await page.locator('#answer-button').click();
    await page.waitForFunction(() => document.querySelector('.authored-solution mjx-container'));
    assert.equal(await page.locator('#single-answer').isVisible(), false);
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth), category.id);
    assert.equal(await page.locator('mjx-merror,[data-mml-node="merror"]').count(), 0);
  }
  const shared = page.url();
  const event = page.waitForEvent('download');
  await page.locator('#download-tex').click();
  const download = await event;
  const tex = fs.readFileSync(await download.path(), 'utf8');
  assert.ok(tex.includes('（Lv6）') && tex.includes('方針・解答・解法'));
  const id = new URL(shared).searchParams.get('problem');
  const editor = await openInEquashare(authored.problems.find(p => p.id === id));
  await editor.close();
  await page.goto(shared);
  await page.waitForFunction(() => document.querySelector('#problem-level').textContent === 'Lv.6');
  await page.waitForFunction(() => document.querySelector('#problem-content mjx-container'));
  assert.equal(await page.locator('#problem-id').textContent(), id);
  assert.equal(await page.locator('#answer').isVisible(), false);
  await page.screenshot({path:'recurrence/build/level6-mobile.png',fullPage:true});
}

async function checkBatch(page, problems, openInEquashare) {
  const {texDocument} = await import('../model.mjs');
  await page.locator('#family').selectOption('reciprocal_forcing');
  await page.locator('[data-level="1"]').click();
  assert.equal(await page.locator('#generate').isDisabled(), true);
  await page.waitForFunction(() => !document.querySelector('#generate-batch').disabled);
  await page.locator('#generate-batch').click();
  await page.waitForFunction(() => document.querySelectorAll('.batch-question mjx-container').length >= 26);
  const questions = page.locator('.batch-question');
  assert.equal(await questions.count(), 14);
  assert.deepEqual(await questions.evaluateAll(cards => cards.map(card => Number(card.dataset.level))),
    [1,1,2,2,3,3,3,4,4,4,5,5,6,6]);
  const ids = await questions.evaluateAll(cards => cards.map(card => card.dataset.problemId));
  assert.equal(new Set(ids).size, 14);
  assert.equal(await page.locator('#answer').isVisible(), false);
  assert.equal(await page.locator('#recipe-details').isVisible(), false);
  assert.equal(await page.locator('#single-actions').isVisible(), false);
  assert.equal(await questions.locator('.question-actions button').count(), 56);
  assert.equal(await questions.locator('.question-hint:visible,.question-answer:visible').count(), 0);
  const first = questions.nth(0), second = questions.nth(1), fixed = questions.nth(13);
  const button = (card, action) => card.locator(`[data-action="${action}"]`);
  assert.deepEqual(await first.locator('.question-actions button').allTextContents(), ['ヒント','答え','Equashare','TeX']);
  assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth));
  await page.screenshot({path:'recurrence/build/batch-mobile.png',fullPage:true});
  const shared = page.url();
  async function checkDownload(card, index, withAnswer) {
    const event = page.waitForEvent('download');
    await button(card, 'tex').click();
    const download = await event;
    const tex = fs.readFileSync(await download.path(), 'utf8');
    assert.equal(download.suggestedFilename(), `recurrence-${ids[index]}.tex`);
    assert.equal(tex, texDocument(problems.find(p => p.id === ids[index]), withAnswer));
  }
  await checkDownload(first, 0, false);
  await button(first, 'hint').click();
  assert.equal(await first.locator('.question-hint').isVisible(), true);
  assert.equal(await questions.locator('.question-hint:visible').count(), 1);
  assert.equal(await questions.locator('.question-answer:visible').count(), 0);
  assert.equal(await button(first, 'hint').getAttribute('aria-expanded'), 'true');
  await button(second, 'answer').click();
  await second.locator('.question-answer mjx-container').first().waitFor();
  assert.equal(await first.locator('.question-answer').isVisible(), false);
  assert.equal(await first.locator('.question-hint').isVisible(), true);
  assert.equal(await questions.locator('.question-answer:visible').count(), 1);
  // Another question's open answer must not leak into this question's TeX.
  await checkDownload(first, 0, false);
  await checkDownload(second, 1, true);
  let editor = await openInEquashare(problems.find(p => p.id === ids[1]), button(second, 'equashare'));
  await editor.close();
  await button(fixed, 'answer').click();
  await fixed.locator('.question-answer mjx-container').first().waitFor();
  assert.equal(await questions.locator('.question-answer:visible').count(), 2);
  assert.equal(await fixed.locator('.solution-note a').count(), 1);
  await checkDownload(fixed, 13, true);
  editor = await openInEquashare(problems.find(p => p.id === ids[13]), button(fixed, 'equashare'));
  await editor.close();
  assert.equal(await page.locator('mjx-merror,[data-mml-node="merror"]').count(), 0);
  for (const width of [320,375,1440]) {
    await page.setViewportSize({width,height:900});
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth), `batch width ${width}`);
  }
  await page.screenshot({path:'recurrence/build/batch-controls-desktop.png',fullPage:true});
  await page.setViewportSize({width:375,height:900});
  await page.screenshot({path:'recurrence/build/batch-controls-mobile.png',fullPage:true});
  await page.emulateMedia({media:'print'});
  assert.equal(await page.locator('.controls').isVisible(), false);
  assert.equal(await page.locator('.batch-question:visible').count(), 14);
  assert.equal(await questions.locator('.question-actions:visible,.question-hint:visible').count(), 0);
  assert.equal(await questions.locator('.question-answer:visible').count(), 2);
  await page.emulateMedia({media:'screen'});
  await button(first, 'hint').click();
  assert.equal(await first.locator('.question-hint').isVisible(), false);
  await button(second, 'answer').click();
  assert.equal(await second.locator('.question-answer').isVisible(), false);
  assert.equal(await fixed.locator('.question-answer').isVisible(), true);
  assert.equal(await button(second, 'answer').getAttribute('aria-expanded'), 'false');
  await checkDownload(second, 1, false);
  await button(second, 'answer').click();
  await second.locator('.question-answer mjx-container').first().waitFor();
  await checkDownload(second, 1, true);
  await page.locator('#generate-batch').click();
  const nextIds = await questions.evaluateAll(cards => cards.map(card => card.dataset.problemId));
  assert.ok(nextIds.every(id => !ids.includes(id)));
  assert.equal(await questions.locator('.question-hint:visible,.question-answer:visible').count(), 0);
  assert.equal(await page.locator('#answer').isVisible(), false);
  await page.goto(shared);
  await page.waitForFunction(() => document.querySelectorAll('.batch-question').length === 14);
  assert.deepEqual(await questions.evaluateAll(cards => cards.map(card => card.dataset.problemId)), ids);
  assert.equal(await questions.locator('.question-hint:visible,.question-answer:visible').count(), 0);
  await page.locator('#generate').click();
  assert.equal(await questions.count(), 0);
  assert.equal(await page.locator('#recipe-details').isVisible(), true);
  assert.equal(await page.locator('#single-actions').isVisible(), true);
  assert.equal(await page.locator('#open-equashare').isVisible(), true);
  assert.equal(await page.locator('#download-tex').isVisible(), true);
  await page.locator('#answer-button').click();
  assert.equal(await page.locator('#single-answer').isVisible(), true);
  assert.equal(await page.locator('#batch-answers').isVisible(), false);
  // An unavailable fixed bank must not yield a partial batch or break single practice.
  await page.route('**/data/level6.json', route => route.fulfill({status:503,body:''}));
  await page.goto(baseURL+'?batch=missing');
  await page.waitForFunction(() => document.querySelector('#batch-status').textContent.includes('取得できません'));
  await page.waitForFunction(() => !document.querySelector('#generate').disabled);
  assert.equal(await page.locator('#generate-batch').isDisabled(), true);
  assert.equal(await questions.count(), 0);
  await page.locator('#generate').click();
  assert.equal(await page.locator('#problem-title').textContent(), '問題');
}
