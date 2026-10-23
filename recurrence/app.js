import { poolFor, chooseProblem, validateBank, texDocument, routeComparison, textbookText,
  chooseBatch, batchFromIds, validateAuthoredBank, problemLevel, mathTextParts,
  problemInstruction, equashareSource } from './model.mjs';

const $ = id => document.getElementById(id);
const state = { bank: null, manifest: null, authored: null, level: 2, family: 'all', current: null,
  batch: null, seen: new Set(), batchSeen: new Map(), hints: 0 };
const levelText = {0: '基本から発展まで、すべての問題を含みます。', 1: '等差・等比数列、定数の数列、一次式の階差を扱います。',
  2: '不動点、階比と階乗、二次式の階差、定数の二階差を扱います。', 3: '基本的な3項間と重根、指数係数の階比、特解、連立の分離、総和の消去、逆数型を扱います。',
  4: '一次分数、倍率による正規化、定数項を含む3項間、正規化する連立を扱います。', 5: '逆数と変数係数、階差と総和、部分和の正規化、対数と二重の階差など、変形を組み合わせる発展問題です。',
  6: 'ガウス型・隣接4項間・非隣接型・ニュートン法など、事前作成した難問を扱います。'};
let mathQueue = Promise.resolve();

function showScrollHints() {
  for (const box of document.querySelectorAll('.math-block')) {
    if (!box.querySelector('mjx-container')) continue;
    const wide = box.scrollWidth > box.clientWidth + 2;
    let hint = box.nextElementSibling?.classList.contains('scroll-help') ? box.nextElementSibling : null;
    if (wide) {
      box.tabIndex = 0;
      if (!hint) { hint = el('p', '長い数式は横にスクロールできます。', 'scroll-help'); box.after(hint); }
    } else {
      box.removeAttribute('tabindex');
      hint?.remove();
    }
  }
}

function el(tag, text, className) {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = text;
  if (className) node.className = className;
  return node;
}

function mathBlock(tex, className = 'math-block') {
  return el('div', '\\[' + tex + '\\]', className);
}

function mathProse(text) {
  const box = el('div', undefined, 'math-prose');
  let paragraph = null;
  const append = node => {
    if (!paragraph) { paragraph = el('p'); box.append(paragraph); }
    paragraph.append(node);
  };
  for (const part of mathTextParts(text)) {
    if (part.type === 'display') {
      box.append(mathBlock(part.text)); paragraph = null;
    } else if (part.type === 'inline') {
      append(document.createTextNode('\\(' + part.text + '\\)'));
    } else {
      part.text.split(/\n\s*\n/g).forEach((text, i) => {
        if (i) paragraph = null;
        if (text.trim() || paragraph) append(document.createTextNode(text.replaceAll('\n', ' ')));
      });
    }
  }
  return box;
}

function problemStatement(p) {
  if (p.level === 6) return mathProse(p.statement);
  const box = el('div');
  box.append(el('p', problemInstruction(p)), mathBlock(p.statement.initials_tex.join(',\\quad ')),
    ...p.statement.recurrences_tex.map(tex => mathBlock(tex)),
    el('p', 'n は 1 以上の整数とする。', 'question-line'));
  return box;
}

function batchHeading(p, index, tag = 'h3') {
  const heading = el('div', undefined, 'batch-question-heading');
  heading.append(el(tag, `問題 ${index + 1}`), el('span', `Lv.${problemLevel(p)}`, 'pill'), el('span', p.id.toUpperCase(), 'problem-id'));
  return heading;
}

function typeset(nodes) {
  mathQueue = mathQueue.then(async () => {
    for (let attempt = 0; !window.MathJax?.startup?.promise && attempt < 150; attempt++) {
      await new Promise(resolve => setTimeout(resolve, 100));
    }
    if (!window.MathJax?.startup?.promise) throw new Error('MathJax is unavailable');
    await window.MathJax.startup.promise;
    if (!window.MathJax.typesetPromise) throw new Error('MathJax is unavailable');
    await window.MathJax.typesetPromise(nodes);
    showScrollHints();
    $('math-warning').hidden = true;
  }).catch(() => { $('math-warning').hidden = false; });
}

function clearMath() {
  if (window.MathJax?.typesetClear) window.MathJax.typesetClear([$('problem-content'), $('answer'), $('hints')]);
}

function updatePool() {
  if (!state.bank) return;
  const pool = poolFor(state.bank, state.level, state.family, state.authored);
  $('selection-count').textContent = pool.length ? `${pool.length} 問から出題できます` : 'この組合せの問題はまだありません';
  $('generate').disabled = !pool.length;
  $('level-help').textContent = levelText[state.level];
  for (const button of document.querySelectorAll('button[data-level]')) {
    button.setAttribute('aria-pressed', String(Number(button.dataset.level) === state.level));
  }
  $('all-levels').setAttribute('aria-pressed', String(state.level === 0));
}

function renderRecipe(p) {
  const list = $('block-list');
  list.replaceChildren(el('span', p.recipe.core.kind, 'block'));
  for (const b of p.recipe.blocks) list.append(el('span', '→', 'block-arrow'), el('span', b.kind, 'block'));
  const table = el('table', undefined, 'score-table');
  const head = el('tr');
  for (const title of ['解法', '操作 B', '発見 R', '計算 A', '条件 T', '式 P', '未評価 U', '合計']) head.append(el('th', title));
  const thead = el('thead'); thead.append(head); table.append(thead);
  const tbody = el('tbody');
  for (const r of p.routes) {
    const row = el('tr');
    for (const value of [r.title, ...['B','R','A','T','P','U'].map(k => r.parts[k]), r.total_score]) row.append(el('td', String(value)));
    tbody.append(row);
  }
  table.append(tbody);
  const wrapper = el('div', undefined, 'math-block'); wrapper.append(table);
  const c = p.classification;
  $('score-info').replaceChildren(wrapper, el('p', `教育上の難易度スコア：${c.score} → Lv.${p.level}。数値の扱いやすさ：${c.numeric_cost}（低いほど簡単）。分類の目安：${c.reason}。出題の細分類：${p.variant.label}。`, 'details-note'));
  const comparison = routeComparison(p.routes);
  $('score-info').append(el('p', comparison.reason + ' スコアは暫定値です。', 'details-note'),
    ...comparison.alternatives.map(note => el('p', note, 'details-note')));
  const metrics = c.metrics;
  $('score-info').append(el('p', `完成式の評価：多項式係数の最高次数 ${metrics.coefficient_degree}、指数の次数 ${metrics.exponent_degree}、式の要素数 ${metrics.nodes}、分数の深さ ${metrics.fraction_depth}。`, 'details-note'));
  const proof = $('proof-info');
  proof.replaceChildren(document.createTextNode(`検証：Lean ${p.lean.lean_version} / mathlib v4.19.0（公理：${p.lean.axioms.join('、') || 'なし'}）、n=${p.finite_check.first_index ?? 1}〜${p.finite_check.checked_terms} の厳密計算　`));
  const run = runLink();
  if (run) proof.append(run);
}

function runLink() {
  if (!/^\d+$/.test(String(state.manifest.run_id))) return null;
  const link = el('a', '生成・検証の実行記録 ↗');
  link.href = `https://github.com/mas256/math-textbooks/actions/runs/${state.manifest.run_id}`;
  link.target = '_blank'; link.rel = 'noopener noreferrer';
  return link;
}

function renderGenerationSummary() {
  const {manifest, bank} = state;
  const counts = Object.entries(manifest.counts).map(([level, count]) => `Lv.${level}：${count}問`).join('、');
  const generated = manifest.generated_at ? new Date(manifest.generated_at).toLocaleString('ja-JP', {timeZone:'Asia/Tokyo'}) + '（日本時間）' : '記録なし';
  const families = new Set(bank.problems.map(p => p.family)).size;
  const variants = new Set(bank.problems.map(p => p.variant.id)).size;
  const summary = $('generation-summary');
  summary.replaceChildren(
    el('p', `生成日時：${generated}。漸化式エンジン v${manifest.engine_version}（コミット ${String(manifest.engine_revision).slice(0, 12)}）、乱数の種 ${manifest.seed}。`),
    el('p', `${counts}。${families}系統・${variants}細分類から、出題の偏りを抑えて選んでいます。`),
    el('p', `全問で、Recipeの再生成、一般項と初期条件・漸化式・定義域条件の n=1〜${manifest.finite_checked_terms} の厳密計算、Lean ${manifest.lean_version} による初期値・全ての添字での漸化式・一意性・定義域条件の証明を通過しています。Lean検証に失敗して除外した候補：${manifest.lean_rejected.length}件。`),
    el('p', '問題は更新を依頼したときにまとめて作り直します。更新すると、以前の問題へのリンクは使えなくなります。難易度6の固定問題は更新しても変わりません。', 'details-note'));
  const run = runLink();
  if (run) summary.append(run);
}

function resetExercise() {
  clearMath();
  state.hints = 0;
  $('hints').replaceChildren();
  $('answer').hidden = true;
  $('answer-button').setAttribute('aria-expanded', 'false');
  $('answer-button').textContent = '答え';
  $('hint-button').disabled = false;
  $('hint-button').textContent = 'ヒント';
  $('single-actions').hidden = false;
  $('copy-link').textContent = 'この問題のリンクをコピー';
  $('recipe-details').open = false;
  $('authored-details').open = false;
  $('authored-details').hidden = true;
  $('action-status').textContent = '';
  for (const id of ['hint-button','answer-button','copy-link','download-tex','open-equashare','print-problem']) $(id).disabled = false;
}

function updateBankStatus() {
  if (state.batch) {
    $('bank-status').textContent = `生成${state.bank.problems.length}問＋固定${state.authored.problems.length}問から出題`;
  } else if (state.current?.level === 6) {
    $('bank-status').textContent = `固定${state.authored.problems.length}問・${state.authored.categories.length}分野 / 解説付き`;
  } else {
    $('bank-status').textContent = `${state.manifest.count} 問 / Lean検証済み`;
  }
}

function renderProblem(p, updateUrl = true) {
  resetExercise();
  state.current = p; state.batch = null;
  updateBankStatus();
  $('problem-title').textContent = '問題';
  $('problem-level').textContent = `Lv.${problemLevel(p)}`;
  $('problem-id').textContent = p.id.toUpperCase();
  const content = $('problem-content');
  content.replaceChildren(...problemStatement(p).childNodes);
  $('recipe-details').hidden = p.level === 6;
  if (p.level === 6) {
    $('authored-details').hidden = false;
    const source = el('a', '出典：' + p.source.location);
    source.href = p.source.url; source.target = '_blank'; source.rel = 'noopener noreferrer';
    $('authored-info').replaceChildren(el('p', p.title), source);
  } else renderRecipe(p);
  if (updateUrl) {
    const url = new URL(location.href); url.search = ''; url.searchParams.set('problem', p.id);
    history.replaceState(null, '', url);
  }
  typeset([content]);
}

function renderBatch(problems, updateUrl = true) {
  resetExercise();
  state.batch = problems; state.current = null;
  updateBankStatus();
  $('problem-title').textContent = 'まとめて演習';
  $('problem-level').textContent = 'Lv.1〜6';
  $('problem-id').textContent = '全14問';
  $('single-actions').hidden = true;
  $('copy-link').textContent = 'この問題セットのリンクをコピー';
  $('recipe-details').hidden = true;
  $('action-status').textContent = '14問を出題しました';
  const content = $('problem-content');
  content.replaceChildren(...problems.map((p, i) => {
    const card = el('section', undefined, 'batch-question');
    card.dataset.level = problemLevel(p); card.dataset.problemId = p.id;
    card.append(batchHeading(p, i), problemStatement(p), questionControls(p, i));
    return card;
  }));
  if (updateUrl) {
    const url = new URL(location.href); url.search = '';
    url.searchParams.set('batch', problems.map(p => p.id).join(','));
    history.replaceState(null, '', url);
  }
  typeset([content]);
}

function questionControls(p, index) {
  const box = el('div', undefined, 'question-tools');
  const actions = el('div', undefined, 'question-actions');
  actions.setAttribute('role', 'group');
  actions.setAttribute('aria-label', `問題 ${index + 1} の操作`);
  const hint = el('div', undefined, 'question-hint hint');
  const answer = el('section', undefined, 'question-answer');
  hint.id = `question-${p.id}-hint`; answer.id = `question-${p.id}-answer`;
  hint.hidden = true; answer.hidden = true;
  const toggle = (label, action, panel, fill) => {
    const button = el('button', label, 'secondary-button');
    button.type = 'button'; button.dataset.action = action;
    button.id = `question-${p.id}-${action}-button`;
    button.setAttribute('aria-controls', panel.id);
    button.setAttribute('aria-expanded', 'false');
    panel.setAttribute('aria-labelledby', button.id);
    panel.setAttribute('role', 'region');
    button.addEventListener('click', () => {
      const open = panel.hidden;
      if (open && !panel.hasChildNodes()) fill();
      panel.hidden = !open;
      button.setAttribute('aria-expanded', String(open));
      button.textContent = open ? `${label}を閉じる` : label;
      if (open) typeset([panel]);
    });
    return button;
  };
  const hintButton = toggle('ヒント', 'hint', hint, () => hint.append(el('strong', '方針'),
    mathProse(p.level === 6 ? p.hint : textbookText(p.routes[0].hint))));
  const answerButton = toggle('答え', 'answer', answer, () => answer.append(solutionCard(p)));
  const equashareButton = el('button', 'Equashare', 'secondary-button');
  equashareButton.type = 'button'; equashareButton.dataset.action = 'equashare';
  equashareButton.title = 'この問題をEquashareで開く（新しいタブ）';
  equashareButton.addEventListener('click', () => openEquashare(p));
  const texButton = el('button', 'TeX', 'secondary-button');
  texButton.type = 'button'; texButton.dataset.action = 'tex';
  texButton.title = 'この問題のTeXを保存（答えを開いている場合は解答も含む）';
  texButton.addEventListener('click', () => download(texDocument(p, !answer.hidden), 'tex', undefined, p.id));
  actions.append(hintButton, answerButton, equashareButton, texButton);
  box.append(actions, hint, answer);
  return box;
}

function solutionCard(p) {
  const card = el('div', undefined, p.level === 6 ? 'authored-solution' : 'generated-solution');
  card.dataset.problemId = p.id;
  const authored = p.level === 6;
  const hint = el('div', undefined, 'method-observation');
  hint.append(el('strong', '方針'), mathProse(authored ? p.hint : textbookText(p.routes[0].hint)));
  const answer = el('div', undefined, 'answer-formula');
  answer.append(authored ? mathProse(p.answer) : mathBlock(p.answer_tex));
  const steps = el('ol', undefined, 'solution-steps');
  for (const step of authored ? p.solution : p.routes[0].steps) {
    const item = el('li'); item.append(mathProse(authored ? step : textbookText(step))); steps.append(item);
  }
  card.append(el('p', authored ? p.title : p.routes[0].title, 'method-title'), hint, answer, steps);
  if (authored) {
    const source = el('p', undefined, 'solution-note');
    const link = el('a', '出典：' + p.source.location);
    link.href = p.source.url; link.target = '_blank'; link.rel = 'noopener noreferrer';
    source.append(link); card.append(source);
  } else {
    card.append(el('p', '問題の型：' + p.family_label, 'solution-note'));
  }
  return card;
}

function stepItem(step) {
  const item = el('li'); item.append(mathProse(textbookText(step)));
  return item;
}

function showHint() {
  if (!state.current) return;
  if (state.hints) return;
  const hints = [state.current].map(p => {
    const hint = el('div', undefined, 'hint');
    hint.append(el('strong', '方針'),
      mathProse(p.level === 6 ? p.hint : textbookText(p.routes[0].hint)));
    return hint;
  });
  $('hints').append(...hints);
  state.hints = 1;
  $('hint-button').disabled = true;
  $('hint-button').textContent = 'ヒント表示済み';
  typeset(hints);
}

function toggleAnswer() {
  const p = state.current;
  if (!p) return;
  const open = $('answer').hidden;
  $('answer').hidden = !open;
  $('answer-button').setAttribute('aria-expanded', String(open));
  $('answer-button').textContent = open ? '答えを閉じる' : '答え';
  if (!open) return;
  if (window.MathJax?.typesetClear) window.MathJax.typesetClear([$('answer')]);
  const fixed = p.level === 6;
  $('single-answer').hidden = fixed;
  $('batch-answers').hidden = !fixed;
  if (fixed) {
    $('batch-answers').replaceChildren(solutionCard(p)); typeset([$('answer')]); return;
  }
  $('method-title').textContent = p.routes[0].title;
  $('method-observation').textContent = '方針：' + textbookText(p.routes[0].hint);
  $('method-choice').hidden = true;
  $('solution-steps').replaceChildren(...p.routes[0].steps.map(stepItem));
  $('answer-formula').replaceChildren(mathBlock(p.answer_tex));
  $('revealed-family').textContent = p.family_label;
  const alternates = $('alternate-container'); alternates.replaceChildren();
  for (const route of p.routes.slice(1, 3)) {
    const box = el('details', undefined, 'alternate');
    box.append(el('summary', '別解：' + route.title));
    box.append(el('p', '方針：' + textbookText(route.hint), 'method-observation'));
    const steps = el('ol', undefined, 'solution-steps');
    steps.append(...route.steps.map(stepItem)); box.append(steps);
    box.addEventListener('toggle', () => { if (box.open) typeset([box]); });
    alternates.append(box);
  }
  typeset([$('answer')]);
}

function download(text, extension, mime = 'text/plain;charset=utf-8', problemId = state.current?.id) {
  if (!state.current && !state.batch) return;
  const link = el('a');
  const url = URL.createObjectURL(new Blob([text], {type:mime}));
  link.href = url; link.download = `recurrence-${problemId}.${extension}`;
  document.body.append(link); link.click(); link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

function openEquashare(p) {
  if (!p) return;
  const url = new URL('../equashare/', location.href);
  url.searchParams.set('prefill', equashareSource(p));
  window.open(url.href, '_blank', 'noopener,noreferrer');
}

function updateBatchAvailability() {
  if (!state.bank || !state.authored) return;
  $('generate-batch').disabled = false;
  $('batch-status').textContent = `難易度6は固定問題${state.authored.problems.length}問から選びます。`;
}

async function loadAuthored() {
  try {
    const response = await fetch('./data/level6.json', {cache:'no-store'});
    if (!response.ok) throw new Error('難易度6の固定問題を取得できませんでした。');
    state.authored = validateAuthoredBank(await response.json());
    $('level-six').disabled = false;
    const group = el('optgroup'); group.label = '難易度6（固定問題）';
    for (const category of state.authored.categories) {
      const option = el('option', category.label); option.value = 'authored:' + category.id; group.append(option);
    }
    $('family').append(group);
    updatePool();
    updateBatchAvailability();
  } catch (error) {
    $('batch-status').textContent = error.message + ' まとめて出題するには再読み込みしてください。';
  }
}

async function load() {
  const authoredLoaded = loadAuthored();
  try {
    const responses = await Promise.all(['manifest.json', 'problems.json'].map(path => fetch('./data/' + path, {cache:'no-store'})));
    for (const r of responses) if (!r.ok) throw new Error('問題データを取得できませんでした。');
    const manifest = await responses[0].json();
    const bytes = await responses[1].arrayBuffer();
    const digest = await crypto.subtle.digest('SHA-256', bytes);
    const hash = [...new Uint8Array(digest)].map(b => b.toString(16).padStart(2,'0')).join('');
    if (hash !== manifest.bank_sha256) throw new Error('検証情報と問題データが一致しません。再読み込みしてください。');
    state.manifest = manifest;
    state.bank = validateBank(JSON.parse(new TextDecoder().decode(bytes)), manifest);
    const present = new Set(state.bank.problems.map(p => p.family));
    const group = el('optgroup'); group.label = '難易度1〜5（生成問題）';
    for (const [key, label] of Object.entries(state.bank.families)) {
      if (!present.has(key)) continue;
      const option = el('option', label); option.value = key; group.append(option);
    }
    $('family').prepend(group);
    $('family').prepend($('family').querySelector('option[value="all"]'));
    $('family').disabled = false;
    $('bank-status').textContent = `${manifest.count} 問 / Lean検証済み`;
    renderGenerationSummary();
    const params = new URL(location.href).searchParams;
    const requested = params.get('problem');
    const requestedBatch = params.get('batch');
    // Single-question practice remains available while the fixed bank loads.
    if (requestedBatch || requested?.startsWith('L6-')) await authoredLoaded;
    const shared = [...state.bank.problems, ...(state.authored?.problems ?? [])].find(p => p.id === requested);
    if (shared) state.level = problemLevel(shared);
    updatePool();
    const first = shared || chooseProblem(poolFor(state.bank, state.level, state.family, state.authored), state.seen, Math.random, state.bank.selection_weights);
    if (shared) state.seen.add(shared.id);
    let restored = false;
    if (requestedBatch && state.authored) {
      try {
        const problems = batchFromIds(state.bank, state.authored, requestedBatch.split(','));
        for (const p of problems) {
          const level = problemLevel(p);
          if (!state.batchSeen.has(level)) state.batchSeen.set(level, new Set());
          state.batchSeen.get(level).add(p.id);
        }
        renderBatch(problems); restored = true;
      } catch { /* Fall back to a single problem if the shared batch is invalid. */ }
    }
    if (!restored) renderProblem(first);
    if (requested && !shared) $('action-status').textContent = '指定された問題がないため、別の問題を表示しました。';
    if (requestedBatch && !restored) $('action-status').textContent = '指定されたまとめ問題を復元できないため、1問を表示しました。';
    updateBatchAvailability();
    document.querySelector('.exercise').setAttribute('aria-busy','false');
  } catch (error) {
    state.bank = null;
    $('generate-batch').disabled = true;
    $('bank-status').textContent = '問題を読み込めません';
    $('load-error').textContent = error.message + ' 時間をおいて再読み込みしてください。';
    $('load-error').hidden = false;
    $('selection-count').textContent = '出題できる問題がありません';
    $('batch-status').textContent = '難易度1〜5の問題を読み込めないため、まとめて出題できません。';
    $('problem-content').replaceChildren();
    document.querySelector('.exercise').setAttribute('aria-busy','false');
  }
}

document.querySelectorAll('button[data-level]').forEach(button => button.addEventListener('click', () => {
  state.level = Number(button.dataset.level); updatePool();
}));
$('all-levels').addEventListener('click', () => { state.level = 0; updatePool(); });
$('family').addEventListener('change', () => { state.family = $('family').value; updatePool(); });
$('generate').addEventListener('click', () => {
  const p = chooseProblem(poolFor(state.bank, state.level, state.family, state.authored), state.seen, Math.random, state.bank.selection_weights);
  if (p) renderProblem(p);
});
$('generate-batch').addEventListener('click', () => {
  try { renderBatch(chooseBatch(state.bank, state.authored, state.batchSeen)); }
  catch (error) { $('batch-status').textContent = error.message; }
});
$('hint-button').addEventListener('click', showHint);
$('answer-button').addEventListener('click', toggleAnswer);
$('copy-link').addEventListener('click', async () => {
  try { await navigator.clipboard.writeText(location.href); $('action-status').textContent = 'リンクをコピーしました'; }
  catch { $('action-status').textContent = 'アドレスバーのURLをコピーしてください'; }
});
$('download-tex').addEventListener('click', () => {
  if (state.current) download(texDocument(state.current, !$('answer').hidden), 'tex');
});
$('open-equashare').addEventListener('click', () => openEquashare(state.current));
$('download-recipe').addEventListener('click', () => download(JSON.stringify(state.current.recipe,null,2), 'json', 'application/json'));
$('download-lean').addEventListener('click', () => download(state.current.lean.source, 'lean'));
$('print-problem').addEventListener('click', () => window.print());
$('retry-math').addEventListener('click', () => {
  if (window.MathJax?.typesetPromise) { typeset([$('problem-content'),$('answer'),$('hints')]); return; }
  $('mathjax-script')?.remove();
  const script = document.createElement('script'); script.id = 'mathjax-script';
  script.src = 'https://cdn.jsdelivr.net/npm/mathjax@4.0.0/tex-svg.js';
  script.addEventListener('load', () => typeset([$('problem-content'),$('answer'),$('hints')]));
  document.head.append(script);
});
load();
window.addEventListener('resize', showScrollHints);
