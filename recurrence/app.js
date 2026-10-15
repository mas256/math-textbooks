import { poolFor, chooseProblem, validateBank, texDocument, routeComparison, textbookText,
  chooseBatch, batchFromIds, validateAuthoredBank, problemLevel, mathTextParts, batchTexDocument,
  problemInstruction, equashareSource } from './model.mjs';

const $ = id => document.getElementById(id);
const state = { bank: null, manifest: null, authored: null, level: 2, family: 'all', current: null,
  batch: null, seen: new Set(), batchSeen: new Map(), hints: 0 };
const levelText = {0: '基本から発展まで、すべての問題を含みます。', 1: '等差・等比数列と、基本的な階差の和を確認します。',
  2: '総和の基本形、単項式の階比、指数で割ると等差になる型を扱います。', 3: '連立、一般の階比、基本的な3項間、対数型、指数の付加項を扱います。', 4: '一次分数、定数項付き3項間、平行移動して対数をとる型、難しい階比を扱います。', 5: '正規化・総和・階差・対数など、複数の変形を組み合わせる発展問題です。',
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
    mathBlock((p.statement.definitions_tex ? p.statement.definitions_tex + '\\qquad ' : '') + p.statement.recurrence_tex),
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
  const names = {power_first_encode:'累乗の更新へ',exponential_force:'指数の付加項',mobius_encode:'一次分数へ',factorial_product:'階比の総積',second_difference:'等差と階差の組合せ',constant:'定数数列', geometric:'等比数列', affine_fixed_point:'特性方程式型（2項間）',
    index_scale:'n に応じた倍率', add_constant:'定数の移動', constant_scale:'定数倍', index_add:'n の一次式を付加', reciprocal:'逆数', linear_combination:'等比数列の組合せ',
    repeated_factor:'一次式を掛けて重解へ', difference_lift:'階差を元の数列へ', sum_encode:'総和を含む式へ', cumulative_sum:'差を足して一段戻す', power_sequence:'指数の数列を元の数列へ',pair_mix:'独立した数列を連立へ',partial_sum_encode:'部分和の数列として与える',sum_relation_encode:'総和と一般項の関係へ',difference_polynomial:'多項式を階差にする'};
  const list = $('block-list');
  list.replaceChildren(el('span', names[p.recipe.core.kind], 'block'));
  for (const b of p.recipe.blocks) list.append(el('span', '→', 'block-arrow'), el('span', names[b.kind] || b.kind, 'block'));
  const table = el('table', undefined, 'score-table');
  const head = el('tr');
  for (const title of ['解法', '操作 B', '発見 R', '計算 A', '条件 T', '式 P', '未評価 U', '合計']) head.append(el('th', title));
  const thead = el('thead'); thead.append(head); table.append(thead);
  const tbody = el('tbody');
  for (const r of p.routes) {
    const row = el('tr');
    for (const value of [r.title, ...['B','R','A','T','P','U'].map(k => r.parts[k]), r.cost]) row.append(el('td', String(value)));
    tbody.append(row);
  }
  table.append(tbody);
  const wrapper = el('div', undefined, 'math-block'); wrapper.append(table);
  $('score-info').replaceChildren(wrapper, el('p', `教育上の難易度：${p.scores.difficulty} → Lv.${p.scores.level}。数値の扱いやすさ：${p.scores.cleanliness}（低いほど簡単）。分類の目安：${p.routes[0].difficulty_rule}。`, 'details-note'));
  const comparison = routeComparison(p.routes);
  $('score-info').append(el('p', comparison.reason + ' スコアは暫定値です。', 'details-note'),
    ...comparison.alternatives.map(note => el('p', note, 'details-note')));
  const metrics = p.quality.metrics;
  $('score-info').append(el('p', `完成式の評価：多項式係数の最高次数 ${metrics.coefficient_degree}、指数の次数 ${metrics.exponent_degree}、式の要素数 ${metrics.nodes}、分数の深さ ${metrics.fraction_depth}。登録済みの解法を係数から検出し、採用条件を確認しています。`, 'details-note'));
  const proof = $('proof-info');
  proof.replaceChildren(document.createTextNode('検証：Lean 4.19.0 / mathlib v4.19.0　'));
  if (/^\d+$/.test(String(state.manifest.run_id))) {
    const link = el('a', '検証実行の記録 ↗');
    link.href = `https://github.com/mas256/math-textbooks/actions/runs/${state.manifest.run_id}`;
    link.target = '_blank'; link.rel = 'noopener noreferrer'; proof.append(link);
  }
}

function renderGenerationSummary() {
  const {comparison, generation_config: config, function_catalog: catalog} = state.bank;
  const summary = $('generation-summary');
  summary.replaceChildren(el('p', `旧版の ${comparison.before.count} 問を同じ基準で再評価し、${comparison.baseline_rejected_count} 問を採用条件から除外しました。調整版は ${comparison.after.count} 問です。`),
    el('p', `多項式係数の最高次数：${comparison.before.max_coefficient_degree} → ${comparison.after.max_coefficient_degree}。式の要素数の最大値：${comparison.before.max_nodes} → ${comparison.after.max_nodes}。平均値：${comparison.before.mean_nodes} → ${comparison.after.mean_nodes}。`),
    el('p', `同じ種類の変形は通常 ${config.max_transforms.index_scale} 回、差を足して戻す操作は ${config.max_transforms.cumulative_sum} 回、全体で ${config.max_blocks} ブロックまで。連続する定数の付加・定数倍は統合し、逆数が連続する候補は除外します。`),
    el('p', 'この比較は式の構造を測った結果です。学習者の正答率や、良問としての評価は今後確認します。'));
  const diversity = comparison.diversity;
  const diversitySummary = $('diversity-summary');
  diversitySummary.replaceChildren();
  if (diversity) {
    diversitySummary.append(el('p', `前版の ${diversity.before.count} 問と今回の ${diversity.after.count} 問では、係数パターンは ${diversity.before.coefficient_patterns} → ${diversity.after.coefficient_patterns} 種類です。初期値だけが違う問題は同じパターンとして数えます。数値の扱いやすさを優先し、同程度の候補から公比・指数の底の偏りを減らして選びます。`));
    const table = el('table', undefined, 'score-table');
    table.append(el('caption', '公比・指数の底の分布'));
    const head = el('tr');
    for (const label of ['型','前版','今回']) head.append(el('th',label));
    const thead=el('thead'); thead.append(head); table.append(thead);
    const tbody=el('tbody');
    const distribution = data => Object.entries(data?.parameters || {}).map(([key,count]) => key.replace('ratio:', '公比 ').replace('base:', '底 ') + `：${count}問`).join('、') || '出題なし';
    for (const family of ['scaled_affine','reciprocal_scaled','ratio_power']) {
      const row=el('tr');
      for (const text of [state.bank.families[family] || family,distribution(diversity.before.families[family]),distribution(diversity.after.families[family])]) row.append(el('td',text));
      tbody.append(row);
    }
    table.append(tbody); diversitySummary.append(table);
  }
  const levelMix=$('level-diversity');
  levelMix.replaceChildren();
  if (comparison.level_diversity) {
    levelMix.append(el('p', '発展問題には、正規化した3項間、階差から階比へ進む型、総和を消去する型、対数と二重の階差を使う型を加えました。Lv3〜5では、逆数を使わない系統を各3種類以上、逆数型の割合を各40%以下にする条件も検査します。'));
    const table=el('table',undefined,'score-table');
    table.append(el('caption','難易度別の構成（逆数型は一次分数型などの系統）'));
    const head=el('tr');
    for (const label of ['難易度','前版：逆数型 / 全問','今回：逆数型 / 全問','今回：逆数以外の系統数']) head.append(el('th',label));
    const thead=el('thead'); thead.append(head); table.append(thead);
    const tbody=el('tbody');
    for (const lv of ['3','4','5']) {
      const before=comparison.level_diversity.before[lv],after=comparison.level_diversity.after[lv];
      const count=data=>`${data.fraction_count} / ${data.count}問（${data.count?Math.round(100*data.fraction_count/data.count):0}%）`;
      const row=el('tr');
      for (const text of [`Lv.${lv}`,count(before),count(after),`${after.nonfraction_families.length} 系統`]) row.append(el('td',text));
      tbody.append(row);
    }
    table.append(tbody);
    const wrapper=el('div',undefined,'math-block'); wrapper.append(table); levelMix.append(wrapper);
    levelMix.append(el('p','難易度の配点は暫定です。系統数と割合の改善は、学習者にとっての良問性や難しさの一致を保証するものではありません。','details-note'));
  }
  const functions = $('function-catalog');
  const normalizers = catalog.scales.filter(p => !p.id.startsWith('inverse:')).map(p => '\\(' + p.normalizer_tex + '\\)').join('、');
  const increments = catalog.exponents.map(p => '\\(' + p.increment_tex + '\\)').join('、');
  functions.replaceChildren(el('p', '正規化の候補：' + normalizers + ' と、それぞれの逆数。階比にはこれらの隣接比を使います。'),
    el('p', '指数係数の指数：' + increments + '。和が閉じた式になる候補を使います。'));
}

function resetExercise() {
  clearMath();
  state.hints = 0;
  $('hints').replaceChildren();
  $('answer').hidden = true;
  $('answer-button').setAttribute('aria-expanded', 'false');
  $('answer-button').replaceChildren(document.createTextNode('解答を見る '), el('span', '↓'));
  $('hint-button').disabled = false;
  $('hint-button').replaceChildren(document.createTextNode('ヒントを見る '), el('span', '＋'));
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
    $('bank-status').textContent = `${state.manifest.count} 問・${Object.keys(state.bank.families).length}系統 / Lean検証済み`;
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
  $('hint-button').replaceChildren(document.createTextNode('まとめてヒントを見る '), el('span', '＋'));
  $('answer-button').replaceChildren(document.createTextNode('まとめて解答を見る '), el('span', '↓'));
  $('recipe-details').hidden = true;
  $('open-equashare').disabled = true;
  $('action-status').textContent = '14問を出題しました';
  const content = $('problem-content');
  content.replaceChildren(...problems.map((p, i) => {
    const card = el('section', undefined, 'batch-question');
    card.dataset.level = problemLevel(p); card.dataset.problemId = p.id;
    card.append(batchHeading(p, i), problemStatement(p));
    return card;
  }));
  if (updateUrl) {
    const url = new URL(location.href); url.search = '';
    url.searchParams.set('batch', problems.map(p => p.id).join(','));
    history.replaceState(null, '', url);
  }
  typeset([content]);
}

function renderBatchAnswers(problems = state.batch, headings = true) {
  const answers = $('batch-answers');
  answers.replaceChildren(...problems.map((p, i) => {
    const card = el('section', undefined, headings ? 'batch-solution' : 'authored-solution');
    card.dataset.problemId = p.id;
    if (headings) card.append(batchHeading(p, i, 'h4'));
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
  }));
}

function showHint() {
  if (!state.current && !state.batch) return;
  if (state.hints) return;
  const hints = (state.batch || [state.current]).map((p, i) => {
    const hint = el('div', undefined, 'hint');
    hint.append(el('strong', state.batch ? `問題 ${i + 1} の方針` : '方針'),
      p.level === 6 ? mathProse(p.hint) : el('span', textbookText(p.routes[0].hint)));
    return hint;
  });
  $('hints').append(...hints);
  state.hints = 1;
  $('hint-button').disabled = true;
  $('hint-button').replaceChildren(document.createTextNode('方針を表示しました'), el('span', '＋'));
  typeset(hints);
}

function toggleAnswer() {
  const p = state.current;
  if (!p && !state.batch) return;
  const open = $('answer').hidden;
  $('answer').hidden = !open;
  $('answer-button').setAttribute('aria-expanded', String(open));
  $('answer-button').replaceChildren(document.createTextNode((state.batch ? 'まとめて' : '') + (open ? '解答を閉じる ' : '解答を見る ')), el('span', open ? '↑' : '↓'));
  if (!open) return;
  if (window.MathJax?.typesetClear) window.MathJax.typesetClear([$('answer')]);
  const fixed = p?.level === 6;
  $('single-answer').hidden = Boolean(state.batch) || fixed;
  $('batch-answers').hidden = !state.batch && !fixed;
  if (state.batch || fixed) {
    renderBatchAnswers(state.batch || [p], Boolean(state.batch)); typeset([$('answer')]); return;
  }
  $('method-title').textContent = p.routes[0].title;
  $('method-observation').textContent = '方針：' + textbookText(p.routes[0].hint);
  $('method-choice').hidden = true;
  $('solution-steps').replaceChildren(...p.routes[0].steps.map(step => el('li', textbookText(step))));
  $('answer-formula').replaceChildren(mathBlock(p.answer_tex));
  $('revealed-family').textContent = p.family_label;
  const alternates = $('alternate-container'); alternates.replaceChildren();
  for (const route of p.routes.slice(1, 3)) {
    const box = el('details', undefined, 'alternate');
    box.append(el('summary', '別解：' + route.title));
    box.append(el('p', '方針：' + textbookText(route.hint), 'method-observation'));
    const steps = el('ol', undefined, 'solution-steps');
    steps.append(...route.steps.map(step => el('li', textbookText(step)))); box.append(steps);
    box.addEventListener('toggle', () => { if (box.open) typeset([box]); });
    alternates.append(box);
  }
  typeset([$('answer')]);
}

function download(text, extension, mime = 'text/plain;charset=utf-8') {
  if (!state.current && !state.batch) return;
  const link = el('a');
  const url = URL.createObjectURL(new Blob([text], {type:mime}));
  link.href = url; link.download = `recurrence-${state.batch ? 'batch-14' : state.current.id}.${extension}`;
  document.body.append(link); link.click(); link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
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
    for (const [key, label] of Object.entries(state.bank.families)) {
      const option = el('option', label); option.value = key; $('family').append(option);
    }
    $('family').disabled = false;
    $('bank-status').textContent = `${manifest.count} 問・${Object.keys(state.bank.families).length}系統 / Lean検証済み`;
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
$('download-tex').addEventListener('click', () => download(state.batch
  ? batchTexDocument(state.batch, !$('answer').hidden) : texDocument(state.current, !$('answer').hidden), 'tex'));
$('open-equashare').addEventListener('click', () => {
  if (!state.current) return;
  const url = new URL('../equashare/', location.href);
  url.searchParams.set('prefill', equashareSource(state.current));
  window.open(url.href, '_blank', 'noopener,noreferrer');
});
$('download-recipe').addEventListener('click', () => download(JSON.stringify(state.current.recipe,null,2), 'json', 'application/json'));
$('download-lean').addEventListener('click', () => download(state.current.lean_source, 'lean'));
$('print-problem').addEventListener('click', () => window.print());
$('generation-details').addEventListener('toggle', () => { if ($('generation-details').open) typeset([$('function-catalog')]); });
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
