export function poolFor(bank, level, family, authored = null) {
  return [...bank.problems, ...(authored?.problems ?? [])].filter(p => (level === 0 || problemLevel(p) === level)
    && (family === 'all' || (p.family ?? 'authored:' + p.category) === family));
}

export function chooseProblem(pool, seen, random = Math.random, familyWeights = {}) {
  if (!pool.length) return null;
  let remaining = pool.filter(p => !seen.has(p.id));
  if (!remaining.length) {
    seen.clear();
    remaining = pool;
  }
  // Balance structural families before selecting a numerical variant.
  const familyOf = p => p.family ?? p.category;
  const families = [...new Set(remaining.map(familyOf))];
  const weights = families.map(f => familyWeights[f] || 1);
  let cursor = random() * weights.reduce((sum, w) => sum + w, 0);
  const family = families.find((f, i) => (cursor -= weights[i]) < 0) || families.at(-1);
  const variants = remaining.filter(p => familyOf(p) === family);
  const problem = variants[Math.floor(random() * variants.length)];
  seen.add(problem.id);
  return problem;
}

export const BATCH_COUNTS = Object.freeze({1:2, 2:2, 3:3, 4:3, 5:2, 6:2});
export const problemLevel = p => p.scores?.level ?? p.level;

export function validateAuthoredBank(bank) {
  if (bank.schema_version !== 1 || bank.level !== 6 || bank.authorship !== 'hand_authored'
    || bank.verification_status !== 'worked_solutions_with_finite_exact_checks_not_lean_certified'
    || !Array.isArray(bank.categories) || !Array.isArray(bank.problems) || bank.problems.length < BATCH_COUNTS[6]) {
    throw new Error('難易度6の固定問題の形式が一致しません。');
  }
  const categories = new Set(bank.categories.map(c => c.id));
  const ids = new Set();
  for (const p of bank.problems) {
    if (!/^L6-[A-Z]\d{2,}$/.test(p.id) || ids.has(p.id) || p.level !== 6
      || p.authorship !== 'hand_authored' || !categories.has(p.category)
      || !['title','statement','hint','answer'].every(k => typeof p[k] === 'string' && p[k].trim())
      || !Array.isArray(p.solution) || !p.solution.length || !p.solution.every(s => typeof s === 'string' && s.trim())
      || !p.source?.url?.startsWith('https://github.com/')
      || typeof p.source.location !== 'string' || !p.source.location.trim()) {
      throw new Error('難易度6の問題・解説・出典を確認できません。');
    }
    ids.add(p.id);
  }
  return bank;
}

// Each level has its own history so exhausting one pool cannot reset another.
// Commit history only after a complete, duplicate-free worksheet is selected.
export function chooseBatch(bank, authored, history = new Map(), random = Math.random) {
  const pools = Object.keys(BATCH_COUNTS).map(Number).map(level => ({level,
    pool: level === 6 ? authored.problems : poolFor(bank, level, 'all')}));
  for (const {level, pool} of pools) {
    if (new Set(pool.map(p => p.id)).size < BATCH_COUNTS[level]) {
      throw new Error(`難易度${level}の問題数が足りないため、まとめて出題できません。`);
    }
  }
  const pending = new Map([...history].map(([level, seen]) => [level, new Set(seen)]));
  const problems = [];
  for (const {level, pool} of pools) {
    const seen = pending.get(level) ?? new Set();
    const selected = new Set();
    for (let i = 0; i < BATCH_COUNTS[level]; i++) {
      const p = chooseProblem(pool.filter(p => !selected.has(p.id)), seen, random,
        level === 6 ? {} : bank.selection_weights);
      problems.push(p); selected.add(p.id);
    }
    pending.set(level, seen);
  }
  history.clear();
  for (const [level, seen] of pending) history.set(level, seen);
  return problems;
}

export function batchFromIds(bank, authored, ids) {
  const all = new Map([...bank.problems, ...authored.problems].map(p => [p.id, p]));
  const problems = ids.map(id => all.get(id));
  if (ids.length !== 14 || new Set(ids).size !== 14 || problems.some(p => !p)
    || Object.entries(BATCH_COUNTS).some(([level, count]) => problems.filter(p => problemLevel(p) === Number(level)).length !== count)) {
    throw new Error('指定されたまとめ問題を復元できません。');
  }
  return problems;
}

// Authored prose uses $...$ and \[...\]; generated explanations use \(...\).
// Return text/math tokens rather than interpreting arbitrary HTML or Markdown.
export function mathTextParts(text) {
  const parts = [];
  const pattern = /\\\[([\s\S]*?)\\\]|\\\(([\s\S]*?)\\\)|\$([^$]*?)\$/g;
  let start = 0;
  for (const match of text.matchAll(pattern)) {
    if (match.index > start) parts.push({type:'text', text:text.slice(start, match.index)});
    parts.push({type:match[1] === undefined ? 'inline' : 'display', text:match[1] ?? match[2] ?? match[3]});
    start = match.index + match[0].length;
  }
  if (start < text.length) parts.push({type:'text', text:text.slice(start)});
  return parts;
}

export function validateBank(bank, manifest) {
  if (bank.schema_version !== '0.2' || !Array.isArray(bank.problems)
    || bank.verification?.status !== 'lean-verified'
    || manifest.status !== 'lean-verified'
    || bank.verification.commit !== manifest.commit
    || bank.proof_source_sha256 !== manifest.proof_source_sha256
    || bank.problems.length !== manifest.count) {
    throw new Error('検証済み問題の形式が一致しません。');
  }
  const ids = new Set();
  for (const p of bank.problems) {
    if (ids.has(p.id) || !/^p\d{3,}$/.test(p.id)
      || p.verification?.status !== 'lean-verified'
      || !p.lean_theorems?.includes(p.id + '_unique')
      || !p.routes?.length || p.routes[0].parts.U !== 0
      || p.quality?.accepted !== true || p.quality?.version !== bank.score_version
      || !p.routes.every(r => r.complete && r.certificate)
      || !Number.isInteger(p.scores.level) || p.scores.level < 1 || p.scores.level > 5) {
      throw new Error('問題の検証情報を確認できません。');
    }
    ids.add(p.id);
  }
  return bank;
}

const scoreLabels = {B:'操作', R:'発見', A:'計算', T:'条件の確認', P:'式の複雑さ', U:'未評価部分'};

export function problemInstruction(p) {
  return p.ir?.shape === 'system' ? '次の条件で定められる2つの数列について、一般項をそれぞれ求めよ。'
    : p.ir?.shape === 'power_second' || p.family === 'multiplicative_second' ? '次の条件を満たす正の数列について、一般項を求めよ。'
    : '次の条件で定められる数列について、一般項を求めよ。';
}

// Equashare renders one formula per line, without a document preamble or math delimiters.
export function equashareSource(p) {
  if (p.level === 6) {
    const lines = ['\\text{問題 ' + p.id + '（Lv6）}'];
    let row = '';
    const flush = () => { if (row.trim()) lines.push(row); row = ''; };
    for (const part of mathTextParts(p.statement)) {
      if (part.type === 'display') { flush(); lines.push(part.text.replace(/\s*\n\s*/g, ' ')); }
      else if (part.type === 'inline') row += part.text;
      else part.text.split(/\n\s*\n/g).forEach((text, i) => {
        if (i) flush();
        const prose = text.replace(/\s+/g, ' ');
        if (prose.trim()) row += '\\text{' + escapeTex(prose) + '}';
      });
    }
    flush();
    return lines.join('\n') + '\n';
  }
  return [
    '\\text{問題 ' + p.id.toUpperCase() + (p.scores ? '（Lv' + p.scores.level + '）' : '') + '}',
    '\\text{' + problemInstruction(p) + '}',
    p.statement.definitions_tex,
    p.statement.initials_tex.join(',\\quad '),
    p.statement.recurrence_tex,
    'n\\in\\mathbb{Z},\\quad n\\ge1',
  ].filter(Boolean).join('\n') + '\n';
}

export function routeComparison(routes) {
  const main = routes[0];
  const others = routes.slice(1);
  const difficulty = r => r.difficulty_cost ?? r.cost;
  if (main.difficulty_cost !== undefined && others.some(r => difficulty(r) > difficulty(main))) {
    return {reason:`登録済みの候補で教育上の難易度スコアが最小（${difficulty(main)}）なので、主解法にしています。`,
      alternatives:others.map(r => `主解法との比較：難易度は${difficulty(r)}（主解法は${difficulty(main)}）、操作などの合計は${r.cost}（主解法は${main.cost}）。`)};
  }
  let reason = '登録済みの候補では、この解法だけを検出しました。';
  if (others.length) {
    const tied = others.filter(r => r.cost === main.cost);
    if (!tied.length) reason = `登録済みの候補で合計スコアが最小（${main.cost}）なので、主解法にしています。`;
    else if (tied.every(r => r.numeric_cost > main.numeric_cost)) {
      reason = `合計スコアは同点（${main.cost}）ですが、途中で扱う数値のコストが小さいため、主解法にしています。`;
    } else {
      reason = `合計スコアと数値のコストが同点の解法があります。解法名の順で表示しており、優劣を表す順序ではありません。`;
    }
  }
  const alternatives = others.map(route => {
    const lower = [], higher = [];
    for (const [key,label] of Object.entries(scoreLabels)) {
      const difference = route.parts[key] - main.parts[key];
      if (difference < 0) lower.push(`${label}が${-difference}点低い`);
      if (difference > 0) higher.push(`${label}が${difference}点高い`);
    }
    const differences = [...lower, ...higher];
    return `主解法との比較：${differences.length ? differences.join('、') : '各項目のスコアも同じ'}。合計は${route.cost}（主解法は${main.cost}）。`;
  });
  return {reason, alternatives};
}

// Keep mathematical expressions intact while using the textbook's prose style.
export function textbookText(text) {
  return text.split(/(\\\([\s\S]*?\\\))/g).map((part, i) => i % 2 ? part : part
    .replaceAll('とおけます。', 'とおける。').replaceAll('を得ます。', 'を得る。')
    .replaceAll('となります。', 'となる。').replaceAll('消えます。', '消える。')
    .replaceAll('まとめられます。', 'まとめられる。').replaceAll('定義できます。', '定義できる。')
    .replaceAll('です。', 'である。')).join('');
}

const escapeTex = text => text.replace(/[\\%&#_${}~^]/g, char => ({
  '\\':'\\textbackslash{}', '~':'\\textasciitilde{}', '^':'\\textasciicircum{}'
}[char] || '\\' + char));
const displayMath = tex => '\\[\\fitmath{' + tex + '}\\]\n';
function textbookProse(text) {
  return textbookText(text).split(/(\\\([\s\S]*?\\\))/g).map((part, i) => {
    if (!(i % 2)) return escapeTex(part);
    const tex = part.slice(2, -2);
    return tex.length > 65 || tex.includes('\\begin{aligned}') ? displayMath(tex) : part;
  }).join('') + '\\par\n';
}

const texPreamble = String.raw`% UTF-8 / pLaTeX + dvipdfmx
\documentclass[dvipdfmx,a4paper,11pt,fleqn,openany]{jsbook}
\usepackage{amsmath,amsthm,amssymb,amsfonts}
\everymath{\displaystyle}
\usepackage[paperwidth=210truemm,paperheight=297truemm,margin=20truemm]{geometry}
\usepackage{multicol,enumitem,quotchap}
\usepackage[table]{xcolor}
\usepackage{tcolorbox,graphicx}
\definecolor{shadecolor}{gray}{0.80}
\raggedcolumns
\setlength{\columnsep}{12pt}
\setlength{\columnseprule}{0.4pt}
\setlength{\parskip}{0pt}
\setlength{\emergencystretch}{1em}
\setlist[enumerate,1]{label=(\arabic*),leftmargin=\leftmargini,parsep=3pt}
\newsavebox{\mathbox}
\newcommand{\fitmath}[1]{\sbox{\mathbox}{$\displaystyle #1$}%
\ifdim\wd\mathbox>\linewidth
\resizebox{\linewidth}{!}{\usebox{\mathbox}}%
\else\usebox{\mathbox}\fi}
\begin{document}
`;

function generatedStatementTex(p) {
  let text = '';
  if (p.statement.definitions_tex) text += textbookProse('\\(' + p.statement.definitions_tex + '\\) とおく。');
  text += textbookProse('\\(' + p.statement.initials_tex.join(',\\quad ') + '\\) とし、');
  text += displayMath(p.statement.recurrence_tex);
  const system = p.statement.initials_tex.some(tex => /b_/.test(tex));
  text += system ? 'を満たす数列 $a_n$, $b_n$ の一般項をそれぞれ求めよ。\\par\n'
    : (p.ir?.shape === 'power_second' || p.family === 'multiplicative_second') ? 'を満たす正の数列の一般項を求めよ。\\par\n'
    : 'を満たす数列の一般項を求めよ。\\par\n';
  return text;
}

function generatedSolutionTex(p, standalone = false) {
  const section = standalone ? '\\section*' : '\\subsection*';
  let text = section + '{方針}\n' + textbookProse(p.routes[0].hint);
  text += section + '{解答}\n' + displayMath(p.answer_tex);
  text += standalone ? '\\section*{解法}\n\\subsection*{' + escapeTex(p.routes[0].title) + '}\n'
    : '\\subsection*{解法：' + escapeTex(p.routes[0].title) + '}\n';
  for (const step of p.routes[0].steps) text += textbookProse(step);
  text += 'したがって、求める一般項は\\par\n' + displayMath(p.answer_tex) + 'である。\\par\n';
  for (const route of p.routes.slice(1)) {
    text += '\\subsection*{別解：' + escapeTex(route.title) + '}\n';
    text += '方針：' + textbookProse(route.hint);
    for (const step of route.steps) text += textbookProse(step);
  }
  return text;
}

export function texDocument(p, includeAnswer = false) {
  if (p.level === 6) {
    let text = texPreamble + '\\chapter{問題演習}\n\\begin{multicols*}{2}\n';
    text += '\\section*{問題 ' + escapeTex(p.id) + '（Lv6）}\n' + authoredProseTex(p.statement);
    text += '\\end{multicols*}\n';
    if (includeAnswer) text += '\\chapter{方針・解答・解法}\n\\begin{multicols*}{2}\n'
      + authoredSolutionTex(p) + '\\end{multicols*}\n';
    return text + '\\end{document}\n';
  }
  let text = texPreamble + '\\chapter{問題演習}\n\\begin{multicols*}{2}\n以下、\\,$n$は正の整数とする。\\par\n';
  text += '\\section*{問題 ' + escapeTex(p.id) + (p.scores ? '（Lv' + p.scores.level + '）' : '') + '}\n';
  text += generatedStatementTex(p) + '\\end{multicols*}\n';
  if (includeAnswer) {
    text += '\\chapter{方針・解答・解法}\n\\begin{multicols*}{2}\n'
      + generatedSolutionTex(p, true) + '\\end{multicols*}\n';
  }
  return text + '\\end{document}\n';
}

function authoredProseTex(text) {
  return mathTextParts(text).map(part => part.type === 'display' ? displayMath(part.text)
    : part.type === 'inline' ? '\\(' + part.text + '\\)'
    : part.text.split(/\n\s*\n/g).map(p => escapeTex(p.replaceAll('\n', ' '))).join('\\par\n'))
    .join('') + '\\par\n';
}

function authoredSolutionTex(p) {
  return '\\subsection*{方針}\n' + authoredProseTex(p.hint)
    + '\\subsection*{解答}\n' + authoredProseTex(p.answer)
    + '\\subsection*{解法}\n' + p.solution.map(authoredProseTex).join('')
    + '出典：' + escapeTex(p.source.location) + '。\\par\n';
}

export function batchTexDocument(problems, includeAnswer = false) {
  let text = texPreamble + '\\chapter{まとめて演習（14問）}\n\\begin{multicols*}{2}\n';
  text += '難易度1・2・5・6は各2問、難易度3・4は各3問。添字の範囲は各問の指定に従う。\\par\n';
  const heading = (p, i) => '\\section*{問題 ' + (i + 1) + '（Lv' + problemLevel(p) + '）}\\label{q:' + p.id + '}\n';
  problems.forEach((p, i) => {
    text += '\\par\\noindent\\begin{minipage}{\\linewidth}\n' + heading(p, i);
    text += p.level === 6 ? authoredProseTex(p.statement)
      : generatedStatementTex(p) + 'ただし、$n\\ge1$ とする。\\par\n';
    text += '\\end{minipage}\\par\\medskip\n';
  });
  text += '\\end{multicols*}\n';
  if (includeAnswer) {
    text += '\\chapter{方針・解答・解法}\n\\begin{multicols*}{2}\n';
    problems.forEach((p, i) => {
      text += '\\section*{問題 ' + (i + 1) + '（Lv' + problemLevel(p) + '）}\n';
      if (p.level !== 6) { text += generatedSolutionTex(p); return; }
      text += authoredSolutionTex(p);
    });
    text += '\\end{multicols*}\n';
  }
  return text + '\\end{document}\n';
}
