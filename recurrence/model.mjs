export function poolFor(bank, level, family) {
  return bank.problems.filter(p => (level === 0 || p.scores.level === level)
    && (family === 'all' || p.family === family));
}

export function chooseProblem(pool, seen, random = Math.random, familyWeights = {}) {
  if (!pool.length) return null;
  let remaining = pool.filter(p => !seen.has(p.id));
  if (!remaining.length) {
    seen.clear();
    remaining = pool;
  }
  // Balance structural families before selecting a numerical variant.
  const families = [...new Set(remaining.map(p => p.family))];
  const weights = families.map(f => familyWeights[f] || 1);
  let cursor = random() * weights.reduce((sum, w) => sum + w, 0);
  const family = families.find((f, i) => (cursor -= weights[i]) < 0) || families.at(-1);
  const variants = remaining.filter(p => p.family === family);
  const problem = variants[Math.floor(random() * variants.length)];
  seen.add(problem.id);
  return problem;
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

export function texDocument(p, includeAnswer = false) {
  let text = String.raw`% UTF-8 / pLaTeX + dvipdfmx
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
\chapter{問題演習}
\begin{multicols*}{2}
以下、\,$n$は正の整数とする。\par
`;
  text += '\\section*{問題 ' + escapeTex(p.id) + (p.scores ? '（Lv' + p.scores.level + '）' : '') + '}\n';
  if (p.statement.definitions_tex) text += textbookProse('\\(' + p.statement.definitions_tex + '\\) とおく。');
  text += textbookProse('\\(' + p.statement.initials_tex.join(',\\quad ') + '\\) とし、');
  text += displayMath(p.statement.recurrence_tex);
  const system = p.statement.initials_tex.some(tex => /b_/.test(tex));
  text += system ? 'を満たす数列 $a_n$, $b_n$ の一般項をそれぞれ求めよ。\\par\n'
    : p.family === 'power_second' ? 'を満たす正の数列の一般項を求めよ。\\par\n'
    : 'を満たす数列の一般項を求めよ。\\par\n';
  text += '\\end{multicols*}\n';
  if (includeAnswer) {
    text += '\\chapter{方針・解答・解法}\n\\begin{multicols*}{2}\n';
    text += '\\section*{方針}\n' + textbookProse(p.routes[0].hint);
    text += '\\section*{解答}\n' + displayMath(p.answer_tex);
    text += '\\section*{解法}\n\\subsection*{' + escapeTex(p.routes[0].title) + '}\n';
    for (const step of p.routes[0].steps) text += textbookProse(step);
    text += 'したがって、求める一般項は\\par\n' + displayMath(p.answer_tex) + 'である。\\par\n';
    for (const route of p.routes.slice(1)) {
      text += '\\subsection*{別解：' + escapeTex(route.title) + '}\n';
      text += '方針：' + textbookProse(route.hint);
      for (const step of route.steps) text += textbookProse(step);
    }
    text += '\\end{multicols*}\n';
  }
  return text + '\\end{document}\n';
}
