export function poolFor(bank, level, family) {
  return bank.problems.filter(p => (level === 0 || p.scores.level === level)
    && (family === 'all' || p.family === family));
}

export function chooseProblem(pool, seen, random = Math.random) {
  if (!pool.length) return null;
  let remaining = pool.filter(p => !seen.has(p.id));
  if (!remaining.length) {
    seen.clear();
    remaining = pool;
  }
  // Balance structural families before selecting a numerical variant.
  const families = [...new Set(remaining.map(p => p.family))];
  const family = families[Math.floor(random() * families.length)];
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
      || !Number.isInteger(p.scores.level) || p.scores.level < 1 || p.scores.level > 4) {
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

export function texDocument(p, includeAnswer = false) {
  const math = text => '\\[\n' + text + '\n\\]\n';
  let text = '% UTF-8 / LuaLaTeX\n\\documentclass{ltjsarticle}\n\\usepackage{amsmath}\n\\begin{document}\n';
  text += '\\section*{問題 ' + p.id + '}\n数列の一般項 $a_n$ を求めよ。$n\\geq 1$ とする。\n';
  text += math(p.statement.initials_tex.join(',\\quad '));
  text += math(p.statement.recurrence_tex);
  if (includeAnswer) {
    text += '\\section*{解答}\n' + p.routes[0].title + '\n';
    const comparison = routeComparison(p.routes);
    text += '\n着眼点：' + p.routes[0].hint + '\n';
    text += '\n' + comparison.reason + ' スコアは暫定値です。\n';
    for (const step of p.routes[0].steps) text += '\n' + step + '\n';
    text += math(p.answer_tex);
    for (const [index, route] of p.routes.slice(1).entries()) {
      text += '\\subsection*{別解：' + route.title + '}\n';
      text += '\n着眼点：' + route.hint + '\n' + comparison.alternatives[index] + '\n';
      for (const step of route.steps) text += '\n' + step + '\n';
    }
  }
  return text + '\\end{document}\n';
}
