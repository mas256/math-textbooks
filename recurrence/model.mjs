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

export function texDocument(p, includeAnswer = false) {
  const math = text => '\\[\n' + text + '\n\\]\n';
  let text = '% UTF-8 / LuaLaTeX\n\\documentclass{ltjsarticle}\n\\usepackage{amsmath}\n\\begin{document}\n';
  text += '\\section*{問題 ' + p.id + '}\n数列の一般項 $a_n$ を求めよ。$n\\geq 1$ とする。\n';
  text += math(p.statement.initials_tex.join(',\\quad '));
  text += math(p.statement.recurrence_tex);
  if (includeAnswer) {
    text += '\\section*{解答}\n' + p.routes[0].title + '\n';
    for (const step of p.routes[0].steps) text += '\n' + step + '\n';
    text += math(p.answer_tex);
    for (const route of p.routes.slice(1)) {
      text += '\\subsection*{別解：' + route.title + '}\n';
      for (const step of route.steps) text += '\n' + step + '\n';
    }
  }
  return text + '\\end{document}\n';
}
