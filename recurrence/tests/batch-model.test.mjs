import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {BATCH_COUNTS, chooseBatch, batchFromIds, problemLevel, validateAuthoredBank,
  validateBank, mathTextParts, batchTexDocument, poolFor, texDocument, equashareSource} from '../model.mjs';

// Candidates exercise selection/export only; this does not certify them.
const bank = JSON.parse(fs.readFileSync(new URL('../build/candidates.json', import.meta.url), 'utf8'));
const authored = JSON.parse(fs.readFileSync(new URL('../authored/level6.json', import.meta.url), 'utf8'));
const counts = problems => Object.fromEntries(Object.keys(BATCH_COUNTS)
  .map(level => [level, problems.filter(p => problemLevel(p) === Number(level)).length]));
function seededRandom(seed = 42) {
  return () => ((seed = (1664525 * seed + 1013904223) >>> 0) / 2 ** 32);
}

test('level six and all-level practice include fixed problems and respect category filters', () => {
  assert.deepEqual(poolFor(bank, 6, 'all', authored), authored.problems);
  assert.equal(poolFor(bank, 0, 'all', authored).length, bank.problems.length + authored.problems.length);
  for (const category of authored.categories) {
    const pool = poolFor(bank, 6, 'authored:' + category.id, authored);
    assert.ok(pool.length > 0);
    assert.ok(pool.every(p => p.level === 6 && p.category === category.id));
    assert.equal(poolFor(bank, 1, 'authored:' + category.id, authored).length, 0);
  }
  assert.equal(poolFor(bank, 6, 'geometric', authored).length, 0);
});

test('all fixed questions can be exported singly with original index ranges and optional solutions', () => {
  for (const p of authored.problems) {
    const question = texDocument(p), solution = texDocument(p, true);
    assert.ok(question.includes('（Lv6）'));
    assert.ok(!question.includes('以下、\\,$n$は正の整数とする'));
    assert.ok(!question.includes('方針・解答・解法'));
    assert.ok(solution.includes('方針・解答・解法'));
    for (const part of mathTextParts(p.statement).filter(part => part.type !== 'text')) {
      assert.ok(question.includes(part.text));
    }
    for (const part of mathTextParts(p.answer).filter(part => part.type !== 'text')) {
      assert.ok(solution.includes(part.text));
    }
  }
});

test('fixed questions keep their original mathematics and index ranges in Equashare', () => {
  for (const p of authored.problems) {
    const source = equashareSource(p);
    assert.ok(source.startsWith('\\text{問題 ' + p.id + '（Lv6）}'));
    assert.doesNotMatch(source, /\\(?:documentclass|usepackage|fitmath|chapter|section)|(?<!\\)\\[()[\]]|\$/);
    for (const part of mathTextParts(p.statement).filter(part => part.type !== 'text')) {
      assert.ok(source.includes(part.text.replace(/\s*\n\s*/g, ' ')), p.id);
    }
    assert.ok(!source.includes('n\\in\\mathbb{Z},\\quad n\\ge1'), 'do not impose n>=1 on fixed questions');
  }
  const sample = {...authored.problems[0], statement:'条件 $a_0=1$ とする。', hint:'秘密のヒント', answer:'秘密の解答'};
  assert.ok(!equashareSource(sample).includes('秘密'));
});

test('every batch has the requested 2/2/3/3/2/2 distribution, ordered and without duplicates', () => {
  const history = new Map(), random = seededRandom();
  const before = JSON.stringify({bank, authored});
  for (let i = 0; i < 500; i++) {
    const selected = chooseBatch(bank, authored, history, random);
    assert.equal(selected.length, 14);
    assert.equal(new Set(selected.map(p => p.id)).size, 14);
    assert.deepEqual(counts(selected), BATCH_COUNTS);
    assert.deepEqual(selected.map(problemLevel), [1,1,2,2,3,3,3,4,4,4,5,5,6,6]);
    for (const p of selected) assert.ok((p.level === 6 ? authored : bank).problems.includes(p));
  }
  assert.equal(JSON.stringify({bank, authored}), before, 'fixed questions and certification metadata must not change');
});

test('each level completes its own cycle before repeating, including across batch boundaries', () => {
  const history = new Map(), cycles = new Map(), random = seededRandom(123);
  const poolSize = level => level === 6 ? authored.problems.length
    : bank.problems.filter(p => problemLevel(p) === level).length;
  for (let i = 0; i < 100; i++) {
    for (const p of chooseBatch(bank, authored, history, random)) {
      const level = problemLevel(p);
      let seen = cycles.get(level) ?? new Set();
      if (seen.size === poolSize(level)) seen = new Set();
      assert.ok(!seen.has(p.id), `premature repeat at level ${level}: ${p.id}`);
      seen.add(p.id); cycles.set(level, seen);
    }
  }
});

test('pools exactly the batch size can be recycled without duplicates in a worksheet', () => {
  const tiny = {problems:bank.problems.filter((p, i, all) =>
    all.slice(0, i).filter(q => problemLevel(q) === problemLevel(p)).length < BATCH_COUNTS[problemLevel(p)])};
  const fixed = {...authored, problems:authored.problems.slice(0, 2)};
  const history = new Map();
  for (let i = 0; i < 3; i++) {
    const selected = chooseBatch(tiny, fixed, history, () => 0);
    assert.equal(new Set(selected.map(p => p.id)).size, 14);
    assert.deepEqual(counts(selected), BATCH_COUNTS);
  }
});

test('an incomplete level rejects the whole batch without advancing any history', () => {
  const history = new Map([[1, new Set(['existing'])]]);
  const snapshot = [...history].map(([level, seen]) => [level, [...seen]]);
  assert.throws(() => chooseBatch(bank, {...authored, problems:[]}, history), /難易度6/);
  assert.deepEqual([...history].map(([level, seen]) => [level, [...seen]]), snapshot);
});

test('fixed bank validation preserves its separate verification status and rejects broken questions', () => {
  assert.equal(validateAuthoredBank(authored), authored);
  assert.throws(() => validateBank(authored, {status:'lean-verified'}));
  for (const change of [p => {p.solution = [];}, p => {p.category = 'missing';},
    p => {p.level = 5;}, p => {p.source.url = 'javascript:alert(1)';}]) {
    const invalid = structuredClone(authored);
    change(invalid.problems[0]);
    assert.throws(() => validateAuthoredBank(invalid));
  }
  const duplicate = structuredClone(authored);
  duplicate.problems[1].id = duplicate.problems[0].id;
  assert.throws(() => validateAuthoredBank(duplicate));
});

test('shared batches preserve question order and reject missing, duplicate or wrongly allocated IDs', () => {
  const selected = chooseBatch(bank, authored, new Map(), () => 0);
  const ids = selected.map(p => p.id);
  assert.deepEqual(batchFromIds(bank, authored, ids), selected);
  assert.throws(() => batchFromIds(bank, authored, ids.slice(1)));
  assert.throws(() => batchFromIds(bank, authored, ['missing', ...ids.slice(1)]));
  assert.throws(() => batchFromIds(bank, authored, [ids[1], ...ids.slice(1)]));
  const anotherFixed = authored.problems.find(p => !ids.includes(p.id));
  assert.throws(() => batchFromIds(bank, authored, [anotherFixed.id, ...ids.slice(1)]));
});

test('math tokens preserve inline and display mathematics and keep prose as text', () => {
  assert.deepEqual(mathTextParts(String.raw`条件 $a_0=1$ と \(x>0\)。\[a_n=2^n\]`), [
    {type:'text', text:'条件 '}, {type:'inline', text:'a_0=1'}, {type:'text', text:' と '},
    {type:'inline', text:'x>0'}, {type:'text', text:'。'}, {type:'display', text:'a_n=2^n'},
  ]);
  assert.deepEqual(mathTextParts('<script>alert(1)</script>'), [{type:'text', text:'<script>alert(1)</script>'}]);
  for (const p of authored.problems) {
    for (const text of [p.statement, p.hint, p.answer, ...p.solution]) {
      const plain = mathTextParts(text).filter(part => part.type === 'text').map(part => part.text).join('');
      assert.ok(!plain.includes('$') && !plain.includes('\\[') && !plain.includes('\\]'), p.id);
    }
  }
});

test('batch TeX has one preamble, all 14 questions, and optional worked solutions for every fixed problem', () => {
  const base = chooseBatch(bank, authored, new Map(), () => 0);
  // Cover all 60 fixed questions, including n=0, multi-part tasks, and piecewise formulas.
  for (let i = 0; i < authored.problems.length; i += 2) {
    const selected = [...base.slice(0, 12), ...authored.problems.slice(i, i + 2)];
    const question = batchTexDocument(selected), solution = batchTexDocument(selected, true);
    for (const tex of [question, solution]) {
      assert.equal((tex.match(/\\documentclass/g) ?? []).length, 1);
      assert.equal((tex.match(/\\begin\{document\}/g) ?? []).length, 1);
      assert.equal((tex.match(/\\end\{document\}/g) ?? []).length, 1);
      assert.ok(!tex.includes('undefined') && !/[\x00-\x08\x0b-\x1f]/.test(tex));
      assert.equal((tex.match(/\\begin\{multicols\*\}/g) ?? []).length,
        (tex.match(/\\end\{multicols\*\}/g) ?? []).length);
    }
    assert.equal((question.match(/\\section\*\{問題 /g) ?? []).length, 14);
    assert.equal((solution.match(/\\section\*\{問題 /g) ?? []).length, 28);
    assert.ok(!question.includes('方針・解答・解法'));
    assert.ok(solution.includes('方針・解答・解法'));
    for (const p of selected) {
      if (p.level !== 6) { assert.ok(solution.includes(p.answer_tex)); continue; }
      for (const field of [p.statement, p.hint, p.answer, ...p.solution]) {
        for (const part of mathTextParts(field).filter(part => part.type !== 'text')) {
          assert.ok(solution.includes(part.text), `${p.id}: missing math ${part.text}`);
        }
      }
    }
  }
});
