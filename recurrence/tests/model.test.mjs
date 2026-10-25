import test from 'node:test';
import assert from 'node:assert/strict';
import { poolFor, chooseProblem, validateBank, texDocument, routeComparison, textbookText, equashareSource, inlineFormulas } from '../model.mjs';

const p = (id, family, level) => ({id,family,level});
const bank = {problems:[p('p001','a',1),p('p002','a',1),p('p003','b',2)]};

// A bank record as written by the Rust engine's recurrence-bank command.
function generated(overrides = {}) {
  return {id:'0123456789ab', problem_hash:'0123456789ab'.padEnd(64,'0'), level:2, family:'geometric',
    family_label:'等比数列', variant:{id:'geometric/base',label:'等比数列',pattern:'constant_coefficient_first'},
    statement:{shape:'single', instruction:'次の条件で定められる数列について、一般項を求めよ。',
      recurrences_tex:['a_{n+1}=2\\,a_{n}+1'], initials_tex:['a_{1}=1'], range_tex:'n\\ge1'},
    answer_tex:'a_{n}=2^{n}-1',
    routes:[{title:'不動点を引く',hint:'係数が一定です。',steps:['不動点を引く。\n\\[b_{n}=a_{n}+1\\]','公比は2です。'],
      score:5,total_score:5,numeric_cost:2,parts:{B:2,R:1,A:2,T:0,P:0,U:0}}],
    classification:{score:5,numeric_cost:2,reason:'理由',metrics:{nodes:5,fraction_depth:0,coefficient_degree:0,exponent_degree:0}},
    recipe:{core:{kind:'geometric'},blocks:[],seed:'1'},
    finite_check:{recipe_replayed:true,formal_verification:false,checked_terms:20},
    lean:{status:'lean-verified',source:'theorem ...',lean_version:'4.19.0',axioms:['propext']},
    ...overrides};
}

test('difficulty and family filters intersect, including empty combinations', () => {
  assert.deepEqual(poolFor(bank,1,'a').map(p=>p.id),['p001','p002']);
  assert.equal(poolFor(bank,2,'a').length,0);
  assert.equal(poolFor(bank,0,'all').length,3);
});

test('all matching instances appear once before recycling', () => {
  const seen = new Set();
  const ids = Array.from({length:3},()=>chooseProblem(bank.problems,seen,()=>0).id);
  assert.equal(new Set(ids).size,3);
  assert.equal(chooseProblem(bank.problems,seen,()=>0).id,'p001');
  assert.equal(chooseProblem([],seen),null);
});

test('only Lean-verified banks matching their manifest can be served', () => {
  const problem = generated();
  const verified = {schema_version:'bank-1', seed:'7', problems:[problem]};
  const manifest = {schema_version:'bank-1', status:'lean-verified', seed:'7', count:1};
  assert.equal(validateBank(verified,manifest),verified);
  assert.throws(()=>validateBank(verified,{...manifest,status:'pending'}));
  assert.throws(()=>validateBank(verified,{...manifest,count:2}));
  assert.throws(()=>validateBank(verified,{...manifest,seed:'8'}));
  for (const broken of [{lean:{status:'pending',source:''}}, {finite_check:{recipe_replayed:false}},
    {level:6}, {id:'P001'}, {problem_hash:'ffff'}, {routes:[]}, {statement:{...problem.statement,recurrences_tex:[]}}]) {
    assert.throws(()=>validateBank({...verified,problems:[generated(broken)]},manifest), JSON.stringify(broken));
  }
  assert.throws(()=>validateBank({...verified,problems:[problem,problem]},{...manifest,count:2}));
});

test('TeX defaults to problem only and adds solutions on request', () => {
  const q=generated();
  assert.ok(!texDocument(q).includes('\\section*{解答}'));
  assert.ok(texDocument(q).includes('問題 0123456789AB（Lv2）'));
  assert.ok(texDocument(q,true).includes(q.answer_tex));
  assert.ok(texDocument(q,true).includes('\\documentclass[dvipdfmx,a4paper,11pt,fleqn,openany]{jsbook}'));
  assert.ok(texDocument(q,true).includes('\\begin{multicols*}{2}'));
  assert.ok(!texDocument(q,true).includes('スコア'));
  // Display equations in explanations stay mathematics, not escaped prose.
  assert.ok(texDocument(q,true).includes('\\[\\fitmath{b_{n}=a_{n}+1}\\]'));
  assert.ok(!texDocument(q,true).includes('\\textbackslash{}['));
  assert.ok(texDocument({...q,statement:{...q.statement,shape:'positive'}}).includes('正の数列'));
  assert.ok(texDocument({...q,statement:{...q.statement,shape:'system'}}).includes('それぞれ求めよ'));
  assert.equal(textbookText('\\(a_n=2^{n-1}\\) です。'), '\\(a_n=2^{n-1}\\) である。');
  assert.equal(textbookText('\\[x です。\\] です。'), '\\[x です。\\] である。');
  assert.ok(texDocument(q,true).includes('係数が一定である。'));
});

test('route explanations distinguish strict wins, numerical tie breaks and display ties', () => {
  const main={score:5,total_score:5,numeric_cost:2,parts:{B:2,R:1,A:2,T:0,P:0,U:0}};
  const other={score:5,total_score:6,numeric_cost:2,parts:{B:1,R:3,A:2,T:0,P:0,U:0}};
  assert.ok(routeComparison([main]).reason.includes('だけを検出'));
  const strict=routeComparison([main,other]);
  assert.ok(strict.reason.includes('最小'));
  assert.ok(strict.alternatives[0].includes('操作が1点低い、発見が2点高い'));
  other.total_score=5; other.numeric_cost=3;
  assert.ok(routeComparison([main,other]).reason.includes('数値のコストが小さい'));
  other.numeric_cost=2;
  assert.ok(routeComparison([main,other]).reason.includes('優劣を表す順序ではありません'));
  other.parts={...main.parts};
  assert.ok(routeComparison([main,other]).alternatives[0].includes('各項目のスコアも同じ'));
  const harder={...other,score:9};
  assert.ok(routeComparison([main,harder]).reason.includes('教育上の難易度スコアが最小（5）'));
});

test('Equashare gets problem-only formulas one per line, without document TeX or math delimiters', () => {
  const q=generated();
  assert.equal(equashareSource(q), String.raw`\text{問題 0123456789AB（Lv2）}
\text{次の条件で定められる数列について、一般項を求めよ。}
a_{1}=1
a_{n+1}=2\,a_{n}+1
n\in\mathbb{Z},\quad n\ge1
`);
  const source=equashareSource(q);
  assert.ok(!source.includes(q.answer_tex));
  assert.ok(!source.includes(q.routes[0].hint));
  assert.doesNotMatch(source, /\\(?:documentclass|usepackage|fitmath|chapter|section)|\\[()[\]]|\$/);
  assert.equal(new URLSearchParams({prefill:source}).get('prefill'),source);
  const system=generated({statement:{shape:'system',instruction:'次の条件で定められる2つの数列について、一般項をそれぞれ求めよ。',
    initials_tex:['a_{1}=1','b_{1}=2'], recurrences_tex:['a_{n+1}=a_{n}+b_{n}','b_{n+1}=a_{n}-b_{n}'], range_tex:'n\\ge1'}});
  assert.ok(equashareSource(system).includes('一般項をそれぞれ求めよ。'));
  assert.ok(equashareSource(system).includes('a_{1}=1,\\quad b_{1}=2\na_{n+1}=a_{n}+b_{n}\nb_{n+1}=a_{n}-b_{n}\n'));
});

test('family weights still bias the choice and exhausted families disappear', () => {
  const pool=[p('p001','a',4),p('p002','mobius',4)];
  const seen=new Set();
  assert.equal(chooseProblem(pool,seen,()=>0.4,{mobius:2}).family,'mobius');
  assert.equal(chooseProblem(pool,seen,()=>0.9,{mobius:2}).family,'a');
});

test('plain-text formulas in engine prose are typeset, and unparsable text is left alone', () => {
  assert.equal(inlineFormulas('a_n=S_n−S_(n−1)で求める。'), '\\(a_{n}=S_{n}-S_{n-1}\\)で求める。');
  assert.equal(inlineFormulas('x_n=x_1^(2^(n−1))'), '\\(x_{n}=x_{1}^{2^{n-1}}\\)');
  assert.equal(inlineFormulas('倍率g_nとg_{n+1}'), '倍率\\(g_{n}\\)と\\(g_{n+1}\\)');
  assert.equal(inlineFormulas('v_1…v_{n−1}'), '\\(v_{1}\\ldots v_{n-1}\\)');
  assert.equal(inlineFormulas('n≥1で正'), 'n≥1で正');
  assert.equal(inlineFormulas('f_(n'), 'f_(n');
  assert.equal(inlineFormulas('H(k)r^(k−1)'), '\\(H(k)r^{k-1}\\)');
  // Formulas already delimited by the engine are not touched again.
  assert.equal(textbookText('\\(a_n\\) です。'), '\\(a_n\\) である。');
  const tex = texDocument(generated({routes:[{...generated().routes[0], steps:['a_n=S_n−S_(n−1)を使う。']}]}), true);
  assert.ok(tex.includes('\\(a_{n}=S_{n}-S_{n-1}\\)を使う。'));
  assert.ok(!tex.includes('\\_'));
});
