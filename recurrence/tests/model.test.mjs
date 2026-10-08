import test from 'node:test';
import assert from 'node:assert/strict';
import { poolFor, chooseProblem, validateBank, texDocument, routeComparison } from '../model.mjs';

const p = (id, family, level) => ({id,family,scores:{level}});
const bank = {problems:[p('p001','a',1),p('p002','a',1),p('p003','b',2)]};

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

test('unverified banks and mismatched manifests are rejected', () => {
  assert.throws(()=>validateBank({schema_version:'0.2',problems:[],verification:{status:'pending'}},{status:'lean-verified'}));
});

test('structurally rejected or incomplete problems cannot be served', () => {
  const problem={id:'p001',verification:{status:'lean-verified'},lean_theorems:['p001_unique'],
    scores:{level:2},quality:{accepted:true,version:'0.3.0'},
    routes:[{parts:{U:0},complete:true,certificate:{kind:'polynomial-normalization'}}]};
  const verified={schema_version:'0.2',score_version:'0.3.0',problems:[problem],
    proof_source_sha256:'proof',verification:{status:'lean-verified',commit:'commit'}};
  const manifest={status:'lean-verified',commit:'commit',proof_source_sha256:'proof',count:1};
  assert.equal(validateBank(verified,manifest),verified);
  problem.quality.accepted=false;
  assert.throws(()=>validateBank(verified,manifest));
  problem.quality.accepted=true;
  problem.routes[0].complete=false;
  assert.throws(()=>validateBank(verified,manifest));
  problem.routes[0].complete=true;
  problem.id='p1000'; problem.lean_theorems=['p1000_unique'];
  assert.equal(validateBank(verified,manifest),verified);
});

test('TeX defaults to problem only and adds solutions on request', () => {
  const q={id:'p001',statement:{initials_tex:['a_1=1'],recurrence_tex:'a_{n+1}=2a_n'},
    answer_tex:'a_n=2^{n-1}',routes:[{title:'等比',hint:'係数が一定です。',steps:['公比は2です。']}]};
  assert.ok(!texDocument(q).includes('\\section*{解答}'));
  assert.ok(texDocument(q,true).includes(q.answer_tex));
  assert.ok(texDocument(q,true).includes('着眼点：係数が一定です。'));
});

test('route explanations distinguish strict wins, numerical tie breaks and display ties', () => {
  const main={cost:5,numeric_cost:2,parts:{B:2,R:1,A:2,T:0,P:0,U:0}};
  const other={cost:6,numeric_cost:2,parts:{B:1,R:3,A:2,T:0,P:0,U:0}};
  assert.ok(routeComparison([main]).reason.includes('だけを検出'));
  const strict=routeComparison([main,other]);
  assert.ok(strict.reason.includes('最小'));
  assert.ok(strict.alternatives[0].includes('操作が1点低い、発見が2点高い'));
  other.cost=5; other.numeric_cost=3;
  assert.ok(routeComparison([main,other]).reason.includes('数値のコストが小さい'));
  other.numeric_cost=2;
  assert.ok(routeComparison([main,other]).reason.includes('優劣を表す順序ではありません'));
  other.parts={...main.parts};
  assert.ok(routeComparison([main,other]).alternatives[0].includes('各項目のスコアも同じ'));
});

test('fractional family receives the configured weight and exhausted families disappear', () => {
  const pool=[p('p001','a',4),p('p002','mobius',4)];
  const seen=new Set();
  assert.equal(chooseProblem(pool,seen,()=>0.4,{mobius:2}).family,'mobius');
  assert.equal(chooseProblem(pool,seen,()=>0.9,{mobius:2}).family,'a');
});
