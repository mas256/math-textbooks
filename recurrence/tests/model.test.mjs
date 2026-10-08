import test from 'node:test';
import assert from 'node:assert/strict';
import { poolFor, chooseProblem, validateBank, texDocument } from '../model.mjs';

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
    answer_tex:'a_n=2^{n-1}',routes:[{title:'等比',steps:['公比は2です。']}]};
  assert.ok(!texDocument(q).includes('\\section*{解答}'));
  assert.ok(texDocument(q,true).includes(q.answer_tex));
});
