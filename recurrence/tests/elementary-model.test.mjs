import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {poolFor, chooseProblem, texDocument} from '../model.mjs';

const bank=JSON.parse(fs.readFileSync(new URL('../build/candidates.json',import.meta.url),'utf8'));
const families=['logarithmic','shifted_logarithmic','exponential_forcing'];

test('every generated elementary exercise can be selected once and exported with its solution',()=>{
  for(const family of families) {
    const pool=poolFor(bank,0,family);
    assert.equal(pool.length,12);
    const seen=new Set();
    for(let i=0;i<pool.length;i++) {
      const before=seen.size;
      const p=chooseProblem(pool,seen,()=>0);
      assert.equal(seen.size,before+1);
      assert.equal(p.family,family);
      assert.ok(poolFor(bank,p.scores.level,family).includes(p));
      const problem=texDocument(p);
      const solution=texDocument(p,true);
      assert.ok(problem.includes(p.statement.recurrence_tex));
      assert.ok(solution.includes(p.answer_tex));
      assert.ok(!problem.includes(p.routes[0].hint));
      assert.ok(solution.includes(p.routes[0].hint));
      for(const text of [problem,solution]) {
        assert.ok(!text.includes('undefined'));
        assert.ok(!/[\x00-\x08\x0b-\x1f]/.test(text));
      }
    }
    assert.equal(seen.size,12);
  }
});

test('the exponential forcing family includes the two teaching levels',()=>{
  assert.equal(poolFor(bank,2,'exponential_forcing').length,6);
  assert.equal(poolFor(bank,3,'exponential_forcing').length,6);
  assert.equal(poolFor(bank,3,'logarithmic').length,12);
  assert.equal(poolFor(bank,4,'shifted_logarithmic').length,12);
});
