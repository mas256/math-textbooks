"""Regression checks for domain guards, typed composition and score boundaries."""
import json
import sys
import copy
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from compiler import compile_blocks
from expr import add, evaluate, latex, mul, num, index, power
from generate import compile_recipe, identity_key, validate
from profiles import EXPONENTS, SCALES, scale_options
from rules import RuleViolation, load_config, normalize_recipe
from scoring import assess, numeric_cost, level, score_routes
from solve import find_routes

assert [level(x) for x in [3,4,7,8,12,13,18,19,25,26]] == [1,2,2,3,3,4,4,5,5,None]
assert [numeric_cost(x) for x in [Fraction(1,2),Fraction(25,8),Fraction(1,7),Fraction(7,11),Fraction(49,64)]] == [0,0,1,3,4]
bank=json.loads((Path(__file__).resolve().parents[1]/'build/candidates.json').read_text())
config=load_config()
for p in bank['problems']:
    assert compile_blocks(p['recipe']) == p['ir']
    validate(p)
    assert p['routes'][0]['cost'] == min(r['cost'] for r in p['routes'])
    assert p['routes'][0]['parts']['U'] == 0
    assert p['scores']['level'] == level(p['scores']['difficulty'])
    assert all('+-' not in step for route in p['routes'] for step in route['steps'])
    assert p['quality']['accepted']
    assert p['quality']['metrics']['coefficient_degree']<=2
    assert all(count<=config['max_transforms'][kind] for kind,count in p['generation']['transform_counts'].items())
    # The forward solver still succeeds after removing construction/formula data.
    stripped={k:v for k,v in p['ir'].items() if k not in {'formula','underlying','exponent_profile'}}
    routes=score_routes(stripped,find_routes(stripped,config))
    assert routes
    for route in routes:
        assert all(evaluate(route['formula'],n)==evaluate(p['ir']['formula'],n) for n in range(12))
bad=dict(bank['problems'][0]['recipe'])
bad['output']='unregistered'
try: compile_blocks(bad)
except AssertionError: pass
else: raise AssertionError('dangling output accepted')

def recipe(blocks, core=None):
    core=core or {'id':'core','kind':'geometric','parameters':{'ratio':num(2),'amplitude':num(8)}}
    previous=core['id']
    blocks=[copy.deepcopy(b) for b in blocks]
    for i,b in enumerate(blocks,1):
        b.update(id=f'b{i}',input=previous)
        previous=b['id']
    return {'schema_version':'0.2','domain':{'index_start':1,'sequence_type':'rational'},'core':core,'blocks':blocks,'output':previous}

combined=recipe([{'kind':'add_constant','value':num(2)},{'kind':'add_constant','value':num(3)}])
normal=normalize_recipe(combined)
assert len(normal['blocks'])==1 and normal['blocks'][0]['value']==num(5)
assert evaluate(compile_blocks(combined)['formula'],0)==13
separated=recipe([{'kind':'add_constant','value':num(1)},
                  {'kind':'index_scale','factor':SCALES['n']},
                  {'kind':'add_constant','value':num(2)}])
try: compile_blocks(separated)
except RuleViolation as e: assert str(e)=='transform_limit:add_constant'
else: raise AssertionError('separated additions escaped the per-type limit')
relaxed=copy.deepcopy(config)
relaxed['max_transforms']['add_constant']=2
assert evaluate(compile_blocks(separated,relaxed)['formula'],0)==11
unknown=recipe([{'kind':'index_scale','factor':mul(index(),add(index(),num(7)))}])
try: compile_blocks(unknown)
except RuleViolation: pass
else: raise AssertionError('unregistered n profile accepted')
inverse_pair=recipe([{'kind':'reciprocal','requires':'positive_input'}]*2)
try: compile_blocks(inverse_pair)
except RuleViolation: pass
else: raise AssertionError('redundant inverse pair accepted')
zero_core={'id':'core','kind':'constant','parameters':{'initial':num(0)}}
try: compile_blocks(recipe([{'kind':'reciprocal','requires':'positive_input'}],zero_core))
except AssertionError: pass
else: raise AssertionError('inversion of zero accepted')

baseline=json.loads((Path(__file__).resolve().parents[1]/'reference/quality-baseline.json').read_text())
monster=next(p for p in baseline['problems'] if p['family']=='reciprocal_scaled')
assessment=assess(monster['ir'],score_routes(monster['ir'],find_routes(monster['ir'],config)),config)
assert not assessment['accepted'] and 'max_coefficient_degree' in assessment['reasons']
assert assessment['metrics']['coefficient_degree']==4
simple=compile_recipe('shifted_scaled',{'r':2,'c':1,'d':1,'s':3},'gap_2')
assert simple['quality']['accepted']
assert all(evaluate(simple['ir']['formula'],n)==(n+1)*(n+3)-1 for n in range(12))
ugly=compile_recipe('second_order',{'r':2,'c':13,'d':17,'s':3})
assert ugly['routes'][0]['parts']['A']>0
assert any(p['routes'][0]['parts']['P']>0 for p in bank['problems'])
for p in bank['problems']:
    number=int(p['id'][1:])
    if number<=len(baseline['problems']):
        assert identity_key(p['ir'])==identity_key(baseline['problems'][number-1]['ir'])
for name,g in scale_options(config):
    product=1
    for k in range(12):
        assert product==evaluate(g,k)/evaluate(g,0)
        assert evaluate(g,k)>0
        product*=evaluate(g,k+1)/evaluate(g,k)
for profile in EXPONENTS.values():
    total=0
    for k in range(12):
        assert evaluate(profile['total'],k)==total
        total+=evaluate(profile['increment'],k)
square=compile_recipe('ratio_power',{'r':2,'c':1,'d':1,'s':3},'square_minus_one')
assert r'\left(n-1\right)' in square['answer_tex'] and r'\left(n+1\right)' in square['answer_tex']
assert len(bank['problems'])==sum(config['quotas'].values())
assert len(set(p['id'] for p in bank['problems']))==len(bank['problems'])
assert {p['generation']['profile'] for p in bank['problems'] if p['family']=='scaled_constant'}=={name for name,_ in scale_options(config)}
print('Checks passed: recipe replay, forward routes without recipes, policy overrides, profile closure, domain guards, old-example rejection, scoring and stable public IDs.')
