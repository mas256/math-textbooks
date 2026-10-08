"""Regression checks for domain guards, typed composition and score boundaries."""
import json
import sys
import copy
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from compiler import compile_blocks
from expr import add, evaluate, latex, mul, num, index, power, nat, nat_const, sub, term
from generate import compile_recipe, identity_key, validate
from profiles import EXPONENTS, SCALES, scale_options
from rules import RuleViolation, load_config, normalize_recipe
from scoring import assess, numeric_cost, level, score_routes
from solve import check_derivation, find_routes
from identity import assign_ids, fingerprint, load_registry

assert [level(x) for x in [3,4,7,8,12,13,18,19,25,26]] == [1,2,2,3,3,4,4,5,5,None]
assert [numeric_cost(x) for x in [Fraction(1,2),Fraction(25,8),Fraction(1,7),Fraction(7,11),Fraction(49,64)]] == [0,0,1,3,4]
bank=json.loads((Path(__file__).resolve().parents[1]/'build/candidates.json').read_text())
config=load_config()
for p in bank['problems']:
    assert compile_blocks(p['recipe']) == p['ir']
    validate(p)
    assert p['routes'][0]['difficulty_cost'] == min(r['difficulty_cost'] for r in p['routes'])
    assert p['routes'][0]['parts']['U'] == 0
    assert p['scores']['level'] == level(p['scores']['difficulty'])
    assert all('+-' not in step for route in p['routes'] for step in route['steps'])
    assert all('--' not in step for route in p['routes'] for step in route['steps'])
    assert p['quality']['accepted']
    assert p['quality']['metrics']['coefficient_degree']<=2
    assert all(count<=config['max_transforms'][kind] for kind,count in p['generation']['transform_counts'].items())
    # The forward solver still succeeds after removing construction/formula data.
    hidden={'formula','b_formula','sum_formula','underlying','exponent_profile','sum_base','power_exponent'}
    if p['ir'].get('shape')=='weighted_sum': hidden.update({'p','q'})
    stripped={k:v for k,v in p['ir'].items() if k not in hidden}
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

# Regression for a published ambiguity: 3 times 2^sum must not read as 32^sum,
# and the entire additive increment belongs inside the summation.
power_example=compile_recipe('ratio_power',{'r':2,'c':1,'d':3,'s':3},'square_minus_one')
step=power_example['routes'][0]['steps'][0]
assert r'3\cdot 2^{' in step and r'\left(2\,j+1\right)' in step
assert r'3\cdot 2^{' in power_example['answer_tex']
assert latex({'op':'choose','args':[nat_const(3),nat_const(2)]})==r'\binom{3}{2}'
assert r'\frac{' in latex(EXPONENTS['tetrahedral']['increment'])
unit_base=compile_recipe('ratio_power',{'r':1,'c':1,'d':3,'s':3},'triangular')
assert all('logarithm' not in route['operations'] for route in unit_base['routes'])
assert unit_base['routes'][0]['operations']==['constant']

# Intermediate errors must be caught even while the final formula stays correct.
particular=compile_recipe('polynomial_forcing',{'r':2,'c':1,'d':3,'s':3})
tampered=copy.deepcopy(particular['routes'][0])
tampered['derivation'][0]['R']=add(tampered['derivation'][0]['R'],num(1))
try: check_derivation(particular['ir'],tampered,0)
except AssertionError: pass
else: raise AssertionError('incorrect intermediate recurrence accepted')
# A non-unit leading coefficient must be divided out in the explanation too.
nonunit={**particular['ir'],'P':num(2),'Q':num(4),'R':mul(num(2),index())}
routes=find_routes(nonunit,config)
assert routes and all('2(An+B)+n' in s for r in routes if r['certificate']['kind']=='linear-particular' for s in r['steps'] if 'A(n+1)' in s)
negative_forcing=compile_blocks(recipe([{'kind':'index_add','value':index()},
                                       {'kind':'reciprocal','requires':'positive_input'}]))
for route in find_routes(negative_forcing,config):
    assert not any('付加項も正' in step for step in route['steps'])
    for n in range(24): check_derivation(negative_forcing,route,n)

registry=load_registry()
known={e['fingerprint']:e['id'] for e in registry['entries']}
previous=json.loads((Path(__file__).resolve().parents[1]/'reference/quality-v0.2.json').read_text())
for p in previous['problems']: assert known[fingerprint(p['ir'])]==p['id']
recent=json.loads((Path(__file__).resolve().parents[1]/'reference/quality-v0.3.json').read_text())
for p in recent['problems']: assert known[fingerprint(p['ir'])]==p['id']
for p in bank['problems']:
    assert known[fingerprint(p['ir'])]==p['id']
    assert fingerprint(json.loads(json.dumps(p['ir'],sort_keys=True)))==fingerprint(p['ir'])
unknown=compile_recipe('constant',{'r':2,'c':1,'d':999,'s':3})
protected=copy.deepcopy(registry)
try: assign_ids([unknown],protected)
except RuntimeError: pass
else: raise AssertionError('unknown problem silently published with a reused ID')
assert protected==registry
assert assign_ids([unknown],protected,True)==1
assert unknown['id']==f"p{registry['next_id']:03}"
assert assign_ids([unknown],protected)==0

diversity=bank['comparison']['diversity']
assert diversity['before']['count']==len(recent['problems'])==70
assert diversity['after']['count']==len(bank['problems'])
assert diversity['after']['coefficient_patterns']>=diversity['before']['coefficient_patterns']
for family in ['scaled_affine','reciprocal_scaled','ratio_power']:
    distribution=diversity['after']['families'][family]['parameters']
    assert len(distribution)==2 and max(distribution.values())-min(distribution.values())<=1
for lv,limits in config['difficulty_mix'].items():
    mix=bank['comparison']['level_diversity']['after'][lv]
    assert len(mix['nonfraction_families'])>=limits['min_nonfraction_families']
    assert mix['fraction_count']*100<=mix['count']*limits['max_fraction_percent']

# Mixed sums need the first boundary; the two roots alone are insufficient.
summed=compile_recipe('weighted_sum',{'r':2,'c':1,'d':1,'s':3},'distinct:identity')
validate(summed)
assert summed['ir']['initials']==[num(1)]
assert evaluate(summed['ir']['formula'],1)==4
bad_boundary=copy.deepcopy(summed)
bad_boundary['ir']['formula']=add(power(num(2),nat()),power(num(3),nat()))
try: validate(bad_boundary)
except AssertionError: pass
else: raise AssertionError('arbitrary two-root combination passed the sum boundary')
lifted=compile_recipe('difference_scaled',{'r':2,'c':1,'d':1,'s':3},'n')
validate(lifted)
wrong_difference=copy.deepcopy(lifted['routes'][0])
wrong_difference['derivation'][0]['transform']=sub(term(1),mul(num(2),term()))
try: check_derivation(lifted['ir'],wrong_difference,0)
except AssertionError: pass
else: raise AssertionError('incorrect adjacent difference accepted')
log_second=compile_recipe('multiplicative_second',{'r':2,'c':1,'d':1,'s':3},'n')
validate(log_second)
assert latex(log_second['ir']['power_increment'])=='n'
assert '2^{n}' in log_second['statement']['recurrence_tex']
assert all(evaluate(log_second['ir']['formula'],n)>0 for n in range(24))
try: compile_recipe('multiplicative_second',{'r':2,'c':1,'d':Fraction(1,2),'s':3},'n')
except RuleViolation as e: assert str(e)=='unregistered_natural_exponent'
else: raise AssertionError('nonintegral registered exponent accepted')
scaled_three=compile_recipe('scaled_second_order',{'r':2,'c':1,'d':1,'s':3},'inverse:n')
assert r'n\,a_{n}' in ' '.join(scaled_three['routes'][0]['steps'])
validate(scaled_three)
assert square['routes'][0]['operations'][-1]=='evaluate_sum'
cube=compile_recipe('ratio_power',{'r':2,'c':1,'d':1,'s':3},'tetrahedral')
assert cube['routes'][0]['operations'][-1]=='evaluate_quadratic_sum'
print('Checks passed: recipe replay, forward routes, intermediate relations, notation, domain guards, balanced selection and all historical public IDs.')

# Educational levels are independent of initial-value arithmetic and TeX length.
for family,profile in [('scaled_second_order','inverse:n'),('scaled_second_order','inverse:consecutive')]:
    variants=[compile_recipe(family,{'r':2,'c':c,'d':d,'s':3},profile) for c,d in [(1,1),(3,9),(6,8)]]
    assert {p['scores']['level'] for p in variants}=={3}
assert not any(p['family']=='constant' for p in bank['problems'])
assert all(any(evaluate(p['ir']['formula'],k)!=evaluate(p['ir']['formula'],0) for k in range(1,8)) for p in bank['problems'])
for shape in ['system','pure_sum','sum_relation']:
    assert any(p['ir'].get('shape')==shape for p in bank['problems']),shape
for level in [3,4]:
    assert any(p['ir'].get('shape')=='system' and p['scores']['level']==level for p in bank['problems'])
    assert any(p['ir'].get('shape') in {'pure_sum','sum_relation','weighted_sum'} and p['scores']['level']==level for p in bank['problems'])
print('New checks passed: nonconstant outputs, stable educational levels, paired modes and distinct summation shapes.')
