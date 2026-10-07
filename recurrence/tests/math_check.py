"""Regression checks for domain guards, typed composition and score boundaries."""
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from compiler import compile_blocks
from expr import evaluate, num
from generate import compile_recipe, validate
from scoring import numeric_cost, level

assert [level(x) for x in [3,4,7,8,12,13,18,19,25,26]] == [1,2,2,3,3,4,4,5,5,None]
assert [numeric_cost(x) for x in [Fraction(1,2),Fraction(25,8),Fraction(1,7),Fraction(7,11),Fraction(49,64)]] == [0,0,1,3,4]
bank=json.loads((Path(__file__).resolve().parents[1]/'build/candidates.json').read_text())
for p in bank['problems']:
    assert compile_blocks(p['recipe']) == p['ir']
    validate(p)
    assert p['routes'][0]['cost'] == min(r['cost'] for r in p['routes'])
    assert p['routes'][0]['parts']['U'] == 0
    assert p['scores']['level'] == level(p['scores']['difficulty'])
    assert all('+-' not in step for route in p['routes'] for step in route['steps'])
bad=dict(bank['problems'][0]['recipe'])
bad['output']='unregistered'
try: compile_blocks(bad)
except AssertionError: pass
else: raise AssertionError('dangling output accepted')
print('Recipe replay, domain samples, route selection and score boundaries passed.')
