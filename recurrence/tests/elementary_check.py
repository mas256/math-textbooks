"""Regression examples for elementary types missing from the original bank."""
import copy
from fractions import Fraction
import json
from pathlib import Path
import sys
from collections import Counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from compiler import compile_blocks
from elementary import evaluate_mod, validate_power_modular
from expr import add, evaluate, geometric_sum, latex, mul, nat, nat_const, num, power, term
from generate import compile_recipe, validate
from rules import RuleViolation, load_config
from scoring import score_routes
from solve import check_derivation, find_routes


def example(family, r, c, d, s, profile):
    return compile_recipe(family, dict(r=r,c=c,d=d,s=s), profile)


# Textbook examples: a_{n+1}=2a_n^2; completion of the square;
# exponential forcing with equal and unequal characteristic multipliers.
log = example('logarithmic', 2, 2, 2, 0, 'square')
shifted = example('shifted_logarithmic', 2, 1, 4, 1, 'square')
distinct = example('exponential_forcing', 3, 2, 1, 2, 'distinct')
resonant = example('exponential_forcing', 2, 2, 1, 2, 'resonant')
assert log['ir']['rhs'] == mul(num(2),power(term(),nat_const(2)))
for k in range(8):
    assert evaluate(log['ir']['formula'],k) == Fraction(2)**(2**(k+1)-1)
    assert evaluate(shifted['ir']['formula'],k) == Fraction(2)**(2**(k+1))+1
    assert evaluate(distinct['ir']['formula'],k) == 3*3**k-2*2**k
    assert evaluate(resonant['ir']['formula'],k) == (k+1)*2**k
assert [p['scores']['level'] for p in (log,shifted,distinct,resonant)] == [3,4,3,2]

# q=3, a decreasing sequence, and a negative shift exercise the other domains.
variants = [log,shifted,distinct,resonant,
    example('logarithmic',3,3,Fraction(1,2),0,'cube'),
    example('shifted_logarithmic',3,2,Fraction(1,2),-1,'cube')]
for p in variants:
    validate(p)
    assert compile_blocks(p['recipe']) == p['ir']
    hidden = {k:v for k,v in p['ir'].items() if k not in {'formula','underlying'}}
    routes = score_routes(hidden,find_routes(hidden,load_config()))
    assert routes
    for route in routes:
        for k in range(8):
            assert evaluate(route['formula'],k) == evaluate(p['ir']['formula'],k)
    bad = copy.deepcopy(hidden)
    bad['rhs'] = add(bad['rhs'],num(1))
    assert not find_routes(bad,load_config()), 'inconsistent coefficient metadata accepted'
    for route in p['routes']:
        for text in [route['hint'],*route['steps']]:
            assert not any(ord(ch)<32 and ch not in '\n\t' for ch in text), repr(text)
            assert '+-' not in text and '--' not in text

for first in (0,-1):
    try:
        example('logarithmic',2,1,first,0,'square')
    except RuleViolation as error:
        assert str(error) == 'nonpositive_logarithm_input'
    else:
        raise AssertionError('invalid logarithm domain accepted')
for degree in (0,1,4,Fraction(3,2)):
    try:
        example('logarithmic',degree,2,2,0,'square')
    except RuleViolation:
        pass
    else:
        raise AssertionError('unregistered degree accepted')
for coefficient in (0,-1):
    try:
        example('logarithmic',2,coefficient,2,0,'square')
    except RuleViolation:
        pass
    else:
        raise AssertionError('nonpositive multiplier accepted')

# An incorrect intermediate substitution or closed form must fail, even when
# its coefficient metadata and final recurrence have not been altered.
bad = copy.deepcopy(shifted['routes'][0])
bad['derivation'][0]['transform'] = term()
try:
    check_derivation(shifted['ir'],bad,0)
except AssertionError:
    pass
else:
    raise AssertionError('incorrect logarithmic substitution accepted')
bad = copy.deepcopy(log)
bad['ir']['formula'] = add(bad['ir']['formula'],num(1))
try:
    validate_power_modular(bad)
except AssertionError:
    pass
else:
    raise AssertionError('modular checks accepted a corrupted formula')

# New natural exponent nodes share exact arithmetic, TeX and Lean semantics.
for q in (2,3):
    g = geometric_sum(q,nat())
    for k in range(12):
        assert evaluate(g,k) == sum(q**j for j in range(k))
    assert r'\sum' not in latex(g), 'the displayed geometric sum must be evaluated'
for k in range(6):
    for modulus in (1000000007,1000000009,998244353):
        exact = evaluate(log['ir']['formula'],k)
        assert evaluate_mod(log['ir']['formula'],k,modulus) == exact.numerator*pow(exact.denominator,-1,modulus)%modulus

bank = json.loads((ROOT/'build/candidates.json').read_text())
for family, profiles in [('logarithmic',{'square','cube'}),
                         ('shifted_logarithmic',{'square','cube'}),
                         ('exponential_forcing',{'distinct','resonant'})]:
    selected = [p for p in bank['problems'] if p['family']==family]
    assert len(selected)==12
    assert {p['generation']['profile'] for p in selected}==profiles
    assert Counter(p['generation']['profile'] for p in selected)=={profile:6 for profile in profiles}
    assert all(p['quality']['accepted'] for p in selected)
print('Elementary checks passed: textbook examples, both powers and forcing cases, domain guards, hidden-formula recognition and tamper detection.')
