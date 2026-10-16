"""Check the mathematical calculations added to the worked explanations."""
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from detailed_exposition import affine_steps, sum_steps
from expr import add, evaluate, index, mul, nat_const, num, power
from algebra import prefix_polynomial


# Both signs, fractions, constant sequences, and the resonant ratio 1 matter.
for first in (Fraction(-3), Fraction(1,2), Fraction(4)):
    for ratio in (Fraction(-2), Fraction(-1), Fraction(0), Fraction(1,2), Fraction(1), Fraction(3)):
        for forcing in (Fraction(-2), Fraction(0), Fraction(3,2)):
            steps, formula = affine_steps(first, ratio, forcing)
            value = first
            for k in range(12):
                assert evaluate(formula,k) == value
                value = ratio*value+forcing

# The displayed standard sums must equal the actual prefix sum, including n=1.
for degree in range(4):
    forcing = add(mul(num(Fraction(-3,2)),power(index(),nat_const(degree))),num(2))
    for first in (Fraction(-1), Fraction(2,3)):
        sum_steps(forcing,first)
        formula=prefix_polynomial(forcing,first)
        for k in range(12):
            assert evaluate(formula,k)==first+sum(evaluate(forcing,j) for j in range(k))

bank=json.loads((ROOT/'build/candidates.json').read_text())
kinds=set()
for p in bank['problems']:
    for route in p['routes']:
        kinds.add(route['certificate']['kind'])
        assert route['steps']
        for step in route['steps']:
            assert isinstance(step,str)
            assert step.count(r'\(')==step.count(r'\)'),(p['id'],step)
            assert 'None' not in step and '+-' not in step and '--' not in step,(p['id'],step)
            for math in re.findall(r'\\\((.*?)\\\)',step,re.S):
                # A misplaced delimiter must not put Japanese prose inside math.
                assert not re.search(r'[ぁ-んァ-ン一-龯]',math),(p['id'],math)
                braces=0
                for token in re.findall(r'\\.|[{}]',math):
                    if token=='{': braces+=1
                    elif token=='}': braces-=1
                    assert braces>=0,(p['id'],math)
                assert braces==0,(p['id'],math)
assert {'power-first-log','exponential-normalization','polynomial-difference',
        'difference-normalization','log-second-difference','paired-modes',
        'mobius-shift','factorial-product','forced-second','arithmetic-difference'} <= kinds

authored=json.loads((ROOT/'authored/level6.json').read_text())
assert len(authored['problems'])==60
# Independent hand-worked arithmetic examples used in the expanded prose.
a=Fraction(2)
for expected in (Fraction(3,2),Fraction(5,8),Fraction(-39,128)):
    a=(a*a-1)/2
    assert a==expected
a=[1]
for n in range(8):a.append(a[-1]+a[n//2])
assert a==[1,2,3,5,7,10,13,18,23]
assert 2026==2*3**6+2*3**5+3**4+1
print(f'Explanation checks passed: affine cases, power sums, {len(kinds)} route kinds, math delimiters and worked arithmetic.')
