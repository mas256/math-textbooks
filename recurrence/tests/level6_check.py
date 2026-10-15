"""Exact, finite mathematical checks of the separate hand-authored Lv6 bank.

These checks are not Lean certificates or proofs of all-index claims. The
worked solutions supply those arguments; this script catches formula errors.
Only the trusted, repository-owned verification expressions are parsed.
"""
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import sys

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from authored_workbook import render

n = sp.Symbol('n', integer=True, nonnegative=True)
m, k, s = sp.symbols('m k s', integer=True, nonnegative=True)
t = sp.Symbol('t', real=True)
x, y, r, c, M, alpha = sp.symbols('x y r c M alpha', real=True)
a = sp.Function('a')
b, A = sp.Function('b'), sp.Function('A')
NAMES = dict(n=n, m=m, k=k, s=s, t=t, x=x, y=y, r=r, c=c, M=M, alpha=alpha, a=a, b=b, A=A)


def parse(text):
    return sp.sympify(text, locals=NAMES)


@lru_cache(maxsize=None)
def reduced(expr):
    # Reduce exact rational multiples of pi explicitly. SymPy may retain very
    # large angles such as 3**7*pi/7 without applying periodicity automatically.
    expr = expr.replace(
        lambda z: z.func in (sp.sin, sp.cos, sp.tan, sp.cot)
                  and (z.args[0] / sp.pi).is_Rational,
        lambda z: z.func(sp.Mod(z.args[0] / sp.pi,
                               1 if z.func in (sp.tan, sp.cot) else 2) * sp.pi))
    expr = sp.expand(expr)
    if expr.has(sp.sin, sp.cos, sp.tan, sp.cot):
        expr = sp.trigsimp(expr, method='fu')
    return sp.simplify(expr)


def assert_zero(expr, context):
    result = reduced(expr)
    if result != 0:
        raise AssertionError(f'{context}: expected zero, got {result}')


def sequence_substitution(expr, index, term, extra=None):
    # Expand finite sums at numeric bounds before substituting closed forms;
    # simplifying binomial/gamma formulas at a symbolic summation index can
    # otherwise introduce removable singularities at the endpoints.
    expr = expr.subs(n, index).doit()
    functions = {a:term, **(extra or {})}
    return expr.xreplace({node: functions[node.func](*node.args) for node in expr.atoms(sp.Function)
                          if node.func in functions}).doit()


def assert_claim(expr, context):
    if expr == sp.true:
        return
    if expr == sp.false:
        raise AssertionError(f'{context}: false claim')
    if isinstance(expr, sp.core.relational.Relational):
        if expr.func == sp.Equality:
            assert_zero(expr.lhs - expr.rhs, context)
            return
        difference = reduced(expr.lhs - expr.rhs)
        result = expr.func(difference, 0)
        if result != sp.true:
            raise AssertionError(f'{context}: cannot establish {result} exactly')
    else:
        assert_zero(expr, context)


def digit_sum(value, base):
    result = 0
    while value:
        value, last = divmod(value, base)
        result += last
    return sp.Integer(result)


def verify_grid(v, params, context):
    formula = parse(v['formula']).subs(params)
    residual = parse(v['residual']).subs(params)
    claims = [parse(claim).subs(params) for claim in v.get('claims', [])]

    @lru_cache(maxsize=None)
    def term(i, j):
        return reduced(formula.subs({n:i,m:j}))

    count = 0
    for index in range(v['samples'] + 1):
        assert_zero(term(index,0)-parse(v['boundaries']['n0']).subs(params).subs(n,index), context+' boundary n,0')
        assert_zero(term(0,index)-parse(v['boundaries']['0m']).subs(params).subs(m,index), context+' boundary 0,m')
        count += 2
    for i in range(v['start'], v['start']+v['samples']):
        for j in range(v['start'], v['start']+v['samples']):
            expressions = [residual, *claims]
            for expr in expressions:
                value = sequence_substitution(expr.subs(m,j), i, None, {A:term})
                assert_claim(value, f'{context} grid ({i},{j})')
                count += 1
    for indices, expected in v.get('special_values', {}).items():
        i,j = map(int,indices.split(','))
        assert_zero(term(i,j)-parse(expected).subs(params), context+' grid value '+indices)
        count += 1
    return count


def verify_problem(p):
    v = p['verification']
    identities = [parse(s) for s in v.get('identities', [])]
    for identity in identities:
        assert_zero(identity, f"{p['id']} algebraic identity")
    count = 0
    for values in v.get('parameter_cases', [{}]):
        params = {NAMES[k]: parse(value) for k, value in values.items()}
        mode = v['mode']
        extra_functions = {}
        if mode == 'grid':
            count += verify_grid(v,params,p['id'])
            continue
        if mode in {'closed_form','system'}:
            formula = parse(v['formula']).subs(params)

            @lru_cache(maxsize=None)
            def term(index):
                return reduced(formula.subs(n, index))

            residual = parse(v['residual']).subs(params)
            if mode == 'system':
                b_formula = parse(v['b_formula']).subs(params)

                @lru_cache(maxsize=None)
                def b_term(index):
                    return reduced(b_formula.subs(n,index))

                extra_functions[b] = b_term
                for index, expected in v['b_initials'].items():
                    assert_zero(b_term(int(index))-parse(expected).subs(params),p['id']+' second initial')
                    count += 1
        elif mode == 'iterate':
            update = parse(v['next']).subs(params)
            first_index = min(map(int, v['initials']))
            terms = {first_index: parse(v['initials'][str(first_index)]).subs(params)}

            def term(index):
                index = int(index)
                if index < first_index:
                    raise AssertionError(f"{p['id']}: invalid index {index}")
                for k in range(max(terms) + 1, index + 1):
                    terms[k] = reduced(update.subs(x, terms[k - 1]))
                return terms[index]

            residual = None
        elif mode == 'recursive':
            order = v['order']
            terms = {int(i):parse(value).subs(params) for i,value in v['initials'].items()}
            assert set(terms) == set(range(order)), p['id']+' incomplete recursive initials'
            step = parse(v['step']).subs(params)

            def term(index):
                assert index.is_Integer if isinstance(index,sp.Basic) else isinstance(index,int)
                index = int(index)
                assert index >= 0, p['id']+' invalid recursive index'
                for target in range(max(terms)+1,index+1):
                    terms[target] = reduced(sequence_substitution(step,target-order,term))
                return terms[index]

            residual = parse(v['residual']).subs(params)
        elif mode == 'digit_sum':
            base = v['base']

            def term(index):
                return digit_sum(int(index), base)

            residual = a(n) - a(sp.floor(n / base)) - n + base * sp.floor(n / base)
        else:
            raise AssertionError(f'Unknown mode: {mode}')

        for index, expected in v['initials'].items():
            assert_zero(term(int(index)) - parse(expected).subs(params), f"{p['id']} initial {index}")
            count += 1
        for index, expected in v.get('special_values', {}).items():
            assert_zero(term(int(index)) - parse(str(expected)).subs(params), f"{p['id']} special value {index}")
            count += 1
        if v.get('generating_function'):
            limit = v['series_terms']
            series = sp.series(parse(v['generating_function']).subs(params),t,0,limit).removeO().expand()
            for index in range(limit):
                assert_zero(series.coeff(t,index)-term(index),p['id']+' generating function coefficient '+str(index))
                count += 1
        if 'odd_prefix_length' in v:
            length = int(parse(v['odd_prefix_length']).subs(params))
            for index in range(length):
                assert term(index)%2 == 1, p['id']+' odd prefix'
                count += 1
            assert term(length)%2 == 0, p['id']+' first even term'
            count += 1
        claims = [parse(s).subs(params) for s in v.get('claims', [])]
        for index in [*range(v['start'], v['start'] + v['samples']), *v.get('additional_indices',[])]:
            if residual is not None:
                assert_zero(sequence_substitution(residual, index, term, extra_functions), f"{p['id']} recurrence n={index}")
                count += 1
            if mode == 'system':
                assert_zero(sequence_substitution(parse(v['b_residual']).subs(params),index,term,extra_functions),p['id']+' second recurrence')
                count += 1
            if index >= v.get('claims_start', v['start']):
                for claim in claims:
                    assert_claim(sequence_substitution(claim, index, term, extra_functions), f"{p['id']} claim n={index}")
                    count += 1
    return count, len(identities)


def validate_structure(bank):
    assert bank['schema_version'] == 1
    assert bank['level'] == 6 and bank['authorship'] == 'hand_authored'
    assert bank['publication_status'] == 'ready_for_practice'
    assert 'not_lean_certified' in bank['verification_status']
    expected = dict(gauss=10, four_term=7, newton=3, symmetric=4, trigonometric=5,
                    nonadjacent=8, other=12, two_dimensional=2, generating_functions=3,
                    number_theory=3, advanced_extensions=3)
    assert Counter(p['category'] for p in bank['problems']) == expected
    assert len({p['id'] for p in bank['problems']}) == sum(expected.values())
    for p in bank['problems']:
        assert p['level'] == 6 and p['authorship'] == 'hand_authored'
        assert p['category'] in expected and p['id'].startswith('L6-')
        assert all(isinstance(p[field], str) and p[field].strip()
                   for field in ['title', 'statement', 'hint', 'answer'])
        assert p['solution'] and all(s.strip() for s in p['solution'])
        assert all(p['source'][field] for field in ['path', 'url', 'location', 'adaptation'])
        assert p['verification']['samples'] > 0
        # Catch accidental broken display-math delimiters in the rendered content.
        for value in [p['statement'], p['hint'], p['answer'], *p['solution']]:
            assert value.count(r'\[') == value.count(r'\]'), p['id']
    for path, content in render(bank).items():
        assert path.read_text(encoding='utf-8') == content, f'Stale document: {path}'


def main():
    bank = json.loads((ROOT / 'authored/level6.json').read_text(encoding='utf-8'))
    validate_structure(bank)
    total = identities = 0
    for p in bank['problems']:
        count, count_identities = verify_problem(p)
        total += count
        identities += count_identities
        print(f"{p['id']}: {count} exact finite checks, {count_identities} symbolic identities", flush=True)
    print(f"PASS: {len(bank['problems'])} authored problems; {total} exact finite checks; "
          f'{identities} symbolic identities. Not Lean-certified.')


if __name__ == '__main__':
    main()
