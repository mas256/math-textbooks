"""Basic logarithmic recurrences and exponential forcing, with forward routes."""
from fractions import Fraction
from math import comb

from expr import add, div, evaluate, geometric_sum, index, latex, mul, nat, nat_const, num, power, sub, term
from rules import RuleViolation, normalize_recipe

FAMILIES = {'logarithmic', 'shifted_logarithmic', 'exponential_forcing'}
SHAPES = {'power_first', 'exponential_first'}


def power_rhs(coefficient, degree, offset):
    """Expand in a_n so shifted exercises require finding the substitution."""
    terms = [num(offset)]
    for j in range(degree + 1):
        factor = coefficient * comb(degree, j) * (-offset) ** (degree - j)
        if factor:
            monomial = num(1) if j == 0 else term() if j == 1 else power(term(), nat_const(j))
            terms.append(mul(num(factor), monomial))
    return add(*terms)


def power_formula(first, coefficient, degree, offset):
    result = num(1) if first == 1 else power(num(first), power(nat_const(degree), nat()))
    if coefficient != 1:
        result = mul(result, power(num(coefficient), geometric_sum(degree, nat())))
    return add(num(offset), result)


def exponential_formula(first, ratio, base, coefficient):
    pr, qr = power(num(ratio), nat()), power(num(base), nat())
    if ratio == base:
        return mul(add(num(first), mul(num(coefficient / ratio), nat())), pr)
    return add(mul(num(first), pr), mul(num(coefficient / (ratio-base)), sub(pr, qr)))


def recipe(family, parameters, profile, config):
    r, c, d, s = (Fraction(parameters[k]) for k in ('r', 'c', 'd', 's'))
    if family == 'exponential_forcing':
        if profile not in {'distinct', 'resonant'}:
            raise RuleViolation('unregistered_exponential_profile')
        if (r == s) != (profile == 'resonant'):
            raise RuleViolation('exponential_profile_mismatch')
        block = dict(kind='exponential_force', ratio=num(r), base=num(s), coefficient=num(c))
    else:
        if profile not in {'square', 'cube'} or r != (2 if profile == 'square' else 3):
            raise RuleViolation('unregistered_power_degree')
        block = dict(kind='power_first_encode', degree=nat_const(int(r)),
                     coefficient=num(c), shift=num(s if family == 'shifted_logarithmic' else 0))
    block.update(id='b1', input='core')
    return normalize_recipe(dict(schema_version='0.2', rule_set_version=config['version'],
        domain=dict(index_start=1, sequence_type='rational'),
        core=dict(id='core', kind='constant', parameters=dict(initial=num(d))),
        blocks=[block], output='b1'), config)


def compile_elementary(recipe):
    assert recipe['domain'] == dict(index_start=1, sequence_type='rational')
    assert recipe['core']['kind'] == 'constant' and len(recipe['blocks']) == 1
    first = evaluate(recipe['core']['parameters']['initial'], 0)
    block = recipe['blocks'][0]
    ir = dict(P=num(1), Q=num(1), R=num(0), reciprocal=False, second_order=False, lhs=term(1))
    if block['kind'] == 'power_first_encode':
        if first <= 0:
            raise RuleViolation('nonpositive_logarithm_input')
        coefficient, offset = [evaluate(block[k], 0) for k in ('coefficient', 'shift')]
        degree = block['degree']['value']
        formula = power_formula(first, coefficient, degree, offset)
        rhs = power_rhs(coefficient, degree, offset)
        ir.update(shape='power_first', power_coefficient=block['coefficient'],
                  power_degree=block['degree'], power_shift=block['shift'], initials=[num(first+offset)])
    else:
        ratio, base, coefficient = [evaluate(block[k], 0) for k in ('ratio', 'base', 'coefficient')]
        formula = exponential_formula(first, ratio, base, coefficient)
        forcing = mul(num(coefficient), power(num(base), nat()))
        rhs = add(mul(num(ratio), term()), forcing)
        ir.update(shape='exponential_first', Q=num(ratio), R=forcing,
                  forcing_base=num(base), forcing_coefficient=num(coefficient), initials=[num(first)])
    ir.update(formula=formula, rhs=rhs, step=rhs, underlying=formula)
    return ir


def elementary_routes(ir):
    """Use only visible coefficients/initials, never formula or Recipe data."""
    first = evaluate(ir['initials'][0], 0)
    L = latex
    M = lambda text: r'\(' + text + r'\)'
    if ir['lhs'] != term(1):
        return []
    if ir['shape'] == 'power_first':
        coefficient, offset = [evaluate(ir[k], 0) for k in ('power_coefficient', 'power_shift')]
        degree = ir['power_degree']['value']
        if degree not in {2, 3} or coefficient <= 0 or first <= offset:
            return []
        if ir['rhs'] != power_rhs(coefficient, degree, offset):
            return []
        initial = first-offset
        formula = power_formula(initial, coefficient, degree, offset)
        uformula = power_formula(initial, coefficient, degree, 0)
        transform = sub(term(), num(offset))
        shifted = bool(offset)
        u = 'u' if shifted else 'a'
        relation = u + r'_{n+1}=' + L(mul(num(coefficient), power(term(variable=u), nat_const(degree))))
        steps = []
        if shifted:
            steps.append('右辺をまとめると '+M(L(sub(term(1),num(offset)))+'='+L(mul(num(coefficient),power(sub(term(),num(offset)),nat_const(degree)))))
                         +' となる。'+M('u_n='+L(transform))+' とおく。')
        steps.append(M(u+'_1='+L(num(initial)))+' は正で、'+M(relation)
                     +' から帰納的に全項が正となる。したがって '+M(r'b_n=\log '+u+'_n')+' とおける。')
        logarithmic_step = str(degree)+'b_n' + (r'+\log '+L(num(coefficient)) if coefficient != 1 else '')
        steps.append('対数をとると '+M('b_{n+1}='+logarithmic_step)
                     +'、'+M(r'b_1=\log '+L(num(initial)))+' である。')
        g = geometric_sum(degree, nat())
        if coefficient == 1:
            steps.append('対数をとった数列は等比数列なので、'+M('b_n='+L(power(num(degree),nat()))+r'\log '+L(num(initial)))+'。')
        else:
            fixed_term = r'\log '+L(num(coefficient)) if degree == 2 else r'\frac{\log '+L(num(coefficient))+'}{'+str(degree-1)+'}'
            steps.append('定数項を消すため '+M('c_n=b_n+'+fixed_term)
                         +' とおくと '+M('c_{n+1}='+str(degree)+'c_n')+' となる。初期値を代入して戻せば、')
            initial_term = L(power(num(degree),nat()))+r'\log '+L(num(initial))+'+' if initial != 1 else ''
            steps.append(M('b_n='+initial_term+r'\left('+L(g)+r'\right)\log '+L(num(coefficient)))+' を得る。')
        steps.append('指数の形に戻すと '+M(u+'_n='+L(uformula))+'。'
                     + (M('a_n=u_n+'+L(num(offset)))+' に戻して一般項を得る。' if shifted else 'これが求める一般項である。'))
        certificate = dict(kind='power-first-log', coefficient=num(coefficient), degree=nat_const(degree),
                           shift=num(offset), ratio=num(degree))
        derivation = [dict(kind='power-first', variable=u, formula=uformula, initials=[num(initial)],
                           coefficient=num(coefficient), degree=nat_const(degree), source='a', transform=transform)]
        operations = (['shift'] if shifted else []) + ['logarithm'] + (['fixed_point'] if coefficient != 1 else []) + ['geometric']
        title = '平行移動してから対数をとる' if shifted else '対数をとって一次の漸化式に直す'
        hint = '平方完成や因数分解で同じ量の累乗を作り、その正値性を確かめて対数をとる。' if shifted else '各項の正値性を確かめ、対数をとって累乗を定数倍に変える。'
        values, discovery, domain = [initial, coefficient, degree, offset], 2 if shifted else 1, 1
    else:
        ratio, base, coefficient = [evaluate(ir[k], 0) for k in ('Q','forcing_base','forcing_coefficient')]
        if ratio <= 0 or base <= 1 or coefficient == 0:
            return []
        forcing = mul(num(coefficient), power(num(base), nat()))
        if ir['rhs'] != add(mul(num(ratio), term()), forcing) or ir['R'] != forcing:
            return []
        formula = exponential_formula(first, ratio, base, coefficient)
        bformula = mul(formula, power(num(1/base), nat()))
        r, q = ratio/base, coefficient/base
        normalized = 'b_{n+1}='+L(mul(num(r),term(variable='b')))+'+'+L(num(q))
        steps = ['付加項の指数に合わせて '+M(r'b_n=\frac{a_n}{'+L(power(num(base),nat()))+'}')+' とおく。倍率は正なので、すべての添字で割ることができる。',
                 '両辺を '+M(L(power(num(base),nat(1))))+' で割ると '+M(normalized)+'、'+M('b_1='+L(num(first)))+' となる。']
        if ratio == base:
            steps.append('倍率が一致するため '+M('b_{n+1}-b_n='+L(num(q)))+'。等差数列の一般項から '+M('b_n='+L(add(num(first),mul(num(q),nat()))))+' を得る。')
        else:
            fixed = q/(1-r)
            steps.append('定数解は '+M('b='+L(num(fixed)))+' である。'+M(r'c_n=b_n-\left('+L(num(fixed))+r'\right)')
                         +' とおくと '+M('c_{n+1}='+L(mul(num(r),term(variable='c'))))+'。')
            steps.append('初項を合わせて '+M('b_n='+L(add(num(fixed),mul(num(first-fixed),power(num(r),nat())))))+' を得る。')
        steps.append(M('a_n='+L(power(num(base),nat()))+'b_n')+' に戻し、指数を整理すると '+M('a_n='+L(formula))+' である。')
        certificate = dict(kind='exponential-normalization', ratio=num(ratio), base=num(base),
                           coefficient=num(coefficient), resonant=ratio==base)
        derivation = [dict(variable='b', formula=bformula, P=num(1), Q=num(r), R=num(q), initials=[num(first)],
                           source='a', transform=div(term(),power(num(base),nat())))]
        operations = ['index_scale'] + (['difference_sum'] if ratio == base else ['fixed_point','geometric'])
        title, hint = '指数で割って定数項に直す', '付加項の指数部分で割り、正規化後の倍率が1になるか確認する。'
        values, discovery, domain = [ratio, base, coefficient, first], 1, 1
    return [dict(title=title, operations=operations, hint=hint, steps=steps, formula=formula,
                 discovery=discovery, domain=domain, intermediate_values=[num(v) for v in values],
                 certificate=certificate, derivation=derivation, complete=True)]


def check_power_derivation(ir, route, k):
    trace = route['derivation'][0]
    f = trace['formula']
    current, following = evaluate(f,k), evaluate(f,k+1)
    assert current > 0
    assert following == evaluate(trace['coefficient'],0)*current**trace['degree']['value']
    assert current == evaluate(trace['transform'],k,{0:evaluate(ir['formula'],k)})
    if k == 0: assert current == evaluate(trace['initials'][0],0)


def evaluate_mod(expr, k, modulus, terms=None):
    op = expr['op']
    if op == 'rational': return expr['num']*pow(expr['den'],-1,modulus)%modulus
    if op in {'index','nat_index','nat_constant','geometric_sum'}: return int(evaluate(expr,k))%modulus
    if op == 'term': return terms[expr['offset']]
    args = expr['args']
    if op == 'pow': return pow(evaluate_mod(args[0],k,modulus,terms),int(evaluate(args[1],k)),modulus)
    xs = [evaluate_mod(x,k,modulus,terms) for x in args]
    if op == 'add': return sum(xs)%modulus
    if op == 'mul':
        result=1
        for x in xs: result=result*x%modulus
        return result
    if op == 'div': return xs[0]*pow(xs[1],-1,modulus)%modulus
    raise ValueError(op)


def validate_power_modular(problem, count=24):
    ir = problem['ir']
    for modulus in (1000000007, 1000000009, 998244353):
        value = evaluate_mod(ir['initials'][0],0,modulus)
        for k in range(count):
            assert value == evaluate_mod(ir['formula'],k,modulus)
            for route in problem['routes']:
                assert value == evaluate_mod(route['formula'],k,modulus)
            value = evaluate_mod(ir['rhs'],k,modulus,{0:value})
    return count*3
