"""Measured expression/numeric costs; educational weights remain provisional."""
from fractions import Fraction
from math import isqrt
from expr import evaluate, polynomial

PREFERRED_NUM = {0, 1, 2, 3, 4, 5, 6, 8, 9, 16, 25}
PREFERRED_DEN = {1, 2, 3, 5, 8, 9}
OPERATIONS = {"constant": 1, "geometric": 2, "fixed_point": 2,
              "shift": 2, "index_scale": 3, "reciprocal": 3,
              "characteristic_distinct": 5, "characteristic_repeated": 6,
              "ratio_product": 2, "evaluate_product": 1,
              "logarithm": 3, "difference_sum": 2, "evaluate_sum": 1,
              "polynomial_shift": 4}
OPERATIONS.update(difference=2,eliminate_sum=3,geometric_sum=4,evaluate_quadratic_sum=2)


def component_cost(n, preferred):
    n = abs(n)
    if n in preferred: return 0
    score = 1 if n <= 10 else 2 if n <= 30 else 3 if n <= 100 else 4 if n <= 1000 else min(8, 5 + len(str(n)) - 4)
    powers = {b ** e for b in (2, 3, 5) for e in range(1, 8) if b ** e <= 125}
    if n <= 100 and isqrt(n) ** 2 == n or n in powers: score = max(0, score - 1)
    return score


def numeric_cost(value):
    value = Fraction(value)
    return component_cost(value.numerator, PREFERRED_NUM) + component_cost(value.denominator, PREFERRED_DEN)


def route_score(operations, discovery=0, arithmetic=0, domain=0, expression=0, unfinished=0):
    parts = {"B": sum(OPERATIONS[o] for o in operations), "R": discovery,
             "A": min(6, arithmetic), "T": domain, "P": expression, "U": unfinished}
    return {"operations": operations, "parts": parts, "cost": sum(parts.values())}


def level(cost):
    for lv, top in enumerate((3, 7, 12, 18, 25), 1):
        if cost <= top: return lv
    return None


def walk(expr):
    yield expr
    for arg in expr.get('args',[]): yield from walk(arg)


def fractions_in(expressions):
    return {Fraction(x['num'],x['den']) for expr in expressions for x in walk(expr) if x['op']=='rational'}


def fraction_depth(expr):
    children=max((fraction_depth(x) for x in expr.get('args',[])),default=0)
    return children + int(expr['op']=='div' or expr['op']=='rational' and expr['den']!=1)


def natural_degree(expr):
    op=expr['op']
    if op in {'nat_index','index'}: return 1
    if op=='triangular': return 2
    if op=='choose': return expr['args'][1]['value']
    if op=='add': return max(map(natural_degree,expr['args']),default=0)
    if op=='mul': return sum(map(natural_degree,expr['args']))
    return 0


def expression_metrics(expressions):
    nodes=[x for expr in expressions for x in walk(expr)]
    return {'nodes':len(nodes),
            'fraction_depth':max(map(fraction_depth,expressions),default=0),
            'display_terms':1+sum(max(0,len(x['args'])-1) for x in nodes if x['op']=='add'),
            'exponent_degree':max((natural_degree(x['args'][1]) for x in nodes if x['op']=='pow' and x['args'][1]['op']!='nat_constant'),default=0)}


def statement_metrics(ir):
    result=expression_metrics([ir['lhs'],ir['rhs']])
    degrees=[]
    keys=('P2','Q2','R2') if ir.get('shape')=='linear_second' else ('P','Q','R')
    for key in keys:
        try: degrees.append(max(polynomial(ir[key]),default=0))
        except ValueError: pass
    if ir.get('shape')=='weighted_sum':
        g=ir['sum_scale']
        for factor in g['args'] if g['op']=='div' else [g]:
            degrees.append(max(polynomial(factor),default=0))
    result['coefficient_degree']=max(degrees,default=0)
    return result


def expression_cost(metrics):
    return min(6,(max(0,metrics['nodes']-18)+9)//10+
               max(0,metrics.get('coefficient_degree',0)-1)+
               max(0,metrics['fraction_depth']-1)+max(0,metrics['exponent_degree']-1))


def score_routes(ir, routes):
    metrics=statement_metrics(ir)
    visible=fractions_in([ir['lhs'],ir['rhs'],*ir['initials']])
    for route in routes:
        values=visible|fractions_in(route['intermediate_values'])
        arithmetic=sum(numeric_cost(x) for x in values)
        expression=max(expression_cost(metrics),expression_cost(expression_metrics([route['formula']])))
        route.update(route_score(route['operations'],route['discovery'],arithmetic,
                                 route['domain'],expression))
        route['numeric_cost']=arithmetic
        route['observed_metrics']=metrics
    return sorted(routes,key=lambda r:(r['cost'],r['numeric_cost'],r['title']))


def assess(ir, routes, config):
    metrics=statement_metrics(ir)
    limits=config['quality_limits']
    reasons=[]
    for metric,key in [('coefficient_degree','max_coefficient_degree'),('nodes','max_statement_nodes'),
                       ('fraction_depth','max_fraction_depth'),('display_terms','max_display_terms')]:
        if metrics[metric]>limits[key]: reasons.append(key)
    if not routes:
        reasons.append('no_registered_forward_route')
    else:
        main=routes[0]
        if main['discovery']>limits['max_discovery']: reasons.append('max_discovery')
        if main['numeric_cost']>limits['max_numeric_cost']: reasons.append('max_numeric_cost')
        if level(main['cost']) not in range(1,5): reasons.append('unsupported_level')
        if not main['complete'] or main['parts']['U']: reasons.append('unfinished_route')
        cert=main['certificate']
        if ir['reciprocal'] and cert['kind']=='polynomial-normalization' and cert['profile']!='identity':
            if evaluate(cert['shift'],0) and evaluate(cert['forcing'],0):
                reasons.append('hidden_shift_before_normalization')
    return {'accepted':not reasons,'reasons':reasons,'metrics':metrics,
            'status':'structural-heuristic','version':config['version']}
