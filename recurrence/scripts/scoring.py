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
OPERATIONS.update(difference=2,eliminate_sum=3,geometric_sum=4,evaluate_quadratic_sum=2,split_pair=2,recover_pair=2,recover_sum=2)


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
    if ir.get('shape')=='system':
        other=expression_metrics([ir['b_lhs'],ir['b_rhs']])
        result={key:max(value,other[key]) for key,value in result.items()}
    degrees=[]
    keys=('P2','Q2','R2') if ir.get('shape')=='linear_second' or ir.get('shape')=='pure_sum' and ir['second_order'] else ('P','Q','R')
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



def educational_cost(ir,route):
    """Calibrate the minimum complete route by its mathematical structure.

    B/R/T remain auditable operation counts. This separate teaching scale is
    independent of coefficient magnitude and display length.
    """
    shape=ir.get('shape');cert=route['certificate'];kind=cert['kind']
    base=route['parts']['B']+route['parts']['R']+route['parts']['T']
    def result(cost,reason):return cost,reason
    if shape=='mobius':return result(14,'シンプルな1次分数を不動点・逆数で解く')
    if shape=='factorial_ratio':
        offsets=cert['offsets']
        if all(t==0 for t in offsets):return result(6,'単項式の階比を総積で処理する')
        if len(offsets)==1:return result(9,'単項式以外の階比を総積で処理する')
        return result(14,'複数の因子をもつ階比を総積で処理する')
    if kind=='arithmetic-difference':return result(14,'階差を等差数列として解き、和で戻す')
    if kind=='forced-second':return result(14,'定数項を消して3項間漸化式を解く')
    if shape=='system':
        degree=max(polynomial(ir['system_forcing']),default=0)
        if degree>0:return result(20,'連立の分離と一次式の特解を組み合わせる')
        if ir['system_scale']!=num_one():return result(14,'正規化してから連立を分離する')
        return result(9,'連立を和・差や一次結合で分離する')
    if shape=='pure_sum':
        if ir['second_order']:return result(20,'部分和の正規化と3項間と差を組み合わせる')
        return result(6,'部分和を求める、または差で総和を消す')
    if shape=='sum_relation':return result(6,'隣接する式の差で総和を消す')
    if shape=='weighted_sum':
        if ir['sum_scale']!=num_one():return result(20,'重みをそろえ、総和を消し、3項間を解く')
        repeated=route['certificate']['roots'][0]==route['certificate']['roots'][1]
        return result(10 if repeated else 7,'総和を消して重解を処理する' if repeated else '総和を消して基本的な3項間に帰着する')
    if shape=='power_second':return result(20,'対数と二重の階差を組み合わせる')
    if kind=='difference-normalization':return result(20,'階差・階比・多項式と等比の和を組み合わせる')
    if ir['reciprocal']:
        if max(polynomial(ir['P']),default=0)==0 and max(polynomial(ir['Q']),default=0)==0 and max(polynomial(ir['R']),default=0)==0:
            return result(14,'定数係数の1次分数を逆数に帰着させる')
        return result(max(20,base),'逆数と変数係数・特解を組み合わせる')
    if ir.get('exponent_profile'):
        degree=natural_degree(ir['Q']['args'][1])
        return result(14 if degree>=2 else 9,'指数係数の階比で指数の和を計算する')
    if kind=='telescoping-product':
        from profiles import SCALES
        profile=cert['profile'].removeprefix('inverse:')
        mono=len(polynomial(SCALES[profile]))==1
        return result(6 if mono else 9,'単項式の倍率の階比を相殺する' if mono else '単項式以外の倍率の階比を相殺する')
    if kind=='polynomial-normalization' and cert['profile']!='identity':
        profile=cert['profile'].removeprefix('inverse:')
        from profiles import SCALES
        mono=len(polynomial(SCALES[profile]))==1
        ratio=evaluate(cert['ratio'],0);forcing=evaluate(cert['forcing'],0);shift=evaluate(cert['shift'],0)
        if forcing:return result(14,'階比の正規化と定数項の消去を組み合わせる')
        if ratio==1 and not shift:return result(6 if mono else 9,'単項式の倍率で正規化する' if mono else '単項式以外の倍率で正規化する')
        return result(10 if mono else 14,'階比の正規化と等比・定数移動を組み合わせる')
    if shape=='linear_second' or ir['second_order']:
        return result(14 if 'index_scale' in route['operations'] else 9,'正規化して3項間を解く' if 'index_scale' in route['operations'] else '基本的な3項間を解く')
    return result(base,'必要な操作・発見・条件確認による評価')


def num_one():
    return {'op':'rational','num':1,'den':1}

def score_routes(ir, routes):
    metrics=statement_metrics(ir)
    visible=fractions_in([ir['lhs'],ir['rhs'],*ir['initials']])
    for route in routes:
        values=visible|fractions_in(route['intermediate_values'])
        arithmetic=sum(numeric_cost(x) for x in values)
        expression=max(expression_cost(metrics),expression_cost(expression_metrics([route['formula']])))
        route.update(route_score(route['operations'],route['discovery'],arithmetic,
                                 route['domain'],expression))
        route['raw_difficulty_cost']=route['parts']['B']+route['parts']['R']+route['parts']['T']
        route['difficulty_cost'],route['difficulty_rule']=educational_cost(ir,route)
        route['difficulty_adjustment']=route['difficulty_cost']-route['raw_difficulty_cost']
        route['numeric_cost']=arithmetic
        route['observed_metrics']=metrics
    return sorted(routes,key=lambda r:(r['difficulty_cost'],r['cost'],r['numeric_cost'],r['title']))


def assess(ir, routes, config):
    metrics=statement_metrics(ir)
    limits=config['quality_limits']
    reasons=[]
    if all(evaluate(ir['formula'],k)==evaluate(ir['formula'],0) for k in range(8)):
        reasons.append('constant_output_sequence')
    for metric,key in [('coefficient_degree','max_coefficient_degree'),('nodes','max_statement_nodes'),
                       ('fraction_depth','max_fraction_depth'),('display_terms','max_display_terms')]:
        if metrics[metric]>limits[key]: reasons.append(key)
    if not routes:
        reasons.append('no_registered_forward_route')
    else:
        main=routes[0]
        if main['discovery']>limits['max_discovery']: reasons.append('max_discovery')
        if main['numeric_cost']>limits['max_numeric_cost']: reasons.append('max_numeric_cost')
        if level(main['difficulty_cost']) not in range(1,6): reasons.append('unsupported_level')
        if not main['complete'] or main['parts']['U']: reasons.append('unfinished_route')
        cert=main['certificate']
        if ir['reciprocal'] and cert['kind']=='polynomial-normalization' and cert['profile']!='identity':
            if evaluate(cert['shift'],0) and evaluate(cert['forcing'],0):
                reasons.append('hidden_shift_before_normalization')
    return {'accepted':not reasons,'reasons':reasons,'metrics':metrics,
            'status':'structural-heuristic','version':config['version']}
