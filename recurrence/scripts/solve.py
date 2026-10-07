"""Recognize registered, complete routes from coefficients and initials only.

This is a bounded forward solver, not a search over every mathematical method.
It never reads Recipe, the family label, or the generated closed formula.
Polynomial identities are checked exactly before a route is offered.
"""
import re
from fractions import Fraction
from itertools import combinations
from math import isqrt

from expr import add, div, evaluate, expand_polynomial, index, latex, mul, nat, neg, num, poly_mul, polynomial, power, reciprocal, shift, sub, term
from profiles import EXPONENTS, scale_options


def p_add(a, b, multiplier=1):
    out = dict(a)
    for d,c in b.items(): out[d] = out.get(d, 0) + multiplier*c
    return {d:c for d,c in out.items() if c}


def proportional(a, b):
    if not b: return None
    d = max(b)
    ratio = a.get(d, 0) / b[d]
    return ratio if a == {d:c*ratio for d,c in b.items() if c*ratio} else None


def shift_and_force(A, B, C):
    """Solve A + h B = q C for the scalar shift h and forcing q."""
    q = proportional(A, C)
    if q is not None: return Fraction(0), q
    degrees = sorted(A.keys() | B.keys() | C.keys())
    for i,j in combinations(degrees, 2):
        ai,aj = A.get(i,0), A.get(j,0)
        bi,bj = B.get(i,0), B.get(j,0)
        ci,cj = C.get(i,0), C.get(j,0)
        determinant = bj*ci-bi*cj
        if not determinant: continue
        h = (ai*cj-aj*ci)/determinant
        q = (bj*ai-bi*aj)/determinant
        if p_add(A, B, h) == {d:c*q for d,c in C.items() if c*q}:
            return h,q
        return None
    return None


def signed(value):
    tex = latex(num(value))
    return tex if tex.startswith('-') else '+' + tex


def linear_tex(ir, variable):
    return (latex(mul(ir['P'], term(1))) + '=' +
            latex(add(mul(ir['Q'],term()),ir['R']))).replace('a_{', variable + '_{')


def finish(ir, title, operations, hint, steps, formula, discovery, values, certificate):
    if ir['reciprocal']:
        operations = ['reciprocal'] + operations
        steps = [rf"\(v_n=\frac{{1}}{{a_n}}\) とおくと、\({linear_tex(ir, 'v')}\) です。"] + steps
        steps.append('置換を戻します。各項と元の漸化式の分母が0にならないことも確認します。')
        title = '逆数をとり、' + title
        hint = 'まず逆数をとり、得られる漸化式の係数と付加項を比較します。'
        formula = reciprocal(formula)
        discovery += 1
    return {'title':title, 'operations':operations, 'hint':hint, 'steps':steps,
            'formula':formula, 'discovery':discovery, 'domain':int(ir['reciprocal']),
            'intermediate_values':[num(x) for x in values],
            'certificate':certificate, 'complete':True}


def normalized_route(ir, g, name, r, q, h, initial):
    variable = 'v' if ir['reciprocal'] else 'a'
    b1 = (initial-h)/evaluate(g,0)
    normalized = name != 'identity'
    operations, steps = [], []
    if h: operations.append('shift')
    if normalized: operations.append('index_scale')
    if normalized or h:
        transform = latex(div(sub(term(),num(h)),g)) if normalized else latex(sub(term(),num(h)))
        transform = transform.replace('a_{',variable+'_{')
        steps.append(rf"\(b_n={transform}\) とおくと、\(b_{{n+1}}={latex(num(r))}b_n{signed(q) if q else ''}\)、\(b_1={latex(num(b1))}\) です。")
    else:
        steps.append(rf"係数は \({latex(num(r))}\)、付加項は \({latex(num(q))}\) です。")
    values = [h,r,q,b1]
    if r == 1:
        if not q:
            operations.append('constant')
            bformula = num(b1)
            steps.append(rf"変形後の数列は一定なので、\(b_n={latex(num(b1))}\) です。" if normalized or h else 'すべての項が初項に等しくなります。')
            title = '係数の比から正規化する' if normalized else '同じ値が続く'
        else:
            operations += ['difference_sum','evaluate_sum']
            bformula = add(num(b1),mul(num(q),sub(index(),num(1))))
            steps.append(rf"差が一定なので、\(b_n={latex(bformula)}\) です。")
            title = '差を足し合わせる'
    else:
        fixed = q/(1-r)
        if q:
            operations.append('fixed_point')
            steps.append(rf"\(x={latex(num(r))}x{signed(q)}\) の解は \({latex(num(fixed))}\) です。\(b_n-{latex(num(fixed))}\) を等比数列として解きます。" if normalized or h else rf"不動点は \({latex(num(fixed))}\) です。\({variable}_n-{latex(num(fixed))}\) が等比数列になります。")
        operations.append('geometric')
        bformula = add(num(fixed),mul(num(b1-fixed),power(num(r),nat())))
        values += [fixed,b1-fixed]
        steps.append(rf"変形後の一般項は \(b_n={latex(bformula)}\) です。" if normalized or h else '初項を用いて等比数列の定数を決めます。')
        title = '係数の比から正規化する' if normalized else '不動点を引いて等比数列にする' if q else '公比を読む'
    formula = add(mul(g,bformula),num(h))
    discovery = (1 if normalized else 0) + int(bool(h)) + int(bool(q and r != 1))
    hint = ('付加項と、左右の係数の差を比較します。' if h else
            '左右の係数を、同じ関数のnとn+1の値として比較します。' if normalized else
            '毎回同じ値になる数を探し、それを引きます。' if q else
            '隣り合う項の関係を読み取ります。')
    certificate = {'kind':'polynomial-normalization','profile':name,
                   'shift':num(h),'ratio':num(r),'forcing':num(q)}
    route = finish(ir,title,operations,hint,steps,formula,discovery,values,certificate)
    routes = [route]
    if normalized and not h and not q:
        factor = latex(div(shift(g),g))
        factor = re.sub(r'(?<![a-zA-Z\\])n(?![a-zA-Z])','j',factor)
        product = rf"\prod_{{j=1}}^{{n-1}}{factor}"
        steps = [rf"隣り合う項の比を掛けると、\({variable}_n={latex(num(initial))}{latex(power(num(r),nat())) if r != 1 else ''}{product}\) です。",
                 rf"途中の因子が消え、積は \({latex(div(g,num(evaluate(g,0))))}\) になります。初項を代入します。"]
        alternate = finish(ir,'積の約分を使う',['ratio_product','evaluate_product'],
                           '倍率の分子と、次の倍率の分母を比較します。',steps,formula,1,values,
                           {'kind':'telescoping-product','profile':name,'ratio':num(r)})
        routes.append(alternate)
    return routes


def polynomial_route(ir, P,Q,R, initial):
    r = proportional(Q,P)
    if r is None or r == 1: return []
    if max(P,default=0) != 0 or max(R,default=0) != 1: return []
    scale = P[0]
    alpha,beta = R.get(1,0)/scale,R.get(0,0)/scale
    A = alpha/(1-r)
    B = (beta-A)/(1-r)
    particular = add(mul(num(A),index()),num(B))
    # The particular solution is accepted only after this exact identity.
    assert polynomial(sub(shift(particular),mul(num(r),particular))) == {d:c/scale for d,c in R.items()}
    amplitude = initial-evaluate(particular,0)
    formula = add(mul(num(amplitude),power(num(r),nat())),particular)
    variable = 'v' if ir['reciprocal'] else 'a'
    transform = latex(add(term(),expand_polynomial(neg(particular)))).replace('a_{',variable+'_{')
    steps = [r"付加項がnの一次式なので、特解を \(u_n=An+B\) とおいて係数を比較します。",
             rf"\(u_{{n+1}}={latex(num(r))}u_n+{latex(ir['R'])}\) を満たす特解は \(u_n={latex(particular)}\) です。",
             rf"\(b_n={transform}\) とおくと、\(b_{{n+1}}={latex(num(r))}b_n\)、\(b_1={latex(num(amplitude))}\) です。等比数列を解いて置換を戻します。"]
    return [finish(ir,'一次式の特解を引く',['polynomial_shift','geometric'],
                   '付加項がnの一次式です。同じ次数の特解を考えます。',steps,formula,2,
                   [r,alpha,beta,A,B,amplitude],{'kind':'linear-particular','particular':particular,'ratio':num(r)})]


def power_routes(ir, config, initial):
    Q=ir['Q']
    if ir['P'] != num(1) or ir['R'] != num(0) or Q['op'] != 'pow': return []
    base,increment = Q['args']
    if base['op'] != 'rational' or evaluate(base,0) <= 0: return []
    for name in config['exponent_profiles']:
        profile=EXPONENTS[name]
        if increment != profile['increment']: continue
        total=profile['total']
        formula=mul(num(initial),power(base,total))
        jtex = re.sub(r'(?<![a-zA-Z\\])n(?![a-zA-Z])','j',latex(increment))
        steps=[rf"倍率を掛け合わせると、\(a_n={latex(num(initial))}{latex(base)}^{{\sum_{{j=1}}^{{n-1}}{jtex}}}\) です。",
               rf"指数の和は \({latex(total)}\) なので、積を評価して一般項を求めます。"]
        main=finish(ir,'比を掛けて指数を足す',['ratio_product','evaluate_product'],
                    '掛けられる数の指数を、1からn−1まで足します。',steps,formula,1,[initial,evaluate(base,0)],
                    {'kind':'exponent-sum','profile':name})
        routes=[main]
        if initial>0:
            steps=[rf"初項と倍率が正なので全項が正です。\(b_n=\log_{{{latex(base)}}}a_n\) とおくと、\(b_{{n+1}}-b_n={latex(increment)}\) です。",
                   rf"差を足し合わせて \(b_n=\log_{{{latex(base)}}}{latex(num(initial))}+{latex(total)}\) とし、指数の形に戻します。"]
            alternate=finish(ir,'対数をとって和にする',['logarithm','difference_sum','evaluate_sum'],
                             '各項の正値性を確認し、対数をとって差の関係にします。',steps,formula,1,
                             [initial,evaluate(base,0)],{'kind':'logarithmic-sum','profile':name})
            alternate['domain']=1
            routes.append(alternate)
        return routes
    return []


def second_routes(ir):
    p,q = evaluate(ir['p'],0),evaluate(ir['q'],0)
    delta=p*p+4*q
    if delta<=0: return []
    u,v=isqrt(delta.numerator),isqrt(delta.denominator)
    if u*u!=delta.numerator or v*v!=delta.denominator: return []
    root=Fraction(u,v)
    r,s=(p+root)/2,(p-root)/2
    first,second=map(lambda x:evaluate(x,0),ir['initials'])
    A=(second-s*first)/(r-s)
    B=first-A
    formula=add(mul(num(A),power(num(r),nat())),mul(num(B),power(num(s),nat())))
    steps=[rf"特性多項式は \(\lambda^2-{latex(num(p))}\lambda{signed(-q)}=(\lambda-{latex(num(r))})(\lambda-{latex(num(s))})\) です。",
           rf"\(a_n=A{latex(num(r))}^{{n-1}}+B{latex(num(s))}^{{n-1}}\) とおき、二つの初期値から \(A={latex(num(A))}\)、\(B={latex(num(B))}\) を求めます。"]
    return [finish(ir,'特性多項式の根を使う',['characteristic_distinct'],
                   '3項間なので、定数係数の特性多項式を作ります。',steps,formula,1,
                   [p,q,r,s,A,B],{'kind':'distinct-roots','roots':[num(r),num(s)]})]


def find_routes(ir, config):
    if ir['second_order']: return second_routes(ir)
    actual_initial=evaluate(ir['initials'][0],0)
    if ir['reciprocal'] and not actual_initial: return []
    initial=1/actual_initial if ir['reciprocal'] else actual_initial
    try:
        P,Q,R = [polynomial(ir[k]) for k in ('P','Q','R')]
    except ValueError:
        return power_routes(ir,config,initial)
    routes=[]
    candidates=[('identity',num(1)),*scale_options(config)]
    for name,g in candidates:
        G,H=(num(1),g['args'][1]) if g['op']=='div' else (g,num(1))
        pg,ph,pgn,phn=map(polynomial,(G,H,shift(G),shift(H)))
        r=proportional(poly_mul(poly_mul(Q,pg),phn),poly_mul(poly_mul(P,pgn),ph))
        if r is None: continue
        A=poly_mul(R,phn)
        B=poly_mul(p_add(Q,P,-1),phn)
        C=poly_mul(P,pgn)
        match=shift_and_force(A,B,C)
        if match is None: continue
        h,q=match
        routes.extend(normalized_route(ir,g,name,r,q,h,initial))
    routes.extend(polynomial_route(ir,P,Q,R,initial))
    return routes
