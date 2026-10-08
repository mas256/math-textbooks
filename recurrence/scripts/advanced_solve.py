"""Forward recognition of registered multi-step routes, without construction data."""
from fractions import Fraction
from math import isqrt

from algebra import geometric_antidifference, integer_log, natural_polynomial, prefix_polynomial
from expr import add, div, evaluate, index, latex, mul, nat, num, poly_mul, polynomial, power, shift, sub, term
from profiles import scale_options
from solve import coefficient_tex, finish, joined, proportional, relation_tex, second_routes, sequence_trace, sequence_tex, signed


def roots_solution(p,q,first,second,variable='b'):
    delta=p*p+4*q
    if delta<0: return None
    if delta==0:
        r=p/2
        if not r: return None
        slope=second/r-first
        linear=add(num(first),mul(num(slope),sub(index(),num(1))))
        formula=mul(linear,power(num(r),nat()))
        steps=[rf"特性多項式は \((\lambda{signed(-r)})^2\) で、重解 \({latex(num(r))}\) を持ちます。",
               rf"\(c_n=\frac{{{variable}_n}}{{{latex(power(num(r),nat()))}}}\) とおくと、\(c_{{n+2}}-2c_{{n+1}}+c_n=0\) です。",
               rf"したがって \(c_{{n+1}}-c_n={latex(num(slope))}\) は一定です。\(c_1={latex(num(first))}\) より \(c_n={latex(linear)}\)、\({variable}_n={latex(formula)}\) です。"]
        return {'formula':formula,'operations':['characteristic_repeated'],'steps':steps,
                'values':[p,q,r,first,second,slope],'roots':[num(r),num(r)],'repeated':True,
                'extra':[sequence_trace('c',linear,num(1),num(slope),first,variable,div(term(),power(num(r),nat())))]}
    u,v=isqrt(delta.numerator),isqrt(delta.denominator)
    if u*u!=delta.numerator or v*v!=delta.denominator: return None
    root=Fraction(u,v);r,s=(p+root)/2,(p-root)/2
    if not r or not s: return None
    A=(second-s*first)/(r-s);B=first-A
    formula=add(mul(num(A),power(num(r),nat())),mul(num(B),power(num(s),nat())))
    steps=[rf"特性多項式は \((\lambda{signed(-r)})(\lambda{signed(-s)})\) なので、根は \({latex(num(r))},{latex(num(s))}\) です。",
           rf"\({variable}_n=A\cdot {latex(power(num(r),nat()))}+B\cdot {latex(power(num(s),nat()))}\) とおきます。初期値から \(A+B={latex(num(first))}\)、\({joined(coefficient_tex(r,'A'),coefficient_tex(s,'B'))}={latex(num(second))}\) です。",
           rf"\(A={latex(num(A))}\)、\(B={latex(num(B))}\) より \({variable}_n={latex(formula)}\) です。"]
    return {'formula':formula,'operations':['characteristic_distinct'],'steps':steps,
            'values':[p,q,r,s,A,B],'roots':[num(r),num(s)],'repeated':False,'extra':[]}


def normalized_seconds(ir,config):
    P,Q,R=map(polynomial,(ir['P2'],ir['Q2'],ir['R2']))
    a1,a2=[evaluate(x,0) for x in ir['initials']]
    routes=[]
    for name,g in [('identity',num(1)),*scale_options(config)]:
        G,H=(num(1),g['args'][1]) if g['op']=='div' else (g,num(1))
        gn,hn,g1,h1,g2,h2=map(polynomial,(G,H,shift(G),shift(H),shift(G,2),shift(H,2)))
        p=proportional(poly_mul(poly_mul(Q,g1),h2),poly_mul(poly_mul(P,g2),h1))
        q=proportional(poly_mul(poly_mul(R,gn),h2),poly_mul(poly_mul(P,g2),hn))
        if p is None or q is None: continue
        b1,b2=a1/evaluate(g,0),a2/evaluate(g,1)
        root=roots_solution(p,q,b1,b2)
        if root is None: continue
        normalized=name!='identity'
        transform=(mul(g['args'][1],term()) if g['op']=='div' and g['args'][0]==num(1) else div(term(),g)) if normalized else term()
        steps=([rf"\(b_n={latex(transform)}\) とおき、各項の係数をそろえます。"] if normalized else [])
        relation=sequence_tex(term(2),'b')+'='+sequence_tex(add(mul(num(p),term(1)),mul(num(q),term())),'b')
        steps += [rf"\({relation}\)、\(b_1={latex(num(b1))}\)、\(b_2={latex(num(b2))}\) です。",*root['steps']]
        if normalized: steps.append(rf"\(a_n={latex(mul(g,root['formula']))}\) と戻します。")
        derivation=[{'variable':'b','formula':root['formula'],'p':num(p),'q':num(q),'initials':[num(b1),num(b2)],'source':'a','transform':transform},*root['extra']]
        routes.append(finish(ir,'正規化して重解を処理する' if normalized and root['repeated'] else '正規化して特性多項式を使う' if normalized else '重解から階差を一定にする' if root['repeated'] else '特性多項式の根を使う',
            (['index_scale'] if normalized else [])+root['operations'],
            '係数を、同じ関数のn・n+1・n+2の値として比較します。' if normalized else '特性多項式が重解を持つ場合は、根のべきで割って階差を調べます。',
            steps,mul(g,root['formula']),1+int(normalized),root['values']+[b1,b2],
            {'kind':'normalized-second','profile':name,'roots':root['roots']},derivation))
    return routes


def difference_routes(ir,config):
    if polynomial(ir['P2'])!=polynomial(add(ir['Q2'],ir['R2'])): return []
    from solve import find_routes
    a1,a2=[evaluate(x,0) for x in ir['initials']]
    base={'P':ir['P2'],'Q':mul(num(-1),ir['R2']),'R':num(0),'reciprocal':False,'second_order':False,'initials':[num(a2-a1)]}
    candidates=find_routes(base,config);routes=[]
    for source in candidates:
        cert=source['certificate']
        if cert['kind']!='polynomial-normalization' or evaluate(cert['forcing'],0) or evaluate(cert['shift'],0): continue
        r=evaluate(cert['ratio'],0)
        if r==1: continue
        name=cert['profile'];g=num(1) if name=='identity' else dict(scale_options(config))[name]
        if g['op']=='div': continue
        amplitude=(a2-a1)/evaluate(g,0)
        H=geometric_antidifference(mul(num(amplitude),g),r)
        constant=a1-evaluate(H,0)
        formula=add(num(constant),mul(H,power(num(r),nat())))
        bformula=source['formula']
        steps=[r"3つの係数を符号も含めて足すと0です。\(b_n=a_{n+1}-a_n\) とおくと、隣接する項の差でまとめられます。",
               rf"\({sequence_tex(mul(base['P'],term(1)),'b')}={sequence_tex(mul(base['Q'],term()),'b')}\)、\(b_1={latex(num(a2-a1))}\) です。",
               rf"\(c_n=\frac{{b_n}}{{{latex(g)}}}\) とおくと \(c_{{n+1}}={latex(num(r))}c_n\)、\(c_1={latex(num(amplitude))}\) なので、\(b_n={latex(bformula)}\) です。",
               rf"\(H(n)={latex(H)}\) とすると、\({latex(num(r))}H(n+1)-H(n)={latex(mul(num(amplitude),g))}\) です。",
               rf"したがって \(b_n=H(n+1){latex(num(r))}^n-H(n){latex(num(r))}^{{n-1}}\) となり、差を足し合わせると中間項が消えます。",
               rf"\(a_n={latex(num(a1))}+H(n){latex(num(r))}^{{n-1}}-H(1)={latex(formula)}\) です。"]
        derivation=[{'variable':'b','formula':bformula,'P':base['P'],'Q':base['Q'],'R':num(0),'initials':[num(a2-a1)],'source':'a','transform':sub(term(1),term())},
                    sequence_trace('c',mul(num(amplitude),power(num(r),nat())),num(r),num(0),amplitude,'b',div(term(),g))]
        routes.append(finish(ir,'階差を正規化し、和の相殺で戻す',['difference','index_scale','geometric','geometric_sum'],
            '3つの係数の和が0です。隣接する項の差を新しい数列にします。',steps,formula,3,
            [a1,a2,amplitude,r,constant,*polynomial(H).values()],{'kind':'difference-normalization','profile':name,'ratio':num(r)},derivation))
    return routes


def sum_routes(ir):
    g,alpha,beta=ir['sum_scale'],evaluate(ir['sum_alpha'],0),evaluate(ir['sum_beta'],0)
    b1=evaluate(ir['initials'][0],0)/evaluate(g,0);b2=(alpha+beta)*b1
    p,q=alpha+beta+1,-alpha
    root=roots_solution(p,q,b1,b2)
    if root is None: return []
    normalized=g!=num(1)
    steps=[rf"\(b_n=\frac{{a_n}}{{{latex(g)}}}\)、\(T_n=\sum_{{k=1}}^n b_k\) とおきます。" if normalized else r"\(b_n=a_n\)、\(T_n=\sum_{k=1}^n b_k\) とおきます。",
           rf"\(b_{{n+1}}={coefficient_tex(alpha,'b_n')}{coefficient_tex(beta,'T_n') if beta<0 else '+'+coefficient_tex(beta,'T_n')}\) です。\(T_1=b_1\) より \(b_1={latex(num(b1))}\)、\(b_2={latex(num(b2))}\) です。",
           rf"1つ添字を進めた式に \(T_{{n+1}}=T_n+b_{{n+1}}\) を代入し、\(T_n\) を消すと、\({sequence_tex(term(2),'b')}={sequence_tex(add(mul(num(p),term(1)),mul(num(q),term())),'b')}\) です。",
           *root['steps'],rf"\(a_n={latex(mul(g,root['formula']))}\) と戻します。"]
    derivation=[{'variable':'b','formula':root['formula'],'p':num(p),'q':num(q),'initials':[num(b1),num(b2)],'source':'a','transform':div(term(),g)},*root['extra']]
    return [finish(ir,'総和を消去し、重解から階差を作る' if root['repeated'] else '総和を消去して3項間を解く',
        (['index_scale'] if normalized else [])+['eliminate_sum']+root['operations'],
        '総和の各項に合わせて正規化し、隣接する2式から総和を消します。' if normalized else '隣接する2式で、部分和の差が1項になることを使います。',
        steps,mul(g,root['formula']),2+int(normalized),root['values']+[alpha,beta,b1,b2],
        {'kind':'sum-to-second','roots':root['roots'],'profile':latex(g)},derivation)]


def power_second_routes(ir):
    base,forcing=ir['power_base'],ir['power_increment']
    r=evaluate(base,0)
    if r not in {2,3} or max(polynomial(forcing),default=0)>1: return []
    first,second=[integer_log(evaluate(x,0),r) for x in ir['initials']]
    d1=second-first
    difference=prefix_polynomial(forcing,d1)
    exponent=prefix_polynomial(difference,first)
    natural=natural_polynomial(exponent)
    formula=power(base,natural)
    steps=[rf"初期値と係数は正です。漸化式から次項も正なので、\(b_n=\log_{{{latex(base)}}}a_n\) とおけます。",
           rf"対数をとると \(b_{{n+2}}-2b_{{n+1}}+b_n={latex(forcing)}\)、\(b_1={first}\)、\(b_2={second}\) です。",
           rf"\(c_n=b_{{n+1}}-b_n\) とおくと、\(c_{{n+1}}-c_n={latex(forcing)}\)、\(c_1={d1}\) です。",
           rf"階差を足し合わせて \(c_n={latex(difference)}\) を得ます。",
           rf"もう一度差を足し合わせると \(b_n={latex(natural)}\) です。したがって \(a_n={latex(formula)}\) となります。"]
    operations=['logarithm','difference','difference_sum','evaluate_sum','difference_sum',
                'evaluate_quadratic_sum' if max(polynomial(forcing),default=0)==1 else 'evaluate_sum']
    derivation=[{'variable':'b','formula':exponent,'p':num(2),'q':num(-1),'forcing':forcing,'initials':[num(first),num(second)],'source':'a','transform':{'op':'log','args':[base,term()]}},
                sequence_trace('c',difference,num(1),forcing,d1,'b',sub(term(1),term()))]
    route=finish(ir,'対数をとり、階差を2回足し合わせる',operations,
                 '各項の次数がそろっています。対数をとって3項間の差に直します。',steps,formula,2,
                 [r,first,second,d1,*polynomial(forcing).values()],{'kind':'log-second-difference','base':base,'forcing':forcing},derivation)
    route['domain']=1
    return [route]


def advanced_routes(ir,config):
    shape=ir['shape']
    if shape=='weighted_sum': return sum_routes(ir)
    if shape=='power_second': return power_second_routes(ir)
    return normalized_seconds(ir,config)+difference_routes(ir,config)
