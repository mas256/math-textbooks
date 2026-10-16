"""Textbook-style exposition shared by the web, TeX exports and workbook.

The numerical data come from the independently recognized route certificate.
"""
from fractions import Fraction
from expr import add, sub, mul, div, num, term, nat, index, power, evaluate, latex, polynomial, expand_polynomial
from profiles import SCALES, EXPONENTS
from solve import signed, coefficient_tex, sequence_tex, relation_tex


def M(tex): return r'\('+tex+r'\)'
def L(e): return latex(e)
def N(x): return L(num(x))
def C(value,symbol):
    return ('+' if value>=0 else '')+coefficient_tex(value,symbol)

def E(tex): return M(r'\begin{aligned}'+tex+r'\end{aligned}')


def second_exposition(p,q,first,second,roots,variable='a'):
    from detailed_exposition import second_steps
    return second_steps(p,q,first,second,roots,variable)


def scalar_exposition(ir,route,variable='a'):
    from detailed_exposition import scalar_steps
    steps = scalar_steps(ir,route,variable)
    return steps if steps is not None else route['steps']


def explain_route(ir,route):
    from detailed_exposition import detailed_route
    return detailed_route(ir,route,_explain_route)


def _explain_route(ir,route):
    cert=route['certificate'];kind=cert['kind']
    if kind=='paired-modes':
        g=cert['scale'];t=evaluate(cert['weight'],0);u,v=cert['u'],cert['v']
        route['title']='和と差で連立を分離する' if t==1 and g==num(1) else '正規化して連立を分離する' if g!=num(1) else '一次結合で連立を分離する'
        route['hint']='2式の係数が対応している。和と差を作り、独立した漸化式に分ける。' if t==1 else '係数の対応を見て、a_nとb_nの一次結合を作る。'
        a1=evaluate(ir['initials'][0],0)/evaluate(g,0);b1=evaluate(ir['b_initial'],0)/evaluate(g,0)
        steps=[]
        if g!=num(1): steps.append(M('x_n='+r'\frac{a_n}{'+L(g)+'}'+r',\quad y_n=\frac{b_n}{'+L(g)+'}')+' とおくと、両式の係数が定数になり、連立漸化式が簡単になる。')
        a,b=('x','y') if g!=num(1) else ('a','b')
        steps.append('2式を '+('加減する' if t==1 else '係数をそろえて加減する')+'ため、'+M('u_n='+a+'_n'+C(t,b+'_n'))+'、'+M('v_n='+a+'_n'+C(-t,b+'_n'))+' とおく。')
        r=evaluate(u['certificate']['ratio'],0);s=evaluate(v['certificate']['ratio'],0)
        steps.append('与式をそれぞれ加減すると、'+E('u_{n+1}&='+coefficient_tex(r,'u_n')+'+'+L(ir['system_forcing'])+r'\\v_{n+1}&='+coefficient_tex(s,'v_n'))+' となる。また、初期条件は '+M('u_1='+N(a1+t*b1)+r',\quad v_1='+N(a1-t*b1))+' である。')
        scalar={'P':num(1),'Q':num(r),'R':ir['system_forcing'],'initials':[num(a1+t*b1)]}
        steps+=scalar_exposition(scalar,u,'u')
        steps.append('一方、'+M('v_{n+1}=v_n')+' より '+M('v_n='+L(v['formula']))+' である。' if s==1 else '一方、'+M(r'\{v_n\}')+' は初項 '+M(N(a1-t*b1))+'、公比 '+M(N(s))+' の等比数列なので '+M('v_n='+L(v['formula']))+' である。')
        steps.append('ここで '+E(a+'_n&='+r'\frac{u_n+v_n}{2}'+r'\\'+b+'_n&='+r'\frac{u_n-v_n}{'+N(2*t)+'}'))
        if g!=num(1): steps.append(M('a_n='+L(mul(g,term(variable='x')))+r',\quad b_n='+L(mul(g,term(variable='y'))))+' に戻すと、両数列の一般項が得られる。')
        return steps
    if kind=='pure-sum-difference':
        route['title']='部分和の漸化式の差をとる';route['hint']='部分和の隣接する2式を引くと、a_nの漸化式が得られる。初項と第2項は別に確認する。'
        R=cert['scalar_ir']['R'];r=evaluate(ir['Q'],0)
        steps=['まず '+M('a_1=S_1='+N(evaluate(ir['initials'][0],0)))+' である。また、'+M('S_2='+N(evaluate(ir['Q'],0))+'S_1+'+N(evaluate(ir['R'],0)))+' より '+M('a_2=S_2-S_1='+N(evaluate(cert['a2'],0)))+' を得る。',
            M(r'n\ge2')+' において、部分和の漸化式から添字を1つ戻した式を引く。'+M('S_{n+1}-S_n=a_{n+1}')+' を用いると '+M('a_{n+1}='+coefficient_tex(r,'a_n')+'+'+L(R))+' となる。']
        steps+=scalar_exposition(cert['scalar_ir'],cert['scalar'])
        steps.append('この式は、別に求めた '+M('a_1')+' と '+M('a_2')+' にも一致する。したがって、すべての '+M(r'n\ge1')+' に対する一般項となる。')
        return steps
    if kind=='pure-partial-sum':
        scalar=cert['scalar'];g=cert['scale'];S=cert['sum_formula']
        route['title']='部分和を求めてから各項に戻す';route['hint']='S_nだけの漸化式なので、まず部分和を数列として解き、隣接差からa_nを求める。'
        steps=['与式は部分和 '+M(r'S_n=\sum_{k=1}^n a_k')+' だけの漸化式である。まず '+M(r'\{S_n\}')+' の一般項を求める。']
        if cert.get('second_order'):
            tmp={**ir,'shape':'linear_second','formula':S}
            steps+= [s.replace('a_{','S_{').replace('a_n','S_n') for s in explain_route(tmp,scalar)]
        else:
            if g!=num(1): steps.append(M('T_n='+r'\frac{S_n}{'+L(g)+'}')+' とおき、係数をそろえる。')
            var='T' if g!=num(1) else 'S'
            first=evaluate(ir['initials'][0],0)/evaluate(g,0)
            tmp={'P':num(1),'Q':scalar['certificate']['ratio'],'R':num(0),'initials':[num(first)]}
            if scalar['certificate']['kind']=='linear-particular': tmp['R']=expand_polynomial(sub(shift_expr(scalar['certificate']['particular']),mul(tmp['Q'],scalar['certificate']['particular'])))
            elif scalar['certificate']['kind']=='polynomial-normalization': tmp['R']=scalar['certificate']['forcing']
            steps+=scalar_exposition(tmp,scalar,var)
        steps.append('したがって、部分和は '+M('S_n='+L(S))+' である。'+M(r'n\ge2')+' のとき、'+M('a_n=S_n-S_{n-1}')+' を使う。')
        steps.append(M('a_n='+L(sub(S,__import__('variety').previous_curve(S))))+' と整理できる。'+M('n=1')+' についても '+M('a_1=S_1='+N(evaluate(ir['initials'][0],0)))+' と一致するので、得られた式はすべての '+M(r'n\ge1')+' で成り立つ。')
        return steps
    if kind=='mixed-sum-relation':
        f=cert['forcing'];alpha=evaluate(cert['alpha'],0);scalar=cert['scalar'];r=alpha/(alpha-1)
        R=expand_polynomial(mul(num(1/(alpha-1)),sub(f,shift_expr(f))))
        route['title']='隣接する部分和の差で総和を消す';route['hint']='S_nとa_nが混ざっている。添字を1つ進めた式から元の式を引き、S_nを消す。'
        steps=['与式に '+M('n=1')+' を代入すると、'+M('S_1=a_1='+N(alpha)+'a_1+'+N(evaluate(f,0)))+' より '+M('a_1='+N(evaluate(ir['initials'][0],0)))+' である。',
            '添字を1つ進めた式と元の式の差をとる。'+M('S_{n+1}-S_n=a_{n+1}')+' なので、',
            E('a_{n+1}&='+N(alpha)+'(a_{n+1}-a_n)'+r'\\&\quad{}+('+L(shift_expr(f))+')'+r'\\&\quad{}-('+L(f)+')'),
            'これを '+M('a_{n+1}')+' について解くと '+M('a_{n+1}='+coefficient_tex(r,'a_n')+'+'+L(R))+' となる。']
        steps+=scalar_exposition({'P':num(1),'Q':num(r),'R':R,'initials':ir['initials']},scalar)
        return steps
    if kind in {'distinct-roots','normalized-second','sum-to-second'}:
        roots=cert['roots'];g=num(1);steps=[];variable='a'
        if kind=='distinct-roots':p,q=[evaluate(ir[k],0) for k in ('p','q')];first,second=[evaluate(x,0) for x in ir['initials']]
        else:
            trace=route['derivation'][0];p,q=[evaluate(trace[k],0) for k in ('p','q')];first,second=[evaluate(x,0) for x in trace['initials']];variable='b'
            if kind=='sum-to-second':
                alpha,beta=[evaluate(ir[k],0) for k in ('sum_alpha','sum_beta')];g=ir['sum_scale']
                steps=['総和の中の項と外側の係数に合わせて '+M('b_n='+r'\frac{a_n}{'+L(g)+'}')+'、'+M(r'T_n=\sum_{k=1}^n b_k')+' とおく。',
                    M('b_{n+1}='+coefficient_tex(alpha,'b_n')+C(beta,'T_n'))+' と、添字を進めた式 '+M('b_{n+2}='+coefficient_tex(alpha,'b_{n+1}')+C(beta,'T_{n+1}'))+' を比較する。',
                    M('T_{n+1}=T_n+b_{n+1}')+' を代入し、元の式を用いて '+M('T_n')+' を消去すると '+M('b_{n+2}='+coefficient_tex(p,'b_{n+1}')+C(q,'b_n'))+' を得る。',
                    'また、'+M('T_1=b_1')+' なので '+M('b_1='+N(first)+r',\quad b_2='+N(second))+' である。']
            else:
                profile=cert['profile'];g=num(1) if profile=='identity' else (div(num(1),SCALES[profile[8:]]) if profile.startswith('inverse:') else SCALES[profile])
                if profile=='identity': variable='a'
                if profile!='identity': steps.append('3つの係数に現れる '+M('n')+'、'+M('n+1')+'、'+M('n+2')+' の対応に着目し、'+M('b_n='+sequence_tex(trace['transform'],'a'))+' とおく。')
                steps.append('係数をそろえると '+M(variable+'_{n+2}='+coefficient_tex(p,variable+'_{n+1}')+C(q,variable+'_n'))+' であり、初期条件は '+M(variable+'_1='+N(first)+r',\quad '+variable+'_2='+N(second))+' となる。')
        steps+=second_exposition(p,q,first,second,roots,variable)
        if variable=='b':steps.append(M('a_n='+L(mul(g,term(variable='b'))))+' に戻して、元の数列の一般項を得る。')
        return steps
    if kind in {'polynomial-normalization','linear-particular'}:
        if not ir['reciprocal']: return scalar_exposition(ir,route)
        base={**ir,'initials':[num(1/evaluate(ir['initials'][0],0))],'reciprocal':False}
        steps=['初項は正である。各項と分母が '+M('0')+' にならないことは、一般項を求めた後に確認する。まず '+M(r'v_n=\frac1{a_n}')+' とおく。',
            '与式の逆数をとると '+M(sequence_tex(mul(ir['P'],term(1)),'v')+'='+sequence_tex(add(mul(ir['Q'],term()),ir['R']),'v'))+' となり、'+M('v_1='+N(evaluate(base['initials'][0],0)))+' である。']
        steps+=scalar_exposition(base,route,'v')
        # Preserve the explicit domain identity computed by the forward solver.
        steps += [s for s in route['steps'] if 'v_n>0' in s or '元の分母は' in s]
        steps.append(M(r'a_n=\frac1{v_n}='+L(route['formula']))+' と戻せば、元の数列の一般項を得る。')
        return steps
    return route['steps']


def shift_expr(e):
    from expr import shift
    return shift(e)
