"""Textbook-style exposition shared by the web, TeX exports and workbook.

The numerical data come from the independently recognized route certificate.
"""
from fractions import Fraction
from expr import add, sub, mul, div, num, term, nat, index, power, evaluate, latex, polynomial
from profiles import SCALES, EXPONENTS
from solve import signed, coefficient_tex, sequence_tex, relation_tex


def M(tex): return r'\('+tex+r'\)'
def L(e): return latex(e)
def N(x): return L(num(x))
def C(value,symbol):
    return ('+' if value>=0 else '')+coefficient_tex(value,symbol)

def E(tex): return M(r'\begin{aligned}'+tex+r'\end{aligned}')


def second_exposition(p,q,first,second,roots,variable='a'):
    r,s=[evaluate(x,0) for x in roots]
    poly=r'\lambda^2'+('+' if -p>=0 else '')+coefficient_tex(-p,r'\lambda')+signed(-q)
    if r==s:
        slope=second/r-first
        return [
            '特性方程式 '+M(poly+'=0')+' は重解 '+M(r'\lambda='+N(r))+' を持つ。そこで、根のべきで割って階差を調べる。',
            M('c_n='+r'\frac{'+variable+'_n}{'+L(power(num(r),nat()))+'}')+' とおくと、与式より '+M('c_{n+2}-2c_{n+1}+c_n=0')+'、すなわち '+M('c_{n+2}-c_{n+1}=c_{n+1}-c_n')+' を得る。',
            '初期条件から '+E('c_1&='+N(first)+r'\\c_2&='+N(second/r)+r'\\c_2-c_1&='+N(slope))+' である。したがって、'+M(r'\{c_n\}')+' は初項 '+M(N(first))+'、公差 '+M(N(slope))+' の等差数列である。',
            'よって '+M('c_n='+N(first)+signed(slope)+'(n-1)')+' を得る。これに '+M(L(power(num(r),nat())))+' を掛ければ、元の数列が求まる。']
    u1=second-s*first;v1=second-r*first
    return [
        '特性方程式は '+M(poly+'=0')+' であり、'+M(r'(\lambda'+signed(-r)+r')(\lambda'+signed(-s)+')=0')+' と因数分解できる。根 '+M(N(r))+ '、'+M(N(s))+' を用いて、与式を隣接する2項の関係にまとめる。',
        E(variable+'_{n+2}'+C(-s,variable+'_{n+1}')+'&='+N(r)+'('+variable+'_{n+1}'+C(-s,variable+'_n')+')'+r'\\'+variable+'_{n+2}'+C(-r,variable+'_{n+1}')+'&='+N(s)+'('+variable+'_{n+1}'+C(-r,variable+'_n')+')'),
        'したがって、'+M('u_n='+variable+'_{n+1}'+C(-s,variable+'_n'))+'、'+M('v_n='+variable+'_{n+1}'+C(-r,variable+'_n'))+' は、それぞれ公比 '+M(N(r))+'、'+M(N(s))+' の等比数列である。',
        '初期条件から '+M('u_1='+N(u1))+ '、'+M('v_1='+N(v1))+' なので、'+E('u_n&='+L(mul(num(u1),power(num(r),nat())))+r'\\v_n&='+L(mul(num(v1),power(num(s),nat()))))+' を得る。',
        'ここで '+M('u_n-v_n='+coefficient_tex(r-s,variable+'_n'))+' である。2式の差をとり、'+M(N(r-s))+' で割れば '+M(variable+'_n')+' が求まる。']


def scalar_exposition(ir,route,variable='a'):
    cert=route['certificate'];kind=cert['kind']
    if kind=='polynomial-normalization':
        r,q,h=[evaluate(cert[k],0) for k in ('ratio','forcing','shift')]
        profile=cert['profile'];g=num(1) if profile=='identity' else (div(num(1),SCALES[profile[8:]]) if profile.startswith('inverse:') else SCALES[profile])
        first=evaluate(ir['initials'][0],0);b1=(first-h)/evaluate(g,0)
        changed=profile!='identity' or h!=0;source='w' if variable in {'u','v'} else 'c' if variable=='b' else 'b'
        target=source if changed else variable
        steps=[]
        if changed:
            steps.append('左右の係数と付加項を比較し、同じ数列の隣接する項としてまとめられる形を考える。'+M(source+'_n='+sequence_tex(div(sub(term(),num(h)),g),variable))+' とおく。')
            steps.append('この置換を与式に代入して整理すると、'+E(relation_tex(num(r),num(q),source)+r'\\'+source+'_1&='+N(b1))+' となる。')
        if r==1:
            if q:
                steps.append('したがって、'+M(target+'_{n+1}-'+target+'_n='+N(q))+' であり、'+M(r'\{'+target+r'_n\}')+' は初項 '+M(N(b1))+'、公差 '+M(N(q))+' の等差数列である。')
                steps.append('等差数列の一般項から '+M(target+'_n='+L(add(num(b1),mul(num(q),sub(index(),num(1))))))+' を得る。')
            else:
                steps.append(M(target+'_{n+1}='+target+'_n')+' より各項は初項に等しい。したがって '+M(target+'_n='+N(b1))+' である。')
        else:
            fixed=q/(1-r)
            if q:
                other='w' if variable in {'u','v'} else 'd' if target in {'b','c'} else 'b'
                steps.append('定数項を消すため、'+M('x='+coefficient_tex(r,'x')+signed(q))+' を満たす数を求めると '+M('x='+N(fixed))+' である。'+M(other+'_n='+target+'_n'+signed(-fixed))+' とおけば、')
                steps.append(E(other+'_{n+1}&='+coefficient_tex(r,target+'_n')+signed(q-fixed)+r'\\&='+N(r)+'('+target+'_n'+signed(-fixed)+')'+r'\\&='+coefficient_tex(r,other+'_n'))+' となり、'+M(other+'_1='+N(b1-fixed))+' である。')
                steps.append('よって '+M(other+'_n='+L(mul(num(b1-fixed),power(num(r),nat()))))+' を得る。'+M(target+'_n='+other+'_n'+signed(fixed))+' に戻す。')
            else:
                steps.append(M(r'\{'+target+r'_n\}')+' は初項 '+M(N(b1))+'、公比 '+M(N(r))+' の等比数列である。したがって '+M(target+'_n='+L(mul(num(b1),power(num(r),nat()))))+' となる。')
        if changed: steps.append('最後に '+M(variable+'_n='+sequence_tex(mul(g,term(variable=source)),source)+signed(h))+' に戻して一般項を得る。')
        return steps
    if kind=='linear-particular':
        p=cert['particular'];r=evaluate(cert['ratio'],0);A=polynomial(p).get(1,0);B=polynomial(p).get(0,0)
        forcing=div(ir['R'],ir['P']);first=evaluate(ir['initials'][0],0);amp=first-evaluate(p,0)
        target='c' if variable=='b' else 'b'
        return ['付加項が '+M('n')+' の一次式なので、それを打ち消す一次式を考える。特解を '+M('u_n=An+B')+' とおく。',
            M('u_{n+1}='+coefficient_tex(r,'u_n')+'+'+L(forcing))+' に代入し、'+M('n')+' の係数と定数項を比較すると '+M('A='+N(A)+r',\quad B='+N(B))+' となる。したがって '+M('u_n='+L(p))+' である。',
            M(target+'_n='+sequence_tex(sub(term(),p),variable))+' とおくと、'+E(target+'_{n+1}&='+coefficient_tex(r,target+'_n')+r'\\'+target+'_1&='+N(first)+'-('+N(evaluate(p,0))+')='+N(amp))+' を得る。',
            'よって '+M(target+'_n='+L(mul(num(amp),power(num(r),nat()))))+' である。'+M(variable+'_n='+target+'_n+u_n')+' に戻せば一般項が求まる。']
    return [s.replace('です。','である。').replace('ます。','る。') for s in route['steps']]


def explain_route(ir,route):
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
            if scalar['certificate']['kind']=='linear-particular': tmp['R']=sub(shift_expr(scalar['formula']),mul(tmp['Q'],scalar['formula']))
            elif scalar['certificate']['kind']=='polynomial-normalization': tmp['R']=scalar['certificate']['forcing']
            steps+=scalar_exposition(tmp,scalar,var)
        steps.append('したがって、部分和は '+M('S_n='+L(S))+' である。'+M(r'n\ge2')+' のとき、'+M('a_n=S_n-S_{n-1}')+' を使う。')
        steps.append(M('a_n='+L(sub(S,__import__('variety').previous_curve(S))))+' と整理できる。'+M('n=1')+' についても '+M('a_1=S_1='+N(evaluate(ir['initials'][0],0)))+' と一致するので、得られた式はすべての '+M(r'n\ge1')+' で成り立つ。')
        return steps
    if kind=='mixed-sum-relation':
        f=cert['forcing'];alpha=evaluate(cert['alpha'],0);scalar=cert['scalar'];r=alpha/(alpha-1)
        R=mul(num(1/(alpha-1)),sub(f,shift_expr(f)))
        route['title']='隣接する部分和の差で総和を消す';route['hint']='S_nとa_nが混ざっている。添字を1つ進めた式から元の式を引き、S_nを消す。'
        steps=['与式に '+M('n=1')+' を代入すると、'+M('S_1=a_1='+N(alpha)+'a_1+'+N(evaluate(f,0)))+' より '+M('a_1='+N(evaluate(ir['initials'][0],0)))+' である。',
            '添字を1つ進めた式と元の式の差をとる。'+M('S_{n+1}-S_n=a_{n+1}')+' なので、',
            E('a_{n+1}&='+N(alpha)+'(a_{n+1}-a_n)'+r'\\&\quad{}+('+L(shift_expr(f))+')-('+L(f)+')'),
            'これを '+M('a_{n+1}')+' について解くと '+M('a_{n+1}='+coefficient_tex(r,'a_n')+'+'+L(R))+' となる。']
        steps+=scalar_exposition({'P':num(1),'Q':num(r),'R':R,'initials':ir['initials']},scalar)
        return steps
    if kind=='polynomial-difference':
        f=cert['forcing'];a1=evaluate(ir['initials'][0],0)
        route['title']='階差を足し合わせる';route['hint']='隣接する項の差がnの多項式になっている。差を初項から順に足す。'
        return ['与式より '+M('a_{n+1}-a_n='+L(f))+' である。'+M(r'n\ge2')+' のとき、'+M(r'k=1,2,\ldots,n-1')+' について足し合わせると、',
            E('a_n-a_1&='+r'\sum_{k=1}^{n-1}'+__import__('re').sub(r'(?<![a-zA-Z\\])n(?![a-zA-Z])','k',L(f))),
            '左辺では途中の項が消える。右辺の和を計算し、初項 '+M('a_1='+N(a1))+' を代入すると '+M('a_n='+L(route['formula']))+' を得る。'+M('n=1')+' のときも初項と一致する。']
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
                if profile!='identity': steps.append('3つの係数に現れる '+M('n')+'、'+M('n+1')+'、'+M('n+2')+' の対応に着目し、'+M('b_n='+sequence_tex(trace['transform'],'a'))+' とおく。')
                steps.append('与式に代入して整理すると '+M('b_{n+2}='+coefficient_tex(p,'b_{n+1}')+C(q,'b_n'))+' であり、初期条件は '+M('b_1='+N(first)+r',\quad b_2='+N(second))+' となる。')
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
        steps += route['steps'][-2:]
        steps.append(M(r'a_n=\frac1{v_n}')+' に戻せば、元の数列の一般項を得る。')
        return steps
    # Registered product, log and antidifference routes retain their checked data;
    # avoid imperative fragments and make each last substitution explicit.
    steps=[s.replace('です。','である。').replace('とおきます。','とおく。').replace('代入します。','代入する。').replace('戻します。','戻す。').replace('とおけます。','とおける。').replace('を得ます。','を得る。').replace('となります。','となる。').replace('消えます。','消える。').replace('まとめられます。','まとめられる。') for s in route['steps']]
    if kind=='difference-normalization':
        steps.insert(3,'階差を足し合わせるには、'+M(r'H(n)')+' を '+M('n')+' の多項式とおき、'+M('rH(n+1)-H(n)')+' が階差の多項式部分と一致するように係数を決める。')
    return steps


def shift_expr(e):
    from expr import shift
    return shift(e)
