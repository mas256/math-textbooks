"""Worked calculations derived from the forward solver's certificates."""
from fractions import Fraction
from math import comb
import re

from expr import (add, sub, mul, div, num, term, nat, nat_const, index,
                  power, evaluate, latex, polynomial, expand_polynomial, shift)
from profiles import SCALES, EXPONENTS
from solve import coefficient_tex, signed, relation_tex, sequence_tex
from algebra import prefix_polynomial, geometric_antidifference, integer_log
from exposition import M, L, N, C, E


def scale(profile):
    if profile == 'identity':
        return num(1)
    return div(num(1), SCALES[profile[8:]]) if profile.startswith('inverse:') else SCALES[profile]


def at_k(expr):
    return re.sub(r'(?<![a-zA-Z\\])n(?![a-zA-Z])', 'k', L(expr))


def affine_steps(first, ratio, forcing, variable='a', auxiliary='b'):
    """Solve x_next=r*x+q, displaying the shift and the initial calculation."""
    x, y = variable, auxiliary
    if ratio == 1:
        formula = add(num(first), mul(num(forcing), nat()))
        if forcing == 0:
            return [M(x+'_{n+1}='+x+'_n')+' なので、隣接する項はすべて等しい。初項から順にたどると '+M(x+'_n='+N(first))+' である。'], formula
        steps = [
            M(x+'_{n+1}-'+x+'_n='+N(forcing))+' に着目する。隣接する項の差が一定なので、等差数列として解ける。',
            '初項から第 '+M('n')+' 項までは '+M('n-1')+' 回進む。したがって '+E(
                x+'_n-'+x+'_1&='+r'\sum_{k=1}^{n-1}('+x+'_{k+1}-'+x+'_k)'
                +r'\\&='+r'\sum_{k=1}^{n-1}'+N(forcing)+'='+L(mul(num(forcing),nat()))),
            '左辺の途中の項は打ち消し合う。初項 '+M(x+'_1='+N(first))+' を戻すと '+M(x+'_n='+L(formula))+' を得る。'+M('n=1')+' でも加える回数が0なので成り立つ。']
        return steps, formula
    if forcing == 0:
        formula = mul(num(first), power(num(ratio),nat()))
        return [
            M(x+'_{n+1}='+coefficient_tex(ratio,x+'_n'))+' では、1回進むごとに '+M(N(ratio))+' 倍される。初項 '+M(x+'_1='+N(first))+' から第 '+M('n')+' 項までの倍率は '+M(L(power(num(ratio),nat())))+' である。',
            'たとえば '+M(x+'_2='+L(mul(num(first),num(ratio))))+'、'+M(x+'_3='+L(mul(num(first),num(ratio**2))))+'。同じ操作を '+M('n-1')+' 回繰り返すので '+M(x+'_n='+L(formula))+' となる。'], formula
    fixed = forcing/(1-ratio)
    amplitude = first-fixed
    formula = add(num(fixed),mul(num(amplitude),power(num(ratio),nat())))
    steps = [
        '定数項があるので、そのままでは等比数列にならない。一定の値 '+M(r'\ell')+' を引いて定数項を消すことを考える。'+M(r'\ell='+coefficient_tex(ratio,r'\ell')+signed(forcing))+' を解くと、',
        E(coefficient_tex(1-ratio,r'\ell')+'&='+N(forcing)+r'\\\ell&='+N(fixed))+' である。この値は、更新しても変わらない値である。',
        M(y+'_n='+x+'_n'+signed(-fixed))+' とおく。上の定数の関係を使うと '+E(
            y+'_{n+1}&='+x+'_{n+1}'+signed(-fixed)
            +r'\\&='+coefficient_tex(ratio,x+'_n')+signed(forcing-fixed)
            +r'\\&='+N(ratio)+r'\left('+x+'_n'+signed(-fixed)+r'\right)'
            +r'\\&='+coefficient_tex(ratio,y+'_n'))+'。これで等比数列になった。',
        '初項も置換して '+M(y+'_1='+N(first)+'-('+N(fixed)+')='+N(amplitude))+'。公比を '+M('n-1')+' 回掛けるので '+M(y+'_n='+L(mul(num(amplitude),power(num(ratio),nat()))))+' となる。',
        '最後に '+M(x+'_n='+y+'_n'+signed(fixed))+' を使って置換を戻すと '+M(x+'_n='+L(formula))+' を得る。']
    return steps, formula


def scalar_steps(ir, route, variable='a'):
    c = route['certificate']
    if c['kind'] == 'polynomial-normalization':
        r,q,h = [evaluate(c[k],0) for k in ('ratio','forcing','shift')]
        g = scale(c['profile'])
        first = evaluate(ir['initials'][0],0)
        g1 = evaluate(g,0)
        b1 = (first-h)/g1
        changed = g != num(1) or h != 0
        target = ('w' if variable in {'u','v'} else 'c' if variable == 'b' else 'b') if changed else variable
        auxiliary = next(x for x in ('d','z','w','c','b') if x not in {target,variable})
        steps = []
        if changed:
            transform = mul(sub(term(),num(h)),g['args'][1]) if g['op']=='div' and g['args'][0]==num(1) else div(sub(term(),num(h)),g)
            steps += [
                '係数に含まれる '+M('n')+' と '+M('n+1')+' の対応をそろえるため、'+M('g(n)='+L(g))+' を使う。'+M(target+'_n='+sequence_tex(transform,variable))+'、すなわち '+M(variable+'_n='+L(add(mul(g,term(variable=target)),num(h))))+' とおく。',
                '添字を進めた項にも同じ置換を行う。'+M(variable+'_{n+1}='+L(add(mul(shift(g),term(1,variable=target)),num(h))))+' を与式に代入し、定数部分を右辺へ移すと、',
                E(L(mul(ir['P'],shift(g),term(1,variable=target)))+'&='+L(add(mul(ir['Q'],g,term(variable=target)),ir['R'],mul(num(h),sub(ir['Q'],ir['P']))))),
                '左辺の係数 '+M(L(mul(ir['P'],shift(g))))+' で割る。'+E(
                    r'\frac{'+L(mul(ir['Q'],g))+'}{'+L(mul(ir['P'],shift(g)))+'}&='+N(r)
                    +r'\\\frac{'+L(add(ir['R'],mul(num(h),sub(ir['Q'],ir['P']))))+'}{'+L(mul(ir['P'],shift(g)))+'}&='+N(q))
                +' なので '+M(relation_tex(num(r),num(q),target))+' となる。',
                '初期条件にも置換を適用すると '+M(target+r'_1=\frac{'+N(first)+'-('+N(h)+')}{'+N(g1)+'}='+N(b1))+' である。']
        else:
            steps.append('与式を '+M(relation_tex(num(r),num(q),variable))+' と見る。初項は '+M(variable+'_1='+N(first))+' である。')
        more, formula = affine_steps(b1,r,q,target,auxiliary)
        steps += more
        if changed:
            steps.append('元の数列へ戻すには '+M(variable+'_n='+L(add(mul(g,term(variable=target)),num(h))))+' に代入する。よって '+M(variable+'_n='+L(add(mul(g,formula),num(h))))+' である。')
        return steps
    if c['kind'] == 'linear-particular':
        p=c['particular'];r=evaluate(c['ratio'],0)
        A,B=polynomial(p).get(1,0),polynomial(p).get(0,0)
        P=evaluate(ir['P'],0)
        f=expand_polynomial(mul(ir['R'],num(1/P)))
        alpha,beta=polynomial(f).get(1,0),polynomial(f).get(0,0)
        first=evaluate(ir['initials'][0],0)
        target=next(x for x in ('b','c','w') if x!=variable)
        particular=next(x for x in ('u','z') if x!=variable)
        amp=first-evaluate(p,0)
        assert (1-r)*A==alpha and A+(1-r)*B==beta
        steps=[
            'まず先頭の係数で割って '+M(variable+'_{n+1}='+L(add(mul(num(r),term(variable=variable)),f)))+' とする。付加項が一次式なので、同じ一次式の形の数列を引けば消せると考える。',
            M(particular+'_n=An+B')+' がこの漸化式を満たすように、'+M('A,B')+' を決める。代入して '+M('A(n+1)+B='+N(r)+'(An+B)+'+L(f))+'。',
            '両辺を '+M('n')+' の係数と定数項に分けると '+E(
                'An+(A+B)&='+coefficient_tex(r,'A')+'n+('+coefficient_tex(r,'B')+signed(beta)+')'+C(alpha,'n')
                +r'\\'+coefficient_tex(1-r,'A')+'&='+N(alpha)
                +r'\\A'+C(1-r,'B')+'&='+N(beta))+' を得る。',
            '上から順に解くと '+E('A&='+N(A)+r'\\B&=\frac{'+N(beta)+'-('+N(A)+')}{'+N(1-r)+'}='+N(B))+'。したがって '+M(particular+'_n='+L(p))+' である。',
            '元の数列と、この特解の漸化式を引き算する。'+M(target+'_n='+variable+'_n-'+particular+'_n')+' とおくと '+E(
                target+'_{n+1}&=('+coefficient_tex(r,variable+'_n')+'+'+L(f)+')-('+coefficient_tex(r,particular+'_n')+'+'+L(f)+')'
                +r'\\&='+N(r)+'('+variable+'_n-'+particular+'_n)='+coefficient_tex(r,target+'_n'))+' となり、付加項が消える。',
            '初項は '+M(target+'_1='+N(first)+'-('+N(evaluate(p,0))+')='+N(amp))+'。よって '+M(target+'_n='+L(mul(num(amp),power(num(r),nat()))))+' である。',
            M(variable+'_n='+target+'_n+'+particular+'_n')+' に戻すと '+M(variable+'_n='+L(add(mul(num(amp),power(num(r),nat())),p)))+' を得る。']
        return steps
    return None


def second_steps(p,q,first,second,roots,variable='a'):
    r,s=[evaluate(x,0) for x in roots]
    x=variable
    assert p==r+s and q==-r*s
    # Use an independent symbol instead of a sequence term in the characteristic equation.
    poly=r'\lambda^2'+C(-p,r'\lambda')+signed(-q)
    steps=[
        '係数が一定の3項間漸化式では、等比数列の形 '+M(x+'_n='+r'\lambda^{n-1}')+' を試すと、'+M(r'\lambda^{n+1}='+N(p)+r'\lambda^n'+C(q,r'\lambda^{n-1}'))+' となる。そこで特性方程式 '+M(poly+'=0')+' を考える。',
        '因数分解すると '+M(r'(\lambda'+signed(-r)+r')(\lambda'+signed(-s)+')=0')+'。根は '+M(r'\lambda='+N(r))+('（重解）' if r==s else '、'+M(N(s)))+' である。']
    if r==s:
        slope=second/r-first
        c='c' if x!='c' else 'd'
        formula=mul(add(num(first),mul(num(slope),nat())),power(num(r),nat()))
        steps += [
            '重解では、単に2つの等比数列を足す方法では独立な式が2本得られない。'+M(c+'_n='+r'\frac{'+x+'_n}{'+L(power(num(r),nat()))+'}')+' とおき、根のべきを取り除く。',
            '与式の3項に '+M(x+'_{n}='+L(power(num(r),nat()))+c+'_n')+'、'+M(x+'_{n+1}='+L(power(num(r),nat(1)))+c+'_{n+1}')+'、'+M(x+'_{n+2}='+L(power(num(r),nat(2)))+c+'_{n+2}')+' を代入する。共通のべきで割ると '+M(c+'_{n+2}=2'+c+'_{n+1}-'+c+'_n')+' となる。',
            'これを移項すると '+M(c+'_{n+2}-'+c+'_{n+1}='+c+'_{n+1}-'+c+'_n')+'。隣接する差が一定、すなわち '+M(r'\{'+c+r'_n\}')+' は等差数列である。',
            '初期値と公差は '+E(c+'_1&='+N(first)+r'\\'+c+r'_2&=\frac{'+N(second)+'}{'+N(r)+'}='+N(second/r)+r'\\'+c+'_2-'+c+'_1&='+N(second/r)+'-('+N(first)+')='+N(slope)),
            'したがって '+M(c+'_n='+L(add(num(first),mul(num(slope),nat()))))+'。根のべきを掛けて戻すと '+M(x+'_n='+L(formula))+' となる。']
        return steps
    u1,v1=second-s*first,second-r*first
    uexpr=mul(num(u1),power(num(r),nat()));vexpr=mul(num(v1),power(num(s),nat()))
    steps += [
        '2つの根は '+M(N(r+s)+'='+N(p))+ '、'+M(N(r*s)+'='+N(-q))+' を満たす。この関係で与式をまとめ直すと '+E(
            x+'_{n+2}'+C(-s,x+'_{n+1}')+'&='+N(r)+'('+x+'_{n+1}'+C(-s,x+'_n')+')'
            +r'\\'+x+'_{n+2}'+C(-r,x+'_{n+1}')+'&='+N(s)+'('+x+'_{n+1}'+C(-r,x+'_n')+')')+' となる。',
        '同じ形が隣接して現れたので '+M('u_n='+x+'_{n+1}'+C(-s,x+'_n'))+'、'+M('v_n='+x+'_{n+1}'+C(-r,x+'_n'))+' とおく。すると '+M('u_{n+1}='+coefficient_tex(r,'u_n'))+'、'+M('v_{n+1}='+coefficient_tex(s,'v_n'))+' という2つの等比数列に分かれる。',
        '初項は元の初期条件から '+E('u_1&='+N(second)+'-('+N(s)+')('+N(first)+')='+N(u1)+r'\\v_1&='+N(second)+'-('+N(r)+')('+N(first)+')='+N(v1))+'。したがって '+E('u_n&='+L(uexpr)+r'\\v_n&='+L(vexpr))+' である。',
        '最後は補助数列の定義を引く。'+E('u_n-v_n&=('+x+'_{n+1}'+C(-s,x+'_n')+')-('+x+'_{n+1}'+C(-r,x+'_n')+')'+r'\\&='+coefficient_tex(r-s,x+'_n'))+'。根が異なるので '+M(N(r-s))+ ' で割れる。',
        'よって '+E(x+r'_n&=\frac{u_n-v_n}{'+N(r-s)+'}'+r'\\&='+L(add(mul(num(u1/(r-s)),power(num(r),nat())),mul(num(-v1/(r-s)),power(num(s),nat())))))+' を得る。']
    return steps


def sum_steps(forcing, initial, variable='a'):
    """Show standard power sums, with a checked exact polynomial antiderivative."""
    coeff=polynomial(forcing)
    degree=max(coeff,default=0)
    assert degree<=3
    n=index();m=nat()
    sums={0:m,1:mul(num(Fraction(1,2)),n,m),
          2:mul(num(Fraction(1,6)),n,m,sub(mul(num(2),n),num(1))),
          3:power(mul(num(Fraction(1,2)),n,m),nat_const(2))}
    symbols={0:'1',1:'k',2:'k^2',3:'k^3'}
    rows=[r'\sum_{k=1}^{n-1}'+symbols[d]+'&='+L(sums[d]) for d in sorted(coeff) if coeff[d]]
    total=add(*(mul(num(c),sums[d]) for d,c in coeff.items()))
    result=prefix_polynomial(forcing,initial)
    assert polynomial(add(num(initial),total))==polynomial(result)
    return [
        '隣接する項の差を足すと '+E(
            variable+'_n-'+variable+'_1&=('+variable+'_2-'+variable+'_1)+('+variable+'_3-'+variable+'_2)'+r'\cdots+('+variable+'_n-'+variable+'_{n-1})'
            +r'\\&=\sum_{k=1}^{n-1}\left('+at_k(forcing)+r'\right)')+'。途中の項が消え、初項と第 '+M('n')+' 項だけが残る。',
        '必要な和の公式は '+E(r'\\'.join(rows) if rows else r'\sum_{k=1}^{n-1}0=0')+' である。足す範囲が '+M('1')+' から '+M('n-1')+' までであることに注意する。',
        '係数ごとに和を分け、これらの公式を代入すると '+E(
            variable+'_n&='+N(initial)+r'+\sum_{k=1}^{n-1}\left('+at_k(forcing)+r'\right)'
            +r'\\&='+L(add(num(initial),total))+r'\\&='+L(result))+' を得る。'+M('n=1')+' では和は空になり、初項にも一致する。']


def elementary_steps(ir,route):
    c=route['certificate'];kind=c['kind']
    first=evaluate(ir['initials'][0],0)
    if kind=='exponential-normalization':
        r,s,q=[evaluate(c[k],0) for k in ('ratio','base','coefficient')]
        pr,ps=power(num(r),nat()),power(num(s),nat())
        steps=[
            '付加項に '+M(L(ps))+' があるので、各項を同じべきで割り、指数部分を定数に変えることを考える。'+M(r'b_n=\frac{a_n}{'+L(ps)+'}')+' とおく。底 '+M(N(s))+' は正なので、すべての添字で割れる。',
            '次項の分母は '+M(L(power(num(s),nat(1))))+' である。与式をこの数で割ると '+E(
                r'\frac{a_{n+1}}{'+L(power(num(s),nat(1)))+r'}&=\frac{'+L(mul(num(r),term()))+'}{'+L(power(num(s),nat(1)))+r'}+\frac{'+L(mul(num(q),ps))+'}{'+L(power(num(s),nat(1)))+'}'
                +r'\\b_{n+1}&='+coefficient_tex(r/s,'b_n')+signed(q/s))+'。指数が1つずれているため、係数にも '+M(N(s))+' で割る操作が必要になる。',
            '初項は '+M('b_1='+N(first)+r'/1='+N(first))+' である。']
        more,bformula=affine_steps(first,r/s,q/s,'b','c')
        steps+=more
        steps.append('最後に '+M('a_n='+L(ps)+'b_n')+' に戻す。'+M(L(ps)+r'\left('+L(power(num(r/s),nat()))+r'\right)='+L(pr))+' と指数法則でまとめると '+M('a_n='+L(route['formula']))+' を得る。')
        return steps
    if kind!='power-first-log':
        return None
    d=c['degree']['value'];coefficient=evaluate(c['coefficient'],0);h=evaluate(c['shift'],0)
    initial=first-h;u='u' if h else 'a'
    steps=[]
    if h:
        steps.append('右辺の係数を、同じ一次式の平方・立方にまとめられないか調べる。展開公式を逆に使うと '+M(L(sub(term(1),num(h)))+'='+L(mul(num(coefficient),power(sub(term(),num(h)),nat_const(d)))))+' となる。')
        steps.append(M('u_n='+L(sub(term(),num(h))))+' とおけば '+M('u_{n+1}='+L(mul(num(coefficient),power(term(variable='u'),nat_const(d)))))+'、'+M('u_1='+N(first)+'-('+N(h)+')='+N(initial))+' となる。')
    steps += [
        '初項 '+M(u+'_1='+N(initial))+' と係数 '+M(N(coefficient))+' は正である。正の項から次の項も正になるので、帰納的に全項が正であり、対数をとれる。',
        '累乗を定数倍に変えるため '+M(r'b_n=\log '+u+'_n')+' とおく。'+M(r'\log(xy)=\log x+\log y')+'、'+M(r'\log(x^d)=d\log x')+' を使うと '+E(
            r'b_{n+1}&=\log\left('+L(mul(num(coefficient),power(term(variable=u),nat_const(d))))+r'\right)'
            +r'\\&='+str(d)+r'\log '+u+r'_n+\log '+N(coefficient)
            +r'\\&='+str(d)+r'b_n+\log '+N(coefficient))+'。初項は '+M(r'b_1=\log '+N(initial))+' である。']
    D=L(power(num(d),nat()))
    if coefficient==1:
        steps.append(M(r'\log1=0')+' より '+M('b_{n+1}='+str(d)+'b_n')+'。したがって '+M('b_n='+D+r'\log '+N(initial))+' である。')
    else:
        shiftlog=r'\frac{\log '+N(coefficient)+'}{'+str(d-1)+'}'
        steps += [
            '定数項を消す値を求めると '+M(r'\ell='+str(d)+r'\ell+\log '+N(coefficient))+ '、したがって '+M(r'\ell=-'+shiftlog)+' である。'+M('c_n=b_n+'+shiftlog)+' とおく。',
            E('c_{n+1}&='+str(d)+r'b_n+\log '+N(coefficient)+'+'+shiftlog+r'\\&='+str(d)+r'\left(b_n+'+shiftlog+r'\right)='+str(d)+'c_n')+' なので、公比 '+M(str(d))+' の等比数列になる。',
            '初項は '+M(r'c_1=\log '+N(initial)+'+'+shiftlog)+'。これを '+M('n-1')+' 回 '+M(str(d))+' 倍してから置換を戻すと '+E(
                'b_n&='+D+r'\left(\log '+N(initial)+'+'+shiftlog+r'\right)-'+shiftlog
                +r'\\&='+D+r'\log '+N(initial)+r'+\frac{'+D+r'-1}{'+str(d-1)+r'}\log '+N(coefficient))+' となる。']
    steps += [
        '対数の係数を指数に移し、'+M(r'\log '+u+'_n=b_n')+' を元に戻す。'+M(r'\log(x^t)=t\log x')+' より '+M(u+'_n='+L(route['derivation'][0]['formula']))+' である。']
    if h:steps.append(M('a_n=u_n'+signed(h))+' に代入して '+M('a_n='+L(route['formula']))+' を得る。')
    return steps


def extension_steps(ir,route):
    c=route['certificate'];kind=c['kind']
    if kind=='mobius-shift':
        p,q,r,s=[evaluate(x,0) for x in ir['mobius_coefficients']]
        h=evaluate(c['shift'],0);base=c['scalar_ir']
        P,Q,R=[evaluate(base[k],0) for k in ('P','Q','R')]
        first=evaluate(ir['initials'][0],0)
        steps=[
            '分数の一次式では、更新しても変わらない値を基準にすると形を簡単にできる。'+M(r'x=\frac{'+coefficient_tex(p,'x')+signed(q)+'}{'+coefficient_tex(r,'x')+signed(s)+'}')+' を解く。',
            '分母を払って移項すると '+M(coefficient_tex(r,'x^2')+C(s-p,'x')+signed(-q)+'=0')+'。この方程式の解のうち '+M('x='+N(h))+' を使う。',
            'この値を次項から引くと '+E(
                'a_{n+1}'+signed(-h)+r'&=\frac{'+coefficient_tex(p-h*r,'a_n')+signed(q-h*s)+'}{'+coefficient_tex(r,'a_n')+signed(s)+'}'
                +r'\\&=\frac{'+N(P)+r'\left(a_n'+signed(-h)+r'\right)}{'+coefficient_tex(r,'a_n')+signed(s)+'}')+'。不動点の方程式により分子が '+M('a_n'+signed(-h))+' を因子に持つことが、この置換を選ぶ理由である。',
            M(r'v_n=\frac1{a_n'+signed(-h)+'}')+' とおき、逆数をとる。'+M('a_n='+N(h)+r'+1/v_n')+' も使うと '+E(
                'v_{n+1}&='+r'\frac{'+coefficient_tex(r,'a_n')+signed(s)+'}{'+N(P)+r'\left(a_n'+signed(-h)+r'\right)}'
                +r'\\&=\frac{'+coefficient_tex(Q,'v_n')+signed(R)+'}{'+N(P)+'}')+'。初項は '+M(r'v_1=\frac1{'+N(first)+'-('+N(h)+')}='+L(base['initials'][0]))+' である。']
        steps+=scalar_steps(base,c['scalar'],'v')
        steps += [
            '元の数列は '+M('a_n='+N(h)+r'+\frac1{v_n}')+' である。得られた '+M('v_n')+' は全項で正なので、この逆数は定義できる。',
            '元の分母は '+M(coefficient_tex(r,'a_n')+signed(s)+'='+N(P)+r'\frac{v_{n+1}}{v_n}')+'。右辺の各因子は正であり、元の分母もすべての項で零にならない。']
        return steps
    if kind=='factorial-product':
        from level_extensions import factorial_expr
        from math import factorial
        first=evaluate(ir['initials'][0],0);r=evaluate(c['ratio'],0)
        factors=''.join(r'\prod_{k=1}^{n-1}(k'+('+'+str(t) if t else '')+')' for t in c['offsets'])
        steps=[
            '各更新で '+M('n')+' の一次式を掛けるので、初項からの倍率を積で表す。初項と倍率は零でないため '+M(r'\frac{a_{n+1}}{a_n}='+L(ir['Q']))+' とできる。',
            '隣接する比を掛けると '+E(
                r'\frac{a_n}{a_1}&=\frac{a_2}{a_1}\frac{a_3}{a_2}\cdots\frac{a_n}{a_{n-1}}'
                +r'\\&='+L(power(num(r),nat()))+factors)+'。左辺では途中の項が約分され、定数の倍率は '+M('n-1')+' 個になる。']
        for t in sorted(set(c['offsets'])):
            steps.append('因子 '+M('k'+('+'+str(t) if t else ''))+' の積は、'+M(str(t+1))+ ' から '+M('n'+signed(t-1))+' までの連続した整数の積である。したがって '+M(r'\prod_{k=1}^{n-1}(k'+('+'+str(t) if t else '')+')='+L(div(factorial_expr(t),num(factorial(t)))))+'。末尾までの階乗から、手前の '+M(str(t)+'!')+' を除けばよい。')
        steps.append('それぞれの積をこの階乗表示に置き換え、初項 '+M('a_1='+N(first))+' を掛けると '+M('a_n='+L(route['formula']))+' を得る。'+M('n=1')+' の空積は1であり、初期値にも一致する。')
        return steps
    if kind=='arithmetic-difference':
        diff=evaluate(c['first_difference'],0);inc=evaluate(c['increment'],0)
        a1,a2=[evaluate(x,0) for x in ir['initials']]
        b=add(num(diff),mul(num(inc),nat()))
        return [
            '3項の係数 '+M('1,-2,1')+' は、隣接する差をもう一度引いた形に対応する。与式を '+M('a_{n+2}-a_{n+1}=(a_{n+1}-a_n)'+signed(inc))+' とまとめる。',
            M('b_n=a_{n+1}-a_n')+' とおくと '+M('b_{n+1}-b_n='+N(inc))+'。初項は '+M('b_1='+N(a2)+'-('+N(a1)+')='+N(diff))+' である。',
            '階差数列は公差 '+M(N(inc))+' の等差数列なので '+M('b_n='+L(b))+' となる。元の数列へ戻すため、今度はこの階差を足す。',
            *sum_steps(b,a1),
            'この計算は2つの初期値を使っている。'+M('n=2')+' を代入しても '+M('a_2='+N(a2))+' に一致する。']
    if kind=='forced-second':
        from exposition import explain_route
        h=evaluate(c['shift'],0);base=c['scalar_ir'];scalar=c['scalar']
        P,Q,R,F=[evaluate(ir[k],0) for k in ('P2','Q2','R2','F2')]
        first,second=[evaluate(x,0) for x in ir['initials']]
        # Simultaneously rename every auxiliary to keep the outer b distinct.
        names={'a':'b','b':'c','c':'d','d':'e'}
        inner=explain_route(base,scalar)
        inner=[re.sub(r'(?<![A-Za-z\\])([abcd])(?=_(?:n|\{|\d))',lambda m:names[m[1]],s) for s in inner]
        return [
            '定数項を消すため、すべての項が一定の値 '+M(r'\ell')+' になる場合を考える。'+M(coefficient_tex(P,r'\ell')+'='+coefficient_tex(Q+R,r'\ell')+signed(F))+' より '+M(coefficient_tex(P-Q-R,r'\ell')+'='+N(F))+'、したがって '+M(r'\ell='+N(h))+' である。',
            M('b_n=a_n'+signed(-h))+' とおき、'+M('a_n=b_n'+signed(h))+' を3つの項すべてに代入する。一定の数の関係が打ち消し合うので '+M('b_{n+2}='+coefficient_tex(Q/P,'b_{n+1}')+C(R/P,'b_n'))+' となる。',
            '初期条件も '+M('b_1='+N(first)+'-('+N(h)+')='+L(base['initials'][0]))+'、'+M('b_2='+N(second)+'-('+N(h)+')='+L(base['initials'][1]))+' と変わる。',
            *inner,
            M('a_n=b_n'+signed(h))+' に戻すと '+M('a_n='+L(route['formula']))+' を得る。']
    return None


def antidifference_steps(ir,route):
    c=route['certificate'];r=evaluate(c['ratio'],0);g=scale(c['profile'])
    a1,a2=[evaluate(x,0) for x in ir['initials']]
    amplitude=(a2-a1)/evaluate(g,0)
    f=mul(num(amplitude),g);H=geometric_antidifference(f,r)
    coeff=polynomial(H);degree=max(coeff,default=0)
    letters={0:'C',1:'B',2:'A'}
    unknown='+'.join(letters[j]+('n^2' if j==2 else 'n' if j==1 else '') for j in range(degree,-1,-1))
    rows=[]
    fc=polynomial(f)
    for k in range(degree,-1,-1):
        terms=coefficient_tex(r-1,letters[k])
        for j in range(k+1,degree+1):
            terms+=C(r*comb(j,k),letters[j])
        rows.append(terms+'&='+N(fc.get(k,0)))
    values=r',\quad '.join(letters[k]+'='+N(coeff.get(k,0)) for k in range(degree,-1,-1))
    # The coefficient system is an exact triangular system, not a guessed H.
    for k in range(degree+1):
        assert (r-1)*coeff.get(k,0)+sum(r*comb(j,k)*coeff.get(j,0) for j in range(k+1,degree+1))==fc.get(k,0)
    return [
        '3項の係数に '+M('P(n)=Q(n)+R(n)')+' の関係があるので、'+M('b_n=a_{n+1}-a_n')+' とおく。与式を差でまとめると '+M(L(mul(ir['P2'],term(1,variable='b')))+'='+L(mul(num(-1),ir['R2'],term(variable='b'))))+' となる。',
        '初項は '+M('b_1='+N(a2)+'-('+N(a1)+')='+N(a2-a1))+'。さらに '+M(r'c_n=\frac{b_n}{'+L(g)+'}')+' とおくと '+M('c_{n+1}='+coefficient_tex(r,'c_n'))+'、'+M('c_1='+N(amplitude))+'。よって '+M('b_n='+L(mul(f,power(num(r),nat()))))+' である。',
        'この階差は「多項式×等比のべき」である。和の途中の項を消すため、'+M('F_n=H(n)'+L(power(num(r),nat())))+' として '+M('F_{n+1}-F_n=b_n')+' となる多項式 '+M('H(n)')+' を探す。',
        'べきをくくると、必要な条件は '+M(N(r)+'H(n+1)-H(n)='+L(f))+'。右辺と同じ次数の '+M('H(n)='+unknown)+' を代入し、次数の高い順に係数を比べると '+E(r'\\'.join(rows))+' となる。',
        '上から順に解くと '+M(values)+'。したがって '+M('H(n)='+L(H))+' であり、この式は上の多項式の恒等式を満たす。',
        'あとは階差を足す。'+E(
            r'a_n-a_1&=\sum_{k=1}^{n-1}(F_{k+1}-F_k)=F_n-F_1'
            +r'\\&=H(n)'+L(power(num(r),nat()))+'-H(1)')+'。ここで '+M('H(1)='+N(evaluate(H,0)))+' なので '+M('a_n='+L(route['formula']))+' を得る。'+M('n=1')+' では差の和が0となり、初項に戻る。']


def detailed_route(ir,route,original):
    c=route['certificate'];kind=c['kind']
    if kind in {'power-first-log','exponential-normalization'}:
        return elementary_steps(ir,route)
    if kind in {'mobius-shift','factorial-product','arithmetic-difference','forced-second'}:
        return extension_steps(ir,route)
    if kind=='polynomial-difference':
        return ['与式の '+M('a_{n+1}-a_n='+L(c['forcing']))+' は添字の多項式である。各項を直接求める代わりに、初項からの差をまとめて足す。',*sum_steps(c['forcing'],evaluate(ir['initials'][0],0))]
    if kind=='difference-normalization':
        return antidifference_steps(ir,route)
    if kind=='log-second-difference':
        base=c['base'];r=evaluate(base,0)
        first,second=[integer_log(evaluate(x,0),r) for x in ir['initials']]
        diff=second-first
        f=c['forcing'];difference=prefix_polynomial(f,diff)
        return [
            '積や商で結ばれた項を差に変えるため、対数をとる。初期値は正であり、正の項から次も正になるので '+M(r'b_n=\log_{'+L(base)+'}a_n')+' を全項で定義できる。',
            '対数の積・商・累乗の公式を使うと '+M('b_{n+2}-2b_{n+1}+b_n='+L(f))+'。初期値は '+M('b_1='+N(first))+ '、'+M('b_2='+N(second))+' である。',
            '左辺を隣接する差の差と見て '+M('c_n=b_{n+1}-b_n')+' とおく。'+M('c_{n+1}-c_n='+L(f))+'、'+M('c_1='+N(second)+'-('+N(first)+')='+N(diff))+' となる。',
            *sum_steps(f,diff,'c'),
            '今度は '+M('b_{n+1}-b_n=c_n')+' を足す。同じ計算をもう一度行い、初項 '+M('b_1='+N(first))+' を戻す。',
            *sum_steps(difference,first,'b'),
            '最後に '+M('a_n='+L(base)+'^{b_n}')+' と指数の形に戻して '+M('a_n='+L(route['formula']))+' を得る。']
    if kind in {'exponent-sum','logarithmic-sum'}:
        profile=EXPONENTS[c['profile']];inc,total=profile['increment'],profile['total']
        base=ir['Q']['args'][0];first=evaluate(ir['initials'][0],0)
        steps=original(ir,route)[:1]
        steps.append('指数の和を '+M(r'T_n=\sum_{k=1}^{n-1}\left('+at_k(inc)+r'\right)')+' とする。'+M('T_1=0')+'、'+M('T_{n+1}-T_n='+L(inc))+' なので、階差の和として計算できる。')
        steps+=sum_steps(inc,0,'T')
        steps.append('この多項式は '+M('T_n='+L(total))+' とも表せる。'+(
            M(r'b_n=\log_{'+L(base)+'}'+N(first)+'+T_n')+' を '+M('a_n='+L(base)+'^{b_n}')+' に戻すと、'
            if kind=='logarithmic-sum' else '初項に、各更新で掛けた底のべきをまとめて掛けると、')
            +M('a_n='+L(route['formula']))+' を得る。')
        return steps
    if kind=='telescoping-product':
        g=scale(c['profile']);r=evaluate(c['ratio'],0)
        reciprocal=ir['reciprocal'];x='v' if reciprocal else 'a'
        first=1/evaluate(ir['initials'][0],0) if reciprocal else evaluate(ir['initials'][0],0)
        formula=mul(num(first/evaluate(g,0)),g,power(num(r),nat()))
        steps=[]
        if reciprocal:
            steps.append('分子に '+M('a_n')+'、分母にも '+M('a_n')+' があるので、'+M(r'v_n=1/a_n')+' により一次の式に変える。逆数をとると '+M(L(mul(ir['P'],term(1,variable='v')))+'='+L(add(mul(ir['Q'],term(variable='v')),ir['R'])))+'、'+M('v_1='+N(first))+' となる。')
        steps += [
            '係数を因数ごとに見ると '+M('g(n)='+L(g))+' を使って '+M(x+'_{n+1}='+N(r)+r'\frac{g(n+1)}{g(n)}'+x+'_n')+' と書ける。この形なら繰り返し代入した積の分子・分母を約分できる。',
            E(x+'_n&='+N(first)+L(power(num(r),nat()))+r'\frac{g(2)}{g(1)}\frac{g(3)}{g(2)}\cdots\frac{g(n)}{g(n-1)}'
                +r'\\&='+N(first)+L(power(num(r),nat()))+r'\frac{g(n)}{g(1)}')+'。中間の '+M('g(2),g(3),'+r'\ldots,g(n-1)')+' が順に打ち消し合う。',
            M('g(1)='+N(evaluate(g,0)))+' を代入すると '+M(x+'_n='+L(formula))+' である。'+M('n=1')+' の積は空積1とし、初項にも一致する。']
        # Avoid juxtaposing numeric factors in the displayed prefactor.
        steps[-2]=steps[-2].replace(N(first)+L(power(num(r),nat())),L(mul(num(first),power(num(r),nat()))))
        if reciprocal:
            steps += [s for s in route['steps'] if '元の分母は' in s][-1:]
            steps.append(M(r'a_n=1/v_n')+' に戻して '+M('a_n='+L(route['formula']))+' を得る。')
        return steps
    steps=original(ir,route)
    if kind=='paired-modes':
        p,q,z,w=[evaluate(x,0) for x in ir['matrix']]
        t=evaluate(c['weight'],0);g=c['scale']
        a,b=('x','y') if g!=num(1) else ('a','b')
        r,s=p+t*z,p-t*z
        detail='一次結合の重みは、両方の係数を同じ倍率にするために選ぶ。実際、'+E(
            N(p)+'+'+N(t)+r'\cdot('+N(z)+')&='+N(r)
            +r'\\'+N(q)+'+'+N(t)+r'\cdot('+N(w)+')&='+N(t*r)
            +r'\\'+N(p)+'-'+N(t)+r'\cdot('+N(z)+')&='+N(s)
            +r'\\'+N(q)+'-'+N(t)+r'\cdot('+N(w)+')&='+N(-t*s))+'。このため和の式は '+M('u_n')+' だけ、差の式は '+M('v_n')+' だけで表せる。付加項は和の側に集まり、差の側では消える。'
        pos=next(i for i,s0 in enumerate(steps) if '与式をそれぞれ加減' in s0)
        steps.insert(pos,detail)
        steps.append('定義を加えると '+M('u_n+v_n=2'+a+'_n')+'、引くと '+M('u_n-v_n='+coefficient_tex(2*t,b+'_n'))+'。したがって求めた式を代入し、'+E('a_n&='+L(route['formula'])+r'\\b_n&='+L(route['b_formula']))+' を得る。')
    elif kind=='pure-sum-difference':
        r=evaluate(ir['Q'],0);R=ir['R']
        from variety import previous_curve
        steps.insert(1,'差をとる2式を並べると '+E(
            'S_{n+1}&='+coefficient_tex(r,'S_n')+'+'+L(R)
            +r'\\S_n&='+coefficient_tex(r,'S_{n-1}')+'+'+L(previous_curve(R)))+'。下の式は '+M(r'n\ge2')+' で使える。辺々引くと '+M('a_{n+1}='+N(r)+'(S_n-S_{n-1})+('+L(R)+')-('+L(previous_curve(R))+')')+' となり、'+M('S_n-S_{n-1}=a_n')+' で部分和を消せる。')
    elif kind=='pure-partial-sum':
        from variety import previous_curve
        S=c['sum_formula'];prev=previous_curve(S)
        steps.insert(len(steps)-1,'添字を1つ戻す際は、'+M('n')+' を含む係数にも指数にも '+M('n-1')+' を代入する。したがって '+M('S_{n-1}='+L(prev))+'。これを '+M('S_n')+' から引けば、最初の '+M('n-1')+' 項が消えて第 '+M('n')+' 項だけが残る。')
    elif kind=='mixed-sum-relation':
        alpha=evaluate(c['alpha'],0);f=c['forcing']
        steps.insert(3,'未知の次項を左に集めると '+M(coefficient_tex(1-alpha,'a_{n+1}')+'='+coefficient_tex(-alpha,'a_n')+'+'+L(expand_polynomial(sub(shift(f),f))))+'。'+M(N(1-alpha))+ ' は零でないので、両辺をこれで割って次項の係数を1にする。')
    elif kind in {'normalized-second','sum-to-second'}:
        trace=route['derivation'][0]
        p,q=[evaluate(trace[k],0) for k in ('p','q')]
        if kind=='sum-to-second':
            alpha,beta=[evaluate(ir[k],0) for k in ('sum_alpha','sum_beta')]
            steps.insert(2,'総和の更新を展開すると '+E(
                'b_{n+2}&='+coefficient_tex(alpha,'b_{n+1}')+C(beta,'T_n')+C(beta,'b_{n+1}')
                +r'\\&='+coefficient_tex(alpha+beta,'b_{n+1}')+'+(b_{n+1}'+C(-alpha,'b_n')+')'
                +r'\\&='+coefficient_tex(p,'b_{n+1}')+C(q,'b_n'))+'。2行目で '+M(coefficient_tex(beta,'T_n')+'=b_{n+1}'+C(-alpha,'b_n'))+' を使っている。')
        else:
            g=scale(c['profile'])
            if g!=num(1):
                steps.insert(1,'3つの項を '+M('a_{n+j}=g(n+j)b_{n+j}')+' として代入し、'+M(L(mul(ir['P2'],shift(g,2))))+' で割る。次項と当該項の係数はそれぞれ '+E(
                    r'\frac{'+L(mul(ir['Q2'],shift(g)))+'}{'+L(mul(ir['P2'],shift(g,2)))+'}&='+N(p)
                    +r'\\\frac{'+L(mul(ir['R2'],g))+'}{'+L(mul(ir['P2'],shift(g,2)))+'}&='+N(q))+' となり、添字に依存しなくなる。')
    return steps
