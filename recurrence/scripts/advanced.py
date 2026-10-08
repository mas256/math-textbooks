"""Typed compositions for non-fractional, multi-step school exercises."""
from algebra import geometric_antidifference, natural_polynomial, prefix_polynomial
from expr import add, div, evaluate, expand_polynomial, index, mul, nat, nat_const, num, power, reduce_linear_coefficients, shift, sub, term

ADVANCED_BLOCKS={'repeated_factor','difference_lift','sum_encode','cumulative_sum','power_sequence'}


def quotient(a,b):
    return a if b==num(1) else div(a,b)


def compile_advanced(recipe):
    core=recipe['core']; params=core['parameters']
    assert core['kind'] in {'constant','geometric'}
    ratio=evaluate(params.get('ratio',num(1)),0)
    amplitude=evaluate(params.get('amplitude',params.get('initial')),0)
    formula=num(amplitude) if core['kind']=='constant' else mul(num(amplitude),power(num(ratio),nat()))
    P,Q,R=num(1),num(ratio),num(0)
    P2,Q2,R2=num(1),num(0),num(0)
    scale=num(1); underlying=formula
    second=False; sums=[]; forcing=None; shape='linear_second'
    p=q=None
    for block in recipe['blocks']:
        assert shape=='linear_second', 'No block follows a terminal sum/power statement'
        kind=block['kind']
        if kind=='linear_combination':
            assert not second and not sums and scale==num(1)
            other=block['other_core']; s=evaluate(other['ratio'],0)
            assert s!=ratio
            formula=add(formula,mul(other['initial'],power(num(s),nat())))
            p,q=num(ratio+s),num(-ratio*s)
            P2,Q2,R2=num(1),p,q
            second=True; underlying=formula
        elif kind=='repeated_factor':
            assert not second and not sums and core['kind']=='geometric' and scale==num(1)
            formula=mul(add(num(amplitude),mul(block['slope'],sub(index(),num(1)))),power(num(ratio),nat()))
            p,q=num(2*ratio),num(-ratio*ratio)
            P2,Q2,R2=num(1),p,q
            second=True; underlying=formula
        elif kind=='index_scale':
            assert not sums
            factor=block['factor']
            if second:
                if factor['op']=='div' and factor['args'][0]==num(1):
                    g=factor['args'][1]
                    P2,Q2,R2=mul(P2,shift(g,2)),mul(Q2,shift(g)),mul(R2,g)
                else:
                    P2,Q2,R2=mul(P2,factor,shift(factor)),mul(Q2,factor,shift(factor,2)),mul(R2,shift(factor),shift(factor,2))
            elif factor['op']=='div' and factor['args'][0]==num(1):
                assert P==num(1)
                g=factor['args'][1];P,Q=shift(g),mul(Q,g)
            else:
                P,Q,R=mul(P,factor),mul(Q,shift(factor)),mul(R,factor,shift(factor))
            scale=mul(scale,factor);formula=mul(factor,formula)
        elif kind=='difference_lift':
            assert not second and not sums and R==num(0) and ratio!=1
            initial=evaluate(block['initial'],0)
            H=geometric_antidifference(mul(num(amplitude),scale),ratio)
            if initial==evaluate(H,0):
                from rules import RuleViolation
                raise RuleViolation('degenerate_difference_lift')
            formula=add(num(initial-evaluate(H,0)),mul(H,power(num(ratio),nat())))
            P2,Q2,R2=P,expand_polynomial(add(P,Q)),mul(num(-1),Q)
            second=True;underlying=formula
            p=q=None
        elif kind=='sum_encode':
            assert second and p is not None and not sums
            alpha,beta=num(-evaluate(q,0)),num(evaluate(p,0)+evaluate(q,0)-1)
            assert evaluate(underlying,1)==evaluate(add(alpha,beta),0)*evaluate(underlying,0), 'Incompatible sum boundary'
            shape='weighted_sum'
            body=quotient(term(),scale)
            summation={'op':'prefix_sum','args':[body]}
            lhs=term(1)
            rhs=mul(shift(scale),add(mul(alpha,body),mul(beta,summation)))
        elif kind=='cumulative_sum':
            assert not second and len(sums)<2
            if not sums: forcing=formula
            sums.append(formula)
            formula=prefix_polynomial(formula,evaluate(block['initial'],0))
        elif kind=='power_sequence':
            assert not second and len(sums)==2 and block['base']['op']=='rational'
            assert evaluate(block['base'],0)>1
            try:
                exponent=natural_polynomial(formula)
                increment=natural_polynomial(forcing)
            except AssertionError as e:
                from rules import RuleViolation
                raise RuleViolation('unregistered_natural_exponent') from e
            base=block['base'];formula=power(base,exponent)
            lhs=mul(term(2),term())
            rhs=mul(power(base,increment),power(term(1),nat_const(2)))
            shape='power_second';second=True
        else: raise ValueError('Unsupported advanced composition: '+kind)
    assert second
    initials=[num(evaluate(formula,0)),num(evaluate(formula,1))]
    if shape=='linear_second':
        P2,Q2,R2=reduce_linear_coefficients(P2,Q2,R2)
        lhs=mul(P2,term(2));rhs=add(mul(Q2,term(1)),mul(R2,term()))
    ir={'formula':formula,'initials':initials[:1] if shape=='weighted_sum' else initials,
        'lhs':lhs,'rhs':rhs,'step':None,'P':num(1),'Q':num(1),'R':num(0),
        'underlying':formula,'reciprocal':False,'second_order':True,'shape':shape}
    if shape=='linear_second': ir.update(P2=P2,Q2=Q2,R2=R2)
    elif shape=='weighted_sum': ir.update(sum_scale=scale,sum_alpha=alpha,sum_beta=beta,sum_base=underlying,p=p,q=q)
    else: ir.update(power_base=base,power_increment=increment,power_exponent=exponent)
    return ir
