"""Typed paired sequences and the two distinct meanings of summation problems."""
from fractions import Fraction
import copy
from algebra import prefix_polynomial
from expr import add, sub, mul, div, num, term, index, nat, power, shift, evaluate, polynomial, expand_polynomial, latex
from profiles import SCALES
from rules import normalize_recipe, RuleViolation

VARIETY_FAMILIES={'arithmetic','polynomial_difference','coupled_symmetric','coupled_weighted',
    'coupled_scaled','coupled_forced','pure_sum','pure_sum_scaled','sum_relation'}


def chain(core,blocks,config):
    previous='core'
    for i,b in enumerate(blocks,1): b.update(id=f'b{i}',input=previous);previous=b['id']
    return normalize_recipe({'schema_version':'0.2','rule_set_version':config['version'],
        'domain':{'index_start':1,'sequence_type':'rational'},'core':{'id':'core',**core},
        'blocks':blocks,'output':previous},config)


def variety_recipe(family,parameters,profile,config):
    r,c,d,s=(Fraction(parameters[x]) for x in ('r','c','d','s'))
    core={'kind':'geometric','parameters':{'ratio':num(r),'amplitude':num(d)}}
    blocks=[]
    if family in {'arithmetic','polynomial_difference'}:
        core={'kind':'constant','parameters':{'initial':num(d)}}
        f=num(c) if family=='arithmetic' else mul(num(c),SCALES[profile])
        blocks=[{'kind':'difference_polynomial','forcing':f,'profile':profile}]
    elif family.startswith('coupled_'):
        if family=='coupled_weighted' and c==1: raise RuleViolation('redundant_pair_weight')
        if r==s or not s or s==1 and c==0: raise RuleViolation('degenerate_pair')
        if family=='coupled_forced':
            h=num(c) if profile=='constant' else add(mul(num(-c),index()),num(-c/(r-1)))
            blocks.append({'kind':'index_add','value':h})
        blocks.append({'kind':'pair_mix','other_core':{'kind':'geometric','ratio':num(s),'initial':num(c)},
                       'weight':num(c if family=='coupled_weighted' else 1)})
        if family=='coupled_scaled': blocks.append({'kind':'index_scale','factor':SCALES[profile],'profile':profile})
    elif family in {'pure_sum','pure_sum_scaled'}:
        if family=='pure_sum':
            h=num(-d/r) if profile=='constant' else add(mul(num(c),index()),num(-d/r))
        else:
            if r==s: raise RuleViolation('repeated_root')
            blocks.append({'kind':'linear_combination','other_core':{'kind':'geometric','ratio':num(s),'initial':num(c)}})
            h=None
        if h is not None: blocks.append({'kind':'index_add','value':h})
        if family=='pure_sum_scaled': blocks.append({'kind':'index_scale','factor':SCALES[profile],'profile':profile})
        blocks.append({'kind':'partial_sum_encode'})
    else:
        h=num(c) if profile=='constant' else mul(num(c),index())
        blocks.extend([{'kind':'index_add','value':h},{'kind':'sum_relation_encode'}])
    return chain(core,blocks,config)


def truncated(recipe,blocks):
    return {**recipe,'blocks':copy.deepcopy(blocks),'output':blocks[-1]['id'] if blocks else 'core'}


def previous_curve(e):
    """Lower a geometric exponent by factoring 1/r, never using negative Nat powers."""
    if e['op']=='pow' and e['args'][1]==nat(): return div(e,e['args'][0])
    if 'args' in e:
        args=[previous_curve(x) for x in e['args']]
        return (add if e['op']=='add' else mul)(*args) if e['op'] in {'add','mul'} else {**e,'args':args}
    return shift(e,-1)


def compile_variety(recipe,config):
    from compiler import compile_blocks
    blocks=recipe['blocks'];terminal=next((b for b in blocks if b['kind'] in {'pair_mix','partial_sum_encode','sum_relation_encode','difference_polynomial'}),None)
    kind=terminal['kind']
    if kind=='difference_polynomial':
        initial=recipe['core']['parameters']['initial'];forcing=terminal['forcing']
        formula=prefix_polynomial(forcing,evaluate(initial,0))
        return {'formula':formula,'initials':[initial],'lhs':term(1),'rhs':add(term(),forcing),
                'P':num(1),'Q':num(1),'R':forcing,'step':add(term(),forcing),'underlying':formula,
                'reciprocal':False,'second_order':False,'difference_polynomial':True}
    before=blocks[:blocks.index(terminal)]
    base=compile_blocks(truncated(recipe,before),config)
    if kind=='pair_mix':
        other=terminal['other_core'];r=evaluate(base['Q'],0);s=evaluate(other['ratio'],0);t=evaluate(terminal['weight'],0)
        g=next((b['factor'] for b in blocks[blocks.index(terminal)+1:] if b['kind']=='index_scale'),num(1))
        u=base['formula'];v=mul(other['initial'],power(other['ratio'],nat()))
        a=mul(g,num(Fraction(1,2)),add(u,v));b=mul(g,num(Fraction(1,2)/t),sub(u,v))
        p,q,z=num((r+s)/2),num(t*(r-s)/2),num((r-s)/(2*t))
        forcing=base['R'];lead=g;following=shift(g)
        rhs=add(mul(following,add(mul(p,term()),mul(q,term(variable='b')))),mul(g,following,num(Fraction(1,2)),forcing))
        brhs=add(mul(following,add(mul(z,term()),mul(p,term(variable='b')))),mul(g,following,num(Fraction(1,2)/t),forcing))
        return {'shape':'system','formula':a,'b_formula':b,'initials':[num(evaluate(a,0))],'b_initial':num(evaluate(b,0)),
            'lhs':mul(lead,term(1)),'rhs':rhs,'b_lhs':mul(lead,term(1,'b')),'b_rhs':brhs,
            'system_scale':g,'matrix':[p,q,z,p],'system_forcing':forcing,'weight':num(t),
            'P':lead,'Q':p,'R':forcing,'underlying':a,'reciprocal':False,'second_order':False}
    if kind=='partial_sum_encode':
        S=base['formula'];prev=previous_curve(S);formula=sub(S,prev)
        if evaluate(prev,0)!=0: raise RuleViolation('partial_sum_boundary')
        if base['second_order']:
            lhs=mul(base['P2'],{'op':'sum_term','offset':2})
            rhs=add(mul(base['Q2'],{'op':'sum_term','offset':1}),mul(base['R2'],{'op':'sum_term','offset':0}))
        else:
            lhs=mul(base['P'],{'op':'sum_term','offset':1});rhs=add(mul(base['Q'],{'op':'sum_term','offset':0}),base['R'])
        return {**base,'shape':'pure_sum','formula':formula,'sum_formula':S,'initials':[num(evaluate(S,k)) for k in range(2 if base['second_order'] else 1)],
            'lhs':lhs,'rhs':rhs,
            'underlying':formula}
    # The relation uses S_n and a_n together; it is not labelled pure summation.
    r=evaluate(recipe['core']['parameters']['ratio'],0);d=recipe['core']['parameters']['amplitude']
    h=before[-1]['value'];poly_sum=shift(prefix_polynomial(h,0))
    S=add(mul(num(1/(r-1)),d,sub(power(num(r),nat(1)),num(1))),poly_sum)
    alpha=num(r/(r-1));f=expand_polynomial(sub(poly_sum,add(mul(alpha,h),mul(num(1/(r-1)),d))))
    return {**base,'shape':'sum_relation','sum_formula':S,'sum_alpha':alpha,'sum_forcing':f,
        'lhs':{'op':'sum_term','offset':0},'rhs':add(mul(alpha,term()),f)}


def finish_route(formula,operations,certificate,values=(),discovery=1,b_formula=None):
    return {'title':'','hint':'','steps':[],'formula':formula,'operations':operations,'certificate':certificate,
        'discovery':discovery,'domain':0,'intermediate_values':[num(x) for x in values],
        'derivation':[],'complete':True,**({'b_formula':b_formula} if b_formula else {})}


def variety_routes(ir,config):
    from solve import find_routes
    shape=ir.get('shape')
    if not shape:
        f=ir['R'];initial=evaluate(ir['initials'][0],0);degree=max(polynomial(f),default=0)
        a=prefix_polynomial(f,initial)
        operations=['difference_sum']+(['evaluate_sum'] if degree<2 else ['evaluate_quadratic_sum'])
        out=finish_route(a,operations,{'kind':'polynomial-difference','forcing':f},[initial,*polynomial(f).values()],0)
        out['derivation']=[{'variable':'a','formula':a,'P':num(1),'Q':num(1),'R':f,'initials':[num(initial)],'source':None}]
        return [out]
    if shape=='system':
        p,q,z,w=[evaluate(x,0) for x in ir['matrix']]
        t=next((Fraction(i) for i in (1,2,3) if z*i*i==q and p==w),None)
        if t is None: return []
        g=ir['system_scale'];a1=evaluate(ir['initials'][0],0)/evaluate(g,0);b1=evaluate(ir['b_initial'],0)/evaluate(g,0)
        r,s=p+q/t,p-q/t
        def scalar(r,initial,F):
            return find_routes({'P':num(1),'Q':num(r),'R':F,'initials':[num(initial)],'reciprocal':False,'second_order':False},config)
        u_routes=scalar(r,a1+t*b1,ir['system_forcing']);v_routes=scalar(s,a1-t*b1,num(0))
        routes=[]
        for u in u_routes:
            for v in v_routes:
                a=mul(g,num(Fraction(1,2)),add(u['formula'],v['formula']));b=mul(g,num(Fraction(1,2)/t),sub(u['formula'],v['formula']))
                ops=(['index_scale'] if g!=num(1) else [])+['split_pair']+u['operations']+['recover_pair']
                # The second independent geometric mode is required, but is evaluated in parallel.
                route=finish_route(a,ops,{'kind':'paired-modes','weight':num(t),'scale':g,'u':u,'v':v},
                    [p,q,z,w,a1,b1,r,s],1+int(g!=num(1))+int(t!=1)+u['discovery'],b)
                routes.append(route)
        return routes
    if shape=='sum_relation':
        alpha=evaluate(ir['sum_alpha'],0);f=ir['sum_forcing']
        if alpha==1: return []
        R=mul(num(1/(alpha-1)),sub(f,shift(f)))
        base={'P':num(1),'Q':num(alpha/(alpha-1)),'R':expand_polynomial(R),'initials':ir['initials'],'reciprocal':False,'second_order':False}
        routes=find_routes(base,config)
        for route in routes:
            scalar=copy.deepcopy(route)
            route['operations']=['eliminate_sum']+route['operations'];route['discovery']+=1
            route['certificate']={'kind':'mixed-sum-relation','scalar':scalar,'forcing':f,'alpha':num(alpha)}
        return routes
    # Solve S_n as a sequence, then recover a_n from adjacent partial sums.
    if ir['second_order']:
        base={**ir,'shape':'linear_second'}
        routes=find_routes(base,config)
        out=[]
        for scalar in routes:
            S=scalar['formula'];a=sub(S,previous_curve(S))
            if evaluate(previous_curve(S),0)!=0: continue
            out.append(finish_route(a,scalar['operations']+['recover_sum'],
                {'kind':'pure-partial-sum','scale':num(1),'scalar':scalar,'sum_formula':S,'second_order':True},
                [evaluate(x,0) for x in ir['initials']],scalar['discovery']+1))
        return out
    P,Q,R=ir['P'],ir['Q'],ir['R'];a1=evaluate(ir['initials'][0],0)
    routes=[]
    for name,g in [('identity',num(1)),*[(name,SCALES[name]) for name in config['scale_profiles']]]:
        from solve import proportional
        from expr import poly_mul, poly_divmod, from_polynomial
        try:
            r=proportional(poly_mul(polynomial(Q),polynomial(g)),poly_mul(polynomial(P),polynomial(shift(g))))
            quotient,remainder=poly_divmod(polynomial(R),poly_mul(polynomial(P),polynomial(shift(g))))
        except ValueError: continue
        if r is None or remainder: continue
        candidates=find_routes({'P':num(1),'Q':num(r),'R':from_polynomial(quotient),'initials':[num(a1/evaluate(g,0))],
            'reciprocal':False,'second_order':False},config)
        for scalar in candidates:
            S=mul(g,scalar['formula']);a=sub(S,previous_curve(S))
            if evaluate(previous_curve(S),0)!=0: continue
            ops=(['index_scale'] if name!='identity' else [])+scalar['operations']+['recover_sum']
            route=finish_route(a,ops,{'kind':'pure-partial-sum','scale':g,'scalar':scalar,'sum_formula':S},
                [a1,r],1+int(name!='identity')+scalar['discovery'])
            routes.append(route)
    # A second registered route eliminates S directly; this often shortens
    # constant-forcing cases, and is used when assigning the level.
    if P==num(1) and Q['op']=='rational':
        r=evaluate(Q,0);forcing=expand_polynomial(sub(R,shift(R,-1)))
        initial=ir['initials'][0]
        scalar_ir={'P':num(1),'Q':Q,'R':forcing,'initials':[initial],'reciprocal':False,'second_order':False}
        for scalar in find_routes(scalar_ir,config):
            a2=(r-1)*evaluate(initial,0)+evaluate(R,0)
            if evaluate(scalar['formula'],1)!=a2: continue
            routes.append(finish_route(scalar['formula'],['eliminate_sum']+scalar['operations'],
                {'kind':'pure-sum-difference','scalar':scalar,'scalar_ir':scalar_ir,'a2':num(a2)},
                [evaluate(initial,0),a2,r],scalar['discovery']+1))
    return routes


def check_variety_route(ir,route,n,terms):
    cert=route['certificate'];kind=cert['kind']
    if kind=='paired-modes':
        assert all(evaluate(route['b_formula'],k)==evaluate(ir['b_formula'],k) for k in (n,n+1))
        t=evaluate(cert['weight'],0);g=cert['scale']
        u=cert['u']['formula'];v=cert['v']['formula']
        a=evaluate(route['formula'],n)/evaluate(g,n);b=evaluate(route['b_formula'],n)/evaluate(g,n)
        assert a+t*b==evaluate(u,n) and a-t*b==evaluate(v,n)
    elif kind=='pure-partial-sum':
        assert sum((evaluate(route['formula'],k) for k in range(n+1)),Fraction(0))==evaluate(cert['sum_formula'],n)
    elif kind=='mixed-sum-relation':
        assert sum((evaluate(route['formula'],k) for k in range(n+1)),Fraction(0))==evaluate(cert['alpha'],n)*evaluate(route['formula'],n)+evaluate(cert['forcing'],n)
