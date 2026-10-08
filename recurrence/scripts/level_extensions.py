"""Simple fractional transformations, factorial products and additive second differences."""
import copy
from fractions import Fraction
from math import factorial,isqrt
from expr import add,sub,mul,div,num,nat,nat_const,index,term,power,evaluate,latex,lean,polynomial,expand_polynomial
from rules import normalize_recipe,RuleViolation

FAMILIES={'mobius','factorial_ratio','forced_second','arithmetic_difference'}
FACTOR_PROFILES={'monomial':(0,), 'monomial_squared':(0,0),'shifted_1':(1,),'shifted_2':(2,),
                 'pair_01':(0,1),'pair_02':(0,2),'pair_12':(1,2)}
def factorial_expr(offset):return {'op':'factorial','args':[nat(offset)]}

def recipe(family,parameters,profile,config):
 r,c,d,s=(Fraction(parameters[x]) for x in ('r','c','d','s'))
 if family=='mobius':
  core={'kind':'affine_fixed_point','parameters':{'ratio':num(r),'fixed_point':num(c),'amplitude':num(d),'constant_term':num((1-r)*c)}}
  blocks=[{'kind':'mobius_encode','shift':num(s)}]
 elif family=='factorial_ratio':
  core={'kind':'constant','parameters':{'initial':num(d)}}
  blocks=[{'kind':'factorial_product','ratio':num(r),'offsets':list(FACTOR_PROFILES[profile])}]
 elif family=='arithmetic_difference':
  core={'kind':'constant','parameters':{'initial':num(d)}}
  blocks=[{'kind':'second_difference','first_difference':num(s),'increment':num(c)}]
 else:
  if r==s or r==1 or s==1:raise RuleViolation('degenerate_forced_second')
  core={'kind':'geometric','parameters':{'ratio':num(r),'amplitude':num(d)}}
  blocks=[{'kind':'linear_combination','other_core':{'kind':'geometric','ratio':num(s),'initial':num(c)}}, {'kind':'add_constant','value':num(c)}]
 previous='core'
 for i,b in enumerate(blocks,1):b.update(id=f'b{i}',input=previous);previous=b['id']
 return normalize_recipe({'schema_version':'0.2','rule_set_version':config['version'],'domain':{'index_start':1,'sequence_type':'rational'},'core':{'id':'core',**core},'blocks':blocks,'output':previous},config)

def compile_extension(recipe):
 params=recipe['core']['parameters'];b=recipe['blocks'][-1];kind=b['kind']
 P,Q,R=num(1),num(1),num(0)
 if kind=='mobius_encode':
  ratio=evaluate(params['ratio'],0);c=evaluate(params['fixed_point'],0);h=evaluate(b['shift'],0)
  base=add(params['fixed_point'],mul(params['amplitude'],power(params['ratio'],nat())))
  R=num((1-ratio)*c);Q=params['ratio'];formula=add(num(h),div(num(1),base))
  m=[add(num(1),mul(num(h),R)),num(h*ratio-h-h*h*evaluate(R,0)),R,num(ratio-h*evaluate(R,0))]
  if not evaluate(m[0],0) or not evaluate(m[1],0):raise RuleViolation('degenerate_fraction_numerator')
  rhs=div(add(mul(m[0],term()),m[1]),add(mul(m[2],term()),m[3]))
  return {'shape':'mobius','formula':formula,'initials':[num(evaluate(formula,0))],'lhs':term(1),'rhs':rhs,'step':rhs,
          'P':P,'Q':Q,'R':R,'mobius_coefficients':m,'mobius_shift':num(h),'underlying':base,'reciprocal':True,'second_order':False}
 if kind=='factorial_product':
  offsets=b['offsets'];r=b['ratio'];first=params['initial']
  factor=mul(r,*(add(index(),num(t)) for t in offsets))
  formula=mul(first,power(r,nat()),*(div(factorial_expr(t),num(factorial(t))) for t in offsets))
  return {'shape':'factorial_ratio','formula':formula,'initials':[first],'lhs':term(1),'rhs':mul(factor,term()),'step':mul(factor,term()),
          'P':P,'Q':factor,'R':R,'underlying':formula,'reciprocal':False,'second_order':False}
 first=params['initial'];diff=b['first_difference'];inc=b['increment']
 formula=add(first,mul(diff,nat()),div(mul(inc,nat(),sub(nat(),nat_const(1))),num(2)))
 return {'shape':'linear_second','formula':formula,'initials':[first,add(first,diff)],'lhs':term(2),'rhs':add(mul(num(2),term(1)),mul(num(-1),term()),inc),
         'P':P,'Q':Q,'R':R,'P2':P,'Q2':num(2),'R2':num(-1),'F2':inc,'underlying':formula,'reciprocal':False,'second_order':True}

def routes(ir,config):
 from solve import find_routes,finish
 from advanced_solve import normalized_seconds
 shape=ir.get('shape')
 if shape=='mobius':
  p,q,r,s=[evaluate(x,0) for x in ir['mobius_coefficients']];a1=evaluate(ir['initials'][0],0)
  delta=(s-p)**2+4*r*q
  if delta<0:return []
  u,v=isqrt(delta.numerator),isqrt(delta.denominator)
  if u*u!=delta.numerator or v*v!=delta.denominator:return []
  result=[]
  for h in sorted({(-(s-p)+sign*Fraction(u,v))/(2*r) for sign in (1,-1)}):
   P=p-h*r;Q=r*h+s
   if P<=0 or Q<=0 or a1<=h:continue
   base={'P':num(P),'Q':num(Q),'R':num(r),'initials':[num(1/(a1-h))],'reciprocal':False,'second_order':False}
   for scalar in find_routes(base,config):
    formula=add(num(h),div(num(1),scalar['formula']))
    derivation=[{'variable':'v','formula':scalar['formula'],'P':num(P),'Q':num(Q),'R':num(r),'initials':base['initials'],'source':'a','transform':div(num(1),sub(term(),num(h)))}]
    for d in copy.deepcopy(scalar['derivation']):
     if d.get('source'):d['source']='v' if d['source']=='a' else 'w'
     d['variable']='w' if d['variable']=='b' else d['variable'];derivation.append(d)
    route=finish({**ir,'reciprocal':False},'不動点からの差の逆数をとる',['fixed_point','reciprocal']+scalar['operations'],
      '分子と分母が一次式なので、次項との差をまとめられる不動点を探す。',[],formula,2,
      [p,q,r,s,h,P,Q,a1],{'kind':'mobius-shift','shift':num(h),'scalar':scalar,'scalar_ir':base},derivation)
    route['domain']=1;result.append(route)
  return result
 if shape=='factorial_ratio':
  coeff=polynomial(ir['Q']);initial=evaluate(ir['initials'][0],0);r=coeff[max(coeff)]
  for offsets in FACTOR_PROFILES.values():
   factor=mul(num(r),*(add(index(),num(t)) for t in offsets))
   if polynomial(factor)!=coeff:continue
   formula=mul(num(initial),power(num(r),nat()),*(div(factorial_expr(t),num(factorial(t))) for t in offsets))
   route=finish(ir,'階比を掛け合わせて階乗にまとめる',['ratio_product','evaluate_product'],
      '次項と前項の比を初項から掛け合わせ、連続する整数の積を階乗で表す。',[],formula,1,
      [r,initial],{'kind':'factorial-product','ratio':num(r),'offsets':list(offsets)},
      [{'variable':'a','formula':formula,'P':num(1),'Q':factor,'R':num(0),'initials':ir['initials'],'source':None}])
   return [route]
  return []
 P,Q,R,F=[evaluate(ir.get(k,num(0)),0) for k in ('P2','Q2','R2','F2')]
 first,second=[evaluate(x,0) for x in ir['initials']]
 if Q==2*P and R==-P:
  increment=F/P;diff=second-first
  b=add(num(diff),mul(num(increment),sub(index(),num(1))))
  formula=add(num(first),mul(num(diff),nat()),div(mul(num(increment),nat(),sub(nat(),nat_const(1))),num(2)))
  return [finish(ir,'階差を等差数列として解く',['difference','difference_sum','evaluate_sum'],
      '隣接する項の差でまとめると、その階差数列が等差数列になる。',[],formula,1,
      [first,second,increment],{'kind':'arithmetic-difference','increment':num(increment),'first_difference':num(diff)},
      [{'variable':'b','formula':b,'P':num(1),'Q':num(1),'R':num(increment),'initials':[num(diff)],'source':'a','transform':sub(term(1),term())}])]
 if P-Q-R==0:return []
 h=F/(P-Q-R)
 base={**ir,'F2':num(0),'initials':[num(first-h),num(second-h)]}
 result=[]
 for scalar in normalized_seconds(base,config):
  derivation=copy.deepcopy(scalar['derivation']);derivation[0]['transform']=sub(term(),num(h))
  route=finish(ir,'定数項を消して3項間を解く',['shift']+scalar['operations'],
    '一定の値を引いて定数項を消し、斉次の3項間漸化式に帰着させる。',[],add(num(h),scalar['formula']),scalar['discovery']+1,
    [h,first,second,P,Q,R,F],{'kind':'forced-second','shift':num(h),'scalar':scalar,'scalar_ir':base},derivation)
  result.append(route)
 return result

def exposition(ir,route):
 from exposition import M,L,N,E,scalar_exposition,explain_route
 c=route['certificate'];kind=c['kind']
 if kind=='mobius-shift':
  h=c['shift'];base=c['scalar_ir'];v1=base['initials'][0]
  steps=['分子と分母が一次式なので、まず '+M('x= '+ir_tex(ir,'x'))+' を満たす不動点を求める。このうち '+M('x='+L(h))+' に着目する。',
    M('v_n='+r'\frac{1}{a_n-'+L(h)+'}')+' とおく。与式から '+M('a_{n+1}-'+L(h))+' を計算して逆数をとると、',
    E(L(base['P'])+'v_{n+1}&='+L(base['Q'])+'v_n'+('+' if evaluate(base['R'],0)>=0 else '')+L(base['R'])),
    '初期条件は '+M('v_1='+L(v1))+' である。']
  steps+=scalar_exposition(base,c['scalar'],'v')
  steps+=['元の数列は '+M('a_n='+L(h)+r'+\frac1{v_n}')+' である。得られた '+M('v_n')+' はすべての '+M(r'n\ge1')+' で正なので、この置換は定義できる。',
          '元の分母は '+M(L(ir['mobius_coefficients'][2])+'a_n+'+L(ir['mobius_coefficients'][3]))+' であり、'+M(L(base['P'])+r'\frac{v_{n+1}}{v_n}')+' に等しいので、すべての項で零にならない。']
  return steps
 if kind=='factorial-product':
  r=c['ratio'];offsets=c['offsets'];first=ir['initials'][0]
  factors=''.join(r'\prod_{k=1}^{n-1}(k'+('+'+str(t) if t else '')+')' for t in offsets)
  steps=['与式から '+M(r'\frac{a_{n+1}}{a_n}='+L(ir['Q']))+' である。'+M(r'n\ge2')+' のとき、これを '+M(r'k=1,2,\ldots,n-1')+' について掛け合わせると、',
         M(r'\frac{a_n}{a_1}='+L(power(r,nat()))+factors)+' を得る。左辺では途中の項が相殺される。']
  for t in sorted(set(offsets)):
   steps.append(M(r'\prod_{k=1}^{n-1}(k'+('+'+str(t) if t else '')+')='+L(div(factorial_expr(t),num(factorial(t)))))+' なので、初項を代入して一般項が得られる。')
  steps.append(M('n=1')+' のときも '+M('0!=1')+' を用いると、初項と一致する。')
  return steps
 if kind=='arithmetic-difference':
  diff=c['first_difference'];inc=c['increment']
  return ['与式を '+M('a_{n+2}-a_{n+1}=(a_{n+1}-a_n)+'+L(inc))+' とまとめ、'+M('b_n=a_{n+1}-a_n')+' とおく。',
          M('b_{n+1}=b_n+'+L(inc))+ '、'+M('b_1='+L(diff))+' より、階差数列は等差数列である。したがって '+M('b_n='+L(add(diff,mul(inc,sub(index(),num(1))))))+' を得る。',
          M(r'n\ge2')+' のとき、階差を足し合わせると '+M(r'a_n=a_1+\sum_{k=1}^{n-1}b_k')+' である。等差数列の和を計算して一般項を求める。',
          M('n=1')+' のときも初項と一致する。']
 h=c['shift'];base=c['scalar_ir'];scalar=c['scalar']
 # The inner second-order exposition uses a for its input; rename it to b and
 # rename its auxiliary b to c before substituting into the outer sequence.
 inner=explain_route(base,scalar)
 import re
 inner=[re.sub(r'\ba_n\b','b_n',s).replace('a_{','b_{') for s in inner]
 inner=[s for s in inner if 'b_n=b_{n}' not in s and not s.startswith('与式に代入して整理すると')]
 return ['定数項を打ち消すため、一定の値 '+M('x='+L(h))+' を与式に代入する。この値を引き、'+M('b_n=a_n-'+L(h))+' とおく。',
         M('b_{n+2}='+L(base['Q2'])+'b_{n+1}'+('+' if evaluate(base['R2'],0)>=0 else '')+L(base['R2'])+'b_n')+' となり、初期条件は '+M('b_1='+L(base['initials'][0])+r',\quad b_2='+L(base['initials'][1]))+' である。',*inner,
         M('a_n=b_n+'+L(h))+' に戻せば、元の数列の一般項が求まる。']

def ir_tex(ir,variable):
 return latex(ir['rhs']).replace('a_{n}',variable)


def proofs(p):
 name,ir=p['id'],p['ir'];kind=ir['shape'];init=lean(ir['initials'][0])
 if kind=='factorial_ratio':
  Q=lean(ir['Q']);step=f'(fun n x => {Q} * x)';cert=f'FirstCertificate {name} {init} {step}'
  lines=[f'def {name} (n : ℕ) : ℚ := {lean(ir["formula"])}',f'theorem {name}_valid : {cert} := by','  constructor',f'  · norm_num [{name}]','  · intro n',
   f'    simp only [{name}, Nat.add_assoc, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]', '    norm_num <;> ring',
   f'theorem {name}_unique (a : ℕ → ℚ) (ha : FirstCertificate a {init} {step}) :',f'    ∀ n, a n = {name} n := first_unique {name}_valid ha']
 else:
  from generate import proofs as original_proofs
  base={**p,'id':name+'_base','ir':{'formula':ir['underlying'],'underlying':ir['underlying'],'initials':[num(evaluate(ir['underlying'],0))],
     'P':ir['P'],'Q':ir['Q'],'R':ir['R'],'reciprocal':False,'second_order':False}}
  lines=[original_proofs(base),f'def {name} (n : ℕ) : ℚ := {lean(ir["formula"])}']
  h=lean(ir['mobius_shift']);P,Q,R=[lean(ir[k]) for k in ('P','Q','R')];m=[lean(x) for x in ir['mobius_coefficients']]
  step=f'(fun n x => ({m[0]} * x + {m[1]}) / ({m[2]} * x + {m[3]}))';cert=f'FirstCertificate {name} {init} {step}'
  lines += [f'theorem {name}_positive (n : ℕ) : 0 < {name}_base n := by unfold {name}_base; positivity',
   f'theorem {name}_valid : {cert} := by',f'  have hv := reciprocal_certificate {name}_base_valid {name}_positive (by intro n; positivity)',
   f'  have hs := shifted_fraction_certificate hv.1 hv.2.1 {h}',
   f'  have heq : {name} = (fun n => 1 / {name}_base n + {h}) := by',f'    funext n; simp [{name}, {name}_base] <;> ring',
   '  rw [heq]','  convert hs using 1 <;> norm_num <;> ring',
   f'theorem {name}_domain (n : ℕ) : {m[2]} * {name} n + {m[3]} ≠ 0 ∧ {name} n - {h} ≠ 0 := by',
   f'  have hv := reciprocal_certificate {name}_base_valid {name}_positive (by intro n; positivity)',
   f'  have heq : {name} n = 1 / {name}_base n + {h} := by simp [{name}, {name}_base] <;> ring',
   '  rw [heq]','  constructor',
   f'  · convert hv.2.1 n using 1 <;> norm_num <;> ring',
   f'  · simpa using hv.2.2 n',
   f'theorem {name}_unique (a : ℕ → ℚ) (ha : FirstCertificate a {init} {step}) :',f'    ∀ n, a n = {name} n := first_unique {name}_valid ha',f'#print axioms {name}_domain']
 lines += [f'#print axioms {name}_valid',f'#print axioms {name}_unique']
 return '\n'.join(lines)+'\n'
