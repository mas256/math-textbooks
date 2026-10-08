"""Lean output from the same advanced IR used for statements and exact checks."""
import re

from expr import evaluate, lean, num
from scoring import walk


def ring_step(name,formula):
    denominators={lean(x['args'][1]) for x in walk(formula) if x['op']=='div'}
    lines=[]
    for i,den in enumerate(sorted(denominators)):
        lines.extend(f'    have h{offset}_{i} : {re.sub(r"\bn\b", "(n + "+str(offset)+")", den) if offset else den} ≠ 0 := by positivity' for offset in (0,1,2))
    lines.append(f'    simp only [{name}, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *')
    if denominators:
        facts=', '.join(f'h{o}_{i}' for i in range(len(denominators)) for o in (0,1,2))
        lines.append(f'    field_simp [{facts}] <;> ring')
    else: lines.append('    ring')
    return lines


def advanced_proofs(problem):
    name,ir=problem['id'],problem['ir'];shape=ir['shape']
    init=lean(ir['initials'][0])
    lines=[f'def {name} (n : ℕ) : ℚ := {lean(ir["formula"])}']
    if shape=='linear_second':
        second=lean(ir['initials'][1])
        P,Q,R=[lean(ir[k]) for k in ('P2','Q2','R2')]
        F=lean(ir.get('F2',num(0)))
        forcing=f' + {F}' if ir.get('F2',num(0))!=num(0) else ''
        step=f'(fun n x y => ({Q} * y + {R} * x{forcing}) / {P})'
        cert=f'GeneralSecondCertificate {name} {init} {second} {step}'
        if ir.get('F2',num(0))!=num(0):
            lines += [f'theorem {name}_valid : {cert} := by','  constructor',f'  · norm_num [{name}]',f'  · norm_num [{name}]','  · intro n',f'    apply (eq_div_iff (show {P} ≠ 0 by positivity)).2',*ring_step(name,ir['formula']),f'theorem {name}_unique (a : ℕ → ℚ) (ha : GeneralSecondCertificate a {init} {second} {step}) :',f'    ∀ n, a n = {name} n := general_second_unique {name}_valid ha']
            lines += [f'#print axioms {name}_valid',f'#print axioms {name}_unique']
            return '\n'.join(lines)+'\n'
        lines += [f'theorem {name}_valid : {cert} := by',
                  f'  apply linear_second_certificate {name} {init} {second} (fun n => {P}) (fun n => {Q}) (fun n => {R})',
                  f'  · norm_num [{name}]',f'  · norm_num [{name}]','  · intro n; positivity','  · intro n',
                  *ring_step(name,ir['formula'])]
        lines += [f'theorem {name}_unique (a : ℕ → ℚ) (hi : a 0 = {init}) (hj : a 1 = {second})',
                  f'    (ha : ∀ n : ℕ, {P} * a (n + 2) = {Q} * a (n + 1) + {R} * a n) :',
                  f'    ∀ n, a n = {name} n := by',f'  apply general_second_unique {name}_valid',
                  f'  exact linear_second_certificate a {init} {second} (fun n => {P}) (fun n => {Q}) (fun n => {R}) hi hj (by intro n; positivity) ha']
    elif shape=='weighted_sum':
        base=name+'_base';g=lean(ir['sum_scale']);alpha,beta=lean(ir['sum_alpha']),lean(ir['sum_beta'])
        first,second=[lean(num(evaluate(ir['sum_base'],k))) for k in (0,1)]
        p,q=lean(ir['p']),lean(ir['q'])
        gfn=f'(fun n : ℕ => {g})'
        cert=f'WeightedSumCertificate {name} {init} {gfn} {alpha} {beta}'
        lines += [f'def {base} (n : ℕ) : ℚ := {lean(ir["sum_base"])}',
                  f'theorem {base}_valid : SecondCertificate {base} {first} {second} {p} {q} := by',
                  '  constructor',f'  · norm_num [{base}]',f'  · norm_num [{base}]','  · intro n',*ring_step(base,ir['sum_base']),
                  f'theorem {name}_valid : {cert} := by',
                  f'  apply weighted_sum_from_second {name} {base} {gfn} {init} {first} {second} {alpha} {beta}',
                  f'  · convert {base}_valid using 1 <;> norm_num',
                  '  · norm_num','  · intro n; positivity',
                  f'  · intro n; simp only [{name}, {base}] <;> ring',
                  f'  · norm_num [{name}]',
                  f'theorem {name}_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a {init} {gfn} {alpha} {beta}) :',
                  f'    ∀ n, a n = {name} n := weighted_sum_unique {name}_valid ha']
    else:
        base,E,F=lean(ir['power_base']),lean(ir['power_exponent']),lean(ir['power_increment'])
        second=lean(ir['initials'][1]);step=f'(fun n x y => {base} ^ ({F}) * y ^ 2 / x)'
        cert=f'GeneralSecondCertificate {name} {init} {second} {step}'
        E1,E2=[re.sub(r'\bn\b',f'(n + {k})',E) for k in (1,2)]
        he=[f'  have he : ∀ n : ℕ, ({E2}) + ({E}) = ({F}) + 2 * ({E1}) := by',
            '    intro n','    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]','    ring']
        h=f'  have h := multiplicative_certificate {base} (fun n : ℕ => {E}) (fun n : ℕ => {F}) (by norm_num) he'
        lines += [f'theorem {name}_valid : {cert} := by',*he,h,f'  convert h.1 using 1 <;> norm_num [{name}]',
                  f'theorem {name}_domain : ∀ n, {name} n ≠ 0 := by',f'  intro n; unfold {name}; positivity',
                  f'theorem {name}_unique (a : ℕ → ℚ) (hi : a 0 = {init}) (hj : a 1 = {second})',
                  f'    (ha : ∀ n : ℕ, a (n + 2) * a n = {base} ^ ({F}) * a (n + 1) ^ 2) :',
                  f'    ∀ n, a n = {name} n := by',f'  apply general_second_unique {name}_valid',
                  f'  apply multiplicative_from_relation a {init} {second} (fun n => {base} ^ ({F})) hi hj',
                  '  · norm_num','  · norm_num','  · intro n; positivity','  · exact ha',f'#print axioms {name}_domain']
    lines += [f'#print axioms {name}_valid',f'#print axioms {name}_unique']
    return '\n'.join(lines)+'\n'
