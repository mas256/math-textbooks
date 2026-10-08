"""Proof export for pairs and for actual partial sums, including n=1 boundaries."""
from expr import lean,evaluate,num
from advanced_proofs import ring_step


def prefix_proof(name,S):
    return [f'theorem {name}_prefix : ∀ n, prefix {name} n = {S} n := by',
        '  intro n','  induction n with',
        f'  | zero => norm_num [prefix, {name}, {S}]',
        '  | succ n ih =>','    rw [prefix_succ, ih]',
        f'    simp only [{name}, {S}, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]',
        '    norm_num <;> ring']


def variety_proofs(problem):
    from generate import proofs
    ir=problem['ir'];name=problem['id'];shape=ir['shape'];init=lean(ir['initials'][0])
    lines=[f'def {name} (n : ℕ) : ℚ := {lean(ir["formula"])}']
    if shape=='system':
        b=name+'_b';lines += [f'def {b} (n : ℕ) : ℚ := {lean(ir["b_formula"])}']
        P=lean(ir['P']);initialb=lean(ir['b_initial'])
        def step(rhs):
            text=lean(rhs,name).replace(f'({name} n)','x').replace(f'({b} n)','y')
            return f'(fun n x y => {text} / {P})'
        A,B=step(ir['rhs']),step(ir['b_rhs']);cert=f'SystemCertificate {name} {b} {init} {initialb} {A} {B}'
        lines += [f'theorem {name}_valid : {cert} := by','  constructor',f'  · norm_num [{name}]',f'  · norm_num [{b}]']
        for _ in range(2):
            lines += ['  · intro n',f'    apply (eq_div_iff (show {P} ≠ 0 by positivity)).2',
                f'    simp only [{name}, {b}, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]','    norm_num <;> ring']
        lines += [f'theorem {name}_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b {init} {initialb} {A} {B}) :',
            f'    ∀ n, a n = {name} n ∧ b n = {b} n := system_unique {name}_valid ha']
    elif shape=='pure_sum':
        S=name+'_sum';base={**problem,'id':S,'ir':{**ir,'formula':ir['sum_formula'],'underlying':ir['sum_formula']}}
        base['ir']['shape']='linear_second' if ir['second_order'] else None
        if not ir['second_order']:base['ir'].pop('shape')
        lines=[proofs(base),*lines,*prefix_proof(name,S)]
        if ir['second_order']:
            P,Q,R=[lean(ir[k]) for k in ('P2','Q2','R2')];second=lean(ir['initials'][1])
            step=f'(fun n x y => ({Q} * y + {R} * x) / {P})'
            cert=f'PureSecondSumCertificate {name} {init} {second} {step}';unique='pure_second_sum_unique'
        else:
            P,Q,R=[lean(ir[k]) for k in ('P','Q','R')]
            step=f'(fun n x => ({Q} * x + {R}) / {P})'
            cert=f'PureSumCertificate {name} {init} {step}';unique='pure_sum_unique'
        lines += [f'theorem {name}_valid : {cert} := by',
            f'  have heq : prefix {name} = {S} := funext {name}_prefix',
            f'  change '+('GeneralSecondCertificate' if ir['second_order'] else 'FirstCertificate')+f' (prefix {name}) {init} '+(second+' ' if ir['second_order'] else '')+step,
            f'  rw [heq]',f'  exact {S}_valid',
            f'theorem {name}_unique (a : ℕ → ℚ) (ha : '+cert.replace(name,'a',1)+') :',
            f'    ∀ n, a n = {name} n := {unique} {name}_valid ha']
    else:
        S=name+'_sum';alpha=lean(ir['sum_alpha']);F=lean(ir['sum_forcing'])
        lines += [f'def {S} (n : ℕ) : ℚ := {lean(ir["sum_formula"])}',*prefix_proof(name,S)]
        cert=f'SumRelationCertificate {name} {init} {alpha} (fun n => {F})'
        lines += [f'theorem {name}_valid : {cert} := by','  constructor',f'  · norm_num [{name}]','  · intro n',
            f'    rw [{name}_prefix]',f'    simp only [{name}, {S}, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]','    norm_num <;> ring',
            f'theorem {name}_unique (a : ℕ → ℚ) (ha : SumRelationCertificate a {init} {alpha} (fun n => {F})) :',
            f'    ∀ n, a n = {name} n := sum_relation_unique {name}_valid ha (by norm_num)']
    lines += [f'#print axioms {name}_valid',f'#print axioms {name}_unique']
    return '\n'.join(lines)+'\n'
