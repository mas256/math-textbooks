"""All-index Lean obligations for the added elementary families."""
from expr import evaluate, lean, lean_step
from elementary import power_formula


def elementary_proofs(problem):
    name, ir = problem['id'], problem['ir']
    formula, initial = lean(ir['formula']), lean(ir['initials'][0])
    step = '(fun n x => ' + lean_step(ir['rhs']) + ')'
    certificate = f'FirstCertificate {name} {initial} {step}'
    lines = [f'def {name} (n : ℕ) : ℚ := {formula}',
             f'theorem {name}_valid : {certificate} := by', '  constructor',
             f'  · norm_num [{name}, geometricSum]', '  · intro n']
    if ir['shape'] == 'power_first':
        lines += [f'    simp only [{name}, geometricSum_succ, pow_succ, pow_add, pow_one, pow_mul, mul_pow] <;> ring']
        offset = lean(ir['power_shift'])
        unshifted = power_formula(evaluate(ir['initials'][0],0)-evaluate(ir['power_shift'],0),
                                  evaluate(ir['power_coefficient'],0), ir['power_degree']['value'], 0)
        lines += [f'theorem {name}_domain : ∀ n, 0 < {name} n - {offset} := by',
                  '  intro n',
                  f'  have he : {name} n - {offset} = {lean(unshifted)} := by',
                  f'    simp only [{name}]; ring', '  rw [he]', '  positivity',
                  f'#print axioms {name}_domain']
    else:
        lines += [f'    simp only [{name}, Nat.cast_add, Nat.cast_one, pow_succ]', '    ring']
    lines += [f'theorem {name}_unique (a : ℕ → ℚ) (ha : FirstCertificate a {initial} {step}) :',
              f'    ∀ n, a n = {name} n := first_unique {name}_valid ha',
              f'#print axioms {name}_valid', f'#print axioms {name}_unique']
    return '\n'.join(lines) + '\n'
