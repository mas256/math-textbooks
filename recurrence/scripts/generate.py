#!/usr/bin/env python3
"""Bounded composition, forward route recognition, screening, then Lean export."""
import argparse
import hashlib
import itertools
import json
import random
import re
from collections import Counter
from fractions import Fraction
from pathlib import Path

from compiler import compile_blocks
from expr import add, div, evaluate, index, latex, lean, mul, nat, neg, num, power, sub
from profiles import EXPONENTS, profile_catalog, scale_options
from rules import CONFIG_PATH, RuleViolation, load_config, normalize_recipe
from scoring import assess, level, score_routes, statement_metrics, walk
from solve import check_derivation, find_routes
from identity import REGISTRY_PATH, assign_ids, identity_key, load_registry
from selection import choose_diverse, diversity_summary

ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build'
FAMILIES={
    'constant':'定数数列', 'geometric':'等比数列', 'affine':'特性方程式型（2項間）',
    'scaled_constant':'階比型', 'shifted_scaled':'階比型＋定数の移動',
    'scaled_affine':'階比型＋特性方程式型', 'second_order':'3項間漸化式',
    'ratio_power':'指数係数の階比型', 'reciprocal_affine':'逆数型＋特性方程式型',
    'reciprocal_scaled':'逆数型＋階比型',
    'polynomial_forcing':'一次式の付加項', 'reciprocal_forcing':'逆数型＋一次式の付加項',
}
SCALED={'scaled_constant','shifted_scaled','scaled_affine','reciprocal_scaled'}


def compile_recipe(family, parameters, profile='gap_2', config=None):
    config=config or load_config()
    r,c,d,s=(Fraction(parameters[x]) for x in ('r','c','d','s'))
    core='constant' if family in {'constant','scaled_constant','shifted_scaled','ratio_power'} else 'geometric' if family in {'geometric','second_order','polynomial_forcing','reciprocal_forcing'} else 'affine_fixed_point'
    params={'initial':num(d)} if core=='constant' else {'ratio':num(r),'amplitude':num(d)}
    if core=='affine_fixed_point': params.update(fixed_point=num(c),constant_term=num((1-r)*c))
    blocks=[]
    if family in SCALED:
        factors=dict(scale_options(config))
        if profile not in factors: raise RuleViolation('disabled_scale_profile')
        blocks.append({'kind':'index_scale','profile':profile,'factor':factors[profile]})
        if family=='shifted_scaled': blocks.append({'kind':'add_constant','value':num(-c)})
    if family=='ratio_power':
        if profile not in config['exponent_profiles']: raise RuleViolation('disabled_exponent_profile')
        blocks.append({'kind':'index_scale','profile':profile,'factor':power(num(r),EXPONENTS[profile]['total'])})
    if family in {'polynomial_forcing','reciprocal_forcing'}:
        # u(n+1)-r*u(n)=c(r-1)n. Positivity follows from the
        # positive initial value and the positive forcing recurrence.
        if d-c-c/(r-1)<=0: raise RuleViolation('nonpositive_initial')
        value=add(mul(num(-c),index()),num(-c/(r-1)))
        blocks.append({'kind':'index_add','value':value})
    if family=='second_order':
        if r==s: raise RuleViolation('repeated_root')
        blocks.append({'kind':'linear_combination','other_core':{'kind':'geometric','ratio':num(s),'initial':num(c)}})
    if family in {'reciprocal_affine','reciprocal_scaled','reciprocal_forcing'}:
        blocks.append({'kind':'reciprocal','requires':'positive_input'})
    previous='core'
    for i,b in enumerate(blocks,1):
        b.update(id=f'b{i}',input=previous)
        previous=b['id']
    recipe={'schema_version':'0.2','rule_set_version':config['version'],
            'domain':{'index_start':1,'sequence_type':'rational'},
            'core':{'id':'core','kind':core,'parameters':params},
            'blocks':blocks,'output':previous}
    recipe=normalize_recipe(recipe,config)
    ir=compile_blocks(recipe,config)
    routes=score_routes(ir,find_routes(ir,config))
    quality=assess(ir,routes,config)
    main=routes[0] if routes else None
    scores={'difficulty':main['cost'] if main else None,
            'level':level(main['cost']) if main else None,
            'cleanliness':main['numeric_cost'] if main else None,
            'quality_proposal':max(0,30-2*main['parts']['P']-main['parts']['R']-main['parts']['A']) if main else 0,
            'quality_status':'structural-heuristic','version':config['version']}
    return {'family':family,'family_label':FAMILIES[family],'recipe':recipe,'ir':ir,
            'statement':{'initials_tex':[f'a_{{{i+1}}}={latex(v)}' for i,v in enumerate(ir['initials'])],
                         'recurrence_tex':latex(ir['lhs'])+'='+latex(ir['rhs']),
                         'condition':'n は 1 以上の整数とする。数列の一般項 a_n を求めよ。'},
            'answer_tex':'a_n='+latex(ir['formula']),'routes':routes,'scores':scores,'quality':quality,
            'generation':{'profile':profile if family in SCALED|{'ratio_power'} else None,
                          'transform_counts':dict(Counter(b['kind'] for b in recipe['blocks']))}}


def proofs(problem):
    name,ir=problem['id'],problem['ir']
    init=lean(ir['initials'][0])
    lines=[f"def {name} (n : ℕ) : ℚ := {lean(ir['formula'])}"]
    if ir['second_order']:
        p,q,sec=lean(ir['p']),lean(ir['q']),lean(ir['initials'][1])
        cert=f'SecondCertificate {name} {init} {sec} {p} {q}'
        lines += [f'theorem {name}_valid : {cert} := by','  constructor',
                  f'  · norm_num [{name}]',f'  · norm_num [{name}]',
                  '  · intro n',f'    simp only [{name}, pow_succ, pow_add] <;> ring',
                  f'theorem {name}_unique (a : ℕ → ℚ) (ha : SecondCertificate a {init} {sec} {p} {q}) :',
                  f'    ∀ n, a n = {name} n := second_unique {name}_valid ha']
    else:
        Pn,Qn,Rn=[lean(ir[x]) for x in ('P','Q','R')]
        Pfn,Qfn,Rfn=[f'(fun n : ℕ => {s})' for s in (Pn,Qn,Rn)]
        underlying=name+'_base' if ir['reciprocal'] else name
        if ir['reciprocal']: lines.append(f"def {underlying} (n : ℕ) : ℚ := {lean(ir['underlying'])}")
        base_init=lean(num(evaluate(ir['underlying'],0)))
        base_step=f'(fun n x => ({Qn} * x + {Rn}) / {Pn})'
        lines += [f'theorem {name}_base_valid : FirstCertificate {underlying} {base_init} {base_step} := by',
                  f'  apply linear_certificate {underlying} {base_init} {Pfn} {Qfn} {Rfn}',
                  f'  · norm_num [{underlying}]','  · intro n; positivity','  · intro n']
        if ir.get('exponent_profile')=='square_minus_one':
            lines += ['    have he : (n + 1) * (n + 3) = n * (n + 2) + (2 * (n + 1) + 1) := by ring']
            lines += [f'    simp only [{underlying}, Nat.add_assoc]', '    rw [he]', '    simp only [pow_add] <;> ring']
        elif 'exponent_profile' in ir:
            lines += [f'    simp only [{underlying}, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right, pow_succ, pow_add] <;> ring']
        else:
            denominators={lean(x['args'][1]) for x in walk(ir['underlying']) if x['op']=='div'}
            for i,den in enumerate(sorted(denominators)):
                next_den=re.sub(r'\bn\b','(n + 1)',den)
                lines += [f'    have hd{i} : {den} ≠ 0 := by positivity',
                          f'    have he{i} : {next_den} ≠ 0 := by positivity']
            lines += [f'    simp only [{underlying}, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *']
            if denominators:
                facts=', '.join(f'{h}{i}' for i in range(len(denominators)) for h in ('hd','he'))
                lines.append(f'    field_simp [{facts}] <;> ring')
            else: lines.append('    ring')
        if ir['reciprocal']:
            actual_step=f'(fun n x => {Pn} * x / ({Qn} + {Rn} * x))'
            lines += [f'theorem {name}_positive (n : ℕ) : 0 < {underlying} n := by']
            if problem['family']=='reciprocal_forcing':
                lines += ['  induction n with',f'  | zero => norm_num [{underlying}]',
                          f'  | succ n ih => rw [{name}_base_valid.recurrence]; positivity']
            else: lines += [f'  unfold {underlying}','  positivity']
            lines += [f'theorem {name}_valid : FirstCertificate {name} {init} {actual_step} := by',
                      f'  have h := reciprocal_certificate {name}_base_valid {name}_positive (by intro n; positivity)',
                      f'  have heq : {name} = (fun n => 1 / {underlying} n) := by',
                      '    funext n',
                      f'    simp [{name}, {underlying}, div_eq_mul_inv] <;> ring',
                      '  rw [heq]',
                      '  convert h.1 using 1 <;> norm_num',
                      f'theorem {name}_domain : (∀ n : ℕ, {Qn} + {Rn} * {name} n ≠ 0) ∧ (∀ n, {name} n ≠ 0) := by',
                      f'  have h := reciprocal_certificate {name}_base_valid {name}_positive (by intro n; positivity)',
                      f'  simpa [{name}, {underlying}, div_eq_mul_inv] using h.2',f'#print axioms {name}_domain']
        else:
            actual_step=base_step
            lines.append(f'theorem {name}_valid : FirstCertificate {name} {init} {actual_step} := {name}_base_valid')
        lines += [f'theorem {name}_unique (a : ℕ → ℚ) (ha : FirstCertificate a {init} {actual_step}) :',
                  f'    ∀ n, a n = {name} n := first_unique {name}_valid ha']
    lines += [f'#print axioms {name}_valid',f'#print axioms {name}_unique']
    return '\n'.join(lines)+'\n'


def validate(problem):
    ir=problem['ir']
    assert problem['scores']['level'] in range(1,5)
    for n in range(24):
        xs={i:evaluate(ir['formula'],n+i) for i in (0,1,2)}
        assert evaluate(ir['lhs'],n,xs)==evaluate(ir['rhs'],n,xs),(problem.get('id'),n)
        for route in problem['routes']:
            assert evaluate(route['formula'],n)==xs[0],('forward route',route['title'],n)
            check_derivation(ir,route,n)
        if ir['reciprocal']:
            assert xs[0]>0
            assert evaluate(add(ir['Q'],mul(ir['R'],{'op':'term','offset':0})),n,xs)!=0
    return 24


def summarize(problems):
    metrics=[statement_metrics(p['ir']) for p in problems]
    return {'count':len(problems),'mean_nodes':round(sum(x['nodes'] for x in metrics)/len(metrics),2) if metrics else 0,
            'max_nodes':max((x['nodes'] for x in metrics),default=0),
            'max_coefficient_degree':max((x['coefficient_degree'] for x in metrics),default=0),
            'levels':dict(Counter(str(p['scores']['level']) for p in problems)),
            'families':dict(Counter(p['family'] for p in problems))}


def comparison_report(problems,config,counters,rejections):
    baseline=json.loads((ROOT/'reference/quality-baseline.json').read_text())
    previous=json.loads((ROOT/'reference/quality-v0.2.json').read_text())
    # Forward recognition, with no construction history, supplies comparable
    # parameter information even for the frozen snapshot.
    for p in previous['problems']: p['routes']=score_routes(p['ir'],find_routes(p['ir'],config))
    rejected=[]
    for i,p in enumerate(baseline['problems'],1):
        routes=score_routes(p['ir'],find_routes(p['ir'],config))
        assessment=assess(p['ir'],routes,config)
        if not assessment['accepted']:
            rejected.append({'old_id':f'p{i:03}','family':p['family'],
                             'recurrence_tex':p['statement']['recurrence_tex'],**assessment})
    examples=[{'id':p['id'],'family':p['family'],'recurrence_tex':p['statement']['recurrence_tex'],
               'initials_tex':p['statement']['initials_tex'],'answer_tex':p['answer_tex'],
               'metrics':p['quality']['metrics'],'main_route':p['routes'][0]['title']}
              for p in problems if p['family'] in {'shifted_scaled','reciprocal_forcing'}][:12]
    return {'version':config['version'],'baseline_commit':baseline['commit'],
            'before':summarize(baseline['problems']),'after':summarize(problems),
            'candidate_counts':dict(counters),'rejection_reasons':dict(rejections),
            'baseline_rejected_count':len(rejected),'baseline_rejected_examples':rejected,
            'diversity':{'previous_version':previous['version'],'before':diversity_summary(previous['problems']),
                         'after':diversity_summary(problems)},
            'examples':examples,'limits':config,'status':'structural-comparison',
            'note':'式の構造と対応済み解法の比較です。学習者による難易度・良問性の実測は未実施です。'}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--config',type=Path,default=CONFIG_PATH)
    parser.add_argument('--update-id-registry',action='store_true')
    args=parser.parse_args()
    config=load_config(args.config)
    BUILD.mkdir(exist_ok=True)
    parameters=list(itertools.product((2,3),(1,2,3),(1,2,3,4,5,6,8,9,Fraction(1,2)),(3,4)))
    random.Random(config['seed']).shuffle(parameters)
    registry=load_registry()
    problems, fingerprints=[],set()
    counters,rejections=Counter(),Counter()
    for family in FAMILIES:
        quota=config['quotas'].get(family,0)
        if not quota: continue
        profiles=[name for name,_ in scale_options(config)] if family in SCALED else config['exponent_profiles'] if family=='ratio_power' else ['none']
        candidates=[]
        for profile in profiles:
            for r,c,d,s in parameters:
                counters['attempted']+=1
                try: p=compile_recipe(family,{'r':r,'c':c,'d':d,'s':s},profile,config)
                except RuleViolation as e:
                    counters['rule_rejected']+=1
                    rejections[str(e)]+=1
                    continue
                fingerprint=json.dumps([p['ir']['lhs'],p['ir']['rhs'],p['ir']['initials']],sort_keys=True)
                if fingerprint in fingerprints:
                    counters['duplicate']+=1
                    continue
                fingerprints.add(fingerprint)
                counters['unique']+=1
                if not p['quality']['accepted']:
                    counters['quality_rejected']+=1
                    rejections.update(p['quality']['reasons'])
                    continue
                counters['accepted_candidates']+=1
                candidates.append(p)
        selected=choose_diverse(candidates,quota,config,registry)
        if len(selected)!=quota:
            raise RuntimeError(f'{family}: only {len(selected)} acceptable problems for quota {quota}; reasons={dict(rejections)}')
        problems.extend(selected)
    if not problems: raise RuntimeError('No problems were selected')
    added_ids=assign_ids(problems,registry,args.update_id_registry)
    for p in problems:
        validate(p)
        p['lean_theorems']=[p['id']+'_valid',p['id']+'_unique']+([p['id']+'_domain'] if p['ir']['reciprocal'] else [])
        p['lean_source']='import Recurrence.Theory\n\nnamespace Recurrence\n'+proofs(p)+'end Recurrence\n'
    if args.update_id_registry:
        REGISTRY_PATH.write_text(json.dumps(registry,indent=2)+'\n')
    source='import Recurrence.Theory\n\nnamespace Recurrence\n\n'+'\n'.join(proofs(p) for p in problems)+'\nend Recurrence\n'
    (ROOT/'lean/Recurrence/Generated.lean').write_text(source,encoding='utf-8')
    report=comparison_report(problems,config,counters,rejections)
    (BUILD/'quality-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf-8')
    payload={'schema_version':'0.2','score_version':config['version'],'generator_version':'0.3.0',
             'families':{k:v for k,v in FAMILIES.items() if config['quotas'].get(k,0)},'problems':problems,
             'generation_config':config,'function_catalog':profile_catalog(config),
             'comparison':{k:report[k] for k in ('before','after','candidate_counts','rejection_reasons','baseline_rejected_count','diversity')},
             'checks':{'exact_arithmetic_cases':len(problems)*24},
             'proof_source_sha256':hashlib.sha256(source.encode()).hexdigest()}
    (BUILD/'candidates.json').write_text(json.dumps(payload,ensure_ascii=False,indent=2),encoding='utf-8')
    print(f"Generated {len(problems)} problems / {len(payload['families'])} families; {len(problems)*24} exact term checks passed.")
    print('Comparison:',json.dumps({k:report[k] for k in ('before','after','baseline_rejected_count')},ensure_ascii=False))
    print('Candidate screening:',dict(counters),'reasons:',dict(rejections))
    print('Distinct coefficient patterns:',report['diversity']['before']['coefficient_patterns'],'->',report['diversity']['after']['coefficient_patterns'])
    print('New public IDs:',added_ids)


if __name__=='__main__': main()
