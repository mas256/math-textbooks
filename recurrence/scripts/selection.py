"""Cover profiles and coefficients, then balance parameters at equal numeric cost."""
from collections import Counter, defaultdict

from expr import evaluate
from identity import fingerprint, identity_key


def parameter_key(problem):
    ir,certificate = problem['ir'],problem['routes'][0]['certificate']
    if ir.get('shape')=='mobius': return 'fraction:'+','.join(str(evaluate(x,0)) for x in ir['mobius_coefficients'])
    if ir.get('shape')=='factorial_ratio': return 'factor:'+problem['generation']['profile']
    if certificate['kind']=='arithmetic-difference': return 'increment:'+str(evaluate(certificate['increment'],0))
    if certificate['kind']=='forced-second': return 'roots:'+str(certificate['scalar']['certificate']['roots'])
    if ir.get('shape')=='system': return 'modes:'+','.join(str(evaluate(x,0)) for x in ir['matrix'])
    if ir.get('shape') in {'pure_sum','sum_relation'}: return 'sum:'+problem['generation']['profile']
    if ir.get('difference_polynomial'): return 'forcing:'+str(evaluate(ir['R'],0))
    if 'roots' in certificate:
        return 'roots:' + ','.join(sorted(str(evaluate(x,0)) for x in certificate['roots']))
    if ir.get('shape')=='power_second': return 'base:'+str(evaluate(ir['power_base'],0))
    if ir['Q']['op']=='pow': return 'base:' + str(evaluate(ir['Q']['args'][0],0))
    return 'ratio:' + str(evaluate(certificate['ratio'],0))


def choose_diverse(candidates, quota, config, registry):
    ordered=sorted(candidates,key=lambda p:(p['scores']['cleanliness'],p['routes'][0]['parts']['P'],p['scores']['difficulty'],p['statement']['recurrence_tex']))
    profile_count=len({p['generation']['profile'] for p in candidates})
    groups=defaultdict(list)
    for p in ordered:
        profile=p['generation']['profile']
        key=profile if profile and quota>=profile_count else profile.removeprefix('inverse:') if profile else identity_key(p['ir'],False)
        groups[key].append(p)
    known={e['fingerprint'] for e in registry['entries']}
    coefficients,parameters=Counter(),Counter()
    chosen=[]
    while len(chosen)<quota and groups:
        for key in list(groups):
            preferred_inverse=bool(config['scale_profiles'].index(key)%2) if key in config['scale_profiles'] else None
            def rank(p):
                profile=p['generation']['profile']
                orientation = int(profile.startswith('inverse:')!=preferred_inverse) if preferred_inverse is not None and profile else 0
                balance = parameters[parameter_key(p)] if config['selection']['balance_parameters'] else 0
                existing = int(fingerprint(p['ir']) not in known) if config['selection']['prefer_existing_ids'] else 0
                return (coefficients[identity_key(p['ir'],False)],orientation,balance,
                        p['scores']['cleanliness'],p['routes'][0]['parts']['P'],p['scores']['difficulty'],existing,
                        p['statement']['recurrence_tex'],p['statement']['initials_tex'])
            p=min(groups[key],key=rank)
            groups[key].remove(p)
            chosen.append(p)
            coefficients[identity_key(p['ir'],False)]+=1
            parameters[parameter_key(p)]+=1
            if not groups[key]: del groups[key]
            if len(chosen)==quota: break
    return chosen


def diversity_summary(problems):
    families={}
    for family in sorted({p['family'] for p in problems}):
        ps=[p for p in problems if p['family']==family]
        families[family]={'count':len(ps),'coefficient_patterns':len({identity_key(p['ir'],False) for p in ps}),
                          'profiles':dict(Counter(p['generation']['profile'] or 'none' for p in ps)),
                          'parameters':dict(sorted(Counter(parameter_key(p) for p in ps).items()))}
    return {'count':len(problems),'coefficient_patterns':len({identity_key(p['ir'],False) for p in problems}),'families':families}
