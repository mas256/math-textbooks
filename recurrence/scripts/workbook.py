"""Select a structurally balanced 75-question review batch from the generated bank."""
import argparse,copy,hashlib,json
from collections import Counter
from pathlib import Path
from identity import identity_key,fingerprint
from generate import validate

ROOT=Path(__file__).resolve().parents[1]
TARGETS={
 1:{'geometric':5,'arithmetic':6,'polynomial_difference':4},
 2:{'affine':3,'scaled_constant':2,'pure_sum':3,'sum_relation':3,'factorial_ratio':3,'polynomial_difference':1},
 3:{'coupled_symmetric':3,'coupled_weighted':2,'scaled_constant':3,'factorial_ratio':3,'second_order':2,'ratio_power':2},
 4:{'mobius':4,'forced_second':3,'arithmetic_difference':3,'factorial_ratio':2,'scaled_second_order':2,'ratio_power':1},
 5:{'coupled_forced':2,'pure_sum_scaled':3,'weighted_sum':3,'difference_scaled':3,'multiplicative_second':2,'reciprocal_forcing':1,'reciprocal_scaled':1},
}


def select(bank):
    selected=[];distribution={}
    for lv,targets in TARGETS.items():
        chosen=[];coefficients=Counter();profiles=Counter()
        for family,quota in targets.items():
            pool=[copy.deepcopy(p) for p in bank['problems'] if p['family']==family and p['scores']['level']==lv]
            if len(pool)<quota: raise RuntimeError(f'Lv{lv} {family}: {len(pool)} available for quota {quota}')
            for _ in range(quota):
                def rank(p):
                    return (coefficients[identity_key(p['ir'],False)],profiles[p['family'],p['generation']['profile']],
                        p['scores']['cleanliness'],p['routes'][0]['parts']['P'],p['scores']['difficulty'],p['id'])
                p=min(pool,key=rank);pool.remove(p);chosen.append(p)
                coefficients[identity_key(p['ir'],False)]+=1;profiles[p['family'],p['generation']['profile']]+=1
        assert len(chosen)==15
        for i,p in enumerate(chosen,1):p['workbook_number']=f'Lv{lv}-{i:02}';validate(p)
        assert len({identity_key(p['ir'],False) for p in chosen})>=13
        distribution[str(lv)]={'count':15,'families':dict(Counter(p['family'] for p in chosen)),
            'systems':sum(p['ir'].get('shape')=='system' for p in chosen),
            'sums':sum(p['ir'].get('shape') in {'pure_sum','sum_relation','weighted_sum'} for p in chosen),
            'coefficient_patterns':len({identity_key(p['ir'],False) for p in chosen})}
        selected+=chosen
    assert len({fingerprint(p['ir']) for p in selected})==sum(sum(t.values()) for t in TARGETS.values())
    return {'date':'2026-10-08','score_version':bank['score_version'],'generator_commit':'pending',
        'problems':selected,'distribution':distribution,'generation_config':bank['generation_config'],
        'lean_theorems':[t for p in selected for t in p['lean_theorems']],
        'proof_source_sha256':bank['proof_source_sha256']}


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=ROOT/'build/workbook.json');args=parser.parse_args()
    bank=json.loads((ROOT/'build/candidates.json').read_text());batch=select(bank)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(batch,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(batch['distribution'],ensure_ascii=False,indent=2))
