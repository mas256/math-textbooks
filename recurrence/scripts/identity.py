"""Versioned identities and an append-only registry for public problem links."""
import hashlib
import json
import re
from pathlib import Path

from expr import evaluate, polynomial, poly_divmod, poly_gcd

REGISTRY_PATH = Path(__file__).resolve().parents[1] / 'reference/public-problem-ids.json'


def identity_key(ir, include_initials=True):
    initials = [str(evaluate(x,0)) for x in ir['initials']] if include_initials else []
    if ir['second_order']:
        value = ['second',str(evaluate(ir['p'],0)),str(evaluate(ir['q'],0)),initials]
    else:
        try:
            ps = [polynomial(ir[k]) for k in ('P','Q','R')]
            common = poly_gcd(poly_gcd(ps[0],ps[1]),ps[2])
            ps = [poly_divmod(p,common)[0] for p in ps]
            scale = ps[0][max(ps[0])]
            coefficients = [sorted((d,str(c/scale)) for d,c in p.items()) for p in ps]
        except ValueError:
            coefficients = [ir[k] for k in ('P','Q','R')]
        value = [ir['reciprocal'],coefficients,initials]
    return json.dumps(value,sort_keys=True,separators=(',',':'))


def fingerprint(ir):
    return hashlib.sha256(identity_key(ir).encode()).hexdigest()


def load_registry(path=REGISTRY_PATH):
    registry = json.loads(Path(path).read_text())
    assert registry['schema_version']==1 and registry['identity_version']==1
    entries = registry['entries']
    assert len({e['fingerprint'] for e in entries})==len(entries)
    assert len({e['id'] for e in entries})==len(entries)
    assert all(re.fullmatch(r'[a-f0-9]{64}',e['fingerprint']) and re.fullmatch(r'p\d{3,}',e['id']) for e in entries)
    assert registry['next_id']>max((int(e['id'][1:]) for e in entries),default=0)
    return registry


def assign_ids(problems, registry, allow_new=False):
    ids = {e['fingerprint']:e['id'] for e in registry['entries']}
    keys = [fingerprint(p['ir']) for p in problems]
    assert len(set(keys))==len(keys), 'Equivalent problems were selected twice'
    unknown = sorted(set(keys)-ids.keys())
    if unknown and not allow_new:
        raise RuntimeError(f'{len(unknown)} new public problems: run generate.py --update-id-registry and commit the registry before publishing')
    for key in unknown:
        id = f"p{registry['next_id']:03}"
        registry['next_id']+=1
        ids[key]=id
        registry['entries'].append({'fingerprint':key,'id':id})
    for p,key in zip(problems,keys): p['id']=ids[key]
    return len(unknown)
