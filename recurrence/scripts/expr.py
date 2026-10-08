"""A small, shared exact expression IR for LaTeX, Lean and arithmetic checks."""
from fractions import Fraction
from math import comb, factorial


def num(value):
    value = Fraction(value)
    return {"op": "rational", "num": value.numerator, "den": value.denominator}


def index():
    return {"op": "index"}  # school index n; Lean index k = n - 1


def term(offset=0, variable=None):
    return {"op": "term", "offset": offset, **({'variable':variable} if variable else {})}


def add(*args):
    flat = []
    total = Fraction(0)
    for a in args:
        for b in a["args"] if a["op"] == "add" else [a]:
            if b["op"] == "rational": total += Fraction(b["num"], b["den"])
            else: flat.append(b)
    args = flat + ([num(total)] if total else [])
    return args[0] if len(args) == 1 else {"op": "add", "args": args} if args else num(0)


def mul(*args):
    flat, total = [], Fraction(1)
    for a in args:
        for b in a["args"] if a["op"] == "mul" else [a]:
            if b["op"] == "rational": total *= Fraction(b["num"], b["den"])
            else: flat.append(b)
    if not total: return num(0)
    args = ([num(total)] if total != 1 else []) + flat
    if any(a['op']=='div' for a in args):
        numerator=[a['args'][0] if a['op']=='div' else a for a in args]
        denominator=[a['args'][1] for a in args if a['op']=='div']
        return div(mul(*numerator),mul(*denominator))
    return args[0] if len(args) == 1 else {"op": "mul", "args": args} if args else num(1)


def neg(a):
    return mul(num(-1), a)


def sub(a, b):
    return add(a, neg(b))


def div(a, b):
    return {"op": "div", "args": [a, b]}


def reciprocal(expr):
    if expr['op']=='div': return div(expr['args'][1],expr['args'][0])
    if expr['op']=='mul':
        denominators=[a['args'][1] for a in expr['args'] if a['op']=='div' and a['args'][0]==num(1)]
        others=[a for a in expr['args'] if not (a['op']=='div' and a['args'][0]==num(1))]
        if denominators: return div(mul(*denominators),mul(*others))
    return div(num(1),expr)


def power(a, exponent):
    return {"op": "pow", "args": [a, exponent]}


def nat(offset=0):
    return {"op": "nat_index", "offset": offset}  # k + offset


def nat_const(value):
    return {"op": "nat_constant", "value": value}


def triangular():
    return {"op": "triangular"}  # k(k+1)/2 = n(n-1)/2


def shift(expr, offset=1):
    if expr["op"] == "index":
        return add(index(), num(offset))
    if expr["op"] == "nat_index":
        return nat(expr["offset"] + offset)
    if "args" in expr:
        args = [shift(a, offset) for a in expr["args"]]
        if expr["op"] in {'add','mul'}:
            result=(add if expr['op']=='add' else mul)(*args)
            def natural(x):
                return x['op'] in {'nat_index','nat_constant','choose','triangular'} or any(natural(a) for a in x.get('args',[]))
            if natural(result): return result
            try:
                p=polynomial(result)
                if max(p,default=0)<=1: return from_polynomial(p)
            except ValueError: pass
            return result
        return {**expr, "args": args}
    return expr


def evaluate(expr, k, terms=None):
    op = expr["op"]
    if op == "rational": return Fraction(expr["num"], expr["den"])
    if op == "index": return Fraction(k + 1)
    if op == "nat_index": return k + expr["offset"]
    if op == "nat_constant": return expr["value"]
    if op == "triangular": return k * (k + 1) // 2
    if op == "term": return terms[(expr['variable'],expr['offset'])] if 'variable' in expr else terms[expr["offset"]]
    if op == 'sum_term': return terms[('S',expr['offset'])]
    if op == 'prefix_sum':
        return sum((evaluate(expr['args'][0],j,{0:terms[j-k]}) for j in range(k+1)),Fraction(0))
    if op == 'log':
        from algebra import integer_log
        return Fraction(integer_log(evaluate(expr['args'][1],k,terms),evaluate(expr['args'][0],k,terms)))
    a = [evaluate(x, k, terms) for x in expr["args"]]
    if op == "add": return sum(a, Fraction(0))
    if op == "mul":
        out = Fraction(1)
        for x in a: out *= x
        return out
    if op == "div": return a[0] / a[1]
    if op == "pow": return a[0] ** a[1]
    if op == "choose": return comb(int(a[0]), int(a[1]))
    if op == "factorial": return Fraction(factorial(int(a[0])))
    raise ValueError(op)


def latex(expr):
    op = expr["op"]
    if op == "rational":
        u, v = expr["num"], expr["den"]
        return str(u) if v == 1 else ("-" if u < 0 else "") + rf"\frac{{{abs(u)}}}{{{v}}}"
    if op == "index": return "n"
    if op == "nat_constant": return str(expr["value"])
    if op == "nat_index":
        o = expr["offset"] - 1
        return "n" if o == 0 else "n" + (f"+{o}" if o > 0 else str(o))
    if op == "triangular": return r"\frac{n(n-1)}{2}"
    if op == "term":
        o = expr["offset"]
        variable=expr.get('variable','a')
        return variable+"_{n}" if not o else variable+"_{n+" + str(o) + "}"
    if op == 'sum_term': return 'S_{n}' if not expr['offset'] else 'S_{n+'+str(expr['offset'])+'}'
    if op == 'prefix_sum':
        import re
        body=re.sub(r'(?<![a-zA-Z\\])n(?![a-zA-Z])','k',latex(expr['args'][0]))
        return rf"\sum_{{k=1}}^{{n}}{body}"
    if op == 'log': return rf"\log_{{{latex(expr['args'][0])}}}\left({latex(expr['args'][1])}\right)"
    args = expr["args"]
    if op == "factorial": return r"\left("+latex(args[0])+r"\right)!"
    if op == "add":
        # Simplify linear natural-index expressions for display; keep their
        # natural-number type in the proof AST used as an exponent.
        if any(a['op']=='nat_constant' or a['op']=='nat_index' or
               a['op']=='mul' and any(x['op'].startswith('nat_') for x in a['args']) for a in args):
            try:
                p=polynomial(expr)
                if max(p,default=0)<=1: return latex(from_polynomial(p))
            except ValueError: pass
        out = ""
        for a in args:
            text = latex(a)
            out += ("" if not out or text.startswith("-") else "+") + text
        return out
    if op == "mul":
        out = ""
        negative = False
        for a in args:
            if a == num(-1): negative = not negative; continue
            if a["op"] == "rational" and a["num"] < 0:
                negative = not negative
                a = {**a, "num": -a["num"]}
            text = latex(a)
            if a["op"] == "add" or (a["op"] == "nat_index" and a['offset']!=1) or (a["op"] == "rational" and a["num"] < 0):
                text = r"\left(" + text + r"\right)"
            # Adjacent numerical factors must not look like one integer.
            numerical = a['op'] == 'rational' or a['op'] == 'pow' and a['args'][0]['op'] == 'rational'
            out += (r"\cdot " if numerical else r"\,") + text if out else text
        return ("-" if negative else "") + (out or "1")
    if op == "div": return rf"\frac{{{latex(args[0])}}}{{{latex(args[1])}}}"
    if op == "pow":
        if args[1] in (nat_const(0), num(0)): return "1"
        if args[1] in (nat_const(1), num(1)): return latex(args[0])
        base = latex(args[0])
        if args[0]["op"] not in {"rational", "index"} or args[0].get("num", 1) < 0 or args[0].get("den", 1) > 1:
            base = r"\left(" + base + r"\right)"
        return base + "^{" + latex(args[1]) + "}"
    if op == "choose":
        k = args[1].get('value')
        if k in (2, 3) and args[0]['op'] == 'nat_index':
            numerator = mul(*(shift(args[0], -i) for i in reversed(range(k))))
            return latex(div(numerator, num(factorial(k))))
        return rf"\binom{{{latex(args[0])}}}{{{latex(args[1])}}}"
    raise ValueError(op)


def lean(expr, sequence="f"):
    op = expr["op"]
    if op == "rational":
        u, v = expr["num"], expr["den"]
        return f"({u} : ℚ)" if v == 1 else f"(({u} : ℚ) / {v})"
    if op == "index": return "((n : ℚ) + 1)"
    if op == "nat_constant": return str(expr["value"])
    if op == "nat_index": return "n" if expr["offset"] == 0 else f"(n + {expr['offset']})"
    if op == "triangular": return "((n + 1).choose 2)"
    if op == "factorial": return "(("+lean(expr["args"][0])+ ").factorial : ℚ)"
    if op == "term":
        name=sequence+"_b" if expr.get("variable")=="b" else sequence
        return f"({name} n)" if expr["offset"] == 0 else f"({name} (n + {expr['offset']}))"
    if op == 'prefix_sum':
        import re
        body=re.sub(r'\bn\b','k',lean(expr['args'][0],sequence))
        return f'(∑ k ∈ Finset.range (n + 1), {body})'
    a = [lean(x, sequence) for x in expr["args"]]
    if op == "choose": return f"({a[0]}).choose {a[1]}"
    symbol = {"add": " + ", "mul": " * ", "div": " / ", "pow": " ^ "}[op]
    return "(" + symbol.join(a) + ")"


def replace_term(expr):
    if expr["op"] == "term":
        assert expr["offset"] == 0
        return {"op": "variable"}
    return {**expr, "args": [replace_term(a) for a in expr["args"]]} if "args" in expr else expr


def lean_step(expr):
    return lean(expr).replace("(f n)", "x")


def polynomial(expr):
    """Exact expansion only for registered polynomials in the index."""
    op = expr["op"]
    if op == "rational": return {0: Fraction(expr["num"], expr["den"])} if expr['num'] else {}
    if op == "index": return {1: Fraction(1)}
    if op == 'nat_constant': return {0:Fraction(expr['value'])} if expr['value'] else {}
    if op == 'nat_index': return {1:Fraction(1),0:Fraction(expr['offset']-1)} if expr['offset']!=1 else {1:Fraction(1)}
    if op == 'choose':
        result={0:Fraction(1)}
        base=polynomial(expr['args'][0])
        k=expr['args'][1]['value']
        for j in range(k):
            factor=dict(base);factor[0]=factor.get(0,Fraction(0))-j
            result=poly_mul(result,{d:c for d,c in factor.items() if c})
        return {d:c/factorial(k) for d,c in result.items() if c}
    if op == "pow" and expr["args"][1]["op"] == "nat_constant":
        result = {0: Fraction(1)}
        base = polynomial(expr["args"][0])
        for _ in range(expr["args"][1]["value"]): result = poly_mul(result, base)
        return result
    if op == "add":
        result = {}
        for a in expr["args"]:
            for degree, coefficient in polynomial(a).items(): result[degree] = result.get(degree, 0) + coefficient
        return {d:c for d,c in result.items() if c}
    if op == "mul":
        result = {0: Fraction(1)}
        for a in expr["args"]: result = poly_mul(result, polynomial(a))
        return result
    raise ValueError("Not a registered index polynomial")


def poly_mul(a, b):
    out = {}
    for da, ca in a.items():
        for db, cb in b.items(): out[da+db] = out.get(da+db, 0) + ca*cb
    return {d:c for d,c in out.items() if c}


def expand_polynomial(expr):
    p = polynomial(expr)
    return from_polynomial(p)


def from_polynomial(p):
    return add(*(num(c) if d == 0 else mul(num(c), index() if d == 1 else power(index(), nat_const(d)))
                 for d, c in sorted(p.items(), reverse=True) if c))


def poly_divmod(a, b):
    assert b
    rem, quotient = dict(a), {}
    degree = max(b)
    while rem and max(rem) >= degree:
        d = max(rem) - degree
        c = rem[max(rem)] / b[degree]
        quotient[d] = quotient.get(d, 0) + c
        for db, cb in b.items():
            rem[db+d] = rem.get(db+d, 0) - c*cb
        rem = {d:c for d,c in rem.items() if c}
    return quotient, rem


def poly_gcd(a, b):
    while b:
        a, b = b, poly_divmod(a, b)[1]
    if not a: return {}
    leading = a[max(a)]
    return {d:c/leading for d,c in a.items()}


def reduce_linear_coefficients(P, Q, R):
    """Cancel a common *polynomial* factor before displaying/scoring a step."""
    try:
        ps = [polynomial(x) for x in (P,Q,R)]
    except ValueError:
        return P,Q,R
    common = poly_gcd(poly_gcd(ps[0], ps[1]), ps[2])
    if max(common, default=0) == 0:
        return P,Q,R
    quotients = [poly_divmod(p, common) for p in ps]
    assert all(not r for _,r in quotients)
    return tuple(from_polynomial(q) for q,_ in quotients)
