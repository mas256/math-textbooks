"""A small, shared exact expression IR for LaTeX, Lean and arithmetic checks."""
from fractions import Fraction


def num(value):
    value = Fraction(value)
    return {"op": "rational", "num": value.numerator, "den": value.denominator}


def index():
    return {"op": "index"}  # school index n; Lean index k = n - 1


def term(offset=0):
    return {"op": "term", "offset": offset}


def add(*args):
    args = [a for a in args if a != num(0)]
    return args[0] if len(args) == 1 else {"op": "add", "args": args} if args else num(0)


def mul(*args):
    if num(0) in args:
        return num(0)
    args = [a for a in args if a != num(1)]
    return args[0] if len(args) == 1 else {"op": "mul", "args": args} if args else num(1)


def neg(a):
    return mul(num(-1), a)


def sub(a, b):
    return add(a, neg(b))


def div(a, b):
    return {"op": "div", "args": [a, b]}


def power(a, exponent):
    return {"op": "pow", "args": [a, exponent]}


def nat(offset=0):
    return {"op": "nat_index", "offset": offset}  # k + offset


def triangular():
    return {"op": "triangular"}  # k(k+1)/2 = n(n-1)/2


def shift(expr, offset=1):
    if expr["op"] == "index":
        return add(index(), num(offset))
    if expr["op"] == "nat_index":
        return nat(expr["offset"] + offset)
    if "args" in expr:
        return {**expr, "args": [shift(a, offset) for a in expr["args"]]}
    return expr


def evaluate(expr, k, terms=None):
    op = expr["op"]
    if op == "rational": return Fraction(expr["num"], expr["den"])
    if op == "index": return Fraction(k + 1)
    if op == "nat_index": return k + expr["offset"]
    if op == "triangular": return k * (k + 1) // 2
    if op == "term": return terms[expr["offset"]]
    a = [evaluate(x, k, terms) for x in expr["args"]]
    if op == "add": return sum(a, Fraction(0))
    if op == "mul":
        out = Fraction(1)
        for x in a: out *= x
        return out
    if op == "div": return a[0] / a[1]
    if op == "pow": return a[0] ** a[1]
    raise ValueError(op)


def latex(expr):
    op = expr["op"]
    if op == "rational":
        u, v = expr["num"], expr["den"]
        return str(u) if v == 1 else ("-" if u < 0 else "") + rf"\frac{{{abs(u)}}}{{{v}}}"
    if op == "index": return "n"
    if op == "nat_index":
        o = expr["offset"] - 1
        return "n" if o == 0 else "n" + (f"+{o}" if o > 0 else str(o))
    if op == "triangular": return r"\frac{n(n-1)}{2}"
    if op == "term":
        o = expr["offset"]
        return "a_{n}" if not o else "a_{n+" + str(o) + "}"
    args = expr["args"]
    if op == "add":
        out = ""
        for a in args:
            text = latex(a)
            out += ("" if not out or text.startswith("-") else "+") + text
        return out
    if op == "mul":
        out = []
        negative = False
        for a in args:
            if a == num(-1): negative = not negative; continue
            text = latex(a)
            if a["op"] == "add" or (a["op"] == "rational" and a["num"] < 0):
                text = r"\left(" + text + r"\right)"
            out.append(text)
        return ("-" if negative else "") + (r"\,".join(out) or "1")
    if op == "div": return rf"\frac{{{latex(args[0])}}}{{{latex(args[1])}}}"
    if op == "pow":
        base = latex(args[0])
        if args[0]["op"] != "rational" or args[0].get("num", 1) < 0 or args[0].get("den", 1) > 1:
            base = r"\left(" + base + r"\right)"
        return base + "^{" + latex(args[1]) + "}"
    raise ValueError(op)


def lean(expr, sequence="f"):
    op = expr["op"]
    if op == "rational":
        u, v = expr["num"], expr["den"]
        return f"({u} : ℚ)" if v == 1 else f"(({u} : ℚ) / {v})"
    if op == "index": return "((n : ℚ) + 1)"
    if op == "nat_index": return "n" if expr["offset"] == 0 else f"(n + {expr['offset']})"
    if op == "triangular": return "((n + 1).choose 2)"
    if op == "term": return f"({sequence} n)" if expr["offset"] == 0 else f"({sequence} (n + {expr['offset']}))"
    a = [lean(x, sequence) for x in expr["args"]]
    symbol = {"add": " + ", "mul": " * ", "div": " / ", "pow": " ^ "}[op]
    return "(" + symbol.join(a) + ")"


def replace_term(expr):
    if expr["op"] == "term":
        assert expr["offset"] == 0
        return {"op": "variable"}
    return {**expr, "args": [replace_term(a) for a in expr["args"]]} if "args" in expr else expr


def lean_step(expr):
    return lean(expr).replace("(f n)", "x")
