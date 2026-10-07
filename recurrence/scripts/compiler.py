"""Versioned block recipes are the sole source of the mathematical IR."""
from expr import add, div, evaluate, expand_polynomial, mul, nat, num, power, shift, sub, term


def compile_blocks(recipe):
    assert recipe["schema_version"] == "0.2"
    assert recipe["domain"] == {"index_start": 1, "sequence_type": "rational"}
    core = recipe["core"]
    params = core["parameters"]
    P, Q, R = num(1), num(1), num(0)
    if core["kind"] == "constant":
        formula = params["initial"]
    elif core["kind"] == "geometric":
        formula = mul(params["amplitude"], power(params["ratio"], nat()))
        Q = params["ratio"]
    elif core["kind"] == "affine_fixed_point":
        formula = add(params["fixed_point"], mul(params["amplitude"], power(params["ratio"], nat())))
        Q, R = params["ratio"], params["constant_term"]
    else:
        raise ValueError("Unknown core")
    second_order = reciprocal = False
    previous = core["id"]
    extra = {}
    underlying = formula
    for b in recipe["blocks"]:
        assert b["input"] == previous, "The initial compiler supports one typed chain"
        assert not reciprocal and not second_order, "This block cannot follow an inverse or second-order state in v0.1"
        kind = b["kind"]
        if kind == "index_scale":
            factor = b["factor"]
            if factor["op"] == "pow" and factor["args"][1]["op"] == "triangular":
                assert core["kind"] == "constant" and not recipe["blocks"][:recipe["blocks"].index(b)]
                P, Q, R = num(1), power(factor["args"][0], nat(1)), num(0)
            else:
                following = shift(factor)
                P, Q, R = mul(P, factor), mul(Q, following), mul(R, factor, following)
            formula = mul(factor, formula)
        elif kind == "add_constant":
            value = b["value"]
            R = add(R, expand_polynomial(mul(value, sub(P, Q))))
            formula = add(formula, value)
        elif kind == "reciprocal":
            assert b["requires"] == "positive_input"
            reciprocal = True
            underlying, formula = formula, div(num(1), formula)
        elif kind == "linear_combination":
            assert core["kind"] == "geometric"
            other = b["other_core"]
            assert other["kind"] == "geometric"
            r, s = params["ratio"], other["ratio"]
            assert r != s, "Repeated roots have a different construction rule"
            formula = add(formula, mul(other["initial"], power(s, nat())))
            extra = {"p": num(evaluate(add(r, s), 0)), "q": num(-evaluate(mul(r, s), 0))}
            second_order = True
        else:
            raise ValueError("Unknown or unsupported block: " + kind)
        previous = b["id"]
    assert previous == recipe["output"]
    if not reciprocal: underlying = formula
    if second_order:
        lhs, rhs = term(2), add(mul(extra["p"], term(1)), mul(extra["q"], term()))
        step = None
    elif reciprocal:
        step = div(mul(P, term()), add(Q, mul(R, term())))
        lhs, rhs = term(1), step
    else:
        step = div(add(mul(Q, term()), R), P)
        lhs, rhs = mul(P, term(1)), add(mul(Q, term()), R)
    return {"formula": formula, "initials": [num(evaluate(formula, 0))] + ([num(evaluate(formula, 1))] if second_order else []),
            "lhs": lhs, "rhs": rhs, "step": step, "P": P, "Q": Q, "R": R,
            "underlying": underlying, "reciprocal": reciprocal, "second_order": second_order, **extra}
