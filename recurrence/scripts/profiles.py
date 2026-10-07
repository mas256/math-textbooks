"""Finite, role-specific functions, with their products/differences retained."""
from expr import add, div, index, mul, nat, nat_const, num, power, shift, triangular

N = index()
SCALES = {
    "n": N,
    "n_plus_1": add(N, num(1)),
    "n_squared": power(N, nat_const(2)),
    "consecutive": mul(N, add(N, num(1))),
    "gap_2": mul(N, add(N, num(2))),
    "odd": add(mul(num(2), N), num(1)),
}
SCALE_LABELS = {
    "n": "n", "n_plus_1": "n+1", "n_squared": "n²",
    "consecutive": "n(n+1)", "gap_2": "n(n+2)", "odd": "2n+1",
}
EXPONENTS = {
    "triangular": {"total": triangular(), "increment": nat(1), "label": "指数 n の和"},
    "square_minus_one": {
        "total": mul(nat(), nat(2)),
        "increment": add(mul(nat_const(2), nat(1)), nat_const(1)),
        "label": "指数 2n+1 の和",
    },
    "tetrahedral": {
        "total": {"op": "choose", "args": [nat(2), nat_const(3)]},
        "increment": {"op": "choose", "args": [nat(2), nat_const(2)]},
        "label": "指数 n(n+1)/2 の和",
    },
}


def scale_options(config):
    for name in config["scale_profiles"]:
        g = SCALES[name]
        yield name, g
        if config["allow_inverse_scales"]:
            yield "inverse:" + name, div(num(1), g)


def scale_name(factor, config):
    for name, candidate in scale_options(config):
        if candidate == factor:
            return name
    return None


def exponent_name(factor, config):
    if factor["op"] != "pow" or factor["args"][0]["op"] != "rational":
        return None
    for name in config["exponent_profiles"]:
        if factor["args"][1] == EXPONENTS[name]["total"]:
            return name
    return None


def profile_catalog(config):
    from expr import latex
    scales = [{"id": name, "normalizer_tex": latex(g),
               "ratio_tex": latex(div(g['args'][1],shift(g['args'][1])) if g['op']=='div' else div(shift(g),g)),
               "roles": ["normalizer", "telescoping_ratio", "power_after_log"]}
              for name, g in scale_options(config)]
    exponents = [{"id": name, "total_tex": latex(EXPONENTS[name]["total"]),
                  "increment_tex": latex(EXPONENTS[name]["increment"]),
                  "roles": ["exponent_increment"]}
                 for name in config["exponent_profiles"]]
    return {"scales": scales, "exponents": exponents}
