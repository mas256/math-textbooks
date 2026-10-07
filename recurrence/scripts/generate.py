#!/usr/bin/env python3
"""Compile block recipes to one exact IR, a bank, and Lean proof obligations.

The browser selects certified instances. New parameters are introduced only in
this build step, and the publication workflow must check their Lean obligations.
"""
import hashlib
import itertools
import json
import random
from fractions import Fraction
from pathlib import Path

from expr import add, div, evaluate, index, latex, lean, lean_step, mul, nat, neg, num, power, shift, sub, term, triangular
from scoring import level, numeric_cost, route_score

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "build"
N = index()
P = mul(N, add(N, num(2)))
PN = shift(P)

FAMILIES = {
    "constant": "定数数列", "geometric": "等比数列", "affine": "特性方程式型（2項間）",
    "scaled_constant": "階比型", "shifted_scaled": "階比型＋定数の移動",
    "scaled_affine": "階比型＋特性方程式型", "second_order": "3項間漸化式",
    "ratio_power": "指数係数の階比型", "reciprocal_affine": "逆数型＋特性方程式型",
    "reciprocal_scaled": "逆数型＋階比型＋特性方程式型",
}


def block(kind, input_id, **kwargs):
    return {"id": "b" + str(block.counter()), "kind": kind, "input": input_id, **kwargs}


def route(title, operations, hint, discovery=0, domain=0, steps=None):
    return {"title": title, "hint": hint, "steps": steps or [],
            **route_score(operations, discovery=discovery, domain=domain)}


def compile_recipe(family, parameters):
    r, c, d, k, s = (num(parameters[x]) for x in ("r", "c", "d", "k", "s"))
    q = num((1 - parameters["r"]) * parameters["c"])
    bn = add(c, mul(d, power(r, nat())))
    blocks, core = [], "constant" if family in {"constant", "scaled_constant", "shifted_scaled", "ratio_power"} else "geometric" if family in {"geometric", "second_order"} else "affine_fixed_point"
    expr = d if core == "constant" else mul(d, power(r, nat())) if core == "geometric" else bn
    coefP, coefQ, coefR = num(1), num(1), num(0)
    reciprocal, second = False, False
    extra = {}
    core_params = {"initial": d} if core == "constant" else {"ratio": r, "amplitude": d}
    if core == "affine_fixed_point": core_params.update({"fixed_point": c, "constant_term": q})
    if family == "constant":
        routes = [route("同じ値が続く", ["constant"], "隣り合う項の値は変わりますか。",
                        steps=["漸化式から、すべての項が初項に等しいことがわかります。"])]
    elif family == "geometric":
        coefQ = r
        routes = [route("公比を読む", ["geometric"], "前の項にかけられている定数に注目します。",
                        steps=[rf"初項は \({latex(d)}\)、公比は \({latex(r)}\) です。等比数列の一般項を使います。"])]
    elif family == "affine":
        coefQ, coefR = r, q
        routes = [route("不動点を引いて等比数列にする", ["fixed_point", "geometric"], "毎回同じ値になる数を探し、それを引きます。", 1,
                        steps=[rf"\(x={latex(r)}x+{latex(q)}\) を解くと \(x={latex(c)}\) です。",
                               rf"\(b_n=a_n-{latex(c)}\) とおくと、\(b_{{n+1}}={latex(r)}b_n\)、\(b_1={latex(d)}\) になります。",
                               "等比数列の一般項を求め、置換を戻します。"])]
    elif family in {"scaled_constant", "shifted_scaled", "scaled_affine", "reciprocal_scaled"}:
        expr = mul(P, expr)
        blocks.append({"kind": "index_scale", "factor": P})
        coefP, coefQ = P, mul(r if core != "constant" else num(1), PN)
        coefR = mul(q, P, PN) if core != "constant" else num(0)
        operations = ["index_scale"] + (["constant"] if core == "constant" else ["fixed_point", "geometric"])
        discovery = 0 if family == "scaled_constant" else 2
        shift_value = k if family == "reciprocal_scaled" else neg(c) if family == "shifted_scaled" else num(0)
        if shift_value != num(0):
            expr = add(expr, shift_value)
            coefR = add(coefR, mul(shift_value, sub(P, coefQ)))
            blocks.append({"kind": "add_constant", "value": shift_value})
            operations = ["shift"] + operations
        steps = []
        if family == "shifted_scaled":
            steps.append(rf"\(b_n=a_n+{latex(c)}\) とおくと、\({latex(P)}b_{{n+1}}={latex(PN)}b_n\) です。")
            steps.append(rf"\(b_n/{latex(P)}\) は一定なので、初項からその値を決めます。")
        elif family == "scaled_constant":
            steps.append(rf"係数の比は \({latex(div(PN, P))}\) です。\(b_n=a_n/({latex(P)})\) とおくと \(b_{{n+1}}=b_n\) になります。")
        else:
            steps.append(rf"\(b_n=a_n/({latex(P)})\) とおくと \(b_{{n+1}}={latex(r)}b_n+{latex(q)}\) です。")
            steps.append(rf"さらに \(b_n-{latex(c)}\) が等比数列になることを使います。")
        routes = [route("係数の比から正規化する", operations,
                        "n と n+1 の係数は、同じ式を一つずらした形になっています。", discovery, steps=steps)]
        if family == "scaled_constant":
            routes.append(route("積の約分を使う", ["ratio_product", "evaluate_product", "constant"],
                                "隣り合う項の比を順にかけると、途中の因子が約分されます。", 1,
                                steps=[rf"\(a_n=a_1\prod_{{j=1}}^{{n-1}}\frac{{(j+1)(j+3)}}{{j(j+2)}}\) とします。",
                                       r"積は \(n(n+2)/3\) に約分できます。初項を代入します。"] ))
    elif family == "ratio_power":
        expr = mul(d, power(r, triangular()))
        coefQ = power(r, nat(1))
        blocks.append({"kind": "index_scale", "factor": power(r, triangular())})
        routes = [route("比をかけて指数を足す", ["ratio_product", "evaluate_product"],
                        "かけられる数の指数を、1 から n−1 まで足します。", 1,
                        steps=[rf"\(a_n={latex(d)}\prod_{{j=1}}^{{n-1}}{latex(r)}^j\) です。",
                               r"\(1+2+\cdots+(n-1)=n(n-1)/2\) を使って積を評価します。"]),
                  route("対数をとって和にする", ["logarithm", "difference_sum", "evaluate_sum"],
                        "すべての項が正なので、対数をとる方法も使えます。", 1, 1,
                        steps=[rf"初項と係数は正なので全項が正です。\(b_n=\log_{{{latex(r)}}}a_n\) とおくと \(b_{{n+1}}-b_n=n\) です。",
                               "差を足し合わせてから、指数の形に戻します。"])]
    elif family == "reciprocal_affine":
        expr, coefQ, coefR = bn, r, q
        reciprocal = True
        routes = [route("逆数をとって不動点を引く", ["reciprocal", "fixed_point", "geometric"],
                        "分母と分子を a_n で割り、逆数の関係を調べます。", 1, 1,
                        steps=[rf"\(b_n=1/a_n\) とおくと \(b_{{n+1}}={latex(r)}b_n+{latex(q)}\) です。",
                               rf"\(b_n-{latex(c)}\) は公比 \({latex(r)}\) の等比数列です。初項を代入してから逆数を戻します。",
                               "得られた逆数はすべて正なので、各項と漸化式の分母は 0 になりません。"])]
    elif family == "second_order":
        second = True
        A, B = d, c
        expr = add(mul(A, power(r, nat())), mul(B, power(s, nat())))
        blocks.append({"kind": "linear_combination", "other_core": {"kind": "geometric", "ratio": s, "initial": B}})
        extra = {"p": num(parameters["r"] + parameters["s"]), "q": num(-parameters["r"] * parameters["s"])}
        routes = [route("特性多項式の根を使う", ["characteristic_distinct"],
                        "3項間なので、λ²−pλ−q=0 という特性多項式を作ります。", 1,
                        steps=[rf"特性多項式は \((\lambda-{latex(r)})(\lambda-{latex(s)})=0\) です。",
                               rf"\(a_n=A{latex(r)}^{{n-1}}+B{latex(s)}^{{n-1}}\) とおき、二つの初期値を代入すると \(A={latex(A)}\)、\(B={latex(B)}\) になります。"])]
    if family == "reciprocal_scaled":
        reciprocal = True
        operations = ["reciprocal"] + routes[0]["operations"]
        routes = [route("逆数をとり、定数を引いて正規化する", operations,
                        "まず逆数をとると、n の係数の規則が見える形になります。", 2, 1,
                        steps=[rf"\(v_n=1/a_n\) とおくと、\({latex(P)}v_{{n+1}}={latex(coefQ)}v_n+{latex(coefR)}\) です。",
                               rf"\(b_n=(v_n-{latex(k)})/({latex(P)})\) とおくと、\(b_{{n+1}}={latex(r)}b_n+{latex(q)}\) になります。",
                               rf"不動点 \({latex(c)}\) を引いて等比数列を解き、二つの置換を戻します。",
                               "一般項の分母は正です。この正値性から、元の漸化式も全項で定義されます。"])]
    underlying = expr
    if reciprocal:
        expr = div(num(1), underlying)
        blocks.append({"kind": "reciprocal", "requires": "positive_input"})
        step = div(mul(coefP, term()), add(coefQ, mul(coefR, term())))
        lhs, rhs = term(1), step
    elif second:
        step = None
        lhs, rhs = term(2), add(mul(extra["p"], term(1)), mul(extra["q"], term()))
    else:
        step = div(add(mul(coefQ, term()), coefR), coefP)
        lhs, rhs = mul(coefP, term(1)), add(mul(coefQ, term()), coefR)
    routes.sort(key=lambda rt: rt["cost"])
    dcost = routes[0]["cost"]
    initial = evaluate(expr, 0)
    initials = [num(initial)] + ([num(evaluate(expr, 1))] if second else [])
    statement_numbers = {Fraction(v) for v in parameters.values()} | {initial}
    if second: statement_numbers.add(evaluate(expr, 1))
    numeric = sum(numeric_cost(x) for x in statement_numbers)
    recipe_blocks = []
    previous = "core"
    for i, b in enumerate(blocks, 1):
        recipe_blocks.append({"id": f"b{i}", "input": previous, **b})
        previous = f"b{i}"
    recipe = {"schema_version": "0.2", "rule_set_version": "0.2.0",
              "domain": {"index_start": 1, "sequence_type": "rational"},
              "core": {"id": "core", "kind": core, "parameters": core_params},
              "blocks": recipe_blocks, "output": previous,
              "parameters": {key: num(value) for key, value in parameters.items()}}
    return {"family": family, "family_label": FAMILIES[family], "recipe": recipe,
            "ir": {"formula": expr, "initials": initials, "lhs": lhs, "rhs": rhs,
                   "step": step, "P": coefP, "Q": coefQ, "R": coefR,
                   "underlying": underlying, "reciprocal": reciprocal, "second_order": second, **extra},
            "statement": {"initials_tex": [f"a_{{{i+1}}}={latex(v)}" for i, v in enumerate(initials)],
                          "recurrence_tex": latex(lhs) + "=" + latex(rhs),
                          "condition": "n は 1 以上の整数とする。数列の一般項 a_n を求めよ。"},
            "answer_tex": "a_n=" + latex(expr), "routes": routes,
            "scores": {"difficulty": dcost, "level": level(dcost), "cleanliness": numeric,
                       "quality_proposal": 23 if family in {"constant", "geometric"} else 29,
                       "quality_status": "heuristic", "version": "0.2.0"}}


def proofs(problem):
    name, ir = problem["id"], problem["ir"]
    fexpr = lean(ir["formula"])
    init = lean(ir["initials"][0])
    lines = [f"def {name} (n : ℕ) : ℚ := {fexpr}"]
    if ir["second_order"]:
        p, q, sec = lean(ir["p"]), lean(ir["q"]), lean(ir["initials"][1])
        cert = f"SecondCertificate {name} {init} {sec} {p} {q}"
        lines += [f"theorem {name}_valid : {cert} := by", "  constructor",
                  f"  · norm_num [{name}]", f"  · norm_num [{name}]",
                  "  · intro n", f"    simp only [{name}, pow_succ, pow_add]", "    ring",
                  f"theorem {name}_unique (a : ℕ → ℚ) (ha : SecondCertificate a {init} {sec} {p} {q}) :",
                  f"    ∀ n, a n = {name} n := second_unique {name}_valid ha"]
    else:
        Pn, Qn, Rn = [lean(ir[x]) for x in ("P", "Q", "R")]
        Pfn, Qfn, Rfn = [f"(fun n : ℕ => {s})" for s in (Pn, Qn, Rn)]
        underlying = name + "_base" if ir["reciprocal"] else name
        if ir["reciprocal"]:
            lines.append(f"def {underlying} (n : ℕ) : ℚ := {lean(ir['underlying'])}")
        base_init = lean(num(evaluate(ir["underlying"], 0)))
        base_step = f"(fun n x => ({Qn} * x + {Rn}) / {Pn})"
        lines += [f"theorem {name}_base_valid : FirstCertificate {underlying} {base_init} {base_step} := by",
                  f"  apply linear_certificate {underlying} {base_init} {Pfn} {Qfn} {Rfn}",
                  f"  · norm_num [{underlying}]", "  · intro n; positivity", "  · intro n",
                  f"    simp only [{underlying}, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]",
                  "    ring"]
        if ir["reciprocal"]:
            actual_step = f"(fun n x => {Pn} * x / ({Qn} + {Rn} * x))"
            lines += [f"theorem {name}_positive (n : ℕ) : 0 < {underlying} n := by",
                      f"  unfold {underlying}", "  positivity",
                      f"theorem {name}_valid : FirstCertificate {name} {init} {actual_step} := by",
                      f"  have h := reciprocal_certificate {name}_base_valid {name}_positive (by intro n; positivity)",
                      f"  simpa only [{name}, {underlying}] using h.1",
                      f"theorem {name}_domain : (∀ n : ℕ, {Qn} + {Rn} * {name} n ≠ 0) ∧ (∀ n, {name} n ≠ 0) := by",
                      f"  have h := reciprocal_certificate {name}_base_valid {name}_positive (by intro n; positivity)",
                      f"  simpa only [{name}, {underlying}] using h.2"]
            lines.append(f"#print axioms {name}_domain")
        else:
            actual_step = base_step
            lines.append(f"theorem {name}_valid : FirstCertificate {name} {init} {actual_step} := {name}_base_valid")
        lines += [f"theorem {name}_unique (a : ℕ → ℚ) (ha : FirstCertificate a {init} {actual_step}) :",
                  f"    ∀ n, a n = {name} n := first_unique {name}_valid ha"]
    lines += [f"#print axioms {name}_valid", f"#print axioms {name}_unique"]
    return "\n".join(lines) + "\n"


def validate(problem):
    ir = problem["ir"]
    assert problem["scores"]["level"] in range(1, 5)
    for n in range(24):
        xs = {i: evaluate(ir["formula"], n + i) for i in (0, 1, 2)}
        assert evaluate(ir["lhs"], n, xs) == evaluate(ir["rhs"], n, xs), (problem["id"], n)
        if ir["reciprocal"]:
            assert xs[0] > 0
            assert evaluate(add(ir["Q"], mul(ir["R"], term())), n, xs) != 0
    return 24


def main():
    BUILD.mkdir(exist_ok=True)
    parameters = list(itertools.product((2, 3), (1, 2, 3), (1, 2, 3, 4, Fraction(1, 2)), (1, 2), (3, 4)))
    rng = random.Random(20261007)
    rng.shuffle(parameters)
    problems, fingerprints = [], set()
    for family in FAMILIES:
        candidates = []
        for r, c, d, k, s in parameters:
            if r == s: continue
            p = compile_recipe(family, {"r": r, "c": c, "d": d, "k": k, "s": s})
            fingerprint = json.dumps([p["ir"]["lhs"], p["ir"]["rhs"], p["ir"]["initials"]], sort_keys=True)
            if fingerprint in fingerprints: continue
            fingerprints.add(fingerprint)
            candidates.append(p)
        candidates.sort(key=lambda p: p["scores"]["cleanliness"])
        for p in candidates[:5]:
            p["id"] = f"p{len(problems)+1:03}"
            validate(p)
            p["lean_theorems"] = [p["id"] + "_valid", p["id"] + "_unique"] + ([p["id"] + "_domain"] if p["ir"]["reciprocal"] else [])
            p["lean_source"] = "import Recurrence.Theory\n\nnamespace Recurrence\n" + proofs(p) + "end Recurrence\n"
            problems.append(p)
    assert len(problems) == 50
    source = "import Recurrence.Theory\n\nnamespace Recurrence\n\n" + "\n".join(proofs(p) for p in problems) + "\nend Recurrence\n"
    generated = ROOT / "lean/Recurrence/Generated.lean"
    generated.write_text(source, encoding="utf-8")
    payload = {"schema_version": "0.2", "score_version": "0.2.0", "generator_version": "0.1.0",
               "families": FAMILIES, "problems": problems,
               "checks": {"exact_arithmetic_cases": len(problems) * 24},
               "proof_source_sha256": hashlib.sha256(source.encode()).hexdigest()}
    (BUILD / "candidates.json").write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Generated {len(problems)} problems / {len(FAMILIES)} families; 1200 exact term checks passed.")


if __name__ == "__main__": main()
