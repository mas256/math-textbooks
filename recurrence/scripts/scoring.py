"""Provisional v0.2 scores; they are not empirically calibrated difficulty."""
from fractions import Fraction
from math import isqrt

PREFERRED_NUM = {0, 1, 2, 3, 4, 5, 6, 8, 9, 16, 25}
PREFERRED_DEN = {1, 2, 3, 5, 8, 9}
OPERATIONS = {"constant": 1, "geometric": 2, "fixed_point": 2,
              "shift": 2, "index_scale": 3, "reciprocal": 3,
              "characteristic_distinct": 5, "characteristic_repeated": 6,
              "ratio_product": 2, "evaluate_product": 1,
              "logarithm": 3, "difference_sum": 2, "evaluate_sum": 1}


def component_cost(n, preferred):
    n = abs(n)
    if n in preferred: return 0
    score = 1 if n <= 10 else 2 if n <= 30 else 3 if n <= 100 else 4 if n <= 1000 else min(8, 5 + len(str(n)) - 4)
    powers = {b ** e for b in (2, 3, 5) for e in range(1, 8) if b ** e <= 125}
    if n <= 100 and isqrt(n) ** 2 == n or n in powers: score = max(0, score - 1)
    return score


def numeric_cost(value):
    value = Fraction(value)
    return component_cost(value.numerator, PREFERRED_NUM) + component_cost(value.denominator, PREFERRED_DEN)


def route_score(operations, discovery=0, arithmetic=0, domain=0, expression=0, unfinished=0):
    parts = {"B": sum(OPERATIONS[o] for o in operations), "R": discovery,
             "A": min(6, arithmetic), "T": domain, "P": expression, "U": unfinished}
    return {"operations": operations, "parts": parts, "cost": sum(parts.values())}


def level(cost):
    for lv, top in enumerate((3, 7, 12, 18, 25), 1):
        if cost <= top: return lv
    return None
