"""Trusted generation policy: limits count types on a normalized path."""
import copy
import json
from collections import Counter
from pathlib import Path

from expr import add, evaluate, mul, num
from profiles import EXPONENTS, SCALES, exponent_name, scale_name

CONFIG_PATH = Path(__file__).resolve().parents[1] / "generation-config.json"


class RuleViolation(ValueError):
    pass


def load_config(path=CONFIG_PATH):
    config = json.loads(Path(path).read_text(encoding="utf-8"))
    assert set(config["scale_profiles"]) <= SCALES.keys()
    assert set(config["exponent_profiles"]) <= EXPONENTS.keys()
    assert all(isinstance(v, int) and v >= 0 for v in config["max_transforms"].values())
    assert isinstance(config["max_blocks"], int) and config["max_blocks"] >= 0
    assert all(isinstance(v, int) and v >= 0 for v in config["quality_limits"].values())
    assert all(isinstance(v, int) and v >= 0 for v in config["quotas"].values())
    assert set(config['selection']) == {'balance_parameters','prefer_existing_ids'}
    assert all(isinstance(v,bool) for v in config['selection'].values())
    for lv,limits in config['difficulty_mix'].items():
        assert lv in {'1','2','3','4'}
        assert set(limits)=={'min_nonfraction_families','max_fraction_percent'}
        assert isinstance(limits['min_nonfraction_families'],int) and limits['min_nonfraction_families']>=0
        assert isinstance(limits['max_fraction_percent'],int) and 0<=limits['max_fraction_percent']<=100
    return config


def normalize_recipe(recipe, config=None):
    config = config or load_config()
    result = copy.deepcopy(recipe)
    previous = result["core"]["id"]
    seen = {previous}
    normalized = []
    for block in result["blocks"]:
        assert block["input"] == previous, "Dangling or reordered input"
        assert block["id"] not in seen, "Duplicate block id"
        previous = block["id"]
        seen.add(previous)
        kind = block["kind"]
        if kind not in config["max_transforms"]:
            raise RuleViolation("unregistered_transform:" + kind)
        if kind in {"add_constant", "constant_scale"}:
            key = "value" if kind == "add_constant" else "factor"
            assert block[key]["op"] == "rational"
            if normalized and normalized[-1]["kind"] == kind:
                operation = add if kind == "add_constant" else mul
                normalized[-1][key] = operation(normalized[-1][key], block[key])
                if normalized[-1][key] == num(0 if kind == "add_constant" else 1):
                    normalized.pop()
                continue
            if block[key] == num(0 if kind == "add_constant" else 1):
                continue
            if kind == "constant_scale" and evaluate(block[key], 0) <= 0:
                raise RuleViolation("nonpositive_constant_scale")
        if kind == "reciprocal":
            assert block["requires"] == "positive_input"
            if normalized and normalized[-1]["kind"] == kind:
                # Reject redundant candidates, including undefined intermediate
                # inversions; never erase a domain obligation by cancellation.
                raise RuleViolation("redundant_inverse_pair")
        if kind == "index_scale":
            name = scale_name(block["factor"], config) or exponent_name(block["factor"], config)
            if name is None:
                raise RuleViolation("unregistered_scale_profile")
            if block.get("profile", name) != name:
                raise RuleViolation("profile_expression_mismatch")
            block["profile"] = name
        if kind == "index_add":
            from expr import polynomial
            if max(polynomial(block["value"]), default=0) > 1:
                raise RuleViolation("unregistered_additive_degree")
        if kind in {'repeated_factor','difference_lift','cumulative_sum','power_sequence'}:
            key='slope' if kind=='repeated_factor' else 'base' if kind=='power_sequence' else 'initial'
            assert block[key]['op']=='rational'
        if kind=='power_sequence' and evaluate(block['base'],0) not in {2,3}:
            raise RuleViolation('unregistered_power_base')
        normalized.append(block)
    assert previous == result["output"], "Dangling output"
    counts = Counter(b["kind"] for b in normalized)
    for kind, count in counts.items():
        if count > config["max_transforms"][kind]:
            raise RuleViolation("transform_limit:" + kind)
    if len(normalized) > config["max_blocks"]:
        raise RuleViolation("block_limit")
    previous = result["core"]["id"]
    for i, block in enumerate(normalized, 1):
        block.update(id=f"b{i}", input=previous)
        previous = block["id"]
    result.update(blocks=normalized, output=previous)
    return result
