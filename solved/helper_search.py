"""Exact shared-helper search with target saturation and unlimited retention."""

from itertools import combinations_with_replacement
from math import isqrt

from .arithmetic import binary_results, missing_operand


def next_values(available, limit):
    choices = {}
    for a, b in combinations_with_replacement(sorted(available), 2):
        for value, recipe in binary_results(a, b, limit):
            if value not in available:
                choices.setdefault(value, recipe)
    return choices


def saturate(available, targets, limit):
    available = set(available)
    writes = []
    while targets - available:
        choices = next_values(available, limit)
        reached = sorted(targets.intersection(choices))
        if not reached:
            break
        for value in reached:
            writes.append((value, *choices[value]))
            available.add(value)
    return frozenset(available), tuple(writes)


def terminal_menu(available, targets, limit):
    """All possible last helpers before the first still-missing target."""
    offered = set()
    for target in targets - available:
        for known in available:
            offered.update(value for value, _ in missing_operand(target, known, limit))
        if target % 2 == 0:
            offered.add(target // 2)
        root = isqrt(target)
        if root * root == target:
            offered.add(root)
    return offered - available


def synthesize(seeds, targets, limit, helper_budget, *, terminal_pruning=True):
    """Return a minimum-write tape within the helper budget, or None after exhaustion.

    Each row is (result, operation, left value, right value). All computed values
    remain available. A physical register bound requires a separate scheduler.
    """
    seeds, targets = tuple(seeds), tuple(targets)
    if (
        type(limit) is not int
        or limit < 1
        or not seeds
        or type(terminal_pruning) is not bool
        or type(helper_budget) is not int
        or helper_budget < 0
        or any(type(v) is not int or not 1 <= v <= limit for v in seeds + targets)
    ):
        raise ValueError("invalid bounded synthesis problem")
    seeds, targets = frozenset(seeds), frozenset(targets)
    initial, tape = saturate(seeds, targets, limit)
    layer = {frozenset(): (initial, tape)}
    for count in range(helper_budget + 1):
        if not layer:
            return None
        following = {}
        for helpers, (available, tape) in layer.items():
            if targets <= available:
                return tape
            if count == helper_budget:
                continue
            choices = next_values(available, limit)
            if terminal_pruning and count + 1 == helper_budget:
                relevant = terminal_menu(available, targets, limit)
                choices = {v: r for v, r in choices.items() if v in relevant}
            for value, recipe in sorted(choices.items()):
                new_helpers = helpers | {value}
                if new_helpers in following:
                    continue
                if value in targets:
                    raise ArithmeticError("target saturation was incomplete")
                closed, tail = saturate(available | {value}, targets, limit)
                witness = tape + ((value, *recipe),) + tail
                if targets <= closed:
                    return witness
                following[new_helpers] = (closed, witness)
        layer = following
    return None
