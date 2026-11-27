"""Minimum-write positive AM programs over a finite menu of integer values.

Support sets count shared ancestors once. Superset dominance is exact in
this unrestricted-retention, positive addition/multiplication model.
"""

from .chains import Chain
from .limits import ResourceLimit


def validate_limits(max_states, max_pairs):
    for value in (max_states, max_pairs):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError("search limits must be nonnegative integers or None")


def _recipes(values):
    positions = {value: i for i, value in enumerate(values)}
    rows = [[]]
    for j, value in enumerate(values[1:], 1):
        recipes = []
        for a, left in enumerate(values[:j]):
            right = value - left
            b = positions.get(right)
            if b is not None and a <= b < j:
                recipes.append(("+", a, b))
            if left > 1 and value % left == 0:
                b = positions.get(value // left)
                if b is not None and a <= b < j:
                    recipes.append(("*", a, b))
        rows.append(recipes)
    return rows


def shortest_from_menu(
    menu, target, write_budget, *, required=(), max_states=100_000, max_pairs=1_000_000
):
    """Return a shortest menu-restricted chain within budget, or None.

    All required values must occur before or at the final target. Only 1 is
    free. Every other value must have a real +/* recipe, including
    any roots or constants supplied in the menu. Resource stops raise
    ResourceLimit. None means exhaustive failure in this menu and budget.
    """
    menu = tuple(menu)
    required = tuple(required)
    if (
        type(target) is not int
        or target < 1
        or type(write_budget) is not int
        or write_budget < 0
        or any(type(value) is not int or value < 1 for value in menu)
        or 1 not in menu
        or target not in menu
        or any(type(v) is not int or not 1 <= v <= target or v not in menu for v in required)
    ):
        raise ValueError(
            "a positive menu containing 1, the target and all required values is required"
        )
    validate_limits(max_states, max_pairs)
    values = tuple(sorted({value for value in menu if value <= target}))
    required = tuple(sorted(set(required) - {1, target}))
    if target == 1:
        return Chain((1,), ())
    recipes = _recipes(values)
    supports = [(0,)]
    states = pairs = 0

    def join_into(lefts, rights, extra, kept):
        nonlocal states, pairs
        for left in lefts:
            for right in rights:
                pairs += 1
                if max_pairs is not None and pairs > max_pairs:
                    raise ResourceLimit("support-pair budget exceeded")
                candidate = left | right | extra
                if candidate.bit_count() > write_budget:
                    continue
                if any(old & candidate == old for old in kept):
                    continue
                remaining = [old for old in kept if candidate & old != candidate]
                states += len(remaining) + 1 - len(kept)
                kept[:] = [*remaining, candidate]
                if max_states is not None and states > max_states:
                    raise ResourceLimit("retained-support budget exceeded")

    for j in range(1, len(values)):
        kept = []
        for _, a, b in recipes[j]:
            join_into(supports[a], supports[b], 1 << j, kept)
        supports.append(tuple(sorted(kept, key=lambda mask: (mask.bit_count(), mask))))
    if not supports[-1]:
        return None
    # Join whole ancestor supports, rather than independently optimizing each
    # required value: incomparable supports can share different later work.
    positions_by_value = {value: i for i, value in enumerate(values)}
    joint = supports[-1]
    allocated_joint = False
    for value in required:
        kept = []
        join_into(joint, supports[positions_by_value[value]], 0, kept)
        if allocated_joint:
            states -= len(joint)
        joint = tuple(sorted(kept, key=lambda mask: (mask.bit_count(), mask)))
        allocated_joint = True
        if not joint:
            return None
    mask = joint[0]
    positions = {0: 0}
    output, tape = [1], []
    for j, value in enumerate(values[1:], 1):
        if not mask & (1 << j):
            continue
        recipe = next(
            (
                (op, positions[a], positions[b])
                for op, a, b in recipes[j]
                if a in positions and b in positions
            ),
            None,
        )
        if recipe is None:
            raise ArithmeticError("a retained support has no internally supported recipe")
        positions[j] = len(output)
        output.append(value)
        tape.append(recipe)
    if (
        output[-1] != target
        or len(tape) != mask.bit_count()
        or len(tape) > write_budget
        or not set(required) <= set(output)
    ):
        raise ArithmeticError("menu witness does not match its support certificate")
    return Chain(tuple(output), tuple(tape))
