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


def shortest_from_menu(menu, target, write_budget, *, max_states=100_000, max_pairs=1_000_000):
    """Return a shortest menu-restricted chain within budget, or None.

    Only 1 is free. Every other value must have a real +/* recipe, including
    any roots or constants supplied in the menu. Resource stops raise
    ResourceLimit. None means exhaustive failure in this menu and budget.
    """
    menu = tuple(menu)
    if (
        type(target) is not int
        or target < 1
        or type(write_budget) is not int
        or write_budget < 0
        or any(type(value) is not int or value < 1 for value in menu)
        or 1 not in menu
        or target not in menu
    ):
        raise ValueError("a positive menu containing 1 and the target is required")
    validate_limits(max_states, max_pairs)
    values = tuple(sorted({value for value in menu if value <= target}))
    if target == 1:
        return Chain((1,), ())
    recipes = _recipes(values)
    supports = [(0,)]
    states = pairs = 0
    for j in range(1, len(values)):
        kept = []
        for _, a, b in recipes[j]:
            for left in supports[a]:
                for right in supports[b]:
                    pairs += 1
                    if max_pairs is not None and pairs > max_pairs:
                        raise ResourceLimit("support-pair budget exceeded")
                    candidate = left | right | (1 << j)
                    if candidate.bit_count() > write_budget:
                        continue
                    if any(old & candidate == old for old in kept):
                        continue
                    remaining = [old for old in kept if candidate & old != candidate]
                    states += len(remaining) + 1 - len(kept)
                    kept = [*remaining, candidate]
                    if max_states is not None and states > max_states:
                        raise ResourceLimit("retained-support budget exceeded")
        supports.append(tuple(sorted(kept, key=lambda mask: (mask.bit_count(), mask))))
    if not supports[-1]:
        return None
    mask = supports[-1][0]
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
    if output[-1] != target or len(tape) != mask.bit_count() or len(tape) > write_budget:
        raise ArithmeticError("menu witness does not match its support certificate")
    return Chain(tuple(output), tuple(tape))
