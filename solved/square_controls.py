"""Finite controls for AM chains with bounded canonical nonsquare count."""

from dataclasses import dataclass

from .chains import Chain


@dataclass(frozen=True)
class Description:
    control: tuple[tuple[str, int, int | None], ...]
    runs: tuple[int, ...]

    @property
    def length(self):
        return len(self.control) - len(self.runs) + sum(self.runs)


def encode(chain):
    values, recipes = chain.values, chain.recipes
    if not values or values[0] != 1 or len(values) != len(recipes) + 1:
        raise ValueError("invalid AM chain dimensions")
    if any(type(v) is not int or v < 1 for v in values):
        raise ValueError("positive integer values required")
    nonsquares = set()
    marked = {0, len(values) - 1}
    for i, recipe in enumerate(recipes, 1):
        if len(recipe) != 3:
            raise ValueError("invalid AM recipe")
        op, a, b = recipe
        if op not in ("+", "*") or any(type(j) is not int or not 0 <= j < i for j in (a, b)):
            raise ValueError("invalid AM operands")
        result = values[a] + values[b] if op == "+" else values[a] * values[b]
        if result != values[i] or values[i] <= values[i - 1]:
            raise ValueError("expected a valid increasing AM chain")
        if values[i] != values[i - 1] ** 2:
            nonsquares.add(i)
            marked.update((i, a, b))
    marks = sorted(marked)
    indices = {old: i for i, old in enumerate(marks)}
    control = []
    runs = []
    for left, right in zip(marks, marks[1:]):
        if right in nonsquares:
            if right != left + 1:
                raise ArithmeticError("an increasing nonsquare after a square must read its head")
            op, a, b = recipes[right - 1]
            control.append((op, indices[a], indices[b]))
        else:
            control.append(("squares", indices[left], None))
            runs.append(right - left)
    if len(marks) > 3 * len(nonsquares) + 2:
        raise ArithmeticError("mark count exceeded its combinatorial bound")
    return Description(tuple(control), tuple(runs))


def expand(description):
    """Evaluate positive expressions, including parameter choices that cease to increase."""
    if any(type(k) is not int or k < 1 for k in description.runs):
        raise ValueError("positive square-run lengths required")
    values = [1]
    recipes = []
    marks = [0]
    position = 0
    for op, a, b in description.control:
        if type(a) is not int or not 0 <= a < len(marks):
            raise ValueError("invalid saved operand")
        if op == "squares":
            if b is not None or position >= len(description.runs):
                raise ValueError("invalid square block")
            index = marks[a]
            for _ in range(description.runs[position]):
                values.append(values[index] ** 2)
                recipes.append(("*", index, index))
                index = len(values) - 1
            position += 1
        elif op in ("+", "*") and type(b) is int and 0 <= b < len(marks):
            x, y = marks[a], marks[b]
            values.append(values[x] + values[y] if op == "+" else values[x] * values[y])
            recipes.append((op, x, y))
        else:
            raise ValueError("invalid marked instruction")
        marks.append(len(values) - 1)
    if position != len(description.runs):
        raise ValueError("unused square parameters")
    return Chain(tuple(values), tuple(recipes))
