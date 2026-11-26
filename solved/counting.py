"""Construct a five-parameter family of shortest defect-two AM endpoints."""

from math import comb, isqrt

from .chains import level


def tower(k):
    if type(k) is not int or k < 0:
        raise ValueError("nonnegative tower index required")
    return 1 << (1 << k)


def lower_witness(k, i, j, h, d=0):
    """Parameters give an actual increasing value sequence from 1, with all writes charged."""
    return nested_witness(k, (i, j), (h,), d)


def _strip(n):
    count = 0
    while n > 1:
        root = isqrt(n)
        if root * root != n:
            break
        n = root
        count += 1
    return n, count


def _tower_index(n):
    if n <= 1 or n.bit_count() != 1:
        return None
    exponent = n.bit_length() - 1
    return exponent.bit_length() - 1 if exponent.bit_count() == 1 else None


def coordinates(n):
    """Recover the unique parameters or return None when n lies outside this family."""
    result = nested_coordinates(n, 2)
    if result is None:
        return None
    k, (i, j), (h,), d = result
    return k, i, j, h, d


def family_size_at_level(n):
    if type(n) is not int or n < 0:
        raise ValueError("expected a nonnegative level")
    return comb(n, 4) if n >= 4 else 0


def charged_steps(values, recipes):
    """Exact parameter charges for the upper bound. First write and 2→4 are normalized."""
    if not values or values[0] != 1 or len(values) != len(recipes) + 1:
        raise ValueError("invalid chain")
    charges = []
    prior_square = False
    for step, (op, a, b) in enumerate(recipes, 1):
        i = step - 1
        if op not in ("+", "*") or any(type(t) is not int or not 0 <= t < step for t in (a, b)):
            raise ValueError("invalid recipe")
        n = values[step]
        if (
            n <= (m := values[i])
            or n != (values[a] + values[b] if op == "+" else values[a] * values[b])
            or step - level(n) > 2
        ):
            raise ValueError("expected an increasing chain of defect at most two")
        square = n == m * m
        if step >= 3 and not square:
            if max(a, b) < i - 2:
                raise ArithmeticError("no operand among last three")
            charges.append(int(prior_square) + int(min(a, b) <= i - 6))
        # Squares counted only in gaps following the initial prefix 1,2,3/4.
        prior_square = square and step >= 3
    return tuple(charges)


def nested_witness(k, indices, gaps, trailing):
    """Generate a witness of defect len(indices); minimality is a separate question."""
    indices = tuple(indices)
    gaps = tuple(gaps)
    if (
        type(k) is not int
        or k < 1
        or not indices
        or any(type(i) is not int or not 0 <= i < k for i in indices)
        or any(a <= b for a, b in zip(indices, indices[1:]))
        or len(gaps) != len(indices) - 1
        or any(type(h) is not int or h < 1 for h in gaps)
        or type(trailing) is not int
        or trailing < 0
    ):
        raise ValueError("invalid nested-witness coordinates")
    row = [1, *(tower(i) for i in range(k + 1))]
    for j, idx in enumerate(indices):
        if j:
            for _ in range(gaps[j - 1]):
                row.append(row[-1] ** 2)
        row.append(row[-1] + tower(idx))
    for _ in range(trailing):
        row.append(row[-1] ** 2)
    return tuple(row)


def nested_coordinates(n, small):
    if type(n) is not int or n < 1 or type(small) is not int or small < 1:
        raise ValueError("invalid endpoint or defect")
    y, d = _strip(n)
    gaps = []
    indices = []
    for _ in range(small - 1):
        x = isqrt(y)
        idx = _tower_index(y - x * x)
        if idx is None:
            return None
        y, power = _strip(x)
        indices.append(idx)
        gaps.append(power + 1)
    if y.bit_count() != 2:
        return None
    b = y & -y
    k = _tower_index(y - b)
    i = _tower_index(b)
    if k is None or i is None or not i < k:
        return None
    indices.append(i)
    indices = tuple(reversed(indices))
    if any(a <= b for a, b in zip(indices, indices[1:])):
        return None
    return k, indices, tuple(reversed(gaps)), d
