"""Exact fractional-linear path operations."""

import math

from .arithmetic import calculate, canonical

IDENTITY = (1, 0, 0, 1)


def compose(outer, inner):
    a, b, c, d = outer
    e, f, g, h = inner
    row = (a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h)
    common = math.gcd(*row)
    if next(v for v in row if v) < 0:
        common = -common
    return tuple(v // common for v in row)


def path_matrix(path):
    matrix = IDENTITY
    for op, k, reverse in path:
        if op == "+":
            step = (1, k, 0, 1)
        elif op == "-":
            step = (-1, k, 0, 1) if reverse else (1, -k, 0, 1)
        elif op == "*":
            step = (k, 0, 0, 1)
        else:
            step = (0, k, 1, 0) if reverse else (1, 0, 0, k)
        matrix = compose(step, matrix)
    return matrix


def relation(left, right, op, target, swapped):
    """Map the first hole to the second under the fixed root identity."""
    a, b, c, d = path_matrix(right)
    inv = (d, -b, -c, a)
    if op == "+":
        bridge = (-1, target, 0, 1)
    elif op == "-":
        bridge = (1, target if swapped else -target, 0, 1)
    elif op == "*":
        bridge = (0, target, 1, 0)
    else:
        bridge = (target, 0, 0, 1) if swapped else (1, 0, 0, target)
    return compose(inv, compose(bridge, path_matrix(left)))


def image(matrix, x, limit):
    a, b, c, d = matrix
    numerator = a * x + b
    denominator = c * x + d
    if not denominator:
        return None
    y, r = divmod(numerator, denominator)
    return y if not r and 1 <= y <= limit else None


def fixed_points(matrix, limit):
    """Isolated integral y=x solutions, independent of determinant factorization."""
    a, b, c, d = matrix
    if c:
        discriminant = (d - a) ** 2 + 4 * c * b
        if discriminant < 0:
            return ()
        root = math.isqrt(discriminant)
        if root * root != discriminant:
            return ()
        ratios = ((a - d + root, 2 * c), (a - d - root, 2 * c))
    elif d != a:
        ratios = ((b, d - a),)
    else:
        return ()
    return sorted({n // m for n, m in ratios if n % m == 0 and 1 <= n // m <= limit})


def trace(value, path, limit):
    steps = []
    for op, k, rev in path:
        a, b = (k, value) if rev else (value, k)
        value = calculate(op, a, b, limit)
        steps.append((value, canonical(op, a, b)))
    return value, steps
