"""Represent every legal root of a balanced affine component by one arithmetic progression."""

from math import gcd

from .cycles import _component
from .rational import compose, path_matrix


def balanced_domain(edges, constants, limit):
    """Return range for covered components, None for nonidentity cycles or nonlinear prefixes.

    Every vertex map and every executed path prefix must be affine in the chosen root.
    An empty range is an infeasibility certificate within this component grammar.
    """
    _, transforms, loops = _component(edges, constants, limit)
    if loops:
        return None
    guards = prefix_guards(edges, transforms)
    if any(c for _, _, c, _ in guards):
        return None
    return affine_range(guards, limit)


def prefix_guards(edges, transforms):
    guards = set(transforms.values())
    for e in edges:
        for vertex, path in ((e.left, e.left_path), (e.right, e.right_path)):
            prefix = transforms[vertex]
            for step in path:
                prefix = compose(path_matrix((step,)), prefix)
                guards.add(prefix)
    return guards


def affine_range(guards, limit):
    """Intersect the range and divisibility conditions of affine guards."""
    low, high, residue, modulus = 1, limit, 0, 1
    for a, b, _, d in sorted(guards):
        if d < 0:
            a, b, d = -a, -b, -d
        # d <= a*x+b <= L*d. Each transform is invertible, so a is nonzero.
        lo, hi = d - b, limit * d - b
        if a < 0:
            lo, hi, a = -hi, -lo, -a
            # Keep the congruence consistent with the change of sign.
            b = -b
        low = max(low, -((-lo) // a))
        high = min(high, hi // a)
        if low > high:
            return range(0)
        # Substitute x = residue + modulus*k into a*x+b == 0 mod d.
        factor = a * modulus
        rhs = -(a * residue + b)
        g = gcd(factor, d)
        if rhs % g:
            return range(0)
        period = d // g
        k = (rhs // g * pow(factor // g, -1, period)) % period if period > 1 else 0
        residue += modulus * k
        modulus *= period
    first = low + (residue - low) % modulus
    return range(first, high + 1, modulus)
