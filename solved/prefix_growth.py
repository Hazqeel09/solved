"""Sharp growth and next-increment bounds for increasing addition–multiplication chains."""

from .growth_gap import _squares


def _check(previous, head, nonsquares, squares):
    if any(type(v) is not int for v in (previous, head, nonsquares, squares)) or not (
        2 <= previous < head <= previous * previous and nonsquares >= 0 and squares >= 0
    ):
        raise ValueError("expected two legal leading values and nonnegative step counts")


def completion_max(previous, head, nonsquares, squares, *, ceiling=None):
    """Largest final value with exactly these remaining counts, optionally clipped."""
    _check(previous, head, nonsquares, squares)
    if ceiling is not None and (type(ceiling) is not int or ceiling < 1):
        raise ValueError("ceiling must be a positive integer")
    for _ in range(nonsquares):
        if ceiling is not None and head >= ceiling:
            return ceiling
        previous, head = head, head * previous
    if ceiling is not None:
        return _squares(head, squares, ceiling)
    return head ** (1 << squares)


def increment_max(previous, head, nonsquares, squares, *, next_square):
    """Largest next − current on one chain, after the prescribed counts."""
    _check(previous, head, nonsquares, squares)
    if type(next_square) is not bool:
        raise ValueError("specify the next step type")
    if next_square:
        largest = completion_max(previous, head, nonsquares, squares)
        return largest * (largest - 1)
    maximal_heads = [head]
    for _ in range(nonsquares):
        previous, head = head, previous * head
        maximal_heads.append(head)
    if squares == 0:
        return head * (previous - 1)
    best = 0
    # With j nonsquares after the last square, the two heads are powers
    # F[j+3] and F[j+2] of the head immediately before that square.
    upper_power, lower_power = 2, 1
    for earlier in reversed(maximal_heads):
        base = earlier ** (1 << (squares - 1))
        best = max(best, base**upper_power * (base**lower_power - 1))
        upper_power, lower_power = upper_power + lower_power, upper_power
    return best
