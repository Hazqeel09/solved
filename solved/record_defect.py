"""Sharp universal nonsquare count at fixed peak-level defect, from arbitrary seeds."""

from .prefix_growth import completion_max


def max_nonsquares(small):
    if type(small) is not int or small < 0:
        raise ValueError("expected a nonnegative integer small-step count")
    # At b=0 the two Fibonacci numbers are F_1 and F_2.
    previous, current = 1, 1
    b = 0
    while (1 << b) < (current << (small + 1)):
        previous, current = current, previous + current
        b += 1
    return b - 1


def record_max(seeds, nonsquares, squares, *, ceiling=None):
    """Sharp peak with arbitrary positive seeds of maximum >=3 and two working slots.

    An optional ceiling clips the comparison result. Sharpness assumes the true
    extremizing intermediates are permitted by the machine's magnitude cap.
    """
    seeds = tuple(seeds)
    if not seeds or any(type(v) is not int or v < 1 for v in seeds):
        raise ValueError("positive integer seeds required")
    if any(type(v) is not int or v < 0 for v in (nonsquares, squares)):
        raise ValueError("nonnegative step counts required")
    if ceiling is not None and (type(ceiling) is not int or ceiling < 1):
        raise ValueError("positive comparison ceiling required")
    m = max(seeds)
    if m < 3:
        raise ValueError("fixed-seed extremum requires an initial maximum of at least three")
    q = max((v for v in seeds if v < m), default=1)
    q = max(2, q)
    if not nonsquares and not squares:
        return m if ceiling is None else min(m, ceiling)
    if squares and (not nonsquares or q * q < m):
        return completion_max(m, m * m, nonsquares, squares - 1, ceiling=ceiling)
    return completion_max(m, m * q, nonsquares - 1, squares, ceiling=ceiling)
