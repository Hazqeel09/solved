"""Upper envelopes for positive integer arithmetic, evaluated with a saturating threshold."""

from collections import Counter


def _squares(value, count, sentinel):
    value = min(value, sentinel)
    while count and 1 < value < sentinel:
        value = min(value * value, sentinel)
        count -= 1
    return value


def envelope(seeds, writes, limit):
    """Largest and runner-up with unlimited retention and no cap, clipped to limit+1.

    The same upper bounds apply to machines with a cap or fewer registers.
    Clipping is for comparison only and can make both returned entries equal.
    """
    seeds = tuple(seeds)
    if (
        type(writes) is not int
        or writes < 0
        or type(limit) is not int
        or limit < 1
        or not seeds
        or any(type(v) is not int or not 1 <= v <= limit for v in seeds)
    ):
        raise ValueError("invalid positive machine")
    start = sorted(set(seeds), reverse=True)
    h = start[0]
    j = start[1] if len(start) > 1 else None
    if h == 1 and writes:
        h, j, writes = 2, 1, writes - 1
    if not writes:
        return min(h, limit + 1), j
    sentinel = limit + 1
    best = _squares(h, writes, sentinel)
    if h == 2:
        alternative = 3 if j == 1 else 2
    else:
        alternative = max(2 * h, h * (j or 0))
    second = _squares(alternative, writes - 1, sentinel)
    if writes >= 2:
        second = max(second, _squares(h**3, writes - 2, sentinel))
    return best, second


def first_visit_bound(seeds, targets, limit, *, gaps=True):
    """Earliest-arrival lower bound for a set of required integer values."""
    start = frozenset(seeds)
    targets = frozenset(targets)
    envelope(start, 0, limit)
    if any(type(v) is not int or not 1 <= v <= limit for v in targets):
        raise ValueError("invalid target")
    pending = targets - start
    by_step = Counter()
    for k in range(1, limit.bit_length() + 2):
        if not pending:
            break
        top, second = envelope(start, k, limit)
        candidates = {v for v in pending if v <= top and (not gaps or v == top or v <= second)}
        by_step[k] = len(candidates)
        pending = pending - candidates
    if pending:
        raise ArithmeticError("unattained growth bound")
    count = 0
    bound = 0
    for k in sorted(by_step, reverse=True):
        if by_step[k]:
            count += by_step[k]
            bound = max(bound, k + count - 1)
    return bound
