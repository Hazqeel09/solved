"""Certified first-visit exclusions using the first two departures from peak squaring."""

from collections import deque
from itertools import combinations_with_replacement

from .arithmetic import binary_results
from .growth_gap import envelope
from .record_defect import record_max


def _prefixes(seeds, limit):
    # Before the peak first reaches three, there are only two possible labels.
    # Remove steps that add no value in the unlimited-retention relaxation.
    pending = deque([(frozenset(seeds), 0)])
    seen = set()
    while pending:
        values, time = pending.popleft()
        if values in seen:
            continue
        seen.add(values)
        yield values, time
        if max(values) < 3:
            for a, b in combinations_with_replacement(sorted(values), 2):
                for v, _ in binary_results(a, b, limit):
                    if v not in values:
                        pending.append((values | {v}, time + 1))


def one_departure(seeds, steps, limit):
    """All values visited in at most steps with at most one nonsquare, retaining all."""
    values = set(seeds)
    head = max(values)
    reached = set(values)
    for gap in range(steps + 1):
        if gap == steps:
            break
        for a, b in combinations_with_replacement(sorted(values), 2):
            for v, _ in binary_results(a, b, limit):
                if v == head * head:
                    continue
                reached.add(v)
                top = max(head, v)
                for _ in range(steps - gap - 1):
                    top *= top
                    if top > limit:
                        break
                    reached.add(top)
        head *= head
        if head > limit:
            break
        values.add(head)
        reached.add(head)
    return reached


def first_visits(seeds, targets, limit):
    seeds = tuple(seeds)
    # Existing checker provides exact positive-machine input validation.
    envelope(seeds, 0, limit)
    targets = set(targets)
    if any(type(v) is not int or not 1 <= v <= limit for v in targets):
        raise ValueError("invalid target")
    prefixes = list(_prefixes(seeds, limit))
    times = {v: 0 for v in targets.intersection(seeds)}
    for t in range(1, limit.bit_length() + 3):
        missing = targets - times.keys()
        if not missing:
            break
        top, second = envelope(seeds, t, limit)
        accepted = {v for v in missing if v <= top and (v == top or v <= second)}
        if not accepted:
            continue
        possible = set()
        for bank, arrival in prefixes:
            if arrival > t:
                continue
            possible.update(accepted.intersection(bank))
            if max(bank) < 3:
                continue
            k = t - arrival
            both = record_max(bank, 2, k - 2, ceiling=limit) if k >= 2 else 0
            possible.update(v for v in accepted if v <= both)
            if accepted - possible:
                possible.update(accepted.intersection(one_departure(bank, k, limit)))
        times.update((v, t) for v in possible)
    if set(times) != targets:
        raise ArithmeticError("target outside even the relaxed reachability envelope")
    return times


def total_bound(times):
    return max(
        (time + j for j, time in enumerate(sorted((v for v in times.values() if v), reverse=True))),
        default=0,
    )
