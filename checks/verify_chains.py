"""Independent length-first checker using exact growth intervals and positional recipes."""

from bisect import bisect_right
from collections import Counter
from itertools import product

from solved.chains import catalogue


def crosscheck(limit):
    thresholds = [1, 2]
    while thresholds[-1] <= limit:
        thresholds.append(thresholds[-1] ** 2)
    maximum = bisect_right(thresholds, limit) - 1 + 2
    # Fix final length first. Prune only when even repeated maximum growth cannot
    # reach a final endpoint of the required magnitude in the remaining steps.
    endpoints = set()
    counts = Counter()
    for length in range(maximum + 1):
        floor = thresholds[max(0, length - 2)]
        layer = {(1,)}
        for depth in range(1, length + 1):
            next_layer = set()
            for row in layer:
                values = set()
                for a, b in product(row, repeat=2):
                    values.update((a + b, a * b))
                for n in values:
                    if not row[-1] < n <= limit:
                        continue
                    if n ** (1 << (length - depth)) >= floor:
                        next_layer.add((*row, n))
            layer = next_layer
        for row in layer:
            n = row[-1]
            d = length - (bisect_right(thresholds, n) - 1)
            if 0 <= d <= 2:
                counts[d] += 1
                endpoints.add((n, d))
    witnesses, by_defect, sequences = catalogue(limit)
    if (
        endpoints != {(n, d) for d, values in enumerate(by_defect) for n in values}
        or [counts[i] for i in range(3)] != sequences
    ):
        raise ArithmeticError("independent enumerations disagree")
    for n, c in witnesses.items():
        values = [1]
        for op, i, j in c.recipes:
            a, b = values[i], values[j]
            v = a + b if op == "+" else a * b
            if not values[-1] < v <= limit:
                raise ArithmeticError("illegal chain certificate")
            values.append(v)
        if tuple(values) != c.values or values[-1] != n:
            raise ArithmeticError("incorrect witness")
    return len(witnesses), sequences


if __name__ == "__main__":
    print(crosscheck(10**18))
