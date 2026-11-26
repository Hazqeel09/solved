"""Differential check for the four-charge normal form, level counts, and square-root entries."""

import argparse
import json
import time
from bisect import bisect_right
from collections import Counter
from math import comb, isqrt

from solved.chains import catalogue
from solved.counting import coordinates, lower_witness


def filtered(limit):
    if type(limit) is not int or limit < 1:
        raise ValueError("positive cap required")
    thresholds = [1, 2]
    while thresholds[-1] <= limit:
        thresholds.append(thresholds[-1] ** 2)
    endpoints = [set(), set(), set()]
    counts = [0, 0, 0]

    def visit(row, previous_square, paid, nonsquares):
        i = len(row) - 1
        m = row[-1]
        defect = i - (bisect_right(thresholds, m) - 1)
        endpoints[defect].add(m)
        counts[defect] += 1
        low = m + 1 if defect < 2 else thresholds[bisect_right(thresholds, m)]
        sq = m * m
        if low <= sq <= limit:
            visit((*row, sq), i + 1 >= 3, paid, nonsquares)
        if nonsquares == 7:
            return
        gap = int(i >= 2 and previous_square)
        choices = {}
        if paid + gap > 4:
            return
        for k in range(max(0, i - 2), i + 1):
            start = max(0, i - 5) if paid + gap == 4 else 0
            for j in range(start, k + 1):
                far = int(i >= 2 and j <= i - 6)
                fee = gap + far
                if paid + fee > 4:
                    raise ArithmeticError("exterior-index overcharge")
                a, b = row[j], row[k]
                for n in (a + b, a * b):
                    if n != sq and low <= n <= limit:
                        choices[n] = min(choices.get(n, fee), fee)
        for n in sorted(choices):
            visit((*row, n), False, paid + choices[n], nonsquares + 1)

    visit((1,), False, 0, 0)
    return endpoints, counts


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--level", type=int, default=9)
    a = ap.parse_args()
    if not 2 <= a.level <= 16:
        ap.error("benchmark supports complete levels 2 through 16")
    limit = (1 << (1 << a.level)) - 1
    t = time.perf_counter()
    e, c = filtered(limit)
    filtered_s = time.perf_counter() - t
    t = time.perf_counter()
    best, ref, counts = catalogue(limit)
    reference_s = time.perf_counter() - t
    if e != ref or c != counts:
        raise AssertionError("normal form eliminated a real chain")
    d2 = e[2] - e[0] - e[1]
    entries = {n for n in d2 if (r := isqrt(n)) ** 2 != n or r not in d2}
    by = Counter((n.bit_length() - 1).bit_length() for n in d2)
    eb = Counter((n.bit_length() - 1).bit_length() for n in entries)
    lb = Counter()
    for n in d2:
        indices = coordinates(n)
        if indices is not None:
            if lower_witness(*indices)[-1] != n:
                raise AssertionError("coordinate roundtrip failed")
            lb[(n.bit_length() - 1).bit_length()] += 1
    for L in range(1, a.level + 1):
        if by[L] - by[L - 1] != eb[L] or lb[L] != comb(L, 4):
            raise AssertionError("level count identity failed")
    out = {
        "complete_through_level": a.level,
        "chain_counts": counts,
        "shortest_two": len(d2),
        "entries": len(entries),
        "square_entries": sum(isqrt(n) ** 2 == n for n in entries),
        "by_level": by,
        "entries_by_level": eb,
        "lower_family_by_level": lb,
        "lower_family_size": sum(lb.values()),
        "filtered_seconds": filtered_s,
        "reference_seconds": reference_s,
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
