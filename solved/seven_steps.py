"""All-length classification of the seven canonical nonsquaring two-defect sector."""

from itertools import product
from math import isqrt

from .chains import level


def legal_next(values):
    m = values[-1]
    return sorted({v for a in values for b in values for v in (a + b, a * b) if v > m})


def extreme(values, deviate):
    m, k, z = values[-1], values[-2], values[-3]
    if not deviate:
        return m * k
    # Only the first nonsquare after [1,2,3] or [1,2,4] has k=2.
    return m + k if k == 2 else max(m * z, k * k)


def signature_envelope(initial, gaps, deviations=()):
    if initial not in (3, 4) or any(type(q) is not int or q < 0 for q in gaps):
        raise ValueError("invalid initial value or gap")
    ds = set(deviations)
    if not ds <= set(range(len(gaps))):
        raise ValueError("unknown deviation position")
    vals = [1, 2, initial]
    for j, q in enumerate(gaps):
        # Two squares reset the three normalized logs; the capped representative
        # decides feasibility at arbitrary gap lengths without building a tower.
        for _ in range(min(q, 2)):
            vals.append(vals[-1] ** 2)
        vals.append(extreme(vals, j in ds))
        if len(vals) - 1 - level(vals[-1]) > 2:
            return None
    return vals


def base_path(initial, gaps, departures=None):
    departures = {} if departures is None else departures
    row = [1, 2, initial]
    for j, q in enumerate(gaps):
        for _ in range(q):
            row.append(row[-1] ** 2)
        row.append(departures[j] if j in departures else extreme(row, False))
    return row


def classify():
    records = {}
    families = {}
    for initial in (3, 4):
        steps = 7 - (2 if initial == 3 else 1)
        max_words = set()
        deviation_words = []
        counts = [0] * (steps + 1)
        # Exact integer computation of envelope at each compressed signature.
        for gaps in product(range(3), repeat=steps):
            if signature_envelope(initial, gaps) is None:
                continue
            for flags in product((False, True), repeat=steps):
                ds = tuple(j for j, d in enumerate(flags) if d)
                envelope = signature_envelope(initial, gaps, ds)
                if envelope is None:
                    continue
                if len(envelope) - 1 - level(envelope[-1]) != 2:
                    raise ArithmeticError("unexpected smaller defect")
                counts[len(ds)] += 1
                if ds:
                    deviation_words.append((gaps, ds))
                else:
                    max_words.add(tuple(j + 1 for j, q in enumerate(gaps) if q))
        # For maximal steps a gap of length >=1 has the same effect on
        # normalized heads. Extra squares in an existing gap square the endpoint.
        for active in sorted(max_words):
            row = base_path(initial, tuple(int(j + 1 in active) for j in range(steps)))
            families.setdefault(row[-1], row)
        for gaps, ds in deviation_words:
            if any(gaps) or len(ds) != 1:
                raise ArithmeticError("unexpected exceptional class")
            j = ds[0]
            prefix = base_path(initial, gaps[:j])
            for v in legal_next(prefix):
                if v >= extreme(prefix, False):
                    break
                row = base_path(initial, gaps, {j: v})
                if len(row) - 1 - level(row[-1]) == 2:
                    families.setdefault(row[-1], row)
        # A canonical eighth nonsquare cannot occur before the third small step.
        eight_ok = sum(
            signature_envelope(initial, gaps) is not None
            for gaps in product(range(2), repeat=steps + 1)
        )
        if eight_ok:
            raise ArithmeticError("eight-nonsquare counterexample")
        records[str(initial)] = {
            "compressed_survivors_by_deviation_count": counts,
            "maximal_gap_supports": sorted(max_words),
            "deviation_words": [
                {"gaps": g, "positions": [j + 1 for j in ds]} for g, ds in deviation_words
            ],
            "admissible_eight_nonsquare_words": eight_ok,
        }
    # Different minimal representatives can themselves lie on the same squaring ray.
    minimal = {}
    for n, row in sorted(families.items()):
        ancestor = n
        while (root := isqrt(ancestor)) ** 2 == ancestor and root > 1:
            ancestor = root
            if ancestor in minimal:
                break
        else:
            minimal[n] = row
    return records, minimal


def low_defect(n):
    """Exact 0/1/at-least-2 classification from Theorem 1.2 and square-root saturation."""
    if type(n) is not int or n < 1:
        raise ValueError("positive integer required")
    if n == 1:
        return 0
    while (root := isqrt(n)) ** 2 == n:
        n = root

    def power2(k):
        return k > 0 and k & (k - 1) == 0

    if power2(n):
        exponent = n.bit_length() - 1
        if power2(exponent):
            return 0
        return 1 if exponent.bit_count() == 2 else 2
    if n in (3, 27):
        return 1
    if n % 2:
        return 1 if power2(n - 1) and power2((n - 1).bit_length() - 1) else 2
    if n.bit_count() != 2:
        return 2
    a = n.bit_length() - 1
    b = (n & -n).bit_length() - 1
    if power2(a) and power2(b):
        return 1
    half = a // 2
    return 1 if power2(a) and 0 < b - half < half and power2(b - half) else 2


def six_step_witness(h, r):
    """Construct a shortest two-defect witness from the infinite six-nonsquare family."""
    if type(h) is not int or h < 3 or type(r) is not int or r < 0:
        raise ValueError("invalid tower or increment")
    if r and (r.bit_count() != 1 or r.bit_length() > h):
        raise ValueError("increment must have occurred earlier in the tower")
    values = [1, 2]
    for _ in range(h):
        values.append(values[-1] ** 2)
    values.append(values[-1] + (1 << r))
    for _ in range(4):
        values.append(values[-1] * values[-2])
    return tuple(values)


def catalogue():
    signatures, paths = classify()
    return {
        "canonical_nonsquares": 7,
        "small_steps": 2,
        "signatures": signatures,
        "squaring_rays": [
            {"base": n, "minimum_defect_on_entire_ray": low_defect(n), "witness": paths[n]}
            for n in sorted(paths)
        ],
    }


if __name__ == "__main__":
    import json

    print(json.dumps(catalogue(), indent=2))
