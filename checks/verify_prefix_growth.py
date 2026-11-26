"""Exact shortest-chain comparison for the bounds in section 7 of the 2026 AM paper."""

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from time import process_time

from checks.classical import shortest_chain
from solved.chains import level
from solved.prefix_growth import completion_max

ARMS = ("squares", "levels", "paper_initial", "current_prefix")


def can_complete(row, left, n, method):
    m = row[-1]
    # A small step never increases level, so this many are mandatory on
    # any exact-length completion. A shortest search tries shorter lengths first.
    small = left - (level(n) - level(m))
    if small < 0:
        return False
    if method == "levels" or len(row) < 3:
        return True
    if method == "current_prefix":
        return completion_max(row[-2], m, small, left - small, ceiling=n) >= n
    if method != "paper_initial":
        raise ValueError("unknown growth bound")
    past = len(row) - 3
    used = sum(v != h * h for h, v in zip(row[2:], row[3:]))
    return completion_max(2, row[2], used + small, past - used + left - small, ceiling=n) >= n


def compare(stop, reference=None, repeats=3):
    if type(stop) is not int or stop < 1 or type(repeats) is not int or repeats < 1:
        raise ValueError("positive range and repetitions required")
    report = {arm: {"cpu_seconds": []} for arm in ARMS}
    expected = None
    if reference is not None:
        known = dict(
            tuple(map(int, line.split()))
            for line in Path(reference).read_text().splitlines()
            if line.strip() and not line.startswith("#")
        )
        expected = [known[n] for n in range(1, stop + 1)]
    digest = None
    for rep in range(repeats):
        # Rotate the order to reduce first-run bias.
        for arm in ARMS[rep % len(ARMS) :] + ARMS[: rep % len(ARMS)]:
            counts = Counter()
            lengths = []
            started = process_time()
            for n in range(1, stop + 1):
                admissible = (
                    None if arm == "squares" else lambda row, left: can_complete(row, left, n, arm)
                )
                witness = shortest_chain(n, product=True, admissible=admissible, counts=counts)
                lengths.append(len(witness) - 1)
                values = set()
                for v in witness:
                    if values and not any(
                        v - u in values or (v % u == 0 and v // u in values) for u in values
                    ):
                        raise ArithmeticError("invalid witness")
                    values.add(v)
                if witness[0] != 1 or witness[-1] != n or tuple(sorted(values)) != witness:
                    raise ArithmeticError("invalid endpoints or ordering")
            elapsed = process_time() - started
            if expected is None:
                expected = lengths
            if lengths != expected:
                raise ArithmeticError(f"minimum lengths disagree for {arm}")
            digest = hashlib.sha256(bytes(lengths)).hexdigest()
            report[arm]["cpu_seconds"].append(round(elapsed, 6))
            for stat in ("visited", "expanded"):
                if report[arm].setdefault(stat, counts[stat]) != counts[stat]:
                    raise ArithmeticError("nondeterministic search count")
    return {
        "first_target": 1,
        "last_target": stop,
        "repetitions": repeats,
        "length_vector_bytes_sha256": digest,
        "checked_against_supplied_table": reference is not None,
        "arms": report,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stop", type=int, default=256)
    parser.add_argument("--reference", type=Path)
    parser.add_argument("--repeats", type=int, default=4)
    args = parser.parse_args()
    print(json.dumps(compare(args.stop, args.reference, args.repeats), indent=2))
