"""Compare the block classification with every monotone all-pairs chain at each cap."""

import hashlib
import json
from collections import Counter

from solved.chains import chains, level
from solved.seven_steps import low_defect
from solved.two_small_forms import two_small_chains


def replay(chain, limit):
    values = [1]
    for op, i, j in chain.recipes:
        if op not in {"+", "*"} or not 0 <= i <= j < len(values):
            raise ArithmeticError("invalid construction recipe")
        a, b = values[i], values[j]
        result = a + b if op == "+" else a * b
        if not values[-1] < result <= limit:
            raise ArithmeticError("construction leaves the legal interval")
        values.append(result)
    if tuple(values) != chain.values:
        raise ArithmeticError("construction replay disagrees")


def verify(limit):
    expected = set()
    cheaper = set()
    for small, chain in chains(limit, 2):
        if small == 2:
            expected.add(chain.values)
        else:
            cheaper.add(chain.values[-1])
    generated = set()
    ends = set()
    words = Counter()
    for chain in two_small_chains(limit):
        replay(chain, limit)
        row = chain.values
        if row in generated:
            raise ArithmeticError("block classification repeated a sequence")
        generated.add(row)
        ends.add(row[-1])
        events = "".join(
            "S" if level(v) == level(m) else "G" for m, v in zip(row, row[1:]) if v != m * m
        )
        if not events.startswith("GS") or events.count("S") != 2:
            raise ArithmeticError("unexpected event word")
        words[events[2:]] += 1
    if generated != expected:
        raise ArithmeticError(f"classification disagrees at {min(generated ^ expected)}")
    if ends - cheaper != {n for n in ends if low_defect(n) == 2}:
        raise ArithmeticError("shortest endpoint labels disagree")
    h = hashlib.sha256()
    for row in sorted(generated):
        h.update((",".join(map(str, row)) + "\n").encode("ascii"))
    return {
        "limit": limit,
        "chains": len(generated),
        "distinct_endpoints": len(ends),
        "shortest_defect_two_endpoints": len(ends - cheaper),
        "event_words": dict(sorted(words.items())),
        "sorted_comma_separated_value_sequences_sha256": h.hexdigest(),
    }


if __name__ == "__main__":
    print(json.dumps([verify(n) for n in (64, 10**18, 2**128 - 1)], indent=2))
