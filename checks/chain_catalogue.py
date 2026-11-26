"""Print the summary or the full certified finite chain catalogue as JSON."""

import argparse
import json
from collections import Counter

from solved.chains import catalogue, level


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=10**18)
    parser.add_argument("--witnesses", action="store_true")
    args = parser.parse_args()
    best, endpoints, counts = catalogue(args.limit)
    result = {
        "limit": args.limit,
        "sequence_counts_by_defect": counts,
        "endpoint_counts_by_defect": list(map(len, endpoints)),
        "minimum_defect_histogram": dict(
            sorted(Counter(len(c.recipes) - level(n) for n, c in best.items()).items())
        ),
        "distinct_endpoints": len(best),
        "max_writes": max(len(c.recipes) for c in best.values()),
    }
    if args.witnesses:
        result["shortest_witnesses"] = {
            str(n): {"values": c.values, "recipes": c.recipes} for n, c in sorted(best.items())
        }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
