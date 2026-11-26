"""Minimum register count for one-shot evaluation of a small fixed arithmetic DAG."""

from functools import lru_cache


def minimum_registers(seeds, rules, keep=()):
    """Inputs initially occupy distinct registers, outputs in keep may finish anywhere.

    Rules map each distinct new value to its two operand values. Every specified rule must
    execute exactly once. Reads precede destructive overwrite. This is exponential in the
    number of rules, intended as an exact small-island oracle. Arithmetic validity is a
    separate check; names here only identify dependencies.
    """
    seeds = tuple(seeds)
    if len(set(seeds)) != len(seeds) or set(seeds) & rules.keys():
        raise ValueError("distinct seed and result labels required")
    names = (*seeds, *rules)
    bits = {v: 1 << i for i, v in enumerate(names)}
    pinned = set(keep)
    if not pinned <= bits.keys():
        raise ValueError("unknown outgoing value")
    pairs = []
    for v, operands in rules.items():
        if len(operands) != 2 or not set(operands) <= bits.keys():
            raise ValueError("invalid operands")
        a, b = operands
        pairs.append((bits[v], bits[a] | bits[b]))
    seed_mask = (1 << len(seeds)) - 1
    full = (1 << len(names)) - 1
    pin_mask = sum(bits[v] for v in pinned)

    @lru_cache(None)
    def needed(done):
        live = pin_mask
        for out, inputs in pairs:
            if not out & done:
                live |= inputs
        return live & done

    @lru_cache(None)
    def peak(done):
        if done == full:
            return pin_mask.bit_count()
        options = []
        for out, inputs in pairs:
            if done & out or inputs & ~done:
                continue
            later = needed(done | out) & ~out
            options.append(max(needed(done).bit_count(), 1 + later.bit_count(), peak(done | out)))
        if not options:
            raise ValueError("cyclic computation graph")
        return min(options)

    return max(len(seeds), peak(seed_mask))
