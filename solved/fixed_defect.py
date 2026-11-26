"""Bounded-control endpoint encoding for fixed-defect addition–multiplication chains."""

from dataclasses import dataclass

from .chains import level


def radius(defect):
    if type(defect) is not int or defect < 0:
        raise ValueError("nonnegative defect required")
    return defect + (6 * (defect + 1) - 1).bit_length()


@dataclass(frozen=True)
class Segment:
    # Blocks consist of a clipped square run followed optionally by a near multiplication.
    blocks: tuple
    extra: int
    # A reset gives (operator, operand addresses). None marks an ordinary value.
    reset: tuple | None


@dataclass(frozen=True)
class Description:
    defect_budget: int
    prefix: tuple
    segments: tuple[Segment, ...]


def encode(chain, defect):
    values = chain.values
    recipes = chain.recipes
    q = radius(defect)
    if not values or values[0] != 1 or len(values) != len(recipes) + 1:
        raise ValueError("invalid chain length")
    end = len(recipes)
    early = min(end, q)
    events = {}
    marks = set()
    for step, (op, a, b) in enumerate(recipes, 1):
        i = step - 1
        if op not in ("+", "*") or any(type(v) is not int or not 0 <= v <= i for v in (a, b)):
            raise ValueError("invalid operand or operation")
        v = values[step]
        if (
            type(v) is not int
            or v <= values[i]
            or step - level(v) > defect
            or v != (values[a] + values[b] if op == "+" else values[a] * values[b])
        ):
            raise ValueError("not an increasing chain within the defect bound")
        if step <= early or v == values[i] ** 2:
            continue
        if max(a, b) < i - defect:
            raise ArithmeticError("no recent operand")
        if op == "+" or min(a, b) <= i - q:
            events[step] = (op, a, b)
            for operand in (a, b):
                if operand > early and operand <= i - q:
                    marks.add(operand)
    if len(events) > defect:
        raise ArithmeticError("too many resets")
    if end == early:
        return Description(defect, tuple(recipes), ())
    boundaries = sorted(marks | events.keys() | {end})
    saved = {step: n for n, step in enumerate(boundaries)}

    def address(idx, i):
        if idx > i - q:
            return ("near", i - idx)
        if idx <= early:
            return ("prefix", idx)
        return ("saved", saved[idx])

    segments = []
    start = early + 1
    for stop in boundaries:
        ordinary_end = stop - int(stop in events)
        run = 0
        extra = 0
        blocks = []
        for step in range(start, ordinary_end + 1):
            if values[step] == values[step - 1] ** 2:
                run += 1
                continue
            op, a, b = recipes[step - 1]
            i = step - 1
            if op != "*" or min(a, b) <= i - q:
                raise ArithmeticError("unmarked reset")
            extra += max(0, run - q)
            blocks.append((min(q, run), (i - a, i - b)))
            run = 0
        extra += max(0, run - q)
        blocks.append((min(q, run), None))
        reset = None
        if stop in events:
            op, a, b = events[stop]
            reset = (op, address(a, stop - 1), address(b, stop - 1))
        segments.append(Segment(tuple(blocks), extra, reset))
        start = stop + 1
    if len(segments) > 2 * defect + 1:
        raise ArithmeticError("too many unbounded coordinates")
    return Description(defect, tuple(recipes[:early]), tuple(segments))


def decode(desc, *, max_bits=None):
    """Restore an encoded endpoint; optionally cap intermediate bit lengths."""
    q = radius(desc.defect_budget)
    if max_bits is not None and (type(max_bits) is not int or max_bits < 1):
        raise ValueError("invalid bit limit")
    if len(desc.prefix) > q or len(desc.segments) > 2 * desc.defect_budget + 1:
        raise ValueError("description exceeds its fixed control bound")

    def checked(value):
        if max_bits is not None and value.bit_length() > max_bits:
            raise OverflowError("decoded value exceeds the requested bit limit")
        return value

    prefix = [1]
    for op, a, b in desc.prefix:
        if op not in ("+", "*") or any(
            type(j) is not int or not 0 <= j < len(prefix) for j in (a, b)
        ):
            raise ValueError("invalid prefix recipe")
        n = checked(prefix[a] + prefix[b] if op == "+" else prefix[a] * prefix[b])
        if n <= prefix[-1]:
            raise ValueError("prefix is not strictly increasing")
        prefix.append(n)
    history = prefix[-q:]
    saved = []

    def append(n):
        n = checked(n)
        if n <= history[-1]:
            raise ValueError("not an increasing decoded word")
        history.append(n)
        if len(history) > q:
            del history[0]

    def operand(addr):
        kind, j = addr
        if type(j) is not int or j < 0:
            raise ValueError("invalid operand index")
        if kind == "near" and j < len(history):
            return history[-1 - j]
        if kind == "prefix" and j < len(prefix):
            return prefix[j]
        if kind == "saved" and j < len(saved):
            return saved[j]
        raise ValueError("missing operand reference")

    for seg in desc.segments:
        if type(seg.extra) is not int or seg.extra < 0:
            raise ValueError("invalid square excess")
        for squares, pair in seg.blocks:
            if type(squares) is not int or not 0 <= squares <= q:
                raise ValueError("invalid capped run")
            for _ in range(squares):
                append(history[-1] ** 2)
            if pair is not None:
                x, y = pair
                append(operand(("near", x)) * operand(("near", y)))
        if seg.extra:
            if not any(k == q for k, _ in seg.blocks):
                raise ValueError("excess without a saturated run")
            if max_bits is not None and (
                seg.extra >= max_bits.bit_length()
                or ((history[-1].bit_length() - 1) << seg.extra) >= max_bits
            ):
                raise OverflowError("decoded square run exceeds the requested bit limit")
            exponent = 1 << seg.extra
            history[:] = [checked(v**exponent) for v in history]
        if seg.reset:
            op, a, b = seg.reset
            if op not in ("+", "*"):
                raise ValueError("invalid reset operation")
            x, y = operand(a), operand(b)
            append(x + y if op == "+" else x * y)
        saved.append(history[-1])
    return history[-1]
