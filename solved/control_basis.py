"""Finite-basis analysis of unbounded square-run parameter families.

The upward set contains programs below or equal to their cost-indexed
Mersenne target. Every exact solution is minimal in that set. Complete
results therefore give a cutoff for the declared control and domain.
Resource-limited results never report a cutoff.
"""

from dataclasses import dataclass
from math import comb

from .control_profiles import Arithmetic, ResourceLimit, ideal_intersection, in_upset
from .square_controls import Description, validate


def _limit(value, name):
    if value is not None and (type(value) is not int or value < 0):
        raise ValueError(f"{name} must be a nonnegative integer or None")


def _contains(smaller, larger):
    """Inclusion of boxes with a common lower bound; None denotes infinity."""
    return all(b is None or (a is not None and a <= b) for a, b in zip(smaller, larger))


def _maximal(boxes):
    result = []
    for box in boxes:
        if any(_contains(box, kept) for kept in result):
            continue
        result = [kept for kept in result if not _contains(kept, box)]
        result.append(box)
    return result


def _subtract(boxes, point, lower, max_regions):
    result = []
    for box in boxes:
        if any(upper is not None and upper < value for upper, value in zip(box, point)):
            result.append(box)
        else:
            for i, value in enumerate(point):
                if value > lower[i]:
                    upper = list(box)
                    upper[i] = value - 1 if upper[i] is None else min(upper[i], value - 1)
                    result.append(tuple(upper))
        if max_regions is not None and len(result) > max_regions:
            raise ResourceLimit("residual region budget exceeded")
    return _maximal(result)


@dataclass(frozen=True)
class BasisResult:
    status: str
    base: Description
    excess: int
    upper: tuple[int | None, ...]
    minimals: tuple[tuple[int, ...], ...]
    unresolved: tuple[tuple[int | None, ...], ...]
    oracle_calls: int
    point_evaluations: int
    reason: str | None = None

    @property
    def cutoff(self):
        if self.status != "complete":
            return None
        if not self.minimals:
            return 0
        binary = len(self.base.control) - len(self.base.runs)
        return 1 + max(binary + sum(point) - self.excess for point in self.minimals)


class _Queries:
    def __init__(self, base, excess, max_bits, max_queries):
        self.base = base
        self.excess = excess
        self.max_bits = max_bits
        self.maximum = max_queries
        self.oracles = 0
        self.points = 0
        self.cache = {}

    def _charge(self):
        if self.maximum is not None and self.oracles + self.points >= self.maximum:
            raise ResourceLimit("exact-query budget exceeded")

    def ideal(self, upper):
        self._charge()
        self.oracles += 1
        return ideal_intersection(self.base, self.excess, upper, max_bits=self.max_bits)

    def member(self, point):
        point = tuple(point)
        if point not in self.cache:
            self._charge()
            self.points += 1
            self.cache[point] = in_upset(
                Description(self.base.control, point), self.excess, max_bits=self.max_bits
            )
        return self.cache[point]


def minimal_basis(
    base, excess, upper=None, *, max_bits=1_000_000, max_queries=10_000, max_regions=10_000
):
    base = validate(base)
    if type(excess) is not int or not 0 <= excess <= base.length:
        raise ValueError("base must give a nonnegative target index")
    for value, name in ((max_queries, "max_queries"), (max_regions, "max_regions")):
        _limit(value, name)
    if max_bits is not None and (type(max_bits) is not int or max_bits < 1):
        raise ValueError("a positive bit budget or None is required")
    upper = (None,) * len(base.runs) if upper is None else tuple(upper)
    if len(upper) != len(base.runs) or any(
        hi is not None and (type(hi) is not int or hi < lo) for lo, hi in zip(base.runs, upper)
    ):
        raise ValueError("upper bounds must contain the base")
    query = _Queries(base, excess, max_bits, max_queries)
    boxes = [upper]
    minimals = []

    def result(status, reason=None):
        return BasisResult(
            status,
            base,
            excess,
            upper,
            tuple(sorted(minimals)),
            tuple(boxes),
            query.oracles,
            query.points,
            reason,
        )

    while boxes:
        if max_regions is not None and len(boxes) > max_regions:
            return result("resource_limit", "residual region budget exceeded")
        box = boxes.pop()
        try:
            decision = query.ideal(box)
            if decision.empty:
                continue
            point = list(decision.witness)
            witness = tuple(point)
            # The oracle proves membership even if the witness's endpoint is
            # too large to materialize. Preserve that established right bound.
            if query.cache.get(witness) is False:
                raise ArithmeticError("symbolic witness contradicts an exact membership query")
            query.cache[witness] = True
            for i in range(len(point)):
                low, high = base.runs[i], point[i]
                while low < high:
                    middle = (low + high) // 2
                    trial = point.copy()
                    trial[i] = middle
                    if query.member(trial):
                        high = middle
                    else:
                        low = middle + 1
                point[i] = low
            point = tuple(point)
            if not query.member(point):
                raise ArithmeticError("minimization lost its feasible witness")
            for i, value in enumerate(point):
                if value > base.runs[i]:
                    trial = list(point)
                    trial[i] -= 1
                    if query.member(trial):
                        raise ArithmeticError("a reported basis point is not minimal")
            if any(all(a <= b for a, b in zip(known, point)) for known in minimals):
                raise ArithmeticError("residual search returned an already covered point")
            new_boxes = _subtract([*boxes, box], point, base.runs, max_regions)
        except ResourceLimit as error:
            # No newly computed point or partially split region is committed.
            boxes.append(box)
            return result("resource_limit", str(error))
        minimals.append(point)
        boxes = new_boxes
    return result("complete")


def _compositions(total, parts):
    """Lexicographic positive compositions without recursion or range allocation."""
    point = [1] * parts
    point[-1] = total - parts + 1
    while True:
        yield tuple(point)
        tail = point[-1]
        for i in range(parts - 2, -1, -1):
            count = parts - i - 1
            if tail > count:
                point[i] += 1
                point[i + 1 :] = [1] * (count - 1) + [tail - count]
                break
            tail += point[i]
        else:
            return


def admissible_bases(control, excess):
    """Finite lower-corner cover of all positive runs with cost at least excess."""
    control = tuple(tuple(row) for row in control)
    runs = sum(row[0] == "squares" for row in control if row)
    base = validate(Description(control, (1,) * runs))
    if type(excess) is not int or excess < 0:
        raise ValueError("nonnegative integer excess required")
    if base.length >= excess:
        return 1, iter((base,))
    if not runs:
        return 0, iter(())
    binary = len(control) - runs
    total = excess - binary
    count = comb(total - 1, runs - 1)
    return count, (Description(control, row) for row in _compositions(total, runs))


@dataclass(frozen=True)
class ControlCutoff:
    status: str
    control: tuple
    excess: int
    cutoff: int | None
    completed: tuple[BasisResult, ...]
    interrupted: BasisResult | None
    total_bases: int
    reason: str | None = None


def control_cutoff(
    control, excess, *, max_bits=1_000_000, max_queries=10_000, max_regions=10_000, max_bases=10_000
):
    """Cutoff for one entire control/excess family, not for all AM programs."""
    for value, name in (
        (max_queries, "max_queries"),
        (max_regions, "max_regions"),
        (max_bases, "max_bases"),
    ):
        _limit(value, name)
    Arithmetic(max_bits)
    # Freeze before the lower-corner generator can consume a one-shot input.
    control = tuple(tuple(row) for row in control)
    total, bases = admissible_bases(control, excess)
    completed = []
    queries = 0
    for base in bases:
        if max_bases is not None and len(completed) >= max_bases:
            return ControlCutoff(
                "resource_limit",
                control,
                excess,
                None,
                tuple(completed),
                None,
                total,
                "admissible-base budget exceeded",
            )
        available = None if max_queries is None else max(0, max_queries - queries)
        result = minimal_basis(
            base, excess, max_bits=max_bits, max_queries=available, max_regions=max_regions
        )
        queries += result.oracle_calls + result.point_evaluations
        if result.status != "complete":
            return ControlCutoff(
                "resource_limit",
                control,
                excess,
                None,
                tuple(completed),
                result,
                total,
                result.reason,
            )
        completed.append(result)
    return ControlCutoff(
        "complete",
        control,
        excess,
        max((r.cutoff for r in completed), default=0),
        tuple(completed),
        None,
        total,
    )
