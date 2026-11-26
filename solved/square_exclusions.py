"""Exact exclusion certificates for upward sets of square-run parameters.

The target at written length r and fixed excess j is 2**(2**(r-j)) - 1.
A certificate evaluates only its base description; queries never expand the
candidate's potentially enormous integers. See the subtraction-gap manuscript.
"""

from dataclasses import dataclass, field

from .square_controls import Description, expand


def compare_tower_minus_one(value, index):
    """Compare a positive integer with 2**(2**index)-1 without building the tower."""
    if type(value) is not int or value < 1 or type(index) is not int or index < 0:
        raise ValueError("positive integer value and nonnegative integer index required")
    bits = value.bit_length()
    # Here 2**index exceeds the entire bit length of value. Do not construct it.
    if index >= bits.bit_length():
        return -1
    target_bits = 1 << index
    if bits != target_bits:
        return (bits > target_bits) - (bits < target_bits)
    return 0 if value & (value + 1) == 0 else -1


@dataclass(frozen=True)
class OrthantCertificate:
    """Excludes the base's upward parameter set at one fixed length excess.

    If the base is itself a solution, only strict parameter extensions are excluded.
    Construction checks the base exactly and rejects it if it exceeds its target.
    """

    base: Description
    excess: int
    base_is_solution: bool = field(init=False)

    def __post_init__(self):
        if type(self.excess) is not int or self.excess < 0:
            raise ValueError("nonnegative integer excess required")
        if not isinstance(self.base, Description):
            raise ValueError("a square-control description is required")
        # Retain immutable copies even if callers constructed a Description from lists.
        base = Description(tuple(tuple(step) for step in self.base.control), tuple(self.base.runs))
        endpoint = expand(base).values[-1]
        if base.length < self.excess:
            raise ValueError("negative target index")
        comparison = compare_tower_minus_one(endpoint, base.length - self.excess)
        if comparison > 0:
            raise ValueError("base exceeds its target; no exclusion follows")
        object.__setattr__(self, "base", base)
        object.__setattr__(self, "base_is_solution", comparison == 0)

    def excludes(self, candidate, excess):
        """Check membership in the proved region without evaluating candidate values."""
        if not isinstance(candidate, Description) or type(excess) is not int or excess < 0:
            raise ValueError("a description and nonnegative integer excess are required")
        if any(type(run) is not int or run < 1 for run in candidate.runs):
            raise ValueError("positive square-run lengths required")
        if excess != self.excess or tuple(tuple(s) for s in candidate.control) != self.base.control:
            return False
        if len(candidate.runs) != len(self.base.runs):
            raise ValueError("square-run count does not match the control")
        if any(a > b for a, b in zip(self.base.runs, candidate.runs)):
            return False
        return not self.base_is_solution or tuple(candidate.runs) != self.base.runs
