"""Exact positive-polynomial bookkeeping for the normalized-log proof.

A term is a nonnegative rational coefficient times one bounded prefix logarithm
(or the scalar one) and a product of reset atoms. Replaying the concrete atoms
as rational powers verifies the endpoint without evaluating a logarithm.
"""

from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction

from .fixed_defect import encode, radius


@dataclass
class Mass:
    terms: dict
    atoms: tuple
    prefix: tuple
    writes: int

    def restore(self):
        if not self.writes:
            return 1
        result = Fraction(1)
        for (base_index, variables), coeff in self.terms.items():
            if coeff <= 0:
                raise ArithmeticError("expected strictly positive retained terms")
            # U_0 is zero and has no terms. Base -1 denotes the numerical constant 1.
            base = Fraction(2) if base_index < 0 else Fraction(self.prefix[base_index])
            power = coeff * (1 << (self.writes - 1))
            if base_index > 0:
                power /= 1 << (base_index - 1)
            logged = base_index != -1
            for j in variables:
                kind, ratio, den = self.atoms[j]
                if kind == "add":
                    if logged:
                        raise ArithmeticError("product of two logarithmic terms")
                    base = ratio
                    logged = True
                power /= den
            if power.denominator != 1:
                raise ArithmeticError("nonintegral exponent after normalization")
            result *= base**power.numerator
        if result.denominator != 1:
            raise ArithmeticError("nonintegral AM endpoint")
        return result.numerator


def normalized(chain, defect):
    # First verify the labelled chain, the defect budget and the reset bound.
    encode(chain, defect)
    row = chain.values
    q = radius(defect)
    r = len(row) - 1
    early = min(r, q)
    polynomials = [{}] + [{(j, ()): Fraction(1)} for j in range(1, early + 1)]
    atoms = []
    for t in range(early + 1, r + 1):
        op, a, b = chain.recipes[t - 1]
        j, earlier = max(a, b), min(a, b)
        if row[t] == row[t - 1] ** 2:
            polynomials.append(polynomials[-1])
            continue
        result = defaultdict(Fraction)
        for term, c in polynomials[j].items():
            result[term] += c / (1 << (t - j))
        if op == "+":
            idx = len(atoms)
            atoms.append(("add", Fraction(row[earlier] + row[j], row[j]), 1 << (t - 1)))
            result[-1, (idx,)] += 1
        elif earlier <= t - 1 - q:
            idx = len(atoms)
            atoms.append(("mul", None, 1 << (t - earlier)))
            for (base, vs), c in polynomials[earlier].items():
                result[base, vs + (idx,)] += c
        else:
            for term, c in polynomials[earlier].items():
                result[term] += c / (1 << (t - earlier))
        polynomials.append(dict(result))
    if len(atoms) > defect:
        raise ArithmeticError("reset bound failed")
    return Mass(polynomials[-1], tuple(atoms), row[: early + 1], r)
