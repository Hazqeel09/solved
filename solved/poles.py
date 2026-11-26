"""Classify the integral root domain of a balanced nonlinear component."""

from collections import Counter
from dataclasses import dataclass
from math import gcd, prod

from .affine import affine_range, prefix_guards
from .arithmetic import bounded_divisors
from .cycles import _component
from .rational import image


def common_poles(guards):
    bounds = {}
    for a, b, c, d in guards:
        if not c:
            continue
        content = gcd(c, d) if c > 0 else -gcd(c, d)
        p, q = c // content, d // content
        bound = abs(p * b - q * a)
        if not bound:
            raise ValueError("singular guard")
        bounds[p, q] = gcd(bounds.get((p, q), 0), bound)
    return bounds


def inherited_factors(number, operands):
    """Every prime of a normalized determinant came from a primitive operand.

    bounded_divisors is the existing, pinned complete bounded-arithmetic routine for inputs <= 10^18.
    An unhandled operand size leaves an exact symbolic certificate available.
    """
    remaining = number
    powers = Counter()
    for value in sorted(operands):
        shared = gcd(value, remaining)
        if shared <= 1 or shared > 10**18:
            continue
        for prime in bounded_divisors(shared)[1:]:
            # Divisors arrive in increasing order. All constituent primes of a
            # composite divisor have already been completely removed.
            while remaining % prime == 0:
                powers[prime] += 1
                remaining //= prime
        if remaining == 1:
            break
    return dict(powers) if remaining == 1 else None


@dataclass(frozen=True)
class PoleDomain:
    progression: range
    guards: tuple
    poles: tuple
    roots: tuple | None


def nonlinear_domain(edges, constants, limit, max_trials=4096):
    if type(max_trials) is not int or max_trials < 0:
        raise ValueError("invalid enumeration budget")
    constants = tuple(constants)
    _, transport, loops = _component(edges, constants, limit)
    guards = tuple(sorted(prefix_guards(edges, transport)))
    poles = common_poles(guards)
    if loops or not poles:
        return None
    progression = affine_range([g for g in guards if g[2] == 0], limit)
    certificate = tuple(sorted((p, q, bound) for (p, q), bound in poles.items()))

    def result(roots):
        return PoleDomain(progression, guards, certificate, roots)

    size = max(0, (progression.stop - progression.start + progression.step - 1) // progression.step)
    if size <= max_trials:
        candidates = progression
    else:
        ingredients = {e.target for e in edges}
        ingredients.update(
            k for e in edges for path in (e.left_path, e.right_path) for _, k, _ in path
        )
        choices = []
        for (p, q), bound in poles.items():
            factors = inherited_factors(bound, ingredients)
            if factors is not None:
                trials = 2 * prod(e + 1 for e in factors.values())
                if trials <= max_trials:
                    choices.append((trials, p, q, factors))
        if not choices:
            return result(None)
        _, p, q, powers = min(choices, key=lambda item: item[:3])
        divisors = [1]
        for prime, exponent in powers.items():
            divisors = [d * prime**i for d in divisors for i in range(exponent + 1)]
        candidates = sorted(
            (v - q) // p
            for d in divisors
            for v in (d, -d)
            if (v - q) % p == 0 and (v - q) // p in progression
        )
    # The pole condition is necessary. The original bounded integrality
    # condition at every prefix is sufficient as well, by balanced transport.
    return result(
        tuple(x for x in candidates if all(image(g, x, limit) is not None for g in guards))
    )
