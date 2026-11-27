"""Re-derive the exact certificate that D* uniquely maximises E(p^2 q^3, D) for p, q >= 3.

Run as ``python -m checks.verify_icg_energy``. It prints the certificate statistics and
re-checks the factorized model against the definition of the energy for small primes.
"""

from itertools import combinations

from solved import icg_energy as ie


def main():
    cert = ie.prove(3, 3)
    print(
        f"certified on [{cert.p0},inf)x[{cert.q0},inf): {cert.divisor_sets} competitors, "
        f"{cert.branched_forms} sign-branched eigenvalue forms, {cert.inequalities} polynomial "
        "inequalities, all with nonnegative shifted coefficients and positive constant term"
    )
    for p, q in ((3, 5), (5, 3), (7, 3), (3, 7)):
        n = p * p * q**3
        for r in range(1, len(ie.CELLS) + 1):
            for cells in combinations(ie.CELLS, r):
                divisors = [p**a * q**b for a, b in cells]
                assert ie.energy(cells, p, q) == ie.direct_energy(n, divisors)
    print("factorized energies agree with the definition at (3,5), (5,3), (7,3), (3,7)")


if __name__ == "__main__":
    main()
