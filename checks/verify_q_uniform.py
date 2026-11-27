"""Exhaustive exact check of open matroid polynomial conjectures on q-uniform matroids.

For each (q, n, k, m) in RANGES the matroid F(n, k, m) = T_k(PG(n-1, q)) plus m free
points is evaluated with solved.q_uniform and tested with exact arithmetic for:
real-rootedness of Z (Proudfoot-Xu-Young Conj. 5.1), unimodality and log-concavity of the
inverse Z-polynomial (Gao-Ruan-Xie Conj. 1.4, 1.5), and real-rootedness of the Chow and
augmented Chow polynomials (Ferroni-Schroter Conj. 8.18, Stevens Conj. 4.3.3).
Run as ``python -m checks.verify_q_uniform``; it prints the number of matroids checked and
every failure (none are expected).
"""

from solved.matroid_polynomials import report
from solved.q_uniform import QUniform

# (q, n_max, m_max): all 1 <= k <= n <= n_max and 0 <= m <= m_max, free points for n <= 6.
RANGES = (
    (1, 24, 0),
    (2, 16, 40),
    (3, 13, 40),
    (4, 12, 40),
    (5, 11, 40),
    (7, 10, 40),
    (8, 10, 40),
    (9, 10, 40),
    (11, 9, 40),
    (13, 9, 40),
    (16, 9, 40),
)


def instances():
    for q, n_max, m_max in RANGES:
        for n in range(1, n_max + 1):
            for k in range(1, n + 1):
                for m in range(0, (m_max if n <= 6 else 0) + 1):
                    yield q, n, k, m


def run():
    engines, checked, failures = {}, 0, []
    for q, n, k, m in instances():
        engine = engines.setdefault(q, QUniform(q))
        failed = report(engine.polynomials(n, k, m)).open_conjecture_failures()
        checked += 1
        if failed:
            failures.append(((q, n, k, m), failed))
    return checked, failures


def main():
    checked, failures = run()
    print(f"checked {checked} matroids F(n,k,m); failures: {failures if failures else 'none'}")


if __name__ == "__main__":
    main()
