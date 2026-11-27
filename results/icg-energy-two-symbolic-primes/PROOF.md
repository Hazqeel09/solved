# Maximal-energy integral circulant graphs with two symbolic primes

**Status:** every row below is a kernel-checked Lean theorem; see the [statement correspondence](FORMALIZATION.md). Independent mathematical review is pending. A formal proof does not make a statement new; novelty is assessed under *Prior work*.

## Statement

For $n\ge2$ and a set $S$ of proper divisors of $n$, the integral circulant graph $\mathrm{ICG}(n,S)$ has vertex set $\mathbb Z_n$, with $x\sim y$ iff $\gcd(x-y,n)\in S$; its energy is the sum of the absolute values of the eigenvalues of its adjacency matrix.

**Theorem.** For each row, let $p,q$ be distinct primes in the stated range. For every set $S$ of proper divisors of $n$ (the empty set included), $E(\mathrm{ICG}(n,S))$ is at most the listed polynomial in $p,q$, with equality exactly for the listed sets. Rows come in pairs for $p<q$ and $p>q$. For $2p^2q$ and $2p^3q$ only $p<q$ is formalized; for $p>q$ the maximiser depends on the ratio of the primes (see the [companion entry](../icg-energy-exceptional-orders/PROOF.md)), and that part remains a Python certificate.

<!-- BEGIN GENERATED MULTI TABLE -->

| Order | Primes | Maximal energy | Maximising divisor sets | Lean theorem |
|---|---|---|---|---|
| $2pq$ | $3\le p<q$ | $10pq-12p-6q+8$ | $\{1,p,2p,2q\}$; $\{1,2,2p,pq\}$; $\{2,p,2p,q\}$ | `energy_2_p_q_lt` |
| $2pq$ | $3\le q<p$ | $10pq-6p-12q+8$ | $\{1,2p,q,2q\}$; $\{1,2,2q,pq\}$; $\{2,p,q,2q\}$ | `energy_2_p_q_gt` |
| $3pq$ | $5\le p<q$ | $24pq-30p-30q+40$ | $\{1,3p,3q,pq\}$ | `energy_3_p_q_lt` |
| $3pq$ | $5\le q<p$ | $24pq-30p-30q+40$ | $\{1,3p,3q,pq\}$ | `energy_3_p_q_gt` |
| $4pq$ | $3\le p<q$ | $38pq-48p-48q+64$ | $\{1,2,4p,4q,pq,2pq\}$ | `energy_4_p_q_lt` |
| $4pq$ | $3\le q<p$ | $38pq-48p-48q+64$ | $\{1,2,4p,4q,pq,2pq\}$ | `energy_4_p_q_gt` |
| $2p^{2}q$ | $3\le p<q$ | $16p^{2}q-20p^{2}-12pq+16p-6q+8$ | $\{1,p,2p,2p^{2},2q,p^{2}q\}$ | `energy_2_p2_q_lt` |
| $9pq$ | $5\le p<q$ | $112pq-140p-140q+180$ | $\{1,9,3p,3q,pq\}$; $\{3,p,9p,q,9q,3pq\}$ | `energy_9_p_q_lt` |
| $9pq$ | $5\le q<p$ | $112pq-140p-140q+180$ | $\{1,9,3p,3q,pq\}$; $\{3,p,9p,q,9q,3pq\}$ | `energy_9_p_q_gt` |
| $3p^{2}q$ | $5\le p<q$ | $38p^{2}q-48p^{2}-58pq+76p+28q-36$ | $\{1,3p,p^{2},3q,pq\}$; $\{3,p,3p^{2},q,3pq,p^{2}q\}$ | `energy_3_p2_q_lt` |
| $3p^{2}q$ | $5\le q<p$ | $38p^{2}q-48p^{2}-58pq+76p+28q-36$ | $\{1,3p,p^{2},3q,pq\}$; $\{3,p,3p^{2},q,3pq,p^{2}q\}$ | `energy_3_p2_q_gt` |
| $2p^{3}q$ | $3\le p<q$ | $22p^{3}q-28p^{3}-18p^{2}q+24p^{2}-12pq+16p+6q-8$ | $\{1,2,p,2p^{3},2pq,p^{2}q,2p^{2}q,p^{3}q\}$ | `energy_2_p3_q_lt` |
| $6pq$ | $5\le p<q$ | $66pq-84p-84q+112$ | $\{1,2,3,6p,6q,pq,2pq,3pq\}$ | `energy_6_p_q_lt` |
| $6pq$ | $5\le q<p$ | $66pq-84p-84q+112$ | $\{1,2,3,6p,6q,pq,2pq,3pq\}$ | `energy_6_p_q_gt` |
| $15pq$ | $7\le p<q$ | $252pq-324p-324q+428$ | $\{1,15,3p,5p,3q,5q,pq\}$; $\{3,5,p,15p,q,15q,3pq,5pq\}$ | `energy_15_p_q_lt` |
| $15pq$ | $7\le q<p$ | $252pq-324p-324q+428$ | $\{1,15,3p,5p,3q,5q,pq\}$; $\{3,5,p,15p,q,15q,3pq,5pq\}$ | `energy_15_p_q_gt` |
| $35pq$ | $3\le p<q,\ p,q\notin\{5,7\}$ | $844pq-1092p-1092q+1436$ | $\{1,35,5p,7p,5q,7q,pq\}$; $\{5,7,p,35p,q,35q,5pq,7pq\}$ | `energy_35_p_q_lt` |
| $35pq$ | $3\le q<p,\ p,q\notin\{5,7\}$ | $844pq-1092p-1092q+1436$ | $\{1,35,5p,7p,5q,7q,pq\}$; $\{5,7,p,35p,q,35q,5pq,7pq\}$ | `energy_35_p_q_gt` |

<!-- END GENERATED MULTI TABLE -->

The table and the Lean theorems are generated from `checks/expected/icg-families.json` by `python -m scripts.lean_icg_families`.

## Method

1. **Spectral bridge for $k$ primes.** `Solved.ICG.Multi.energy_icgAdj_multi` proves, for pairwise distinct primes $r_0,\dots,r_{k-1}$, that the energy of $\mathrm{ICG}(\prod r_i^{a_i},S)$ is $\sum_u\bigl|\sum_c[\prod r_i^{c_i}\in S]\prod_i T(r_i,a_i,u_i,c_i)\bigr|$ over the exponent box, with local Ramanujan factors $T$. It generalizes H. Dong's two-prime bridge, reusing its circulant-spectrum and character-sum lemmas, and replaces the two-prime steps by inclusion–exclusion over subsets of the primes.
2. **Regions.** On $p<q$ the substitution $p=p_0+x$, $q=p_0+2+x+y$ covers every pair of distinct odd primes $p_0\le p<q$ by $x,y\ge0$; on $p>q$, $q=q_0+y$ and $p=q_0+2+x+y$. Every cell contribution becomes a polynomial in $x,y$, and a polynomial with nonnegative coefficients and a positive constant term is positive on the region.
3. **Search.** The same proved packed branch-and-bound as for $2^ap^b$ runs on the coefficient tables, with monomial weights $x^iy^j$; the maximisers' exact energies are checked by coefficient signs.

The eighteen certificates check in about two minutes.

## Trusted base

The Lean kernel, Mathlib and Dong's bridge lemmas; every registered theorem depends only on `propext`, `Classical.choice` and `Quot.sound` ([axiom audit](../../formal/FormalTests/Axioms.lean)); no `native_decide`. The certificate generator is not trusted: wrong data makes the kernel reject a certificate. Tests compare the generated data at concrete prime pairs with exhaustive search using the definitional energy formula.

## Prior work

Literature checked 27 November 2026; see the [companion entry](../icg-energy-exceptional-orders/PROOF.md) for the sources.

- Jiang and Yang [JY26a] settle odd orders with odd total exponent when every prime with an odd exponent is at least 5; $3pq$ is outside that range because 3 has an odd exponent. [JY26b] treats two primes with exponents of equal parity.
- Le and Sander (Linear Algebra Appl. 437, 2012) are described by later papers as bounding extremal energies through multiplicative divisor sets for arbitrary orders; we found no determination of these maximisers there or elsewhere.

We found no earlier determination of the maximisers for these orders, which have three or four prime factors; the search may be incomplete.

## Reproduction

```sh
python -m scripts.lean_icg_families --check
python -m unittest tests.test_lean_icg
cd formal && lake exe cache get && lake build
```

## References

- [JY26a] J. Jiang, C. Yang, Ramanujan transforms and maximum energy of odd-total-exponent integral circulants, arXiv:2608.29523, <https://arxiv.org/abs/2608.29523>.
- [JY26b] J. Jiang, C. Yang, Maximum energy of integral circulant graphs with same-parity exponents, arXiv:2610.36883, <https://arxiv.org/abs/2610.36883>.
- H. Dong, ai4math-results, Lean sources at <https://github.com/Horace-Maxwell/ai4math-results/tree/6334a95f2e0c2396f492f3476c1d4ce80e4106ab/lean>.
