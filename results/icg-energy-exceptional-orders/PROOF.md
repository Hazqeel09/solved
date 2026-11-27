# Maximal-energy integral circulant graphs at the primes 2 and 3

**Status:** proof draft. Every row of the tables below is a theorem backed by an exact, computer-checked certificate. Independent review is pending. The three conjectures at the end are open. No proof-assistant formalization.

## Setting and prior results

For $n\ge2$ and a nonempty set $\mathcal D$ of proper divisors of $n$, the integral circulant graph $\mathrm{ICG}(n,\mathcal D)$ has vertex set $\mathbb Z_n$, with $a\sim b$ iff $\gcd(a-b,n)\in\mathcal D$. Its energy is
$$E(n,\mathcal D)=\sum_{e\mid n}\varphi(n/e)\Bigl|\sum_{d\in\mathcal D}c(e,n/d)\Bigr|,$$
where $c$ is the Ramanujan sum. The problem is to find $\max_{\mathcal D}E(n,\mathcal D)$ and every maximising $\mathcal D$. Write $\Omega(d)$ for the number of prime factors of $d$ counted with multiplicity. The *even-Ω set* is $\{d\mid n,\ d\ne n:\ \Omega(d)\ \text{even}\}$; the *odd-Ω set* is defined likewise.

As far as we found on 27 November 2026, proved answers exist for exactly three classes:

- **Prime powers $p^s$, every prime.** Sander–Sander [SS11, Thm 1.1]. For $p=2$ there are extra maximisers.
- **$p^aq^b$ with $p,q\ge5$ and $a+b$ even.** Exactly the odd-Ω set and the even-Ω set [JY26b, Thm A].
- **Odd $n$ with odd total exponent, every prime of odd exponent at least 5.** Uniquely the even-Ω set [JY26a, Thm A]. The exclusion of $3$ is a limitation of their semidefinite method [JY26a, Thm B, Remark 4.2].

Every order involving the prime 2 with at least two prime factors lies outside these classes. So does every two-prime order involving 3 with an odd exponent of 3 or with same-parity exponents, and every order with three or more primes and even total exponent. The tables below settle many such orders. They also show that for even orders the maximiser can depend on the relative size of the primes.

## Method

For $n=\prod r_\nu^{a_\nu}$, multiplicativity of $c(e,\cdot)$ gives
$$E(\mathcal D)=\sum_{\alpha}w_\alpha\,|L_\alpha(\mathcal D)|,\qquad L_\alpha(\mathcal D)=\sum_{i\in\mathcal D}\prod_\nu u_\nu(\alpha_\nu,i_\nu),$$
with local Ramanujan sums $u_\nu$ and weights $w_\alpha=\prod_\nu\varphi(r_\nu^{a_\nu-\alpha_\nu})$. When some primes are symbols $p,q$, every term is an integer polynomial in them.

A *region* is the image of $x,y\ge0$ under a substitution $p=s_p(x,y)$, $q=s_q(x,y)$ with nonnegative integer coefficients. The regions used are:

- $p\ge p_0$;
- $p\ge p_0,\ q\ge p+2$, via $(p,q)=(p_0+x,\,p_0+2+x+y)$;
- the mirror of the previous region.

A polynomial whose substituted form has nonnegative coefficients and a positive constant term is positive on the region. Since $|L|=\max(L,-L)$, the claim "$\mathcal M$ is exactly the set of maximisers on the region" follows from three checks:

1. every $\mathcal D^*\in\mathcal M$ has certified constant eigenvalue signs and the same energy polynomial $E^*$;
2. for every other set $\mathcal D$, and every sign choice of its uncertified forms, $E^*-\sum w\,s\,L(\mathcal D)$ is certified positive.

When the maximiser changes inside a region, a *convex certificate* is used instead. For every competitor $\mathcal D$ and sign choice, rational weights $\lambda\ge0$ summing to 1 make $\sum_k\lambda_kE_k-E(\mathcal D)$ certified positive. Hence $E(\mathcal D)<\max_kE_k$, and the maximisers are those candidates attaining $\max_kE_k$.

Primes below the cutoff of a one-variable certificate are handled by exhaustive exact enumeration. Symbolic primes range over odd primes different from the fixed ones. The regions also contain non-prime real points, so the inequalities proved are stronger than needed.

Implementation:

- [`solved/icg_families.py`](../../solved/icg_families.py), with the energy model shared with [`solved/icg_energy.py`](../../solved/icg_energy.py);
- the certificate [`checks/verify_icg_families.py`](../../checks/verify_icg_families.py), registered in `python -m scripts.check_certificates` against [`checks/expected/icg-families.json`](../../checks/expected/icg-families.json).

The engine reproduces every known case exactly:

- [JY26a]'s energy $\tfrac12[n+d_a(p)d_b(q)]$ for odd total exponent, symbolically, with the even-Ω maximiser;
- [JY26b]'s energy $\tfrac12[n+d_ad_b-2g_ag_b]$ and both same-parity maximisers;
- Sander–Sander's $E_{\max}(3\cdot5\cdot7)=520$ with unique maximiser $\{1,15,21,35\}$ [SS11, introduction];
- the definitional energy for every divisor set of several orders.

A fast incremental implementation is differentially tested against a direct reference implementation, and wrong claimed maximisers are rejected. See [`tests/test_icg_families.py`](../../tests/test_icg_families.py).

## Results

The last column counts the competing divisor sets and the polynomial inequalities in the certificate.

### Orders $3^a p^b$, $p\ge5$ prime

| Order | Range | Maximal-energy divisor sets | Competitors / inequalities |
|---|---|---|---|
| $3·p$ | $p\ge 5$ | even-Ω; odd-Ω | 5 / 5 |
| $3·p^2$ | $p\ge 5$ | even-Ω | 30 / 30 |
| $3·p^3$ | $p\ge 5$ | even-Ω; odd-Ω | 125 / 125 |
| $3·p^4$ | $p\ge 5$ | even-Ω | 510 / 510 |
| $3·p^5$ | $p\ge 5$ | even-Ω; odd-Ω | 2,045 / 2,045 |
| $3·p^6$ | $p\ge 5$ | even-Ω | 8,190 / 8,190 |
| $3·p^7$ | $p\ge 5$ | even-Ω; odd-Ω | 32,765 / 32,765 |
| $3^2·p$ | $p\ge 5$ | even-Ω | 30 / 30 |
| $3^2·p^2$ | $p\ge 5$ | even-Ω; odd-Ω | 253 / 263 |
| $3^2·p^3$ | $p\ge 5$ | even-Ω | 2,046 / 2,221 |
| $3^2·p^4$ | $p\ge 5$ | even-Ω; odd-Ω | 16,381 / 18,623 |
| $3^3·p$ | $p\ge 5$ | even-Ω; odd-Ω | 125 / 130 |
| $3^3·p^2$ | $p\ge 5$ | even-Ω | 2,046 / 2,365 |
| $3^3·p^3$ | $p\ge 5$ | even-Ω; odd-Ω | 32,765 / 42,126 |
| $3^4·p$ | $p\ge 5$ | even-Ω | 510 / 567 |
| $3^4·p^2$ | $p\ge 5$ | even-Ω; odd-Ω | 16,381 / 21,813 |
| $3^5·p$ | $p\ge 5$ | even-Ω; odd-Ω | 2,045 / 2,476 |
| $3^6·p$ | $p\ge 5$ | even-Ω | 8,190 / 10,909 |
| $3^7·p$ | $p\ge 5$ | even-Ω; odd-Ω | 32,765 / 48,280 |

### Orders $2^a p^b$, $p$ odd prime

| Order | Range | Maximal-energy divisor sets | Competitors / inequalities |
|---|---|---|---|
| $2·p$ | $p\ge 3$ | {1, p, 2} | 6 / 6 |
| $2·p^2$ | $p\ge 3$ | {1, p, 2}; {1, 2, 2·p}; {p, p^2, 2, 2·p} | 28 / 28 |
| $2·p^3$ | $p\ge 3$ | {1, p, 2·p, 2·p^2}; {1, p^3, 2, 2·p}; {p, p^2, 2, 2·p} | 124 / 124 |
| $2·p^4$ | $p\ge 3$ | {1, p, p^4, 2·p, 2·p^2} | 510 / 510 |
| $2·p^5$ | $p\ge 3$ | {1, p, p^4, p^5, 2, 2·p^3, 2·p^4} | 2,046 / 2,046 |
| $2·p^6$ | $p\ge 3$ | {1, p, p^4, p^5, 2, 2·p^3, 2·p^4}; {1, p^3, p^4, 2, 2·p, 2·p^4, 2·p^5}; {p, p^2, p^5, p^6, 2, 2·p, 2·p^4, 2·p^5} | 8,188 / 8,188 |
| $2·p^7$ | $p\ge 3$ | {1, p, p^4, p^5, 2·p, 2·p^2, 2·p^5, 2·p^6}; {1, p^3, p^4, p^7, 2, 2·p, 2·p^4, 2·p^5}; {p, p^2, p^5, p^6, 2, 2·p, 2·p^4, 2·p^5} | 32,764 / 32,764 |
| $2^2·p$ | $p\ge 3$ | even-Ω | 30 / 30 |
| $2^2·p^2$ | $p\ge 3$ | {1, p^2, 2, 2·p^2, 2^2·p} | 254 / 258 |
| $2^2·p^3$ | $p\ge 3$ | even-Ω | 2,046 / 2,122 |
| $2^2·p^4$ | $p\ge 3$ | {1, p^2, p^4, 2, 2·p^2, 2·p^4, 2^2·p, 2^2·p^3} | 16,382 / 17,426 |
| $2^3·p$ | $p\ge 5$ | {1, 2, 2^2·p, 2^3}; {1, 2·p, 2^2·p, 2^3} | 125 / 125 |
| $2^3·3$ | (enumerated) | {1, 3, 2, 2^2·3, 2^3}; {1, 3, 2·3, 2^2·3, 2^3}; {1, 2, 2^2·3}; {1, 2, 2^2·3, 2^3}; {1, 2·3, 2^2, 2^2·3, 2^3}; {1, 2·3, 2^2·3, 2^3} | exhaustive |
| $2^3·p^2$ | $p\ge 3$ | {1, p^2, 2, 2·p^2, 2^2, 2^2·p^2, 2^3·p}; even-Ω | 2,045 / 2,339 |
| $2^3·p^3$ | $p\ge 3$ | {1, p^2, 2, 2·p^2, 2^2·p, 2^2·p^3, 2^3, 2^3·p^2}; {1, p^2, 2·p, 2·p^3, 2^2·p, 2^2·p^3, 2^3, 2^3·p^2} | 32,765 / 41,665 |
| $2^4·p$ | $p\ge 3$ | {1, 2, 2^2·p, 2^3·p, 2^4}; even-Ω | 509 / 581 |
| $2^4·p^2$ | $p\ge 3$ | {1, p^2, 2, 2·p^2, 2^2·p, 2^3, 2^3·p^2, 2^4·p}; {1, p^2, 2·p, 2^2, 2^2·p^2, 2^3, 2^3·p^2, 2^4·p} | 16,381 / 22,205 |
| $2^5·p$ | $p\ge 3$ | {1, 2, 2^2·p, 2^3, 2^4·p, 2^5}; {1, 2·p, 2^2, 2^3·p, 2^4·p, 2^5} | 2,045 / 2,603 |
| $2^6·p$ | $p\ge 3$ | {1, 2, 2^2·p, 2^3, 2^4·p, 2^5·p, 2^6}; even-Ω | 8,189 / 11,765 |
| $2^7·p$ | $p\ge 3$ | {1, 2, 2^2·p, 2^3, 2^4·p, 2^5, 2^6·p, 2^7}; {1, 2·p, 2^2, 2^3·p, 2^4, 2^5·p, 2^6·p, 2^7} | 32,765 / 53,435 |

### Orders with three or four prime factors

| Order | Range | Maximal-energy divisor sets | Competitors / inequalities |
|---|---|---|---|
| $2·p·q$ | $p<q$, primes $\ge 3$ | {1, p, 2·q, 2·p}; {1, p·q, 2, 2·p}; {q, p, 2, 2·p} | 124 / 124 |
| $2·p·q$ | $p>q$, primes $\ge 3$ | {1, q, 2·q, 2·p}; {1, p·q, 2, 2·q}; {q, p, 2, 2·q} | 124 / 124 |
| $3·p·q$ | $p<q$, primes $\ge 5$ | even-Ω | 126 / 126 |
| $3·p·q$ | $p>q$, primes $\ge 5$ | even-Ω | 126 / 126 |
| $2^2·p·q$ | $p<q$, primes $\ge 3$ | {1, p·q, 2, 2·p·q, 2^2·q, 2^2·p} | 2,046 / 2,266 |
| $2^2·p·q$ | $p>q$, primes $\ge 3$ | {1, p·q, 2, 2·p·q, 2^2·q, 2^2·p} | 2,046 / 2,266 |
| $2·p^2·q$ | $p<q$, primes $\ge 3$ | {1, p, p^2·q, 2·q, 2·p, 2·p^2} | 2,046 / 2,210 |
| $2·p^2·q$ | $p>q$, primes $\ge 3$ | maximum of {1, q, p^2, p^2·q, 2, 2·p·q, 2·p^2}; {1, p, p^2·q, 2·q, 2·p, 2·p^2} | 2,045 / 2,129 (convex) |
| $3^2·p·q$ | $p<q$, primes $\ge 5$ | even-Ω; odd-Ω | 2,045 / 2,263 |
| $3^2·p·q$ | $p>q$, primes $\ge 5$ | even-Ω; odd-Ω | 2,045 / 2,263 |
| $3·p^2·q$ | $p<q$, primes $\ge 5$ | even-Ω; odd-Ω | 2,045 / 2,217 |
| $3·p^2·q$ | $p>q$, primes $\ge 5$ | even-Ω; odd-Ω | 2,045 / 2,111 |
| $2·p^3·q$ | $p<q$, primes $\ge 3$ | {1, p, p^2·q, p^3·q, 2, 2·p·q, 2·p^2·q, 2·p^3} | 32,766 / 40,972 |
| $2·p^3·q$ | $p>q$, primes $\ge 3$ | maximum of {1, q, p^2, p^2·q, 2·q, 2·p, 2·p^2·q, 2·p^3}; {1, p, p^2·q, p^3·q, 2, 2·p·q, 2·p^2·q, 2·p^3}; {1, p·q, p^2, p^3·q, 2, 2·q, 2·p^2, 2·p^2·q}; {q, p, p^2·q, p^3, 2, 2·q, 2·p^2, 2·p^2·q} | 32,763 / 35,887 (convex) |
| $2·3·p·q$ | $p<q$, primes $\ge 5$ | {1, p·q, 3, 3·p·q, 2, 2·p·q, 2·3·q, 2·3·p} | 32,766 / 34,851 |
| $2·3·p·q$ | $p>q$, primes $\ge 5$ | {1, p·q, 3, 3·p·q, 2, 2·p·q, 2·3·q, 2·3·p} | 32,766 / 34,851 |



### Four prime factors with even total exponent

These are not covered by any published theorem. The certificate also proves, with the maximisers exactly the even-Ω and odd-Ω sets:

| Order | Range | Maximal-energy divisor sets | Competitors / inequalities |
|---|---|---|---|
| $3\cdot5\cdot7\cdot p$ | $p\ge 11$ | even-Ω; odd-Ω | 32,765 |
| $3\cdot5\cdot p\cdot q$ | $p\ne q$, primes $\ge 7$ | even-Ω; odd-Ω | 32,765 per ordering |
| $5\cdot7\cdot p\cdot q$ | $p\ne q$ odd primes $\notin\{5,7\}$ | even-Ω; odd-Ω | 32,765 per ordering |

### A ratio-dependent maximiser

**Theorem.** Let $p,q$ be distinct odd primes and $n=2p^2q$. Put
$$A=\{1,q,p^2,p^2q,2,2pq,2p^2\},\qquad B=\{1,p,p^2q,2q,2p,2p^2\}.$$
If $p<q$, $B$ is the unique maximiser. If $p>q$, then $E(A)-E(B)=2(5p^2-6pq+9q-8)$. The unique maximiser is $A$ when $5p^2-6pq+9q-8>0$, roughly $p>\tfrac65q$, and $B$ otherwise. Equality never occurs.

*Proof.* The cases $p<q$ and $p>q$ are the two $2\cdot p^2\cdot q$ rows above (exact and convex certificates). The energy difference is a polynomial identity on the region. A tie would need $(6p-9)\mid(5p^2-8)$. Since $5p^2-8\equiv 13/4\pmod{2p-3}$, this forces $2p-3\mid 13$, so $p\in\{2,8\}$, which is impossible. $\square$

For example, $B$ wins at $(p,q)=(103,101)$ and $(127,109)$, and $A$ wins at $(131,107)$ and $(151,127)$, as the direct definition confirms. Order $2p^3q$ shows the same phenomenon with four candidates. In every proved case before this work, the maximiser was independent of the primes in its range. These examples show that even orders lose that universality.

## Conjectures

**Conjecture 1 (parity law at all odd orders).** Let $n>1$ be odd. If $\sum a_\nu$ is odd, the even-Ω set is the unique maximiser. If $\sum a_\nu\ge2$ is even and $n$ is not a prime power, the maximisers are exactly the even-Ω and odd-Ω sets.

This is [JY26a, JY26b] without the hypothesis that the primes are at least 5. It holds in every certified row with the prime 3 above. It also holds for $3^ap^b$ with up to 19 cells, computed with the same code: $(a,b)=(3,4),(4,3),(2,5),(5,2)$, all for every prime $p\ge5$. It holds at $3\cdot5\cdot7$, and in the four-prime even-total orders above.

**Conjecture 2 (2-adic tensor structure).** Let $a\ge2$, $b\ge1$, and let $p$ be an odd prime, with finitely many exceptions such as $2^3\cdot3$. Let $\mathcal S$ be the family of maximal-energy exponent sets of $\mathrm{ICG}(2^a)$ [SS11, Thm 1.1]. Then the maximisers of $\mathrm{ICG}(2^ap^b)$ are exactly
$$\mathcal D_S=\{2^ip^j\ne n:\ j\equiv[i\in T_S]\pmod 2\},\qquad T_S=\begin{cases}S\setminus\{0\},& b\ \text{odd},\\ (S\setminus\{0,a-1\})\cup\{a\},& b\ \text{even},\end{cases}$$
for $S\in\mathcal S$.

It holds in every certified row with $a\ge2$, and for $(a,b)=(2,5),(3,4),(5,2)$ with up to 19 cells. The case $a=1$ is different: the number of maximisers of $2p^b$ runs $1,3,3,1,1,3,3$ for $b=1,\dots,7$.

**Conjecture 3 (non-universality).** For every $k\ge1$ there are even orders with two odd prime factors whose maximising divisor set changes at least $k$ times as the ratio of the two primes varies.

The orders $2p^2q$ and $2p^3q$ give one change each.

## Limitations

- The certificate covers the 49 listed orders, plus the stated residual enumerations.
- The 17- and 19-cell cases cited under the conjectures came from exploratory runs of the same functions. They are not in the registered certificate.
- The conjectures are supported by these finite families only.
- The convex certificates show that the maximisers lie among the listed candidates. Which candidate wins at a given pair is decided by the explicit candidate energy polynomials stored in the certificate. For $2p^3q$ with $p>q$, those boundaries are not worked out in closed form here.

## References

- [SS11] J. W. Sander, T. Sander, The exact maximal energy of integral circulant graphs with prime power order, <https://arxiv.org/abs/1109.3616>.
- [JY26a] J. Jiang, C. Yang, Ramanujan transforms and maximum energy of odd-total-exponent integral circulants, arXiv:2608.29523 (v2, 30 October 2026), <https://arxiv.org/abs/2608.29523>.
- [JY26b] J. Jiang, C. Yang, Maximum energy of integral circulant graphs with same-parity exponents, arXiv:2610.36883, <https://arxiv.org/abs/2610.36883>.
- [R26] D. G. Roldán, Graph energy maximisation for integral circulant graphs of order $p^2q^3$, arXiv:2604.09491, <https://arxiv.org/abs/2604.09491>.
- [IB11] A. Ilić, M. Bašić, New results on the energy of integral circulant graphs, <https://arxiv.org/abs/1104.4261> (minimal energy for even $n$).

AI assistance: the certificates, code and this write-up were produced with Anthropic Claude. The literature status was checked on 27 November 2026. The novelty of individual rows is subject to the limits of that search.
