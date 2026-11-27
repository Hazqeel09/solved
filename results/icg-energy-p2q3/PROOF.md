# The maximal-energy divisor set of integral circulant graphs of order $p^2q^3$

**Status:** proof draft (independent re-verification of known results), awaiting Lean verification.

**Priority.** This is an independent re-verification of a known result. The statement is Conjecture 1.3 of Roldán [R26]. Earlier treatments:

- S. Park claims a proof for all distinct odd primes (manuscript, 21 August 2026).
- J. A. Schreib gives a written proof of the case $q=3$ (5 September 2026).
- Jiang and Yang prove the case $q\ge5$ as part of a general theorem [JY26, Theorem A].
- The Omega Institute announced an arithmetic certificate for $q=3$ [OI26].
- H. Dong proves the case $q=3$ for all orders $p^{2r}3^{2s+1}$, with a Lean formalization bridged to the graph energy of Mathlib's circulant graphs [D26].

The certificate here was developed independently of these, before we found them. We claim no priority. This entry is not yet formalized in Lean.

## Statement

For a positive integer $n$ and a nonempty set $\mathcal D$ of proper divisors of $n$, the integral circulant graph $\mathrm{ICG}(n,\mathcal D)$ has vertex set $\mathbb Z_n$, with $a\sim b$ iff $\gcd(a-b,n)\in\mathcal D$. Its energy is the sum of the absolute values of its eigenvalues:
$$E(n,\mathcal D)=\sum_{e\mid n}\varphi(n/e)\,\Bigl|\sum_{d\in\mathcal D}c(e,n/d)\Bigr| ,$$
where $c$ is the Ramanujan sum [R26, eqs. (1)–(2)].

**Theorem.** Let $p,q$ be distinct odd primes and $n=p^2q^3$. Among all nonempty sets $\mathcal D$ of proper divisors of $n$, the energy $E(n,\mathcal D)$ is uniquely maximised by
$$\mathcal D^*=\{1,\;p^2,\;pq,\;q^2,\;p^2q^2,\;pq^3\}=\{p^aq^b\mid n:\ a+b\ \text{even}\},$$
and
$$E(n,\mathcal D^*)=(5p^2-8p+4)(q-1)(3q^2-2q+1)+(p-1)(2p-1)(q^3-2q^2+2q-2)+(p^2-2p+2)(q-1)(q^2+1)+(p-1)q^3$$
[R26, Thm 1.2].

The proof establishes the strict inequality $E(\mathcal D)<E(\mathcal D^*)$ for the polynomial extension of the energy at every real pair $p,q\ge3$.

## Proof

**Factorization.** Write $d=p^aq^b$ with $(a,b)\in\{0,1,2\}\times\{0,1,2,3\}\setminus\{(2,3)\}$, and $e=p^\alpha q^\beta$. The Ramanujan sum $c(e,\cdot)$ is multiplicative, so
$$c(e,n/d)=u_\alpha(a)\,v_\beta(b),\qquad u_\alpha(a)=c(p^\alpha,p^{2-a}),\quad v_\beta(b)=c(q^\beta,q^{3-b}).$$
Hölder's formula $c(j,m)=\mu(m/g)\varphi(m)/\varphi(m/g)$ with $g=\gcd(j,m)$ gives, for a prime $r$,
$$c(r^\alpha,r^i)=\begin{cases}1,& i=0,\\ r^i-r^{i-1},& 1\le i\le\alpha,\\ -r^{i-1},& i=\alpha+1,\\ 0,& i\ge\alpha+2,\end{cases}$$
which is a polynomial in $r$. Hence
$$E(\mathcal D)=\sum_{\alpha=0}^{2}\sum_{\beta=0}^{3} w_{\alpha\beta}\,|L_{\alpha\beta}(\mathcal D)|,\qquad L_{\alpha\beta}(\mathcal D)=\sum_{(a,b)\in\mathcal D}u_\alpha(a)v_\beta(b),\qquad w_{\alpha\beta}=\varphi(p^{2-\alpha})\varphi(q^{3-\beta}),$$
with every $u$, $v$ and $w$ an integer polynomial in $(p,q)$. This is the Kronecker structure behind [R26, Thm 1.1]. The right-hand side defines a function of real $(p,q)$, which we keep calling $E(\mathcal D)$.

**Certificates.** Call an integer polynomial $f(p,q)$ *certified nonnegative* on $[3,\infty)^2$ if every coefficient of $f(3+x,\,3+y)$ is $\ge0$. Call it *certified positive* if, in addition, the constant coefficient is $>0$. Then $f\ge0$, respectively $f>0$, for all real $p,q\ge3$.

1. Each of the twelve forms $L_{\alpha\beta}(\mathcal D^*)$ is certified nonnegative, or its negative is. Hence $E(\mathcal D^*)$ equals the explicit polynomial $E^*=\sum w_{\alpha\beta}s^*_{\alpha\beta}L_{\alpha\beta}(\mathcal D^*)$ on $[3,\infty)^2$. It agrees with [R26, Thm 1.2].
2. Fix $\mathcal D\ne\mathcal D^*$. For each class $(\alpha,\beta)$, either $\pm L_{\alpha\beta}(\mathcal D)$ is certified nonnegative, which fixes its sign $s_{\alpha\beta}$ (or the form is identically zero), or the class is *free*. At every point, $|L|=sL$ for the true sign $s\in\{\pm1\}$. So $E(\mathcal D)=\sum w\,s\,L$ for some choice of signs on the free classes.
3. For every such choice, $E^*-\sum_{\alpha\beta}w_{\alpha\beta}s_{\alpha\beta}L_{\alpha\beta}(\mathcal D)$ is certified positive.

Combining 1–3 gives $E(\mathcal D)<E(\mathcal D^*)$ for every $\mathcal D\ne\mathcal D^*$ and all real $p,q\ge3$, in particular for all distinct odd primes. $\square$

The certificate covers 2,046 competitors, branches over the sign of 1,212 forms in total, and consists of 3,658 polynomial inequalities. Every inequality passes the coefficient test, so no subdivision of the domain or finite residue is needed.

## Verification

- [`solved/icg_energy.py`](../../solved/icg_energy.py) implements exact bivariate integer polynomials, the factorized energy, the certificate and an independent energy straight from the definition. `python -m checks.verify_icg_energy` re-derives the certificate in seconds.
- [`tests/test_icg_energy.py`](../../tests/test_icg_energy.py) checks the following:
  - the factorized energy equals the defining sum for all 2,047 divisor sets at eight prime pairs, in both orders;
  - the Ramanujan sums agree with the exponential sums for $m<60$;
  - $E^*$ equals [R26, Thm 1.2] as a polynomial;
  - the certificate succeeds on $[3,\infty)^2$;
  - exhaustive exact maximisation agrees for all distinct primes $3\le p,q<60$.
- Negative controls show the test is not vacuous: certifying a wrong maximiser fails, and so does the domain $[1,\infty)^2$.

During exploration a separate vectorized search confirmed $\mathcal D^*$ for all 5,852 ordered pairs of distinct primes up to 400. It also confirmed 13,560 pairs in which one prime lies in $\{3,5,7\}$ and the other is below 20,000. That search is evidence only; the theorem rests on the certificate.

## References

- [R26] D. G. Roldán, Graph energy maximisation for integral circulant graphs of order $n=p^2q^3$, arXiv:2604.09491 (v1, 10 April 2026), Conjecture 1.3, Theorems 1.1–1.2. <https://arxiv.org/abs/2604.09491>
- [JY26] J. Jiang, C. Yang, Ramanujan transforms and maximum energy of odd-total-exponent integral circulants, arXiv:2608.29523 (v2, 30 October 2026), Theorem A. It requires every prime with odd exponent to be at least 5; the case $q=3$ is outside its hypotheses. <https://arxiv.org/abs/2608.29523>
- [JY26b] J. Jiang, C. Yang, Maximum energy of integral circulant graphs with same-parity exponents, arXiv:2610.36883. <https://arxiv.org/abs/2610.36883>
- [D26] H. Dong, ai4math-results, paper 1 version 3 (9 November 2026), <https://github.com/Horace-Maxwell/ai4math-results/tree/8e81669b092b3620034c95d8690dbeb99da07ef1/papers/icg-q3-general>.
- [P26] S. Park, Exact energy maximisation for integral circulant graphs of order $p^2q^3$, <https://github.com/coshaman/papers/tree/2f730393e3d5bed4d9641d7d79b1bdc57fbff05d>.
- [S26] J. A. Schreib, The Roldán universality conjecture, <https://github.com/jamesschreib/roldan-universality-conjecture/tree/95bb002688c65948a15cc9380e8e1f08f8bd6801>.
- [OI26] Omega Institute research tracker, issue #19144, "prove Roldan Conjecture 1.3 … including the open case q = 3", closed 23 October 2026 as "Proved" (unreviewed). <https://github.com/the-omega-institute/trureturing/issues/19144>

AI assistance: the certificate, code and write-up were produced with Anthropic Claude. The literature status was checked on 27 November 2026.
