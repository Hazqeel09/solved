# Matroid polynomial conjectures on q-uniform matroids with free points

**Status:** finite verification, with one elementary proposition proved in full. Independent review pending.

## Questions

For a loopless matroid $M$ of rank $r$ with lattice of flats $\mathcal L(M)$, write $P_M$ for its Kazhdan–Lusztig polynomial, $Z_M$ for its $Z$-polynomial, $Q_M$ for its inverse Kazhdan–Lusztig polynomial, $Y_M$ for its inverse $Z$-polynomial, $\underline H_M$ for its Chow polynomial and $H_M$ for its augmented Chow polynomial. Definitions and normalizations are those of Elias–Proudfoot–Wakefield [EPW, Thm 2.2], Proudfoot–Xu–Young [PXY, Def. 2.1], Gao–Xie [GX, relation (14)], Gao–Ruan–Xie [GRX, eqs. (2)–(3)] and Ferroni–Matherne–Schulte–Vecchi [FMSV, Thms 1.3–1.4]; they are restated in the docstring of [`solved/matroid_polynomials.py`](../../solved/matroid_polynomials.py).

The following conjectures were open on 27 November 2026 as far as the cited literature shows:

1. $Z_M$ has only real zeros for every matroid [PXY, Conj. 5.1]. It is proved for sparse paving matroids [XZ26].
2. $Y_M$ has unimodal coefficients, and log-concave coefficients with no internal zeros [GRX, Conj. 1.4, 1.5]. It is proved for sparse paving matroids [GRX, Thm 1.6].
3. $\underline H_M$ has only real zeros [FMSV, Conj. 1.6; FS22, Conj. 8.18]. It is proved in rank at most 6 [CFL26, Cor. 1.10] and for uniform matroids.
4. $H_M$ has only real zeros [FMSV, Conj. 1.6]. It is proved for uniform matroids [FMSV, Thm 1.10].

The sibling statements for $P_M$ (real-rootedness and log-concavity) and for $Q_M$ (log-concavity) are false [CL26, Bad26]. The engine below reproduces the rank-7 binary counterexample of [CL26, Thm A.4], whose $P_M=1+13t+7t^2+t^3$ has two nonreal zeros.

## The family

Let $q\ge1$ be an integer, and $0\le k\le n$, $m\ge0$. Let $F_q(n,k,m)$ be the truncation $T_k(\mathrm{PG}(n-1,q))$ to rank $k$, extended by $m$ points in general position (iterated free extensions). For a prime power $q$ this is a matroid; truncations and free extensions of a $\mathrm{GF}(q)$-representable matroid are representable over a sufficiently large extension field. For $q=1$, $F_1(n,k,m)=U_{k,n+m}$.

Its proper flats are the sets $X\cup A$ with $X$ a subspace of dimension $x$, $A$ a set of $a$ free points, and $x+a\le k-1$. The lower interval of such a flat is $\mathrm{PG}(x-1,q)\times B_a$. The upper interval is $F_q(n-x,\,k-x-a,\,m-a)$. Hence every invariant above satisfies a recursion in $(n,k,m)$, implemented in [`solved/q_uniform.py`](../../solved/q_uniform.py).

## Finite verification

**Claim.** For every $(q,n,k,m)$ with $1\le k\le n$ in the ranges below, $F_q(n,k,m)$ satisfies conjectures 1–4.

| $q$ | $n\le$ | free points $m$ (only when $n\le 6$) |
|---|---|---|
| 1 | 24 | 0 |
| 2 | 16 | $0,\dots,40$ |
| 3 | 13 | $0,\dots,40$ |
| 4 | 12 | $0,\dots,40$ |
| 5 | 11 | $0,\dots,40$ |
| 7, 8, 9 | 10 | $0,\dots,40$ |
| 11, 13, 16 | 9 | $0,\dots,40$ |

That is 9,371 matroids. Run `python -m checks.verify_q_uniform`. Each decision uses exact integer arithmetic. Real-rootedness is decided by Yun square-free factorization and Sturm sequences over $\mathbb Q$.

The recursion is trusted only through comparison with the independent lattice-of-flats engine. That engine enumerates flats, computes Möbius functions of every interval, and re-verifies each defining identity. It also checks $P_M$ two independent ways, by PXY Lemma 2.2 and by Gao–Xie Theorem 1.3 (4). The comparison, in [`tests/test_q_uniform.py`](../../tests/test_q_uniform.py), covers uniform matroids $U_{k,n+m}$ for $n\le 8$ and $m\le 2$, every truncation of $\mathrm{PG}(n-1,q)$ for $(q,n)\in\{(2,\le6),(3,\le4),(5,\le3)\}$, and explicit free extensions with up to four points. The lattice engine is itself tested against:

- closed forms [EPW Cor. 2.20; GX Thm 3.3; GRX Thms 1.1, 1.3; PXY Ex. 5.3];
- published examples;
- Ferroni–Schröter valuativity under relaxation for all six invariants [FS22, Thm 3.30];
- the Bose–Burton formulas [CL26, Remark 2.7];
- the [CL26] rank-7 counterexample.

This is evidence about one family. It does not resolve any conjecture.

## A proved proposition: modular lattices

**Proposition.** Let $M$ be a loopless matroid whose lattice of flats is modular. Then $Q_M=|\mu(\hat0,\hat1)|$ is constant, and
$$Y_M(t)=\sum_{F\in\mathcal L(M)} |\mu(\hat0,F)|\,|\mu(F,\hat1)|\,t^{\,r-\operatorname{rk}F}.$$
In particular
$$Y_{\mathrm{PG}(r-1,q)}(t)=\sum_{j=0}^{r}\binom{r}{j}_{\!q} q^{\binom j2+\binom{r-j}2}\,t^{j}.$$

*Proof.* Every interval of a modular lattice is modular, so every interval has KL polynomial $1$ [EPW, Prop. 2.14]. Gao–Xie's defining relation $\sum_{F}P_{M|F}\,\widehat Q_{M/F}=0$ for positive rank (relation (16) of [GX]), applied to every interval $[A,B]$, then reads $\sum_{A\le F\le B}\widehat Q_{[F,B]}=\delta_{A,B}$. So $\widehat Q$ is the Möbius function of the incidence algebra. The constants $\mu(A,B)$ satisfy the degree condition $\deg<\operatorname{rk}/2$, and $\widehat Q$ is unique, so $\widehat Q_{[A,B]}=\mu(A,B)$. In a geometric lattice $\mu(A,B)$ has sign $(-1)^{\operatorname{rk}B-\operatorname{rk}A}$, so $Q_{[A,B]}=|\mu(A,B)|$.

Substituting into $Y_M=(-1)^r\sum_F(-1)^{\operatorname{rk}F}Q_{M|F}\,t^{r-\operatorname{rk}F}\mu(F,\hat1)$ [GRX, eqs. (2)–(3)] gives the displayed formula: each sign is $(-1)^{r+\operatorname{rk}F+(r-\operatorname{rk}F)}=1$.

For $\mathrm{PG}(r-1,q)$ there are $\binom rj_q$ flats of corank $j$, with $|\mu(\hat0,F)|=q^{\binom{r-j}2}$ and $|\mu(F,\hat1)|=q^{\binom j2}$. $\square$

**Corollary.** For $q\ge2$ and $1\le j\le r-1$ the coefficients $y_j$ of $Y_{\mathrm{PG}(r-1,q)}$ satisfy
$$\frac{y_j^2}{y_{j-1}y_{j+1}}=\frac{(q^{\,r-j+1}-1)(q^{\,j+1}-1)}{q^2\,(q^{\,j}-1)(q^{\,r-j}-1)}>1 .$$
So $Y_{\mathrm{PG}(r-1,q)}$ is strictly log-concave, and the ratio tends to $1$ as $q\to\infty$, or as $j$ and $r-j$ grow.

*Proof.* The ratio of consecutive Gaussian binomials gives the formula: the exponents $\binom j2+\binom{r-j}2$ have second difference $2$, contributing the factor $q^{-2}$. Write $A=q^j$ and $B=q^{r-j}$. Then numerator minus denominator equals $(q-1)\bigl(q(A+B)-(q+1)\bigr)$, which is positive because $A,B\ge q$. $\square$

The margin is about $\tfrac{q-1}{q}(q^{-j}+q^{j-r})$. So the inverse-$Z$ log-concavity of projective geometries is exponentially thin in the rank. A perturbation of relative size $q^{-r/2}$ in the right shape could break it.

The computations found that deleting points and subspaces from $\mathrm{PG}(r-1,q)$ and truncating it widen this margin. Free points shrink it in rank 4 but widen it in rank 5. None of these crosses it in the ranges checked. These are recorded observations, not claims about all perturbations.

## Limitations

- The verification covers one parametric family and the stated finite ranges. The rank-7 binary searches over random and annealed point sets of $\mathrm{PG}(6,2)$ ran during this work. They are exploratory, record no failure, and are not part of the claim.
- $q$ is used as an integer parameter. The matroid interpretation of $F_q(n,k,m)$ requires $q$ to be a prime power or $q=1$, which holds for every listed $q$.

## References

- [EPW] B. Elias, N. Proudfoot, M. Wakefield, The Kazhdan–Lusztig polynomial of a matroid, <https://arxiv.org/abs/1412.7408>.
- [PXY] N. Proudfoot, Y. Xu, B. Young, The Z-polynomial of a matroid, <https://arxiv.org/abs/1706.05575>.
- [GX] A. L. L. Gao, M. H. Y. Xie, The inverse Kazhdan–Lusztig polynomial of a matroid, <https://arxiv.org/abs/2007.15349>.
- [GRX] A. L. L. Gao, Y. Ruan, M. H. Y. Xie, inverse Z-polynomial of a matroid, <https://arxiv.org/abs/2507.01332>.
- [FMSV] L. Ferroni, J. P. Matherne, M. Schulte, L. Vecchi, Hilbert–Poincaré series of matroid Chow rings and intersection cohomology, <https://arxiv.org/abs/2212.03190>.
- [FS22] L. Ferroni, B. Schröter, Valuative invariants for large classes of matroids, <https://arxiv.org/abs/2208.04893>.
- [CFL26] B. Coron, L. Ferroni, S. Li, Matroid analogues of Gal's conjecture, <https://arxiv.org/abs/2604.04550>.
- [XZ26] M. H. Y. Xie, P. B. Zhang, Real-rootedness of the Z-polynomials of sparse paving matroids and strict interlacing for uniform matroids, <https://arxiv.org/abs/2609.07636>.
- [CL26] R. Cheng, S. Liu, Kazhdan–Lusztig polynomials of matroids need not be unimodal, <https://arxiv.org/abs/2607.24186>.
- [Bad26] E. Badalov, Prescribed Turán sign patterns for inverse Kazhdan–Lusztig polynomials of matroids, <https://arxiv.org/abs/2609.13417>.

AI assistance: computations, code and this write-up were produced with Anthropic Claude. The literature status was checked against the arXiv versions listed on 27 November 2026.
