# The maximal energy of integral circulant graphs of order $2p^b$

**Theorem.** Let $p$ be an odd prime and $b\ge1$. For every set $S$ of proper divisors of $n=2p^b$,

$$E(\mathrm{ICG}(n,S))\ \le\ E_{\max}(2p^b)=2\sum_{j=0}^{b}\varepsilon_j\,(b+1-j)\,p^{\,b-j},\qquad
\varepsilon=(1,-1,-1,1,1,-1,-1,1,\dots),$$

with $\varepsilon_j=1$ for $j\equiv0,3$ and $\varepsilon_j=-1$ for $j\equiv1,2 \pmod 4$. Equality holds for
$$S^*=\{p^b\}\cup\{p^k:\ k<b,\ z_k=1\}\cup\{2p^k:\ k<b,\ w_k=1\},$$
where the corner $(z_k,w_k)$ chosen $r=b-1-k$ steps below the top walks the 4-cycle of the unit square:
$(0,0),(0,1),(1,1),(1,0)$ for $b\equiv0,3\pmod 4$ and $(1,1),(0,1),(0,0),(1,0)$ otherwise.

The first values are $4p-2$, $6p^2-4p-2$, $8p^3-6p^2-4p+2$, $10p^4-8p^3-6p^2+4p+2$. Here $E$ is the sum of the
absolute values of the eigenvalues of the adjacency matrix ($x\sim y$ iff $\gcd(y-x,n)\in S$). The theorem is
Lean-checked (`Solved.ICG.TwoPb.energy_max_all`; see [FORMALIZATION.md](FORMALIZATION.md)). Only the maximum and one
maximiser are formalized; the full list of maximisers (one for $b\equiv0,1$, three for $b\equiv2,3\pmod4$ in
exhaustive searches with $b\le8$ at $p=3,5,7,11$) is not.

## Prior work

The maximal energy is known for prime powers (Sander–Sander, arXiv 1109.3616, 1205.4603), for odd orders
$p^aq^b$ in several regimes (Jiang–Yang, arXiv 2608.29523, 2610.36883; Dong, ai4math-results; Roldán,
arXiv 2604.09491 for $p^2q^3$), and for $2^ap$ (companion entry [icg-energy-even-orders](../icg-energy-even-orders/PROOF.md),
whose certified families include $2p^b$ for $b\le7$). Sander–Sander state that exact maxima beyond prime powers were
open and that the energy is not multiplicative; indeed $E_{\max}(2p)=4p-2>2E_{\max}(p)=4p-4$. Ilić–Bašić
(arXiv 1104.4261) treat even orders for the minimal energy only. Three searches (arXiv, zbMATH, Dong's repository to
v1.26.0, the Omega Institute tracker, 28 November 2026) found no determination of $E_{\max}(2p^b)$ for general
$b$. Le–Sander (Linear Algebra Appl. 437 (2012) 1408–1421) could not be read; citing papers describe it as giving
bounds via multiplicative divisor sets. The search may be incomplete.

## Proof

**Chain form.** Dong's two-prime bridge, applied with the primes in the order $(p,2)$, writes
$E=p^b\bigl(F_2(\zeta_0)+\sum_{k<b}F_2(\zeta_k-\zeta_{k+1})\bigr)$ with $F_2(\alpha,\beta)=|\beta-\alpha|+|\alpha+\beta|
=2\max(|\alpha|,|\beta|)$, states $\zeta_k\in[0,1]^2$, $\zeta_b=([p^b\in S],0)$ and
$\zeta_k=x\zeta_{k+1}+(1-x)c_k$, $x=1/p$, where $c_k=([p^k\in S],[2p^k\in S])$ is a corner of the square. Each step
gains $2(1-x)\|c_k-\zeta_{k+1}\|_\infty$, so $E/p^b$ is twice the $\ell^\infty$ length of the path
$\zeta_b\to\dots\to\zeta_0\to0$.

**Value function.** With $n$ steps left, the optimal remaining value is at most
$W_n(u)=ng+\max_i Q_{n\bmod 4,i}(x^n;u)$, $g=2(1-x)/(1+x^2)$, where each piece is affine in $u$ with coefficients of
the form $\alpha(x)+\beta(x)x^n$; there are $16,10,14,10$ pieces for $n\equiv0,1,2,3$, closed under $s\leftrightarrow t$.
They were found from the exact recursion (computed symbolically and pruned by exact polygon clipping) and equal
the true value function for $n\ge5$. The step $T W_n\le W_{n+1}$ ($n\ge1$) is 400 inequalities, one per piece,
corner and maximising coordinate. Each is certified by nonnegative weights $N_l$ with $\sum N_l=M>0$ and
$M\cdot\text{candidate}\le\sum N_l Q_l$ on the square; with $y=p-3$ and $\tau=x^{n-m_n}\in[0,1]$ the difference is
affine in $(s,t)$ with polynomial coefficients, nonnegative at the four corners as polynomials in $y\ge0$ with
nonnegative coefficients (Bernstein form in $\tau$ where the weights depend on $\tau$). Sixteen base inequalities
give $V_1\le W_1$. Induction along the path gives $E\le p^bW_b(\zeta_b)$.

**Start identity.** The generating function of $\varepsilon$ is $(1-x)/(1+x^2)=g/2$, and
$S(b)=2\sum_{j\le b}\varepsilon_j(b+1-j)x^j=bg+\alpha+x^b\beta_{b\bmod4}$ with $\alpha=2(1+3x^2-2x^3)/(1+x^2)^2$.
At the top states $(0,0)$ and $(1,0)$ every piece is at most $S(b)$ for $b\ge2$, and one piece equals it at $(1,0)$.
Hence $E\le p^bS(b)=E_{\max}(2p^b)$.

**Attainment.** Along the path of $S^*$ every step is an exact identity between pieces,
$Q_{n+1,l}(u)=2(1-x)d_j(c,u)+Q_{n,i}(u')-g$, periodic in $(b\bmod4,n\bmod4)$, and $2(1-x)d_j\le$ the gain. So the
chain value of $S^*$ is at least the top piece, $S(b)$. The case $b=1$ is the certified family $2p$.

## Evidence and checks

- Lean: the whole argument, from Mathlib's eigenvalues, with axioms `propext`, `Classical.choice`, `Quot.sound`
  (audited in `formal/FormalTests/Axioms.lean`). The certificate data are untrusted search output
  (`checks/expected/two-pb-certificates.json`); `solved/lean_two_pb.py` turns them into Lean lemmas.
- `tests/test_lean_two_pb.py`: the pieces against the exact chain recursion ($p=3,5,7$, $n\le6$, grid and random
  points); the start value for $b\le20$; exhaustive maxima over all divisor sets by Ramanujan sums
  ($p=3$, $b\le4$; $p=5$, $b\le3$; $p=7,11$) and by adjacency eigenvalues; data shape and registration.
- The closed form agrees with the branch-and-bound families $2p^b$, $b\le7$ (`closed_form_eq_family`).

Not claimed: the complete list of maximisers, orders $2^ap^b$ with $a,b\ge2$ beyond the certified families, and
novelty beyond the qualified search above.
