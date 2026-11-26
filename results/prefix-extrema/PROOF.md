# Sharp completion and increment bounds from an AM prefix

**Status: research proof draft; independent mathematical review pending.** Automated evidence is scoped below and does not certify the complete argument.

Section 7 of Tarek, Bahig and Anwar asks whether its growth bounds accelerate shortest-chain search and asks about consecutive upper bounds. We give two exact extrema from an arbitrary valid increasing prefix. The second concerns the difference between successive values **on the same chain**. Maximizing each value separately does not in general attain that difference. The hypotheses concern positive integer addition and multiplication with unrestricted retention. [Paper, Theorems 3.1–3.2 and §7](https://doi.org/10.3934/Math.2026667)

**Endpoint theorem.** Suppose the last two values are $k<m$, with $k\ge2$ and $m\le k^2$, as in any valid increasing prefix of length at least two. Prescribe exactly $b$ further canonical nonsquares and $d$ further squares, in any order. Define $E_{-1}=k,\ E_0=m,\ E_{i+1}=E_iE_{i-1}$. The largest attainable endpoint is
$$
M(b,d)=E_b^{2^d}.
$$
It is attained by taking all $b$ nonsquares as products of the two latest values, then taking the $d$ squares.

*Proof.* With last pair $x>y\ge2$ an increasing nonsquare is at most $xy$. Indeed the largest sum is $2x\le xy$, and a nonsquare product uses an operand at most $y$. Inductively the two latest entries after any ordering are bounded above by $E_b^{2^d}$ and $E_{b-1}^{2^d}$. The nonsquare transition follows from multiplication. At a square the old largest becomes the second largest and fits the new bound since $E_b\le E_{b-1}^2$. This holds also for $b=0$ by the prefix hypothesis. The constructive ordering proves sharpness of the endpoint. Specializing to $(k,m)=(2,3)$ or $(2,4)$ recovers the published bounds with their respective initial step counts.

**Consecutive-increment theorem.** After the prescribed $b,d$ steps, take one more step and maximize its increment. Write $F_0=0,F_1=1$ for the Fibonacci sequence.

- If the next step is a square, the answer is $M(b,d)(M(b,d)-1)$.
- If the next step is a nonsquare and $d=0$, the answer is $E_b(E_{b-1}-1)$.
- If the next step is a nonsquare and $d\ge1$, let $Z_j=E_{b-j}^{2^{d-1}}$. The exact answer is
  $$
  \max_{0\le j\le b} Z_j^{F_{j+3}}\left(Z_j^{F_{j+2}}-1\right).
  $$

*Proof.* For last pair $x,y$ the largest next nonsquare increment is $x(y-1)$, increasing in both coordinates and attained by multiplying them. If $d=0$, the greedy products maximize both coordinates simultaneously. Otherwise partition by the number $j$ of nonsquares after the last square. Immediately before that square the head is at most $Z_j$, with equality attainable by the endpoint theorem. The square resets the pair to $Z_j^2,Z_j$ in the maximizing history. Following it by $j$ maximal products gives the Fibonacci exponents by induction. Both coordinates dominate those of every chain in the part. Each part has an attaining history. Taking the maximum proves the formula. For example from $k=2,m=3$ with $b=d=1$, the largest next nonsquare increment is 216, attained via $3,9,27,243$. Following the history attaining the largest endpoint 36 instead gives a next increment of only 180.


## Verification

Finite exhaustive continuations check both sharp extrema, including cases where the largest endpoint and the largest next increment use different histories. [Implementation](../../solved/prefix_growth.py) · [Tests](../../tests/test_prefix_growth.py).
