# A sharp nonsquare bound for positive arithmetic with arbitrary seeds

**Status: research proof draft; independent mathematical review pending.** Automated evidence is scoped below and does not certify the complete argument.

The nonsquare bounds of Tarek, Bahig and Anwar concern increasing addition–multiplication chains starting at 1. We allow several initial values, destructive overwrites, and writes below the previous maximum. [Published AM bounds, Corollary 3.1](https://doi.org/10.3934/Math.2026667) · [Previous two-largest-value result](../signed-growth/PROOF.md)

Let $H_i$ be the largest positive integer that has **ever** appeared by time $i$, including every initial seed. Suppose $H_0\ge2$. Take $\lambda(H)=\lfloor\log_2\log_2 H\rfloor+1$. Count an instruction as a square exactly when it writes $H_{i-1}^2$. All other instructions, including recomputation, count as nonsquares. A small step leaves $\lambda(H_i)=\lambda(H_{i-1})$. This agrees with the AM-chain definition in the increasing model. The allowed operations are addition, positive subtraction, multiplication and exact positive division. Registers may overwrite operands.

**Theorem.** With exactly $s\ge0$ small steps, the largest possible total number of nonsquares over all initial banks and value caps is
$$
 B(s)=\max\{b\ge0:\;2^b<2^{s+1}F_{b+2}\}.
$$
Here $F_0=0,F_1=1$. In particular $B(0)=3,\ B(1)=7,\ B(2)=10$. Two initially occupied registers suffice to attain the bound for every $s$. On a prescribed instance with current peak level $L$ and value cap $C$, one also has $b\le\lambda(C)-L+s$. The sharpness statement lets the cap vary.

**Upper bound.** Write $m=H_0$, and use a virtual second head of size $m$ initially. With $b$ nonsquares and $d$ squares so far, the two largest distinct values ever seen are bounded by
$$
 X=m^{2^d F_{b+2}},\qquad Y=m^{2^d F_{b+1}}.
$$
If there is only one distinct value, the bound on the second is vacuous. At a square the new maximum is bounded by $X^2$, the new runner-up by $X\le Y^2$. At a nonsquare the new maximum is at most $XY$. Any sum is at most $2X\le XY$. Subtraction and division cannot exceed the previous maximum. A product of the previous head with itself would count as a square. Every other product uses at least one operand bounded by $Y$. At most one new distinct value can exceed the old head, so after this instruction the second largest is at most $X$. Fibonacci addition proves the induction, even if a previously large value has been overwritten.

A single instruction increases the level by at most one. Since a canonical square always increases the level, after $b+d$ steps the final level is $L+b+d-s$. Put $D=2^{2^{L-1}}$. Then $D\le m<D^2$. The level lower bound and the upper envelope give
$$
 D^{2^{b+d-s}}\le H_{b+d}\le m^{2^d F_{b+2}}<D^{2^{d+1}F_{b+2}}.
$$
Cancel the positive common factor in the exponents to obtain $2^b<2^{s+1}F_{b+2}$. Equality in this last comparison is impossible. The admissible integers form an initial interval since $F_{b+3}\le2F_{b+2}$; the interval is finite since Fibonacci numbers grow as $\varphi^b$, with $\varphi<2$. The fixed-cap bound follows by counting the available level increases.

**Attainment.** Let $b=B(s)$, so
$$
 2^{b-s}<2F_{b+2}<2^{b+1-s}.
$$
The upper strict inequality follows from failure at $b+1$ and $F_{b+2}< F_{b+3}$. Also $b\ge s$. Start with the two distinct seeds $m=U-1,\ k=U-2$ just below the same upper level boundary $U=D^2$, choosing $U\ge4$. Repeatedly multiply the largest two, overwriting the smaller. After $b$ instructions the head is $m^{F_{b+1}}k^{F_b}$. No step is a square. As $U$ tends through the tower boundaries, its logarithm to base $D$ tends to $2F_{b+2}$, strictly between the two displayed powers of two. For all sufficiently large boundaries the achieved level gain is exactly $b-s$, so there were exactly $s$ small steps. All products are positive and bounded by the endpoint. This proves sharpness. The extremizing programs use multiplication alone after the two seeds.

## Exact extremum when the starting values are prescribed

Let $m\ge3$ be the largest starting value. Let $q$ be the maximum of 2 and the largest starting value strictly less than $m$, taking 2 when there is no smaller starting value. Suppose at least two registers are available, $b$ nonsquares and $d$ squares are prescribed, and the output cap permits the extremal path. The largest attainable historical peak is as follows.

- With $b=0$, it is $m^{2^d}$.
- With $d=0$, it is $m^{F_{b+1}}q^{F_b}$.
- With $b,d>0$, it is the larger of
  $$
  \left(m^{F_{b+1}}q^{F_b}\right)^{2^d},\qquad
  \left(m^{F_{b+3}}\right)^{2^{d-1}}.
  $$
  The first is larger precisely when $q^2>m$, with a tie at equality.

For the first expression take all nonsquares as maximal products of the last two heads, then square. If the first nonsquare needs a 2 absent from the seeds, double $m$ by addition. For the second expression first square $m$, then take all nonsquares and finish with the remaining squares. Each construction fits in two working registers, which may overwrite unused seeds.

To prove optimality, partition by the first instruction's type. A nonsquare first gives a pair componentwise bounded by $mq,m$; a square gives $m^2,m$. Each dominating pair is attainable. From then on its head is at most the square of its runner-up. The [prefix recurrence](../prefix-extrema/PROOF.md) bounds all later instructions: a nonrecord result can neither exceed the nonsquare product bound nor raise the runner-up above the prior head. Therefore the maximizing suffix in either part consists of its nonsquares followed by its squares. The Fibonacci identity $F_{b+3}=2F_{b+1}+F_b$ compares the two expressions by the sign of $q^2-m$. The special boundary $m=2$, where doubling is itself a canonical square, is outside this fixed-seed formula.

For example start with 1 and 16 and prescribe two nonsquares and one square. The maximum is $16^5$, attained by $256,4096,1048576$. For the initial bank 7,15 the ordering instead begins with the two nonsquares. The universal $B(s)$ loses this dependence on the starting bank. [Fixed-seed implementation](../../solved/record_defect.py)

## Verification

 The tests enumerate positive four-operation writes with destructive overwrite on small two-register states, including loss of the historical peak, and compare the counts with the theorem. Separate extremal constructions attain the sharp bound for small $s$ with exact integers. [Implementation](../../solved/record_defect.py) · [Tests](../../tests/test_record_defect.py)
