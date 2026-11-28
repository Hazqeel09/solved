# Maximal-energy integral circulant graphs of order $2^ap^b$

**Status:** every statement below is a kernel-checked Lean theorem; see the [statement correspondence](FORMALIZATION.md). Independent mathematical review is pending. Novelty is assessed separately under *Prior work*; a formal proof does not make a statement new.

## Statement

For $n\ge2$ and a set $S$ of proper divisors of $n$, the integral circulant graph $\mathrm{ICG}(n,S)$ has vertex set $\mathbb Z_n$, with $x\sim y$ iff $\gcd(x-y,n)\in S$. Its energy $E(n,S)$ is the sum of the absolute values of the eigenvalues of its adjacency matrix.

**Theorem.** Let $p$ be an odd prime and $n=2^ap^b$ with $a,b\ge1$ and $(a+1)(b+1)\le16$. For every set $S$ of proper divisors of $n$ (the empty set included), $E(n,S)$ is at most the value in the table, and equality holds exactly for the listed sets. The family $2^3p$ is stated for $p\ge5$; its remaining prime $p=3$ is the row $n=24$. All other families hold for every odd prime.

<!-- BEGIN GENERATED TABLE -->

| Order | Primes | Maximal energy | Maximising divisor sets | Lean theorem |
|---|---|---|---|---|
| $2p$ | $p\ge3$ | $4p-2$ | $\{1,2,p\}$ | `energy_1_1` |
| $2p^{2}$ | $p\ge3$ | $6p^{2}-4p-2$ | $\{1,2,p\}$; $\{1,2,2p\}$; $\{2,p,2p,p^{2}\}$ | `energy_1_2` |
| $2p^{3}$ | $p\ge3$ | $8p^{3}-6p^{2}-4p+2$ | $\{1,p,2p,2p^{2}\}$; $\{1,2,2p,p^{3}\}$; $\{2,p,2p,p^{2}\}$ | `energy_1_3` |
| $2p^{4}$ | $p\ge3$ | $10p^{4}-8p^{3}-6p^{2}+4p+2$ | $\{1,p,2p,2p^{2},p^{4}\}$ | `energy_1_4` |
| $2p^{5}$ | $p\ge3$ | $12p^{5}-10p^{4}-8p^{3}+6p^{2}+4p-2$ | $\{1,2,p,2p^{3},p^{4},2p^{4},p^{5}\}$ | `energy_1_5` |
| $2p^{6}$ | $p\ge3$ | $14p^{6}-12p^{5}-10p^{4}+8p^{3}+6p^{2}-4p-2$ | $\{1,2,p,2p^{3},p^{4},2p^{4},p^{5}\}$; $\{1,2,2p,p^{3},p^{4},2p^{4},2p^{5}\}$; $\{2,p,2p,p^{2},2p^{4},p^{5},2p^{5},p^{6}\}$ | `energy_1_6` |
| $2p^{7}$ | $p\ge3$ | $16p^{7}-14p^{6}-12p^{5}+10p^{4}+8p^{3}-6p^{2}-4p+2$ | $\{1,p,2p,2p^{2},p^{4},p^{5},2p^{5},2p^{6}\}$; $\{1,2,2p,p^{3},p^{4},2p^{4},2p^{5},p^{7}\}$; $\{2,p,2p,p^{2},2p^{4},p^{5},2p^{5},p^{6}\}$ | `energy_1_7` |
| $2^{2}p$ | $p\ge3$ | $14p-16$ | $\{1,4,2p\}$ | `energy_2_1` |
| $2^{2}p^{2}$ | $p\ge3$ | $22p^{2}-32p+16$ | $\{1,2,4p,p^{2},2p^{2}\}$ | `energy_2_2` |
| $2^{2}p^{3}$ | $p\ge3$ | $30p^{3}-48p^{2}+32p-16$ | $\{1,4,2p,p^{2},4p^{2},2p^{3}\}$ | `energy_2_3` |
| $2^{2}p^{4}$ | $p\ge3$ | $38p^{4}-64p^{3}+48p^{2}-32p+16$ | $\{1,2,4p,p^{2},2p^{2},4p^{3},p^{4},2p^{4}\}$ | `energy_2_4` |
| $2^{3}p$ | $p\ge5$ | $34p-40$ | $\{1,2,8,4p\}$; $\{1,8,2p,4p\}$ | `energy_3_1` |
| $24$ | $p=3$ | $62$ | $\{1,2,3,8,12\}$; $\{1,3,6,8,12\}$; $\{1,2,12\}$; $\{1,2,8,12\}$; $\{1,4,6,8,12\}$; $\{1,6,8,12\}$ | `energy_3_1_at_3` |
| $2^{3}p^{2}$ | $p\ge3$ | $54p^{2}-80p+40$ | $\{1,2,4,8p,p^{2},2p^{2},4p^{2}\}$; $\{1,4,2p,8p,p^{2},4p^{2}\}$ | `energy_3_2` |
| $2^{3}p^{3}$ | $p\ge3$ | $74p^{3}-120p^{2}+80p-40$ | $\{1,2,8,4p,p^{2},2p^{2},8p^{2},4p^{3}\}$; $\{1,8,2p,4p,p^{2},8p^{2},2p^{3},4p^{3}\}$ | `energy_3_3` |
| $2^{4}p$ | $p\ge3$ | $86p-104$ | $\{1,2,16,4p,8p\}$; $\{1,4,16,2p,8p\}$ | `energy_4_1` |
| $2^{4}p^{2}$ | $p\ge3$ | $138p^{2}-208p+104$ | $\{1,2,8,4p,16p,p^{2},2p^{2},8p^{2}\}$; $\{1,4,8,2p,16p,p^{2},4p^{2},8p^{2}\}$ | `energy_4_2` |
| $2^{5}p$ | $p\ge3$ | $202p-248$ | $\{1,2,8,32,4p,16p\}$; $\{1,4,32,2p,8p,16p\}$ | `energy_5_1` |
| $2^{6}p$ | $p\ge3$ | $470p-584$ | $\{1,2,8,64,4p,16p,32p\}$; $\{1,4,16,64,2p,8p,32p\}$ | `energy_6_1` |
| $2^{7}p$ | $p\ge3$ | $1066p-1336$ | $\{1,2,8,32,128,4p,16p,64p\}$; $\{1,4,16,128,2p,8p,32p,64p\}$ | `energy_7_1` |

<!-- END GENERATED TABLE -->

The table is generated from `checks/expected/icg-families.json` by `python -m scripts.lean_icg_families`, which also writes the Lean theorems, so the two cannot drift apart.

**Theorem (every $a$, $b=1$).** Let $p\ge5$ be prime and $a\ge2$. Then
$$\max_S E(\mathrm{ICG}(2^ap,S))=c_a\,p-d_a,\qquad c_a=\frac{2^a(3a+4)+2(-1)^a}{3},\quad d_a=\frac{2^a(12a+10)+8(-1)^a}{9},$$
over all sets $S$ of proper divisors, and the maximum is attained. For $a\le7$ this agrees with the rows above, which also cover $p=3$ and list every maximiser. Lean: `Solved.ICG.TwoPow.energy_max`; the proof is in *Proof for every $a$* below.

## Method

1. **Spectral bridge.** H. Dong's Lean theorem `ICGGeneral.energy_icgAdj_pq` ([ai4math-results](https://github.com/Horace-Maxwell/ai4math-results/tree/6334a95f2e0c2396f492f3476c1d4ce80e4106ab/lean), Apache-2.0) identifies the energy of $\mathrm{ICG}(r^aq^b,S)$, for distinct primes $r,q$, with $\sum_{u,v}|M_{uv}|$. Here $M=T_a(r)\,Y\,T_b(q)^{\mathsf T}$, the matrix $Y$ is the indicator of $S$ on the exponent box $[0,a]\times[0,b]$, and $T$ holds local Ramanujan sums. The bridge assumes only that the primes are distinct, so it applies with $r=2$.
2. **Polynomials in $p$.** With $r=2$ every entry of $M$ is an integer polynomial in $p$ and linear in $Y$. Substituting $p=p_0+x$ turns "for all $p\ge p_0$" into "for all $x\ge0$". A polynomial with nonnegative coefficients and a positive constant term is then positive.
3. **Branch and bound.** The divisor sets are searched one cell at a time. At each node, every completion's coefficients lie between the current values plus the sums of the negative parts and of the positive parts of the undecided cells. This bounds the energy of the whole subtree by a polynomial $\beta$, and the subtree is closed once $E(p)-\beta$ is certified positive. At the leaves a set either has smaller energy or is one of the claimed maximisers, whose energy is computed exactly from certified signs.
4. **Kernel efficiency.** Kernel reduction costs about 100 µs per list element but a few µs per arithmetic operation on natural-number literals, which the kernel evaluates with GMP. The search therefore stores each coefficient table in one natural number with offset-encoded fields of $w$ bits. A node test is about twenty such operations: the fieldwise positive part takes two bitwise ands, a shift and a multiplication, and the block sums one multiplication. One global size condition, checked by the kernel, keeps every field inside its bits. All nineteen families and $n=24$ check in about one minute.
5. **One prime.** The order $24$ uses the same search with constant tables.

## Proof for every $a$ ($b=1$)

Write $z_k,w_k\in\{0,1\}$ for the indicators of $2^k\in S$ and $2^kp\in S$ ($w_a=0$, since $2^ap=n$). Dong's path identity for $T_a(2)$ (`ICGGeneral.L1mat_path`) and $\|T_1(p)(\alpha,\beta)\|_1=F(\alpha,\beta):=(p-1)|\beta-\alpha|+|(p-1)\alpha+\beta|$ give
$$E(\mathrm{ICG}(2^ap,S))=2^a\Bigl(F(\sigma_0,\tau_0)+\sum_{k<a}F(\sigma_k-\sigma_{k+1},\tau_k-\tau_{k+1})\Bigr),$$
with $\sigma_a=z_a$, $\tau_a=0$, $\sigma_k=(\sigma_{k+1}+z_k)/2$ and $\tau_k=(\tau_{k+1}+w_k)/2$. The energy is thus a sum along a chain whose state $(\sigma,\tau)\in[0,1]^2$ moves by averaging with the next bits. Put $A=\tfrac43(p-1)$, $B=\tfrac23(p-2)$, $g=2p-\tfrac83$, $C=2p-\tfrac89$, $r=-\tfrac12$, and
$$\Phi(s,t)=\max\bigl(Bt-As,\;As-Bt-(A-B)\bigr),\qquad W_n(s,t)=\tfrac12\bigl(ng+C+\tfrac89r^n+(1-r^{n-1})\Phi(s,t)\bigr).$$

1. **Step.** For $s,t\in[0,1]$, bits $z,w$ and $n\ge1$: $F(\tfrac{z-s}2,\tfrac{w-t}2)+W_n(\tfrac{s+z}2,\tfrac{t+w}2)\le W_{n+1}(s,t)$. Both sides are affine in $\mu=r^{n-1}\in[-\tfrac12,1]$, so the two endpoints suffice; each endpoint is a piecewise linear inequality in $s,t$ with coefficients affine in $p$ (`step_one`, `step_half`, `step`).
2. **Base.** Every chain of length two is at most $W_2$: sixteen bit patterns, each a piecewise linear inequality (`base_two`).
3. **Induction.** Every chain of length $n\ge2$ below a top state is at most $W_n$ of that state (`chain_le`). At the top state $(z_a,0)$, $2^aW_a$ is largest for $z_a=1$, where it equals $c_ap-d_a$ (`Wb_top`).
4. **Attainment.** Choosing $(z,w)=(1,0)$ where $\Phi$ takes its first branch and $(0,1)$ otherwise makes each step an equality, and $(z_0,w_0)=(1,0)$ makes the base an equality (`step_ge`, `base_ge_L`, `base_ge_R`, `chain_attain`). The bits define a set $S\ni 2^a$ of proper divisors whose energy is $c_ap-d_a$ (`setOf`, `Ys_setOf`, `energy_max`).

$W_n$ is the exact value function of this chain for $n\ge2$; it was found by value iteration and checked in exact arithmetic before the Lean proof. The same kind of argument, a per-step potential along Dong's path, is how Dong proves the $q=3$ case [D26, Theorem 5]; here the potential is two-dimensional and depends on the remaining length.

## Trusted base

The proofs use the Lean kernel, Mathlib and Dong's bridge. Every registered theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`; [`formal/FormalTests/Axioms.lean`](../../formal/FormalTests/Axioms.lean) fails the build otherwise. No `native_decide` is used. The certificate generator `solved/lean_icg.py` is not trusted: it chooses the cell order, the field width and the coefficient count, and any wrong choice makes the kernel reject the certificate. Regression tests check rejection of wrong energies, wrong maximisers, bad cell orders, wrong mask lengths, a too-small $p_0$, a field width one bit too narrow and too few coefficients.

## Prior work

Literature checked 27 November 2026:

- **Prime powers $p^s$.** Sander and Sander determine every maximiser for every prime [SS11, Thm 1.1].
- **Two distinct odd primes.** [SS11, §1] attributes the identity $E_{\max}(pq)=E_{\max}(p)E_{\max}(q)$ for distinct odd primes to earlier work and notes that it is a direct comparison of four divisor sets. It does not apply to $2p$: here $E_{\max}(2p)=4p-2$, whereas $E_{\max}(2)E_{\max}(p)=4p-4$. In any case $n=2p$ has only eight divisor sets, so that row is a hand computation.
- **Two distinct odd primes in general.** Jiang and Yang [JY26a, JY26b] and Dong [D26] together settle $p^aq^b$ for distinct odd primes; Dong's theorems are Lean-formalized, and his spectral bridge is reused here.

We found no earlier determination of the maximisers for the other even families, or of $E_{\max}(2^ap)$ for general $a$, in the papers above, Dong's repository (to release v1.26.0, 23 November 2026), the Omega Institute's issue tracker or by web search (28 November 2026). Le and Sander (Linear Algebra Appl. 437 (2012)) bound extremal energies of arbitrary order through multiplicative divisor sets; we could not obtain the paper and know it from the citing papers. The maximisers here are not multiplicative (for $2^4p$ the set $\{1,2,16,4p,8p\}$ is not a product of a set of powers of 2 and a set of powers of $p$; a test checks this for every maximiser), so such sets do not attain the maximum. This search may be incomplete. The claimed energies and maximisers come from the exact Python certificates of [the companion entry](../icg-energy-exceptional-orders/PROOF.md); the Lean proofs check those claims without trusting the Python code.

## Observations, not claims

For $n=2^ap$ with $a\le7$ the maximisers alternate between two patterns. Which sets are maximisers for general $a$, and the closed form for $p=3$, are not proved here.

## Reproduction

```sh
python -m scripts.lean_icg_families --check   # generated Lean files, registry and this table are current
python -m unittest tests.test_lean_icg        # generator tests and the closed form against the definitional energy
cd formal && lake exe cache get && lake build # kernel-checks every certificate, theorem and audit
```

## References

- [SS11] J. W. Sander, T. Sander, The exact maximal energy of integral circulant graphs with prime power order, <https://arxiv.org/abs/1109.3616>.
- [JY26a] J. Jiang, C. Yang, Ramanujan transforms and maximum energy of odd-total-exponent integral circulants, arXiv:2608.29523 (v2, 30 October 2026), <https://arxiv.org/abs/2608.29523>.
- [JY26b] J. Jiang, C. Yang, Maximum energy of integral circulant graphs with same-parity exponents, arXiv:2610.36883, <https://arxiv.org/abs/2610.36883>.
- [D26] H. Dong, The maximal energy of integral circulant graphs of order $p^aq^b$ when one prime is 3 or one exponent is at most 2, version 3, 9 November 2026, <https://github.com/Horace-Maxwell/ai4math-results/blob/8e81669b092b3620034c95d8690dbeb99da07ef1/papers/icg-q3-general/note.tex>; Lean sources at <https://github.com/Horace-Maxwell/ai4math-results/tree/6334a95f2e0c2396f492f3476c1d4ce80e4106ab/lean>.
