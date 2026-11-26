# An all-length block classification of two-small-step chains

**Status: research proof draft; independent mathematical review pending.** Automated evidence is scoped below and does not certify the complete argument.

Tarek, Bahig and Anwar give nineteen forms for increasing AM-chains with one small step. Their first question in §7 asks for the extension of Theorem 1.1 to two small steps. We give a constructive classification by blocks. Exactly eleven event words occur over all chain lengths. Each choice has explicit, prefix-dependent parameter ranges. The interval comparisons used in the construction can be evaluated with integer arithmetic even at equality. [Authors’ paper, Theorem 1.1, Corollary 3.1 and §7](https://doi.org/10.3934/Math.2026667)

## Statement

A chain starts at 1 and strictly increases. Each new term is a sum or product of two earlier terms, possibly equal. Put $D_L=2^{2^{L-1}}$ for $L\ge1$. The level of $m\ge2$ is the unique $L$ with $D_L\le m<D_{L+1}$. Give 1 level zero. A step is small if it stays at its previous level. A square in the description means the new term equals the square of the previous largest term, irrespective of its generating recipe.

**Theorem.** The chains with exactly two small steps are precisely the following increasing value sequences.

1. Start with 1, 2 and zero or more successive squares, ending at $A=D_L$. Append the first small term $B$. Choose it among $A+u<A^2$, with $u$ any tower entry including 1 or $A$, and $Au$, with $2\le u<A$ a tower entry.
2. Choose $r\in\{0,1,2\}$ and $0\le s\le4-r$, omitting $(r,s)=(0,4)$. Use the event word $G^r S G^s$. $G$ denotes a nonsquare that increases the level, and $S$ the second small step. For each letter, append the square run and the single event prescribed below.
3. Append any number of squares, including zero, and stop.

The letters pick parameter ranges; they impose no test on a completed chain. A branch with an empty operand range contributes no sequences. Each of the eleven remaining pairs occurs. Several recipes within a family can give the same sequence. The square gaps and event signs of a given sequence are unique.

### Event with no preceding square

Let $P$ be the ordered prefix, $m$ its largest entry and $U=D_{L+1}$ the next boundary above $m$. Set $(l,h)=(m+1,U-1)$ for $S$, and $(l,h)=(U,m^2-1)$ for $G$. Choose operands **already in $P$** from the following intervals, with $u$ the larger one.

| Event | Larger operand | Smaller operand $w$ | Append |
|---|---|---|---|
| Sum | $u\ge\lceil l/2\rceil$ | $\max(1,l-u)\le w\le\min(u,h-u)$ | $u+w$ |
| Product | $u\ge\lceil\sqrt l\rceil$ | $\max(2,\lceil l/u\rceil)\le w\le\min(u,\lfloor h/u\rfloor)$ | $uw$ |

There are at most three candidate larger operands for each operation. For $G$, its larger operand must be at least $\sqrt U=D_L$ and the current level contains at most three terms. For $S$, only one small step has occurred. For $m\ge4$ either lower bound on $u$ is greater than $\sqrt m$, so $u$ lies in the top two levels, which together contain at most three entries. For $m=3$ the prefix is $1,2,3$. The full interval for the second operand matters. For example $1,2,4,5,6,16$ reaches its last term using neither 5 nor 6.

### Event after a positive run of squares

For $z\ge2$ define the integer
$$
c(z)=\max\bigl(\{g\ge1:(U/m)^{2^g}\le z\}\cup\{0\}\bigr).
$$
Equivalently it is the positive part of $\lfloor\log_2(\log z/\log(U/m))\rfloor$. The ratio $U/m>1$ makes this an initial interval. Use repeated squaring of the reduced rational $U/m$ for exact comparisons.

Choose $g\ge1$, put $H=m^{2^g}$, and append the $g$ squares from $m$ through $H$. Pick one of the following events. For rows with a cutoff, the complementary integer range gives $S$.

| Appended value | Operand range | Parameter range for $G$ |
|---|---|---|
| $H+w$ | $w$ any earlier entry strictly below $H$ | Empty. Every such sum is $S$. |
| $2H$ | Use $H$ twice | $1\le g\le c(2)$ |
| $Hw$ | $w\in P,\ 2\le w\le m$ | $1\le g\le c(w)$ |
| $H\,m^{2^{g-d}}$ | $1\le d<g$ | $1\le d\le c(m)$ |

The last row is indexed by the distance $d$ between the head and the selected inner square. Once $d$ is chosen, **every** $g\ge d+1$ gives the same sign. Thus retaining an arbitrarily old value need not introduce a distinct case for every total run length.

## Proof of the theorem

For a head $m\ge2$, every new value is at most $m^2$, and squaring sends level $L$ exactly to $L+1$. Before the first small step induction gives the unique tower. From its head $A$ the only way to increase level is to attain $A^2$. If an operation avoids $A$, each operand is at most $\sqrt A$ when $A\ge4$, hence its sum or product is at most $A$. For $A=2$, the sole smaller operand is 1. This proves the first list and shows that the first small step is a canonical nonsquare.

Every small step is a nonsquare. Count $1\to2$ as a big nonsquare. For one small step, Corollary 3.1 of the paper bounds the integer number of nonsquares by four. For two it bounds it by seven, with either possible start $1,2,3$ or $1,2,4$. Apply the first bound to the prefix ending just before the second small step, the second to the whole chain. Removing the initial nonsquare and first small step leaves at most two further big nonsquares before $S$. Removing both small steps and the initial nonsquare leaves at most four further big nonsquares in all. All intervening steps are thus runs of squares. This gives the stated word.

With gap zero the largest legal nonsquare is at most $m^2-1$. Inverting the two monotone operand expressions on $[l,h]$ gives the displayed intervals, including both ends. For gap $g\ge1$, put $x=m^{2^{g-1}}$ and $y=U^{2^{g-1}}$. After the run the boundary above $H=x^2$ is $V=y^2$. Two operands smaller than $H$ are at most $x$, hence their sum and product are at most $H$. Every event must use $H$. Since $y\ge x+1$, we have $V-H\ge2x+1$. Adding any proper earlier operand stays strictly below $V$.

For a fixed multiplier $w$, crossing the boundary is equivalent to $w\ge(U/m)^{2^g}$. This covers doubling by addition as well. For the inner-run multiplier, take the common positive $2^{g-d}$-th root on both sides of the crossing inequality. The result is $m^{2^d}m\ge U^{2^d}$, equivalent to $d\le c(m)$. Equality crosses the boundary. A head multiplied by itself extends the square run. These cases exhaust all increasing nonsquares and establish necessity. Conversely every allowed choice is an available sum or product, greater than the head, with the indicated sign. The two prescribed small steps are the only ones. This proves sufficiency at every length.

### Why exactly eleven event words occur

The counting bound initially permits a twelfth word, SGGGG. This word uses seven nonsquares in total. Apply the earlier all-length classification of the seven-nonsquare sector. When every nonsquare after the first three entries is a product of the largest two entries, replace each nonempty square gap by one square. Each extra square in such a gap raises both inputs of the next product, and every later value, to their squares. Thus the level change at every later event is preserved. Trailing squares also preserve the event word. The possible compressed gap supports and their signs are as follows. Positions start at 1 after the listed prefix. [Seven-nonsquare proof and admissible supports](../seven-nonsquares/PROOF.md)

| Prefix | Supports giving GSGGG | Supports giving GGSGG |
|---|---|---|
| 1,2,3 | {1}, {2}, {2,4} | ∅, {3}, {4}, {5} |
| 1,2,4 | {3}, {1,3} | ∅, {1}, {4}, {5}, {1,4}, {1,5} |

For example, the empty support after 1,2,3 gives 6,18,108,1944,209952. Its two small steps are at 3 and 108. The only other surviving seven-nonsquare histories have one nonmaximal event. Before trailing squares their sequences are 1,2,3,5,15,75,1125,84375 and 1,2,3,6,18,108,648,69984. Their words are GSGGG and GGSGG respectively. This excludes SGGGG at every size. Every other pair occurs already at endpoints up to 84,375, as verified by the complete sequence comparison below. For an explicit witness of each word take the two exceptional histories, their prefixes after the second small step, and the following additional histories and their prefixes: 1,2,4,5,6,16 and 1,2,3,9,10,81,810,65610.

## Explicit specialization with exactly three nonsquares

Here $r=s=0$. Between $B$ and the second small step there are $g\ge0$ squares. Write $T$ for the initial tower including $A$.

- For $g=0$ and $A=2$ there is no choice. For $g=0,\ A\ge4$, choose any member of the first-small list for $A$ larger than $B$, any $B+w$ with $w\in T\cup\{B\}$, or any $Bw$ with $w\in T,\ 2\le w\le\sqrt A$. Exclude the sum $8+8$ when $A=4,B=8$, and the product $B\sqrt A$ when $B=A\sqrt A$.
- For $g\ge1$ put $H=B^{2^g}$. Every sum $H+w$ with an available $w\le H$ works, except doubling at $A=2,g=1$. Every product $Hw$ with tower entry $2\le w\le A$ works, except $A=2,g=1,w=2$ and $A\ge4,g=1,B=A\sqrt A,w=A$.
- For the other products take $w=B^{2^{g-d}}$ with $1\le d\le g$. Every $d\ge2$ works. For $d=1$, if $B=A+u$, take all choices at $A\ge16$, and $B=5,6$ at $A=4$. If $A=2^{2^a}$ and $B=A\,2^{2^b}$, take exactly $b\le a-2$. The case $A=2,B=3,d=1$ has no choice. Append any trailing squares.

Indeed, at $A\ge4$ we have $A<B\le A\sqrt A$. Among immediate sums, $2B\le2A\sqrt A\le A^2$, with equality only when $A=4,B=8$. A product using $B$ and $A$ or $B$ already exceeds the boundary. The next largest tower multiplier is $\sqrt A$, with the stated equality exception. For a positive gap and a tower multiplier the hardest test is $g=1,w=A$, where $B^2A\le A^4$. At $A=2$ compare $3^2\cdot2$ with $4^2$, then $3^4\cdot2$ with $4^4$. For a multiplier on the $B$ run the strict test is $B^{2^d+1}<A^{2^{d+1}}$. At $d=2$ this follows from $B^5\le A^{15/2}<A^8$ for $A\ge4$, and $3^5<2^8$ for $A=2$. The cutoff makes every larger $d$ admissible. At $d=1$ reduce $B^3<A^4$ using $B\le2A$ for sums and $3\cdot2^b<2^a$ for products. This yields the list.

## Verification

The bounded generator can stream distinct sequences and one instruction witness per sequence. An independent all-pairs enumerator supplies the finite oracle. The comparison checks entire sequences, replays every witness, and compares endpoint minima against the paper's zero/one-small families. The bounds in the theorem itself are independent of the verification caps. [Generator](../../solved/two_small_forms.py) · [Reproducible comparison](../../checks/verify_two_small.py) · [Counts and digests](../../checks/expected/two-small-classification.json)

This gives a parameterized classification of witnesses. Distinct words and parameter values may end at the same integer; a disjoint list of shortest endpoint expressions would be a further result. The proof is a research manuscript awaiting independent review.
