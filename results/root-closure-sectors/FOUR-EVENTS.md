# Four nonsquares: a complete candidate-menu argument

**Status: proof draft.** The all-length coverage argument and the support-set
search proof await independent review and are not fully formalized. The
exchange identity in Section 4 and its three-versus-four instruction count
are checked in Lean. Finite tests are additional evidence, not the proof of
the unrestricted sector statement.

## 1. Statement, model and menu

Let an increasing AM chain from 1 have exactly two small steps, four
canonical nonsquares, r writes, and square endpoint N=R². All earlier
values remain available. Only addition and multiplication costed one write
each are permitted.

**Claim.** A chain for R using at most r−1 writes exists inside the menu below.
The bound is independent of the initial tower height and all square-run
lengths.

Let A be the tower head before the first small value B. Define M to contain:

* All source values and the integer square roots of square source values.
* The canonical tower 1,2,4,16,… through R.
* 3, 6 and R, and R/2 when integral.
* 2√A when integral.
* A+u when B=Au, and A√u when √u is integral.

Discard values greater than R. Every noninitial menu value must be
constructed by actual AM instructions; it is not a free seed. The menu
has size linear in the source length. No polynomial bound on the number
of possible computation supports is claimed.

Remove a trailing canonical square, or stop early if R is already present.
Otherwise the noninitial event order is either SG or GS, with S the second
small step and G the additional big nonsquare. Write the history as

    T, B, g squares, H=B^(2^g), C, h squares, K=C^(2^h), D=N.

For SG, C is small and D big; for GS, C is big and D small. The first
small value is A+u or Au with a tower operand. The first-small bounds and
positive-gap event description are established in the
[three-event argument](PROOF.md) and the
[two-small-step classification](../two-small-steps/PROOF.md).

Any doubling after 2 has been made can be written as multiplication by the
retained 2. This preserves the available values, cost, and canonical event
classification. We use that normalization throughout; remaining additions
have distinct operands. There is no assumption that a prefix is individually
shortest.

The source literature concerns complete chains, not just cheap endpoints:
[Tarek, Bahig and Anwar, Section 5](https://doi.org/10.3934/Math.2026667).
Shared computation graphs also motivate the support-set accounting below.
The 2026 MCM study uses free shifts and a different arithmetic model, so
neither its hardware costs nor its experimentally assumed word-width bound
is transferred here.
[Cantaloube et al.](https://doi.org/10.4230/LIPIcs.CP.2026.11).

## 2. Reconstruction tools

The following operations preserve the necessary operands explicitly.

**Low-event prefix.** A square chain with at most three canonical nonsquares
and at most two small steps has a one-write-shorter root construction from
its values, their roots, the canonical tower, and the helpers 3,6,2√A.
The three-event proof already covers two small steps. With one small step,
the same positive-gap product argument applies. At zero gap the additional
products with A have available factor roots; products with B itself give a
retained root. A big final addition is possible only at A=2 or A=4 and
gives a retained tower root. With at most two events, delete a trailing
square or halve the first tower product. These observations do not replace
a shared prefix by an arbitrary shortest program.

**Halve a final run.** If h>0 and D=Kw is square, w must be square.
When √w is available before the last square producing K, delete that square
and append √K·√w. The only possibly missing roots are √B and √C:
roots of tower and inner-run values are already present.
If w=C, reconstruct √C using the low-event prefix, perform h squares,
and multiply by the retained √C. This saves a write.

**Insert √B while retaining B.** If B is square, it is a tower product
B=Au with both A and u square and u≥4. Replace the initial terminal A
write and the B write by

    √B=√A·√u,    B=(√B)².

The cost is unchanged. This retains every old value except A and adds √B.
It may be used only if the remaining recipe does not read the missing A.

**Root a product prefix.** Alternatively, stop the initial tower at √A,
construct √B, and take roots of each subsequent multiplicative write.
This saves one write when every required operand root is available.
The positivity of all factors preserves strict increase.

**Two product writes after a positive run.** Suppose g>0 and C=Hv,
D=Cw. A square D has v,w both square, both equal to the same nonsquare,
or the two nonsquares are 2 and B.

Indeed, the only nonsquare values preceding H are 2 and possibly B;
all tower values from 4 onward and all positive B-run values are squares.
For two square factors, remove the last square producing H and execute
the two rooted products. If √B is missing, root the first product prefix
instead. Equal nonsquare factors give R=√H·v and save two writes.
For the mixed pair, squarehood requires 2B to be square. The first-small
forms imply B=2A or B=18. Build √(2B) as 2√A or 6, insert that one
extra write using already available tower operands, and multiply by √H.
Deleting the H square leaves a net saving of at least one. An inserted
smaller value is scheduled before its later users; positive AM dependencies
allow increasing numerical order without losing shared values.

**Two products at zero gap.** If neither later instruction uses B, omit it
and use the low-event prefix construction. Otherwise the endpoint has the
form Bxy with tower x,y, or B²x with tower x. This includes the case where
C avoids B but D reads it; B must not be deleted in that case.

For B²x, squarehood forces x square and the root is B√x. If B is a
power of two, write B=Au. The Bxy case is a product of four tower
factors. All are square, or exactly two of u,x,y equal 2. In the first
case halve the tower and the three products. In the second combine the
two factors 2 into the root factor 2; the intermediate R/2 is included
in M and is a product of available tower roots. If B is a proper first
sum, its odd part must be square, forcing A=16,B=18. Square products
then give 144 or 576; the event-level requirements exclude 144, and
√576=24 has the chain 1,2,4,6,24. All these constructions lie in M
and save at least one write.

## 3. Coverage of the two event orders

### A. Positive final gap

For either order, h>0 excludes a squared additive endpoint: a proper
addition after a square lies between consecutive squares, and a doubled
square is not square. Apply the final-run tool unless w=B and √B is
missing. Then B=Au is a square tower product and A≥16.

For GS, the big event C must be a product of square values. A sum
cannot cross the boundary because B≤A√A, and a factor 2 is too small
to make a big product in this case. Root the multiplicative prefix,
retain √B, perform the h rooted squares and multiply by √B.

For SG, insert √B at unchanged cost when C does not read A. If C is
a product reading A, both operands are square, so root the product prefix.
The remaining possibility is C=H+A. Big growth at D requires

    B C^(2^h) ≥ (A^(2^(g+1)))^(2^h).

If g≥1, B≤A√A and A≥16 give
B(B^(2^g)+A)² < A^(2^(g+2)), excluding that inequality even at h=1.
For example, put A=s² with s≥4: the left side is less than
4s^(3+6·2^g), while the right side is s^(8·2^g).
The exponent difference is at least one.

Thus g=0. The h=1 condition becomes u(u+1)²≥A.
If u is below √A in the tower then u≤A^(1/4), and
u(u+1)²<u⁴≤A for u≥4, a contradiction. Therefore u=√A.
For h≥2 the condition would imply (u+1)⁴≥u⁵, false for u≥4.
The only remaining pattern is g=0,h=1,A=u². Section 4 supplies
its three-write root construction using the extra menu values A+u,A√u.

### B. Zero final gap, order GS

If D avoids C, delete C and use the low-event construction. For products
using C, the preceding tools cover all cases:

* When g>0, the big event C is a product Hv, and D=Cw is covered by
  the positive-run two-product tool.
* When g=0 and C is a product, either C avoids B or is B times a tower
  value. The zero-gap two-product tool applies.
* The only remaining additive big value is C=5 after 1,2,3. Its products
  with 1,2,3 are not squares. The values 4 and 6 have product recipes
  and are already covered.

For proper sums using C, the complete first-big-event alternatives are:

| Prefix | Possible C |
|---|---|
| g=0 | AB or A², with the additional value 5 when A=2,B=3 |
| g>0, A=2,B=3 | 3^(3·2^(g−1)), and 18 when g=1 |
| g>0, A≥4 | B=A√A and C=B^(3·2^(g−1)); also C=A⁴ when g=1 |

This table follows by comparing the largest and second-largest available
cofactors with the next level boundary. A positive-gap event reads its
head. A lag of at least two gives B^(5·2^(g−2)), below the boundary:
use 3⁵<4⁴ for B=3, and B≤A^(3/2) for the other case. At zero
gap the only nonreset large cofactor is A. This also recovers the
corresponding one-small-step chain cases in the cited classification.

For C=AB with B=A+u proper, a tower addend w gives
D=A²+Au+w. If u≥2, the only possible square is (A+u/2)²:
the entire w range lies strictly between its two neighboring squares.
Thus w=u²/4. The tower restriction allows u=2,w=1 or u=4,w=4,
giving roots A+1 and A+2. If u=1, a tower addend gives no square.
The addend B gives a retained root only when u=1; for even u it lies
strictly between (A+u/2)² and (A+u/2+1)².
For power-of-two B, the two-power square test leaves only 36.
Doublings were normalized as products and are already covered.

For positive g, C=3^(3·2^(g−1)) gives a squared proper sum only
at g=1, with C+9=36. At g≥2, tower addends 1 and 2 are excluded by
the square gap and modulo four. A B-run addend of exponent at least two
factors off a square and leaves one more than a square; the addend 3
has odd 3-adic valuation. The exceptional C=18 has no squared proper
sum outside the already retained cases. In the power-of-two row,
the two-power test leaves C+H=576 at A=4,B=8,g=1. The reset values
A² and A⁴ give no new squared proper sums. The roots 6 and 24 are
built from the listed small helpers. All roots described in this paragraph
are in M with the required write budget.

### C. Zero final gap, order SG

If D avoids C, delete C and apply the low-event tool. A product using C
is covered by the two-product tools unless C is a proper sum.

At g=0 write C=B+t. If the final cofactor is a square tower value,
C must be square; the three-event sum classification gives roots 3 or 6,
each obtainable in one write from the tower, before multiplying by the
available cofactor root. Cofactor 2 gives a squared doubling, which can
only reach the level boundary. Cofactor B cannot give a square:
for power-of-two B the exponent-difference condition makes the 2-adic
valuation odd. For a proper first sum, coprimality of its odd part with
a power of two forces B=18; the tower addends 1,2,4,16 then give no
square B(B+t). A doubled C was already converted to a product.

At g>0 write C=H+t with t≤√H. A square cofactor cannot help because
C is not square. Cofactor 2 is either too small for G or is excluded
by the finite A=2,g=1 cases. The only remaining cofactor is nonsquare B.
If t is a positive B-run square, its B-adic exponent is odd after the
extra multiplication by B, and the remaining factor is coprime to B;
squarehood is impossible unless B itself is square, already excluded.
If t is a tower value, the odd part of B must be square. This either
forces B=18, whose growth is too small for G, or B is a power of two,
where the two-power square test excludes the result. For t=B, g≥2
is too small for G: B(H+B)<A^(2^(g+1)), using B≤A√A for A≥4
and 3⁵+3²=252<256 for A=2, followed by squaring growth.
At g=1, squarehood requires B+1 square, giving B=3 or 8 and roots
6 or 24. Their short chains use the small menu values.

Finally consider a proper addition D=C+w. If w<H, then w≤√U for
U=A^(2^(g+1)), while C<U≤D. The only possible square is D=U.
The full canonical tower in M supplies its root. For w=H, a proper
additive C is too small for G, apart from the directly checked A=2
and A=4 initial cases, which give no nonboundary square. A product
C=Hv at g>0 gives D=H(v+1), so v+1 must be square. The only
possible cofactor is v=B with B=3 or 8. The event inequalities leave
only B=3,g=2, yielding 324 with root 18. At g=0, a proper-sum B is
too small to cross the boundary in B(v+1) for A≥16; A=4 gives no
nonboundary square. For power-of-two B, v+1 would have to be square,
but v is a tower value and cannot equal 8. If C avoids B, the sum C+B
is also below the boundary. This completes SG.

Every branch has retained its required intermediate values and uses only M.
No step treats a shortest endpoint construction as an interchangeable
replacement for its entire shared history.

## 4. An infinite missing-helper family

Let v=2^(2^j), j≥0, u=v² and A=u². From the tower through A,
four writes construct

    B=Au,  C=B+A,  K=C²,  N=KB.

The root is R=v⁷(v²+1). Three writes instead suffice:

    X=A+u,  Y=Av,  R=XY.

The identity R²=N and the four-versus-three suffix costs are checked by
SolvedRootBlocks.exchange_program and exchange_cost. All values increase
for v≥2. The source uses j+7 writes and has level j+5, so it lies
in the SG four-event sector. The root construction uses j+6 writes and
has level j+4.

There is a strict menu gap for every j. Restrict the root construction
to original values and integer roots of original square values, keeping
only values at most R. That bare menu is the tower through A together
with v³, B, C and R. The value C is not square because v²+1 lies
between consecutive squares.

Every value in the bare menu before R except C is a power of two, while
R is not. Also R>2C. The final operation is therefore forced to be
C·v³. Constructing C is forced to use B+A: products of the earlier
powers of two cannot give C, and two values at most A cannot reach C.
The value v³ requires u, since two earlier tower values below u are
at most v and have sum and product at most u. Consequently every
bare-menu chain contains u and the five larger values v³,A,B,C,R.
Reaching u requires at least j+2 writes by the growth bound, so the
bare-menu optimum is at least j+7. The sequence consisting of the
tower through u, then v³,A,B,C,R attains that cost.

The new helpers X,Y thus save at least one write over every bare-menu
program throughout this infinite family. This is a restricted-menu lower
bound, not an unrestricted global optimality claim. At j=0 it replaces
the seven-write bare-menu construction of 640 by

    1,2,4,16,20,32,640.

## 5. Exact shared-support synthesis and verification

For each permitted value, the implementation stores inclusion-minimal sets
of noninitial values sufficient to construct it. A recipe v=x+y or xy
combines supports S_x and S_y as S_x∪S_y∪{v}. All operands are smaller
than the output, so processing values in increasing order is complete.
Only 1 has empty support.

If S₁⊆S₂ both produce the same value, S₂ can be discarded: for every
future context K, S₁∪K⊆S₂∪K. Keeping only a cheapest support would
be unsound, because equal-cost supports may share different future helpers.
No recipe conflict arises on shared values: either recipe computes the
same integer, with smaller operands, so the union remains schedulable.
The least-cardinality retained target support gives a minimum-write
program within the menu. This argument allows exponential antichains;
it claims no polynomial-time bound.

[Implementation](../../solved/menu_programs.py) ·
[Independent subset-enumeration tests](../../tests/test_menu_programs.py).
Optional state and pair limits raise ResourceLimit, which never means
infeasibility. An exhausted search returning no chain means only that the
declared finite menu and write budget have no solution.

The complete level-12 root-sector check now includes 162,271 four-event
square chains. The four-event nontrivial menu branch succeeds in 23,207
cases; other cases have trailing or retained roots. The exchange family
is independently tested for j=0,…,8, including the exact bare-menu optimum.
These finite checks exercise the implementation. They do not establish
the unrestricted coverage argument above.

The same implementation now supports an explicit `required` output set.
Ancestor supports are joined across those outputs, with every shared value
counted once. The [joint-support proof and obstruction](../root-retention-obstruction/PROOF.md)
state its exact scope. The menu-completeness theorem in this manuscript
concerns the endpoint root; it does not assert that the same menu is
complete for arbitrary additional required values.
