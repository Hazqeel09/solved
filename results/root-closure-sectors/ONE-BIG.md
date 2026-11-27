# One big event on either side of the second small step

**Status: proof draft.** This gives an all-length root construction for the
GSG event order. Independent review remains pending. The first-big-prefix
classification is inherited from the cited 2026 paper; three supporting
growth inequalities are formalized, but the full case coverage is not.
The overall defect-two root-closure question remains open.

## 1. Statement and prefix notation

Use the increasing AM model and canonical-event convention of
[the main manuscript](PROOF.md). S is the second small step; G is a big
canonical nonsquare after the first small step. Let a source have r writes,
exactly two small steps, event word GSG, and square endpoint N.

**Claim.** A legal AM program for √N uses at most r−1 writes.
For histories containing a non-power-of-two value, the candidate menu M of
[FOUR-EVENTS.md](FOUR-EVENTS.md) suffices. Power-only histories use the
separate [exponent-chain construction](POWER-HISTORIES.md); no completeness
claim about M is needed for that branch.

Remove a trailing canonical square or stop at a retained root. Otherwise
write the source as

    T, B, e squares, C, g squares, H, D, h squares, K, N,

where T ends at A=2^(2^k), B is the first small value, C is the first G,
D is the second small value, and N the final G. Put P equal to the prefix
through C, Q equal to its previous largest value, and U equal to the next
level boundary after C. Thus H=C^(2^g), K=D^(2^h), and

    H<D<U^(2^g).

Doublings can be written as multiplication by the retained 2. In the rest
of the argument a proper addition has distinct operands.

The complete first-G alternatives are:

| First-small prefix | First G, C | Q | U |
|---|---|---|---|
| e=0, A≥4 | AB or A² | B | A⁴ |
| A=2, B=3, e=0 | 4,5,6 | 3 | 16 |
| A=2, B=3, e=1 | 18 | 9 | 256 |
| A=2, B=3, e≥1 | 3^(3·2^(e−1)) | 3^(2^e) | 2^(2^(e+2)) |
| A≥4, B=A√A, e≥1 | B^(3·2^(e−1)) | B^(2^e) | A^(2^(e+2)) |
| A≥4, B=A√A, e=1 | A⁴ | A³ | A⁸ |

The first small value at A≥4 satisfies B≤A√A. If it is not a power of
two, B=A+u for a proper tower value u≤√A, so B≤A+√A and B is not
square. These facts and the table follow from Tarek, Bahig and Anwar's
one-small-step chain classification, Section 5; see also the derivation in
[FOUR-EVENTS.md, Section 3B](FOUR-EVENTS.md).
[Primary source](https://doi.org/10.3934/Math.2026667).

There is a useful deletion case. If the final instruction avoids D and h=0,
delete D. If N=H² its root is retained. Otherwise the resulting one-small-step
history has two big nonsquares. Its classified endpoint is 18 or A⁴, with
no intervening gaps. Only A⁴ is square, and the canonical tower constructs
its root A² within budget. Thus we may assume the final instruction reads D
when h=0.

## 2. Growth bounds that hold for the whole prefix families

Every row of the table satisfies

    C²(C+1)<U²,       Q²+C<U,       2C+Q<U.                 (1)

Every row except the three fixed heads C=4,5,6 also satisfies

    (C+Q)³<U².                                             (2)

Here is an all-parameter verification. For the A≥4 rows choose an integer
s≥2 with C≤s⁵, Q≤s³ and U=s⁸. At e=0 take s=√A; at e≥1 take
s=A^(2^(e−1)), including the reset row. Then

    C²(C+1)≤s¹⁵+s¹⁰<s¹⁶,
    Q²+C≤s⁶+s⁵<s⁸,    2C+Q≤2s⁵+s³<s⁸.

Also (C+Q)³≤s⁹(s²+1)³<s¹⁶. The last strict inequality follows from

    64(s²+1)³≤125s⁶<128s⁶≤64s⁷       (s≥2).

The scalar inequality, its prefix-sum consequence, and the head gap in (1)
are proved in Lean as `scalar_cubic_gap`, `one_big_sum_cube`, and
`one_big_head_gap`.

For the powers-of-three row put m=2^(e−1), so C=27^m, Q=9^m and
U=256^m. The elementary inequality x^m+y^m≤(x+y)^m reduces (1)–(2)
to the strict integer comparisons

    27²·28<256²,   9²+27<256,   2·27+9<256,   36³<256².

The C=18 row is a direct integer check. The heads 4,5,6 satisfy (1)
directly; they are deliberately excluded from (2).

Two consequences will be used repeatedly.

**Positive g, zero h.** Every increasing event after H reads H. A proper
addend is at most √H; a noncanonical multiplier is at most √H. Hence a
final sum is bounded by H(√H+1). With m=2^(g−1),

    H(√H+1)=C^(2m)(C^m+1)≤[C²(C+1)]^m<U^(2^g).

It cannot be big. If D is a proper sum, D=H+t with t≤√H and is
nonsquare. A square final cofactor cannot make Dw square. Every nonsquare
old cofactor lies in P and is at most C, so

    Dw≤C(H+√H)≤[C²(C+1)]^m<U^(2^g).

Consequently both D and N must be products whenever g>0,h=0 and N
is a square big event.

**A proper second sum followed by a positive final run.** Whenever (2)
holds, such a source is impossible. At g=0, D≤C+Q. At g>0, D≤H+√H
and Q²≥C imply H+√H≤(C+Q)^(2^g). Thus D³<U^(2^(g+1)). For h≥1
the largest noncanonical final product is D^(3·2^(h−1)); the corresponding
big-step boundary is U^(2^(g+h)). Raising the preceding strict inequality
excludes that boundary. A final addition is no larger than this product.
The three small exceptional heads are handled by the constructions below.

## 3. Positive final gap h

After a positive D-run, a square endpoint must have N=Kw with w square.
A proper sum is in the square gap, and twice a square is nonsquare.

If √w is already present before the final square producing K, delete that
square and multiply √K by √w. This saves a write. A positive inner-run
cofactor has such a root. If w=D and D is square, reconstruct √D from
the preceding GS four-event history, perform h squares, and multiply by
the retained √D. Again the saving is one write.

For the mixed-first prefixes needed here, that GS root construction uses
only prefix values, their roots, the canonical tower, and 3,6. In particular,
it does not require a new half of √D outside M. To check this scope in the
four-event proof: the AB row gives retained B, √A·B, the exceptional 24,
or additive roots A+1,A+2; the reset row gives retained B or A times an
available tower root. The fixed rows use 3,6,9. The powers-of-three row
uses the root-prefix construction in the next paragraph. At positive g,
square factors have available roots or the same root-prefix construction
applies. All these values and the needed √D are in the outer menu M.

If B is a power of two, P consists entirely of powers of two. By (2), D
cannot be a proper sum when h>0. Thus every source value is a power of two
and the exponent-chain theorem applies.

Now suppose B is not a power of two. Every square value in P has an
already available root, with just one possible exception:

    B=3, e≥2, X=3^(2^(e−1)), Y=3^(2^(e−2)), Q=X², C=X³.

Here √C=XY may be absent. Replace the Q and C writes by XY and (XY)².
This costs the same, adds √C, retains C and all earlier values except Q.
It is legal because X,Y were already present.

If the later D recipe does not read Q, the original continuation remains
legal and the final-square deletion works. If it reads Q, it cannot be a
proper sum by (2). Multiplying Q by either nonsquare old value 2 or 3
cannot exceed C, hence cannot produce D>H≥C. The required factors are
therefore square. Instead stop the initial 3-run at X, construct XY and
take roots of the subsequent product and square instructions. This costs
one fewer write than the original prefix and retains the root of every
square old value, including Q and C. It supplies √D, all subsequent run
roots, and the last √C cofactor. This completes h>0 without dropping an
operand needed later.

## 4. Positive gap g and zero final gap

Section 2 has reduced this case to D=Hv and N=Hvw. Power-only sources
are already covered. For a mixed-first prefix, the following are exhaustive.

* If both v,w are square and their roots are available, delete the last
  H square and execute the two rooted products. This saves one write.
* If v=w is nonsquare, use √H·v, saving two writes.
* In the exceptional square-C powers-of-three prefix of Section 3, the
  root-prefix construction retains every required square factor root.
  Append g rooted squares and the two rooted products, saving one write.

For distinct nonsquare cofactors, classify the square-product pairs:

| Prefix | Possible distinct pair with square product |
|---|---|
| C=AB, A≥4, B proper | B,C; also 2,B and 2,C only at A=16,B=18 |
| C=A², B proper | 2,B only at A=16,B=18 |
| 1,2,3,5 | none |
| 1,2,3,9,18 | 2,18 |
| 1,2,3,9,27 | 3,27 |
| Higher square-C powers-of-three prefix | none |

This uses the square-free parts, not a primality assumption on B. A proper
B=A+u has square odd part only for A=16,u=2, by the two-power square test.
The additional pairs involving 2 are too small for the big event: checking
g=1 gives respectively 2·288³<65536², 36·256²<65536²,
36·18²<256², and 81·27²<256². The strict bounds propagate to larger g.

For the pair B,C with C=AB, the g=1 endpoint is A³B⁴. At A≥16,
B≤3A/2 gives A³B⁴≤(81/16)A⁷<A⁸. At A=4,B=5 it is also below
U². The only case that reaches the boundary is A=4,B=6,g=1. At g=2,
144·24⁴=47,775,744<256⁴, and the bound propagates to larger g. Its endpoint is 82,944 and its root 288.
Either order of the two cofactors is handled by

    1,2,4,6,24,144,288.

The source has seven writes and this root program has six. Its new value
144 is exactly R/2, already part of M. The A=2 prefix C=6 has nonsquare
palette {2,3,6}, with no distinct square-product pair. This finishes g>0.

## 5. No square gaps after the first big event

Here g=h=0. A final instruction avoiding D was handled in Section 1.

### Final additions

Write N=D+w. If w<C, then w≤Q<√U by (1). A square in
U≤D+w<U+√U must equal U, whose root is in the canonical tower.
If w=C, a proper additive D gives N≤2C+Q<U, and a product D avoiding
C gives N≤Q²+C<U. It remains to consider D=Cv and N=C(v+1).

For the AB row with proper B and A≥4, N≤AB(B+1)<A⁴. For the reset
row, N≤A²(B+1)<A⁴. If B is a power-of-two first product, write B=Au.
In the AB row, v=B is inadmissible at u=√A because D=AB²=U. At the
next tower choice u≤A^(1/4), AB(B+1)<A⁴. Tower multipliers v≤A
also give AB(v+1)<A⁴. These inequalities hold already at A=4; the
u≤A^(1/4) alternative begins at A≥16.

For a positive-gap power-of-two first G, the square test for C(v+1)
requires v=8 and C square. But 9C<U in that row. In the powers-of-three
row with e≥2, C is square, and the only old v with v+1 square is 3;
again 4C<U. The five fixed prefixes in Section 6 cover the remaining
initial cases. Thus a squared final sum gives only the canonical boundary U.

### Proper second additions with a power-only prefix

If B is a power of two but the source is mixed, D is a proper sum C+t.
A final product Dw can be square only when the exponents of C and t differ
by three, and the total 2-adic valuation is even. The complete exceptions
in the prefix table are:

| C | t | D | Largest square Dw from an old cofactor | U |
|---:|---:|---:|---:|---:|
| 16 | 2 | 18 | 144 | 256 |
| 256 (A=16,B=32 reset) | 32 | 288 | 9,216 | 65,536 |
| 32 | 4 | 36 | 144 | 256 |
| 512 | 64 | 576 | 36,864 | 65,536 |

For C=A², writing A=2^a bounds the smallest gap by a/2, so only
a=2,4 need inspection. For C=AB the gap to B is a and all other gaps
are at least a+log₂(B/A). In the positive-gap power row the smallest
gap is 3a·2^(e−2), giving only a=2,e=1. The reset A⁴ row has
smallest gap a and all remaining gaps at least five. These exhaust
the possibilities for a gap of three. Every displayed square is below its boundary.
This rules out a square big product. If D and N are products, the source
is power-only and Section 2 of POWER-HISTORIES supplies the constructor.

### Mixed first value and C=AB, A≥4

The only product D avoiding C that exceeds C is B². Multiplying it by
an old square tower value stays below U; the other old cofactors B,C are
nonsquare. Otherwise D=Cv with v in the tower or v=B. The case N=C²v
has a square endpoint exactly when v is a square tower value, and the root
C√v uses one fewer write, preserving C and the available tower root.

For other cofactors, a single uncancelled odd part of B forces B=18,A=16.
The parity condition then bounds the product of the two tower cofactors
by 32, giving N≤9,216<U. Two additional B factors leave B³ nonsquare.
One additional B factor and a tower value t give N=AB²t: squarehood
requires t square. Proper tower t≤√A is too small for U (at A=4 there
is no such nontrivial square t); t=A gives the retained root C.

If D=C+t is a proper sum, an old cofactor w≤B is too small since
B(C+B)<U. For w=C and t=B, N=AB²(A+1) is nonsquare. For a tower
t, the odd part of B is coprime to C+t, so squarehood forces B=18,A=16.
The four possibilities t=1,2,4,16 make none of 288(288+t) square.
Thus the root C√v and retained-root cases exhaust this row.

### Mixed first value and reset C=A², A≥4

A product D avoiding C is AB or B². The only square big product arising
from these is C·B², with root AB. A product D=Cv gives N=Cvw.
Distinct nonsquare cofactors can only be 2,B at B=18; their product is too
small for U. Equal B cofactors give the same root AB. Two square tower
cofactors reach U only at v=w=A, giving retained C. A cofactor C gives
C²v, with root C√v when v is a square tower value. Other possibilities
are nonsquare or below U.

The root AB is built directly from retained A,B, omitting the unnecessary
C and D writes. The root C√v retains C and adds one multiplication.
A proper D=C+t lies in the square gap above A², because t≤B<2A+1.
Its only nonsquare old cofactors are 2,B, and B(C+B)<U. Hence no proper
sum produces an additional square big product.

### Higher powers-of-three prefix

Let e≥2, X=3^(2^(e−1)), Y=3^(2^(e−2)), Q=X² and C=X³. The
root-prefix program through XY=√C retains every square-prefix root and
saves one write. If D and its factors are square, apply this program,
then the two rooted products. A nonsquare product D>C must be C times
2 or 3; a square final product requires the same nonsquare cofactor and
is constructed as √C times that cofactor, within the budget.

A proper D=C+t is not square. For t=1,2 use the square gap. For t=3
use its odd 3-adic valuation. Every other old t is 3^(2^j), j≥1;
after factoring t, the remainder is one plus a positive even power of 3,
strictly between consecutive squares. A final square cofactor cannot help.
The nonsquare old cofactors are only 2,3, and 3(C+Q)<U, excluding a big
product. This completes the infinite rows.

## 6. Fixed initial palettes and verification

The remaining prefixes have finite old palettes. Enumerating both operations
for D with C<D<U, then both operations for N≥U, excluding N=D²,
gives the following exact square-endpoint sets. Recipes avoiding D are
included, so the table is deliberately broader than the residual case.

| Prefix | Square endpoints N | Roots needing a construction |
|---|---|---|
| 1,2,3,4 | 16,36 | 6 |
| 1,2,3,5 | 16,25 | 4 |
| 1,2,3,6 | 16,36 | 4 |
| 1,2,3,9,18 | 324,729,2916 | 27,54 |
| 1,2,3,9,27 | 324,729,6561 | 18,81 |

The roots 4 and 6 use 1,2,4 and 1,2,3,6. From 1,2,3,9 one more
write gives 18,27 or81. Root54 uses 1,2,3,9,18,54. All save at least
one write relative to their sources and use M. The finite palette test
checks the table independently, including sums, products and old-only recipes.

This completes GSG for arbitrary A,e,g,h and trailing square runs. The
remaining event orders at this stage are SGG, SGGG and GSGG; the later
[two-big extension](TWO-BIG.md) also eliminates GSGG. Every shortest chain
of a remaining counterexample must contain a non-power-of-two value.
No closure claim is made for the remaining mixed SGG and SGGG histories.

The implementation reuses the shared candidate-menu solver and the power
constructor. A resource stop remains `ResourceLimit`, not an impossibility
claim. Independent tests enumerate the one-G prefixes, check the growth
bounds, replay all reconstructed instructions, exercise long square runs
and verify the 288 shared-helper exception. These finite checks supplement,
rather than establish, the all-parameter argument above.
