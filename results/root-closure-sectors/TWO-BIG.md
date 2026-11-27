# Two big events after the second small step

**Status: proof draft; independent review pending.** This manuscript covers
the entire GSGG event order for arbitrary tower heights and square-run
lengths. The suffix growth bound and two product-program identities are
checked in Lean. The complete case classification remains a written proof.

The [marked-root obstruction](../root-retention-obstruction/PROOF.md) rules
out blanket root retention. Every reconstruction below specifies the values
its continuation actually needs. No general root-saturation premise is used.

## 1. Claim, notation and reusable bounds

Work with increasing addition–multiplication chains from 1, unlimited
retention and one write per sum or product. A canonical square is defined
by its value, not the written recipe. Normalize doubling as multiplication
by the retained 2. A proper sum then has distinct operands.

**Claim.** A two-small-step chain of r writes, event word GSGG and square
endpoint N has a root program of at most r−1 writes.

Remove a trailing canonical square first. Otherwise use

    T, B, e squares, C, g squares, H, D, h squares, K, E, j squares, J, N.

T ends at A. B is the first small value; C the first big nonsquare; D the
second small value; E,N the last two big nonsquares. Thus H=C^(2^g),
K=D^(2^h), J=E^(2^j). Let Q be the value before C and U the next
level boundary after C. Put V=U^(2^g), so H<D<V. The boundary for E
is V^(2^h), and that for N is V^(2^(h+j+1)).

The complete C-prefix table is in [ONE-BIG.md, Section 1](ONE-BIG.md),
derived from the published one-small-step classification. For a first value
B that is not a power of two, its nonconstant rows are

* A≥4, B=A+u with a proper tower u≤√A, C=AB or A²;
* B=3, C=27^m, Q=9^m, U=256^m, m=2^(e−1), e≥1.

The other mixed prefixes end at 4,5,6 or18. The fixed C=27 case will also
be separated when useful. The preceding manuscript proves

    C²(C+1)<U²,  Q²+C<U,  2C+Q<U,                         (1)

and, except at C=4,5,6,

    (C+Q)³<U².                                            (2)

[Primary background: Tarek, Bahig and Anwar, §§3–5](https://doi.org/10.3934/Math.2026667).
The statements here concern costed AM programs, not expression trees or
free-shift arithmetic.

### The cubic barrier

From any prefix with head D≥2, a suffix containing b canonical nonsquares
and s squares has endpoint at most

    D^(2^s F_(b+2)),

where F₁=F₂=1. Initially both leading values are at most D. A nonsquare
is bounded by the product of the two leading bounds; a square doubles the
head exponent. The same Fibonacci induction as the existing global bound
therefore applies to an arbitrary prefix. The Lean relation `TailCounted`
counts those exact suffix events, `tail_envelope` proves the bound, and
`two_event_cubic_barrier` gives the consequence

    D³<V²  ⇒  two further big nonsquares are impossible.   (3)

Indeed b=2 gives an upper bound (D³)^(2^s), while two big events require
at least (V²)^(2^s). This argument includes arbitrary gaps between events.
The formal extension reuses the existing nonsquare-product bound and
Fibonacci inequalities.

If B is a power of two, the prefix through H is power-only. A proper second
sum has D³<V² by (2), including positive g via
H+√H≤(C+Q)^(2^g). Equation (3) excludes it. Thus D is power-only.
From a power-of-two head a proper sum is below the next level boundary:
it is less than twice the head, which is at most that boundary. Therefore
both later big events are products or doublings, and the whole source is
power-only. The [existing exponent constructor](POWER-HISTORIES.md) applies.
Henceforth assume B is not a power of two.

### A targeted cubic-prefix enrichment

One mixed prefix can have an old square whose root is absent:

    B=3, e≥2, Y²=X, Q=X², C=X³,

where X and Y are consecutive retained powers in the initial 3-run.
Replace the Q,C writes by XY,(XY)². This adds √C=XY, retains C and
every old value except Q, at unchanged cost.

If D does not read Q, replay the C-run and D unchanged. If D reads Q,
it cannot be a proper sum: (2) would give D³<V², contradicting (3).
It is therefore a product Q·z. Since D>H≥C=QX, z>X. The only such
available partners are Q,C and values in the C-run; all are squares.
Keep the initial history through X, construct √C, replay the C-run on
roots, and form √D using the available √Q=X and √z. This costs one
fewer write through √D; squaring once restores D. We have therefore
constructed D while retaining √C at no more than the original prefix cost.

This contract preserves D and √C. It does not claim to preserve every
intermediate discarded by the second construction. That narrower contract
is exactly what its uses below require.

## 2. A positive final gap j

A square endpoint after a positive E-run must be N=Jw with w square.
Proper sums lie in the square gap; twice a square is nonsquare.

If √w is present before the last square producing J, delete that square
and multiply √J by √w. If w=E, use the completed GSG theorem on the
prefix through E to obtain √E, perform j squares, and multiply by the
retained √E. Its cost is at most (r_E−1)+j+1=r−1. This recursive
construction requires only √E and its own successive squares. It makes
no assumption about the other values retained by the GSG root program.

The roots of positive E-run and D-run values are already available. Among
older values, the only possibly absent square roots are those of D and C;
tower roots and positive earlier-run roots are present, and B is nonsquare.
The following bounds leave just two exceptional families.

### Exclude small fixed cofactors

For a fixed old cofactor w, failure to reach the final boundary already at
j=1 implies failure for every larger j: raise the j=1 strict inequality,
using w≤w^(2^(j−1)).

If h≥1, then E≤D^(3·2^(h−1)). For w≤D,

    E²w≤D^(3·2^h+1)<V^(4·2^h).

Thus these old cofactors cannot produce N's big step.

Now h=0. At g>0, D≤H√H and E≤DH, hence E²D≤H^(13/2).
Every mixed C-prefix other than C=6 satisfies C¹³<U⁸. For A≥4 use
C≤3A²/2 and 3¹³<2²⁵; for the powers-of-three row use 27¹³<256⁸.
The fixed 4,5,18 cases are direct comparisons. Consequently E²w<V⁴
for every w≤D, excluding these cofactors.

At g=0, A≥4 and B proper, Q=B and C≤AB, so

    E²w≤D³C²≤C⁵B³≤A⁵B⁸<A¹⁶=U⁴.

The last inequality follows from B≤3A/2 and 3⁸<2¹⁴. The fixed rows
have the following bounds, obtained from their exact small-step palettes:

| C | Maximum D | Maximum old square w≤D | Upper bound (DC)²w | U⁴ |
|---:|---:|---:|---:|---:|
| 4 | 12 | 9 | 20,736 | 65,536 |
| 5 | 15 | 9 | 50,625 | 65,536 |
| 6 | 12 | 9 | 46,656 | 65,536 |
| 18 | 162 | 81 | 688,747,536 | 4,294,967,296 |
| 27 | 243 | 81 | 3,486,784,401 | 4,294,967,296 |

This leaves the higher powers-of-three row at g=0 and C=6 at g>0.

### The powers-of-three exception

Let C=3^(3m), Q=3^(2m), X=3^m, m=2^(e−1), e≥2, and g=h=0.
If w≤C, then E²w≤C⁵Q²=3^(19m)<2^(32m)=U⁴. Thus the missing-root
cofactor must be D itself, and D must be square.

If D≠CQ, the next largest possible value is at most Q²=CX; both
products avoiding C and smaller cofactors obey this bound. Then
E²D≤3^(18m)<U⁴. With D=CQ, if E≠DC, the next bound is E≤DQ,
giving E²D≤3^(19m)<U⁴. Therefore

    D=CQ,   E=DC,   w=D.

At j=2, E⁴D=3^(37m)<2^(64m)=U⁸, so j=1 is forced. Since m is even,
keep the initial 3-run through X and its predecessor Y=√X, then write

    √C=XY,  √D=√C·X,  √E=√D·√C,  E=(√E)²,  √N=E·√D.

This replaces six source writes after X by five.

### The base-six exception

Let C=6 and g>0. At g=1 the second-small palette is
37,38,39,42,72,108,216; none is square. All older square roots are present.
For g≥2, the only missing cofactor root can be √D. Squarehood requires
D=Hv with v square. If v≠√H then v≤H^(1/4), giving
E²D≤H^(23/4)<V⁴ because 6²³<16¹⁶. Thus D=H√H.
If E≠DH, then E≤D√H=H², so E²D≤H^(11/2)<V⁴ because 6¹¹<16⁸.
Hence E=DH and w=D. At j=2, E⁴D=H^(23/2)<V⁸, forcing j=1.

Delete the last H-run square, retaining X=√H and Y=√X, and write

    √D=XY,  √E=√D·X,  E=(√E)²,  √N=E·√D.

This replaces five source writes after X by four. The two exceptional
identities and their exact suffix costs are Lean-checked as
`twenty_one_program`, `twenty_one_cost`, `thirteen_program` and `thirteen_cost`.
All operands X,Y were already constructed; none is a free root operation.
This completes j>0.

## 3. No final gap: the last step is a product

Put W=V^(2^h), the boundary for E, so K<W and N≥W². A final instruction
avoiding E is at most K²<W². A proper sum reading E is at most K²+K,
which is less than W² for integers K<W. Therefore

    N=Ew,   w≤K.                                          (4)

Doubling is included as the cofactor w=2.

### Positive h

A proper E=K+t, t≤√K, is nonsquare. A square cofactor cannot make Ew
square, and a nonsquare cofactor is at most D. But

    D(K+√K)≤2D^(2^h+1)≤D^(2^(h+1))<W².

Thus E=Kv with v≤√K. If w<K then w≤√K, giving N≤K²<W².
Consequently

    N=K²v,   v square,   √N=K√v.                       (5)

When √v is already available, retain the original prefix through K and
append one multiplication, saving one of the E,N writes. If v=D, apply
the GS four-event root construction to D, perform h+1 squares to reach K,
and multiply by the retained √D. This costs at most r−1.

The only other missing root is √C in the cubic prefix of Section 1.
Use its targeted enrichment to retain D and √C at the original D-prefix
cost, perform h squares, and multiply by √C. The returned program has one
fewer write. The mixed-first GS root constructions use only source values,
their roots, the canonical tower and 3,6, as detailed in ONE-BIG.md; all
required values therefore belong to M.

### Zero h and positive g

Here K=D. By (1), E cannot be a proper sum, because
E≤D+H≤H(√H+1)<V. Also C³<U² implies H³<V².

If E avoids D, it is a product of old values. To exceed D>H it reads H.
Equation (4) and N≥V² force w=D and E=H²: using a proper old cofactor
at either position gives N≤H³. Thus N=H²D and D is square.

If E=Du, a final cofactor w=D gives N=D²u with u square. When w<D,
both u,w are at most H. Unless both equal H, one is at most √H and
again N≤D·H√H≤H³<V². Thus every square endpoint has one of the forms

    N=D²u with u square,       or       N=H²D with D square.   (6)

For the first form, keep D and multiply by √u. An already available root
suffices; the only missing one is √C, supplied by the targeted enrichment.
For the second, write D=Hv with v square. If √v is available, insert
√D=√H·√v before the last square producing H, then restore H and write
H√D. This uses two writes beyond the original H-prefix, versus three in
the source. If √v=√C is missing, use the rooted cubic prefix, perform g
rooted squares to √H, form √D, restore H and multiply. Its one-write
saving is the same. These programs use only M and satisfy their actual
operand requirements. This completes every case with g+h>0 and j=0.

## 4. All three final events adjacent

It remains that g=h=j=0. The second-small value D and the two big values
E,N immediately follow C. For every proper B=A+u at A≥4,

    B²<A³,   B³<A⁴.                                       (7)

These follow directly from B≤A+√A and A≥4, including the endpoint A=4.
A proper D is excluded by (2)–(3). A proper E also cannot reach the final
boundary: N≤D(D+C). For the AB and reset rows, D≤CB and the bound is
below U² by (7) and B≤A+√A. For C=27^m,Q=9^m with m≥2,

    D(D+C)≤59049^m+6561^m<65536^m=U².

The last comparison holds at m=2 (3,529,831,122<4,294,967,296) and
propagates along square runs. The five fixed prefixes are treated separately
in Section 5. We may therefore use products for D,E,N in the infinite rows.

### Mixed AB prefix

Let C=AB, A≥4, B proper. A product D avoiding C can only be B², which
has D³<U² by (7). Otherwise D=Cv. If v≤√A, then
N≤D²C≤A⁴B³<A⁸=U². Hence v=A or v=B.

For D=CA=A²B, any E with a proper cofactor below C, or any final cofactor
below D, gives N≤A⁴B³<U². The only remaining possibility is E=DC,w=D,
which gives N=A⁵B³, nonsquare because A is square and B is nonsquare.

For D=CB=AB², if E reads D and w=D then squarehood forces E/D to be a square tower
value, at most A. Hence N≤A³B⁴. If w<D and E reads D, both of its
old cofactors must equal C: otherwise N≤DBC=A²B⁴<U². A product E
avoiding D can be big only at E=C², again giving N=A³B⁴.

At A≥16, A³B⁴≤(81/16)A⁷<A⁸. At A=4, B=5 fails the boundary, while
B=6 yields the single endpoint 82,944 with D=144. Its root is obtained
by doubling the retained D:

    1,2,4,6,24,144,288.

Both possible E histories, E=576 and E=3456, are covered. The root program
has six writes and the sources have seven.

### Mixed reset prefix

Let C=A², A≥4, B proper. Products D avoiding C are AB or B², whose
cubes are below U². In D=Cv, proper tower v≤√A is also too small for
two big events. Thus D=CA or CB.

A product E avoiding D gives N≤DC²≤A⁶B<U². If E=Du with u<C,
then N≤D²B≤A⁴B³<U². If E=DC but w<D, the bound DC² again applies.
Therefore N=D²C. Its root DA is a single multiplication after the original
D-prefix, saving one write. The value A=√C was retained from the start.

### Higher powers-of-three prefix

Let C=27^m,Q=9^m,X=3^m, m≥2 a power of two. A product D avoiding C
can only be Q²=CX, so choose a product representation D=Cv. If v is 2
or3 then N≤D²C≤9C³<U². The last inequality follows from
9·27⁶=3²⁰<256⁴ and raising to m/2. Thus every possible D is a product
of square values and is square.

Old nonsquare cofactors are only 2 and3. If E uses either, it must read D:
old-only products with such cofactors are below U. A square N would then
need a matching nonsquare cofactor, giving N≤9D<U². So E is also a
product of square values. An old-only big E is C². Finally squarehood
forces the last cofactor w to be square.

Keep the 3-run through X, construct √C=XY with Y=√X, and take roots of
the D,E,N products. The initial change saves one write and retains every
square operand root used by those three products. This is a specific
rootable product sequence, not a general history-retention theorem.

## 5. Fixed zero-gap palettes

For these prefixes, exhaustive application of both operations gives the
following square endpoints. Require C<D<U, E≥U, N≥U², E≠D² and N≠E².
The enumeration includes proper sums and products using only older values.

| Prefix | (D,E,N) possibilities |
|---|---|
| 1,2,3,4 | (8,32,256), (9,36,324), (12,48,576) |
| 1,2,3,5 | none |
| 1,2,3,6 | (9,36,324), (9,54,324) |
| 1,2,3,9,18 | (162,1458,236196) |
| 1,2,3,9,27 | (243,2187,531441) |

Roots 16 and18 use the canonical tower or 1,2,3,6,18. Root24 uses
1,2,3,4,12,24. Root486 is the retained D=162 times3. Root729 is the
retained C=27 squared. Each program saves at least one write and lies in M.
The independent fixed-palette test verifies the entire table, not only its
positive examples.

## 6. Implementation and verification scope

The [constructor](../../solved/root_sectors.py) uses the existing power-only
constructor, direct final-square deletion, the completed GSG prefix
constructor, and the two explicit exceptional programs when j>0. For j=0,
the complete candidate menu M and its exact shared-support solver suffice
by Sections 3–5. Resource exhaustion remains `ResourceLimit`; it is not
mathematical infeasibility. Every returned instruction sequence is replayed
and its endpoint, saving and defect are checked.

The all-length result covers all e,g,h,j and trailing square runs. It reduces
the remaining unmarked root-closure question to mixed histories with event
order SGG or SGGG. It does not claim to settle those orders.

The finite root certificate, independent prefix/shape tests, complete small
palettes, recipe aliases and large-parameter exceptional families test the
implementation and case boundaries. They do not replace the unrestricted
argument. The general suffix bound and two source/root block identities have
Lean proofs, while the prefix classification and complete sector theorem
retain the stated written-proof scope.
