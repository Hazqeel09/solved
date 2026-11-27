# Root reconstruction when the second small step occurs late

**Status: proof draft.** Independent review remains pending. This manuscript
extends the root construction to the event words GGS and GGSG, for arbitrary
initial tower heights and square-run lengths. It does not settle the full
root-closure question. The classification of the starting histories is an
explicit dependency on published work, not a new classification claim.

## 1. Statement and the published prefix classification

Use the increasing AM-chain model, level and canonical-event convention of
[the main manuscript](PROOF.md). Ignore the initial write 2 and the first
small step when forming an event word. S denotes the second small step;
G denotes a subsequent big canonical nonsquare. Canonical squares between
events do not enter the word.

**Theorem.** If a chain of r writes has exactly two small steps, event word
GGS or GGSG, and square endpoint N, the candidate menu of
[FOUR-EVENTS.md, Section 1](FOUR-EVENTS.md) contains a program for √N of
at most r−1 writes. No bound is imposed on any square run.

A trailing canonical square gives the result immediately. A root already
present in the history also gives a shorter prefix. Henceforth suppose
neither shortcut applies. Normalize doubling as multiplication by 2.
All other sums have distinct operands.

Before the second small step the chain has exactly one small step and two
big nonsquares. Tarek, Bahig and Anwar classify such *histories*, including
all intervening square runs, into Cases XVIII and XIX of Theorem 1.1.
Their Section 5, equations (5.24) and (5.25), gives precisely these prefixes:

* F: `1,2,3,6,18`, followed by g≥0 squares. Write W=18 and H=W^(2^g).
* P: the canonical tower through A=2^(2^k), k≥1, followed by
  B=A√A, C=AB, W=BC=A⁴, then g≥0 squares to H=W^(2^g).

There are no square gaps between the first small step and those two G
events. This restriction is essential; an arbitrary cheap construction of
H would not preserve the required history.
[Primary source, 2026](https://doi.org/10.3934/Math.2026667).

For GGS append the small value D=N. For GGSG append D, then h≥0 squares
to K=D^(2^h), then the big nonsquare N. Trailing squares have already
been removed. Let U be the next level boundary after H. It is
256^(2^g) in F and H² in P. The small-step condition is H<D<U.

After a positive square run ending at X, every older value is at most
√X. Any increasing noncanonical operation therefore reads X. A proper
sum X+t lies strictly between consecutive squares, and doubling X is
not square. A square product Xw requires w square. These facts are proved
in the main manuscript and apply independently of the written recipe alias.

## 2. The prefix-root and final-run constructions

For P with A≥16, all noninitial prefix values except 2 are squares.
Stop the initial tower at √A, then construct

    √B=√A·√(√A),   √C=√A·√B,   √W=√B·√C.

Append g squares to reach √H. This costs one fewer write than the source
prefix and retains the root of *every square prefix value*. Each new value
is a root of a source value. No claim about freely substituting an
individually optimal endpoint program is used.

For the exceptional P prefix A=4 the history is `1,2,4,8,32,256`.
Its square values are 4,256 and the positive W-run values, besides 1.
All their roots lie in the canonical tower. Constructing √H by that tower
costs g+3 writes, compared with g+5 writes for the original history to H.

If h>0 and N=Kw is square, w must be square. When √w is already present
before the last square producing K, remove that square and append
√K·√w. This saves one write and keeps all other earlier operands.
If w=D and D is square, first use the GGS construction in Section 3 for
√D, perform h squares, and multiply by the retained √D. This also saves
one write. Positive D-run cofactors have roots already available. Thus the
only unresolved cofactors in this final-run construction are fixed prefix
values whose roots are missing from the original history.

All constructions below stay within the shared candidate menu. The
canonical tower and source roots are candidates with real construction
costs, not free constants. Unioning dependencies and sorting them numerically
is legal in this positive AM model; discarded dead values cannot increase
cost. The finite-menu solver counts each shared ancestor once.

## 3. GGS: the endpoint is the second small value

### Prefix F

At g=0 the possible small values are

    19,20,21,24,36,54,108.

Only 36 is square, and its root 6 is retained. This list follows directly
by applying both operations to the five-value prefix and imposing 18<D<256.
At g>0 a square D must be H times a square cofactor. The only nontrivial
square cofactors are positive W-run entries, and their roots are already
available. Delete the final H square and multiply the two available roots.

### Prefix P

A proper sum cannot be square. Write A=2^a with a=2^k. At g=0 the
largest proper old exponent below the exponent 4a of H is 5a/2.
The two-power square test requires exponent gap 3 and an even lower
exponent. The only possible gap 3 occurs at a=2 with lower exponent 5,
which is odd. At g>0 the square-gap argument applies. Doubling H is
also nonsquare, since H has even exponent.

A product avoiding H can increase the value only at g=0, when it must
be C²; its root is retained. Every other square endpoint is Hw. For
A≥16 the only nonsquare old value is 2, so w is square; apply the
uniform prefix-root construction and the final rooted product. The cost
is exactly one less. For A=4, use the canonical tower to √H and multiply
by √w, also a canonical tower value. This costs at most g+4 writes,
compared with g+6 in the source. These cases prove GGS.

## 4. GGSG with a positive final square run

Let h>0. Section 2 handles every cofactor with an already available root,
and handles w=D by Section 3. In F every square prefix cofactor already
has a root in the history, so F is complete.

In P, consider a fixed prefix cofactor w whose root is missing. Necessarily
w≤H. If D≤2H, then

    wD² ≤ 4H³ < H⁴,

since H≥256. Raising this bound to 2^(h−1), and using w≤w^(2^(h−1)),
shows wD^(2^h)<H^(2^(h+1)), below the required big-step boundary.
Consequently D cannot be additive or a product using 2: any such increasing
product would have to be 2H, since twice every proper earlier value is
smaller than H.

For A≥16, D must therefore be a product of square prefix values. Root the
entire prefix, this product and the h squares; then multiply by the
retained √w. All required roots are retained, with one fewer total write.

For A=4 the only missing square prefix root is √256=16. If g≥1,
every small product D has D≤H√H, so a final big product would require

    256 ≥ (H²/D)^(2^h) ≥ H^(2^(h−1)) ≥ H ≥ 65536,

which is impossible. For g=0 the possible product exponents of D are
9,10,11,13. The last big product with w=256 requires

    2^h·log₂(D)+8 ≥ 16·2^h.

Only h=1, log₂(D)=13 satisfies this inequality. The endpoint is 2³⁴,
and the root 2¹⁷ has the six-write chain

    1,2,4,16,256,65536,131072.

The source has eight writes. This completes all positive h.

## 5. GGSG with no final square run: prefix F

If the final instruction avoids D, a product or sum of earlier values
would have to cross U. At g>0 the only candidate not bounded by H√H
or 2H is H², whose root is retained; at g=0 it is likewise 18².
We may assume the instruction reads D.

No final sum can be big. At g=0, D≤108 and D+18≤126<256.
At g>0, D≤H√H (proper sums are smaller), and

    H√H+H = (18^(3/2))^(2^g)+18^(2^g) < 256^(2^g)=U.

For example, 18^(3/2)<77 and 77+18<256, and (x+y)^m≥x^m+y^m
for positive x,y and integer m≥1 gives the stated bound.

At g=0 the finite palette in Section 3 leaves only N=324 as a square
big product; its root 18 is retained. For g>0, a proper additive D=H+t
has t≤√H and is nonsquare. A square final cofactor would force D square.
A nonsquare cofactor lies in {2,3,6,18}, so

    Dw ≤18(H+√H)<36H<U,

where U/H=(256/18)^(2^g)>36 for g≥1. Thus D must be a product Hv,
and N=Hvw. Since H is square, vw is square. There are three possibilities:

* Both v,w are square. Their roots are already present. Delete the last
  H square, then form √D and √D·√w: a saving of one write.
* v=w is nonsquare. Form √H·v after deleting the last H square: save two.
* They are distinct nonsquares. The sole square-product pair in
  {2,3,6,18} is 2·18=6². Form √H·6 using the retained 6: save two.

This is an exhaustive cofactor classification, not a primality assumption
about H or a restriction to individually shortest prefixes.

## 6. GGSG with no final square run: prefix P

Here U=H². If the final instruction avoids D, only H² can reach U,
with retained root H. If it is an addition using D, then

    H²≤N=D+w<H²+H<(H+1)².

Squarehood forces N=H², again with retained root. This boundary argument
is formalized by `SolvedRootBlocks.square_at_boundary`.

Consider N=Dw. A proper additive D=H+t gives

    N=2^(e+f)(2^(P−e)+1),

where H=2^P, t=2^e, w=2^f. The two-power test forces P−e=3 and
e+f even. At g>0, P−e≥P/2≥8. At g=0 the only possibility is
A=4, H=256, t=32, hence D=288. The allowable odd cofactor exponents
are 1,3,5, producing 576,2304,9216; all are below H². Thus no such
square big product occurs.

It remains that D is a product. For A≥16 every old value except 2 is
square. If D is nonsquare it must be 2H; the only nonsquare cofactor
is 2, and 4H<H². Hence every legal square big product uses square
operands, and the uniform prefix-root construction in Section 2 applies
to both new products. It saves one write.

For A=4 write H=2^P, with P=8·2^g. At g=0 the possible D exponents
are 9,10,11,13. Adding an old cofactor exponent in {0,1,2,3,5,8}
can give an even result ≥16 only at 16 or 18. Root exponent 8 is
retained; root exponent 9 has the five-write chain

    1,2,4,16,256,512,

versus seven source writes.

At g>0 write D=Hv with exponent P+e. Both e and the exponent f of a
final cofactor other than H are at most P/2. Then e+f≥P is possible
only when e=f=P/2, giving N=H² with retained root. Otherwise w=H.
Squarehood forces e even; every old value of even exponent is a canonical
tower value. Construct H by the canonical tower and multiply by √v.
This costs at most g+5 writes, compared with g+7 in the source, and
uses only the shared menu.

This exhausts GGS and GGSG. Every remaining defect-two root-closure
counterexample must have shortest square chains with event order SGG,
GSG, SGGG or GSGG. The later [GSG argument](ONE-BIG.md) eliminates
one of these four orders; the other three remain unresolved.

## 7. Verification and limits

The existing shared-support solver is reused, without a second synthesis
implementation. The API admits the two new event words. The later
[power-only extension](POWER-HISTORIES.md) also admits other event words
when every source value is a power of two. GSG is now covered by the
[one-big extension](ONE-BIG.md); the remaining mixed histories are rejected. Configured resource exhaustion raises
`ResourceLimit`; it does not report mathematical infeasibility.

The complete finite checker independently enumerates legal chains and
replays reconstructed programs. Tests also exercise all final-recipe aliases,
large towers/runs, the A=4 exceptions, retained-root shortcuts and resource
stops. These checks test the implementation and boundary analysis; the
unrestricted claim rests on Sections 1–6 and the cited prefix classification.
The Lean support covers the boundary-square and paired-cofactor identities,
not the whole prefix classification or sector theorem.
