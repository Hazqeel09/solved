# Square-root reconstruction in low-defect sectors

**Status: proof draft; independent mathematical review and novelty assessment
are pending.** The full defect-two root-closure question remains unresolved
here. Menu-based reconstruction may stop at a configured resource limit;
such a stop is not an infeasibility claim. Twenty supporting statements and
program identities across two modules are checked in Lean; the complete sector coverage and
program transformations below retain written proofs.

## Question and result

An increasing addition–multiplication chain starts at 1, uses sums and
products of earlier values, and charges one instruction per write. Put
λ(n)=floor(log₂ log₂ n)+1 for n≥2 and λ(1)=0. A chain's defect is its
length minus its endpoint's level. A canonical square produces the
preceding value squared, whatever its written recipe; 2+2=4 is canonical.

The question is whether

    δ(n²)≤2 implies δ(n)≤2,

where δ uses minimum chain length. This is a locally posed strengthening
of the [known low-defect stability argument](../seven-nonsquares/PROOF.md),
not a conjecture attributed to the authors of the cited paper. Its positive
answer would also prove stability for every base of minimum defect three.
The [267 counterexample](../square-instability/PROOF.md) already disproves
root closure at defect three.

**Theorem.** Suppose an increasing chain has exactly two small steps and
an integer-square endpoint N. If it has three, four or seven canonical
nonsquares, event order GGS, GGSG or GSG after the first small step, or only
powers of two throughout its history, one can
construct an increasing chain for √N using at least one fewer instruction.
Its defect is at most two. Arbitrarily long square runs are included. Here
S is the second small step and G a big canonical nonsquare.

The [executable reconstruction](../../solved/root_sectors.py) accepts
precisely these sectors and supplies every instruction of the new chain.
Unsupported inputs are rejected, not declared impossible. Every output is
replayed and its endpoint and instruction saving are checked.

The three-event argument is self-contained. The [four-event extension](FOUR-EVENTS.md) supplies a finite candidate menu and an exact solver that counts shared ancestors once. Its exchange family shows why source values and their roots alone need not suffice. The [late-small extension](LATE-SMALL.md) covers GGS and GGSG using the published one-small-step prefix classification, with explicit treatment of the exceptional history 1,2,4,8,32,256. The [one-big extension](ONE-BIG.md) covers GSG using uniform prefix-growth bounds and the shared-helper exception at root 288. The [power-only extension](POWER-HISTORIES.md) instead works on the exponent chain and uses Knuth’s classical low-step classification. The seven-event part reuses
the existing [twelve-ray classification](../seven-nonsquares/PROOF.md);
it is not a new independent proof of that classification. The background
model and bounds are from Tarek, Bahig and Anwar's 2026 study, whose §7
asks for the two-small-step extension.
[Primary paper](https://doi.org/10.3934/Math.2026667).

## 1. Elementary square tests

If x²<n<(x+1)², n is not a square. In particular, adding any positive
w≤2x to x² cannot produce a square.

For k≥0, the equation

    y²=2^k+1

has the unique nonnegative solution (y,k)=(3,3). Indeed y>1 and
(y−1)(y+1)=2^k. The two positive factors differ by two. Their common
divisor is two, so after removing their even factors an odd divisor of
a power of two must be 1; the only possible factors are 2 and 4.
The Lean proof establishes the odd-factor and adjacent-factor statements
directly, including the k=0 boundary.

Consequently, for a>b≥0,

    2^a+2^b is square
    iff b is even and a−b=3.

Factor out 2^b: a square has even 2-adic valuation, and its remaining
odd factor must be a square. The root is then 3·2^(b/2). A pure power
of two is square exactly when its exponent is even.

These are arithmetic tests, not claims that square roots are free
instructions. The constructions below explicitly build the required roots.

## 2. Three canonical nonsquares: normal form

Removing a trailing canonical square immediately gives the root in one
fewer write. We may therefore suppose the endpoint is itself the third
canonical nonsquare.

Before the first small step, maximum growth forces the tower

    T = (1,2,4,16,…,A),   A=2^a,   a=2^k.

A nonsquare cannot increase the level at that stage, since the next
boundary is A² and every legal operation is at most A². Thus the two
noninitial nonsquares are exactly the two small steps. Write the chain as

    T, B, B², B⁴, …, H=B^(2^g), D,

with g≥0 and D=N. The case g=0 means the intermediate run is empty.

The first small value is A+u, with u a tower entry and A+u<A², or Au
with a tower entry 2≤u<A. Doubling A, when permitted, can also be
regarded as A·2. Every other additive first value is a non-power-of-two
sum A+u with u<A.

For A≥4 every proper tower entry is at most √A. Hence a proper sum
A+u lies strictly between A and (√A+1)², and doubling A has odd
2-adic valuation. Therefore the first small value B can be square only
in the product case B=Au, with both A and u square tower entries.
For A=2 the first small value is 3, and there is no second immediate
small value: the next integer 4 already crosses the level boundary.

## 3. A positive gap before the last event

Suppose g≥1. Every value before H is at most X=√H. Two operands
smaller than H have product at most H and sum at most 2X≤H.
The final event must therefore read H.

A proper sum H+w, with w<H, has 0<w≤X and is not square by the
square-gap test. Doubling H is twice a square and has odd 2-adic
valuation, so it is not square either.

Thus D=Hw. Since H is square, D is square only when w is square.
There are two reconstruction cases.

* If √w is available before the final square in the run, delete that
  last square and multiply √H by √w. Every operand remains available,
  and the resulting chain is shorter by one write.
* The only unavailable factor root can be w=B. A square tower
  multiplier already has its root in T; an inner B-run value has its
  root one step earlier in the same run. For w=B, Section 2 forces
  B=Au with A,u square tower entries. Stop the initial tower at √A,
  form √B=√A·√u, perform g squares, and multiply by the retained √B.
  This constructs √D=(√B)^(2^g+1) in one fewer write.

The new chains strictly increase. In the first case √D>√H because
w>1. In the second, √B>√A and every later multiplication has a factor
greater than one.

## 4. No gap before the last event

Here g=0 and the prefix before D is T,B. The case A=2 is impossible
as noted above, so A≥4.

### Products

If the final product does not use B, both factors are tower entries.
For their product to be square, either both factors are square or both
are 2. The latter gives D=4 and cannot exceed B. Stop the tower at √A
and multiply the available factor roots. Since D>B>A, the product is
strictly greater than √A. This saves two writes.

Otherwise D=Bw. The small-step condition excludes w=A and w=B,
so w is a tower entry with 2≤w≤√A.

If B is a power of two, write B=2^(a+b), where b is a positive
power of two, and w=2^c. Since a is even, squarehood means either
b,c are both even or both equal 1. In the first case form √B from a
tower stopped at √A and then multiply by √w, saving one write.
In the second B=2A and w=2, so D=4A; construct √D=2√A from the
shortened tower, saving two writes.

If B is not a power of two, write B=2^b(2^(a−b)+1). Multiplying by
a tower value cannot change the odd part. Section 1 therefore requires
a−b=3. The tower exponent restrictions force a=4,b=1: for a≥8,
every proper tower exponent b is at most a/2, making the difference
at least four. Thus B=18, A=16. The permitted multiplier is at most
4, and even total 2-adic valuation forces w=2. This gives D=36;
the root 6 has the chain 1,2,3,6.

### Sums

Every possible squared sum is 9, 36, or 4A.

To check completeness, a sum avoiding B is another first-small sum:
A+u with u<A lies in the square gap, and 2A is not square. If B=A+u is a proper sum and the other operand w is also
below A, then u+w≤2√A, so A+u+w lies strictly between consecutive
squares. If w=A, the result is 2A+u. The two-power criterion gives
b=a−2 for u=2^b. The tower exponents allow only (a,b)=(2,0) or
(4,2), producing 9 or 36. Doubling a proper B requires its odd part
to be square and again gives B=18, D=36.

For a power-of-two B=2^(a+b), a sum with a tower operand 2^c
requires a+b−c=3 and even c. If c=a, then b=3 is not a tower
exponent. If c<a, then c≤a/2; a≥8 is impossible, and the remaining
cases are (a,b,c)=(2,1,0) and (4,1,2), giving 9 and 36.
Doubling B is square only when b=1, giving D=4A.

The roots 3 and 6 have chains 1,2,3 and 1,2,3,6. For 4A, stop
the initial tower at √A and double. These save at least one write
(in fact two in the applicable three-event sources).

This completes the three-event proof without imposing a bound on A,
g, or trailing squares.

## 5. Seven canonical nonsquares

The existing all-length classification supplies twelve ray bases and a
two-small-step witness for each. A ray consists of b,b²,b⁴,… . If a
square endpoint has a positive outer squaring exponent, construct the
same base and append one fewer square. Its cost is exactly one less
than the given two-small-step source, because both length and level
increase by one under squaring.

Only three classified bases are themselves squares. Explicit root
witnesses complete the zero-outer-exponent cases:

| Square base | Root | Root chain | Root writes |
|---:|---:|---|---:|
| 11,019,960,576 | 104,976 | 1,2,3,6,18,324,104976 | 6 |
| 17,179,869,184 | 131,072 | 1,2,4,16,256,65536,131072 | 6 |
| 18,446,744,073,709,551,616 | 4,294,967,296 | 1,2,4,16,256,65536,4294967296 | 6 |

The corresponding source lengths are 8, 8 and 9. The executable routine
reuses the existing ray catalogue and compiles its numerical witnesses
to actual instructions. It does not assume that a square-root operation
is available.

This part inherits the written-proof status of the seven-event
classification. Its bounded certificate and the new reconstruction
checks do not replace an all-length proof of that prerequisite.

## 6. Four events and the remaining counterexample sectors

The published zero/one-small families are root-closed. Therefore a
counterexample to the defect-two question must have a square of minimum
defect exactly two. Every shortest chain for that square has between
three and seven canonical nonsquares: the initial write and both small
steps give the lower bound, and the published nonsquare bound gives
the upper bound.

The [four-event argument](FOUR-EVENTS.md) covers the two intermediate event orders SG and GS, while preserving every required helper. The [late-small argument](LATE-SMALL.md) additionally eliminates GGS and GGSG, and the [one-big argument](ONE-BIG.md) eliminates GSG. Thus **every shortest chain in any remaining counterexample must have event word SGG, SGGG or GSGG**, with five or six canonical nonsquares. This is a structural reduction, not a resolution of the full root-closure question. The [power-only argument](POWER-HISTORIES.md) also requires every shortest chain of a remaining counterexample to contain a non-power-of-two value. The other three orders remain unresolved for such histories; a power-of-two endpoint alone does not put a chain in the supported class.

A stronger composition shortcut has been disproved: a shortest defect-two
source cannot always be shortened while retaining the roots of earlier
square values. The [marked-root obstruction](../root-retention-obstruction/PROOF.md)
formalizes exact costs 6,7,7 for 2000, its square, and the joint requirement
{10,2000}. The endpoint-only constructions above do not require that stronger
property. Subsequent root-sector proofs must preserve their actual operand
requirements explicitly.

## Verification scope

The [finite checker](../../checks/verify_root_sectors.py) uses the
independent all-pairs chain enumerator and directly replays every
returned instruction sequence. Through complete level 12 it checks
335,275 eligible square chains: 32,810 with three events, 162,271 with four,
128,449 with five, 11,339 with six and 406 with seven, restricted to the
proved subclasses. They cover 31,706 distinct roots. Savings are one write
in 283,220 cases, two in 45,895, and three in 6,160.

The GSG extension adds 80,888 histories and 3,616 distinct roots to the
previous certificate, including 6,566 new nontrivial menu reconstructions.
The three-/four-/seven-event counts and prior menu/exponent branch counts
are unchanged. The certificate changes because of this declared scope
extension, not a new numerical interpretation of earlier cases.

A separate level-8 test checks all 51,566 final-instruction variants,
including operand order, addition/product aliases and all reconstruction
rules. Other tests cover long runs, roots absent from the original
history, malformed references, unsupported histories and frozen inputs.
The power constructors are also tested against the existing exact
addition-chain search for targets 1–299 and against independently enumerated
AM histories through complete level six, including their four-event normal
forms and output-allocation limits.
[Stored certificate](../../checks/expected/root-sectors.json) ·
[Tests](../../tests/test_root_sectors.py).

The [Lean module](../../lean/RootSectorLemmas.lean) proves square gaps,
the factor-root product identities, the odd-factor power-of-two lemma,
the unique solution of y²=2^k+1, and the four-event helper-exchange
identity with its exact suffix cost, the paired-cofactor identity and the
late-small boundary-square argument and three universal first-big-prefix
growth inequalities used in GSG. It does not yet prove the full
sector classification or certify the Python implementation universally. The
[power-lifting module](../../lean/PowerChainLift.lean) additionally constructs
a valid increasing AM chain from any addition-only chain, with its extra
initial write charged and endpoint/root equations proved. It does not
formalize Knuth’s classification or exponent extraction.

    python -m scripts.verify root-closure-sectors
    python -m checks.verify_root_sectors
    python -m checks.verify_root_sectors --level 8 --aliases
    python -m scripts.check_formalization
