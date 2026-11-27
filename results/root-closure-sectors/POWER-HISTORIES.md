# Power-only histories: reduce the problem to addition-chain halving

**Status: proof draft, with a classical classification dependency.** The
construction below covers square endpoints of every increasing AM history
of defect at most two whose values are all powers of two, including 1.
It is independent of the order of the canonical events. It does not cover
an arbitrary history merely because its *endpoint* is a power of two.
Independent review of this presentation is pending. No new classification
of ordinary addition chains is claimed.

## 1. The imported theorem and its precise role

For ordinary addition chains put s(m)=ℓ_A(m)−floor(log₂ m). Knuth's
classification, stated as Theorem 4.7.2 in
[Altman's thesis](https://hjaltman.github.io/thesis-FIXED.pdf), characterizes
s(m)=2 by three-set-bit integers and four families of four-set-bit integers.
The zero- and one-small-step cases have one and two set bits, respectively.
Altman's [published treatment](https://arxiv.org/abs/1409.1627) provides the
surrounding low-defect and stability theory.

The five forms for s(m)=2 are:

| Form | Parameter conditions |
|---|---|
| 2^a+2^b+2^c | 0≤a<b<c |
| 2^a+2^(a+1)+2^(a+2)+2^(a+7) | a≥0 |
| 2^a+2^(a+1)+2^b+2^(b+3) | b>a+1, a≥0 |
| 2^a+2^b+2^c+2^(b+c−a) | 0≤a<b<c |
| 2^a+2^b+2^c+2^(b+c−a+1) | 0≤a<b<c |

Every displayed exponent is a distinct bit position. Consequently, if an
even m has s(m)≤2, subtracting one from every bit position preserves its
classification and small-step count. Thus

    ℓ_A(m/2)=ℓ_A(m)−1    whenever m is even and s(m)≤2.

This is a *halving* consequence of the classified forms. Forward stability
alone would not justify the inference: knowing that cheap m remains cheap
under doubling does not rule out a more expensive predecessor m/2.

[Clift's current discussion of trailing zeros](https://www.additionchains.com/DoublingConjecture.html)
independently identifies the closure of these low-step families under
halving and examines higher-step boundaries. Its broader conjecture and
floating-point integer-program checks are not prerequisites here. At three
or more small steps, halving closure cannot be assumed.

## 2. Explicit constructors for the classified numbers

The implementation does not search all addition chains. It reads at most
four set-bit positions and constructs the corresponding program. All values
start from 1 and every doubling or addition is charged one write.

For at most three bits, the usual binary construction costs
floor(log₂ m)+popcount(m)−1. For the four-bit cases, remove the lowest
bit position a, construct the odd part, then perform a doublings. The four
odd-part recipes are as follows.

**135.** Use

    1,2,3,6,12,15,30,60,120,135.

There are nine additions, matching floor(log₂ 135)+2.

**3+9·2^e, e≥2.** Construct 3 in two writes, double e times, and add 1
to obtain u=3·2^e+1. Double u and add the retained u. This produces
3u=3+9·2^e in e+5 writes, equal to its top bit position plus two.

**(1+2^d)(1+2^e), 1≤d<e.** Double 1 d times, add 1 to produce u,
double u e times, and add the retained u. The cost is d+e+2; the top
bit position is d+e.

**1+2^d+2^e+2^(d+e+1), 1≤d<e.** After d doublings retain p=2^d.
Construct u=p+1 and v=u+p. Double v e times and add the retained u.
The cost is d+e+3; the top bit position is d+e+1. Both p and u remain
available when read; this is a shared computation, not an expression tree.

Each recipe is strictly increasing, has the stated endpoint, and uses only
addition. Appending a doublings restores the original scale and increases
both the top bit position and the write count by a. The cited lower-bound
classification establishes optimality in the ordinary addition-only model.
It establishes no unrestricted AM-chain optimality claim. Each displayed
recipe has at most three nondoublings, regardless of its parameters.
The binary cases have at most two; the 135 recipe has exactly three.
Trailing doublings do not change that count.

## 3. Translate the entire AM history to exponents

Consider an increasing AM chain

    1, 2^e₀, 2^e₁, …, 2^e_q,

where e₀=1, with r=q+1 writes. Its exponent history starts from 1 and
has q=r−1 additions:

* A multiplication of values adds their exponents.
* An addition of two powers of two can itself be a power of two only if
  the inputs are equal. After the initial write 2, such an instruction
  increments an already available exponent e by 1. Exponent 1 is
  available throughout, because the value 2 is retained.

For the second fact, if a<b, factoring 2^a from 2^a+2^b leaves the odd
integer 1+2^(b−a)>1. It cannot be a power of two. Multiplication by the
initial value 1 cannot produce an increasing write, so no exponent-zero
operand has to be introduced after the initial write.

The exponent history is strictly increasing and every operand refers to
an earlier entry. Its endpoint E=e_q satisfies

    (r−1)−floor(log₂ E) = r−λ_AM(2^E).

Thus a source AM history of defect at most two supplies an ordinary
addition-chain witness of small-step count at most two. This remains true
if the history is not shortest. There is no substitution of an arbitrary
optimal prefix for a shared intermediate history.

## 4. Root reconstruction and exact write accounting

Suppose the source endpoint N=2^E is square and exceeds 1. Then E is even
and E≥2. Section 1 implies that E/2 has an addition chain of at most
r−2 writes. Section 2 constructs such a chain explicitly.

Lift this exponent chain back to values:

1. Write 2=1+1, charging one instruction.
2. For each exponent sum e_i=e_j+e_k, write 2^e_i=2^e_j·2^e_k.

The compiled program ends at 2^(E/2)=√N and has at most 1+(r−2)=r−1
writes. All references remain available, the values strictly increase and
no exponentiation operation is assumed in the AM program. Powers in the
notation describe values; the executable instructions are addition and
multiplication only.

This proves the power-only root theorem. It also gives a stronger endpoint
normal form: **every power-only AM history of defect at most two has an
equally short or shorter power-only replacement with at most four canonical
nonsquares**. Apply Section 2 to E itself, then lift. Each exponent doubling
becomes a canonical square; at most three other additions, plus the initial
write 2, give the bound four. This replacement preserves the endpoint, not
arbitrary old intermediates needed by a later continuation.

This explains why additional covered histories need not add new distinct
endpoints to a finite certificate: a shorter history in a previously covered
sector can already have the same endpoint. In particular, after combining
it with the other sector arguments, including [GSG](ONE-BIG.md), any remaining defect-two root-closure
counterexample must have event order SGG, SGGG or GSGG in every
shortest chain for its square, **and every such chain must contain at least
one value that is not a power of two**. Its endpoint might still be a power
of two; that case is not excluded by the present theorem.

The constructors run in time proportional to their explicit output up to
integer-arithmetic costs. This is not a claim that arbitrary addition-chain
synthesis has become efficient. Lifting exponent chains can require enormous
integers, so the public compiler requires an explicit output-bit budget and
checks it before allocating the powers. Resource exhaustion is distinct
from a mathematical obstruction. The root routine uses the already
materialized source endpoint's bit length as a sufficient budget.

## 5. Evidence and formal scope

[Implementation](../../solved/power_roots.py) ·
[Tests](../../tests/test_power_roots.py).
The existing chain builder and exact addition-chain search are reused.
The constructor is compared with that independent unrestricted search for
every target 1–299, including class nonmembers. Parameterized tests cover
all four-bit families, zero and large binary scales, halving, operand
references, list-input isolation, malformed inputs and preallocation limits.
The root-sector certificate also enumerates the newly supported power-only
histories in the previously unsupported event orders.

[PowerChainLift.lean](../../lean/PowerChainLift.lean) defines a transformation
from an arbitrary increasing addition-only `SolvedCoverage.Chain r` to a
valid AM `Chain (r+1)`. Its type includes operand legality, the initial 1,
strict increase and every arithmetic equation. `lift_endpoint` proves the
exact endpoint; `lift_root` supplies a root program when the addition-chain
endpoint is half the desired exponent. The initial 2 write is included in
r+1. The `values_increasing` lemma is also registered in the audit.

The classical classification, exponent extraction and the full low-defect
root theorem are not completely formalized here. The finite tests do not
prove their unrestricted quantifiers. The main theorem remains a written
argument dependent on the cited classical classification.
