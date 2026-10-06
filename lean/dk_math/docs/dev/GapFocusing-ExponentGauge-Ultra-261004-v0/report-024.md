# Checkpoint 024: terminal prime products and source multiplicity

The actual support partitions, exact endpoint sums, finite product divisibility
and Nat power thresholds are implemented. Product size gives a correct local
source bound. The formal comparison shows that its single-continuation
aggregate cannot improve even the previous full-support excess budget, and
thus cannot improve the sharper 023 loss frontier.

The two production modules are CoarseTownTerminalProduct and
CoarseTownSourceMultiplicity. Finite calibration belongs to DkMathTest.
The Legendre facade imports both after focused success. Source reuse is in
[source-inventory-024.md](source-inventory-024.md), milestones in
[findings-024.md](findings-024.md), and validation in
[validation-024.md](validation-024.md).

Notation: f(a) is actual squareOffsetPrimeSupport, V the complete-period town,
D left-deleted seats, R left remainder, T outside primes, A active primes,
U uncovered seats, X full support excess, L left loss. Q(a) denotes terminal
primes and C(a) continuing primes. Right analogues use minimum endpoints.
KnownPrimeScales is required where actual support is identified with the
outside-prime world. None of the product or count theorems assumes full cover.

## 1. Exact terminal-source carrier

coarseTownTerminalPrimesAt S n a filters actual support at a by the predicate
coarseTownFiberMaximumAt S n q a. Exact membership is support membership and
the maximum predicate. For certified S and a in V the carrier is a subset
of A and T. Distinctness is provided by Finset; there is no multiset of prime
powers or assumed valuation-one factorization.

The minimum carrier coarseTownMinimumTerminalPrimesAt uses the same actual
support and the unique fiber minimum predicate. The implementation avoids
empty-fiber defaults and reuses 023 extremum semantics.

## 2. Exact disjoint support partition

On every certified full-town seat, Q(a) union C(a) equals f(a), and the two
sets are disjoint. Here C(a) is the existing coarseTownDeletionWitnessPrimes.
An actual supporting prime either has no later fiber seat or has a strictly
later witness. This partition does not assume a is deleted.

Consequently Q.card + C.card = f.card and
product Q * product C = product f. The minimum/right-witness partition and
its cardinality and product divisibility counterparts are implemented too.

## 3. Deletion and nonempty continuing carrier

a belongs to D iff C(a) is nonempty. The proof reuses the 022 equivalence
between deletion and positive deletion multiplicity, then Finset.card_pos.
It does not introduce a new collision relation. On a deleted seat C.card>=1.
The same equivalence is proved for right deletion witnesses.

## 4. Deleted terminal directions are missing

Every q in Q(a) at a deleted seat is a missing active direction. Actual town
support makes q active. Its maximum is a, and the 023 missing/deleted-extremum
equivalence then proves missing membership. The minimum-oriented theorem
uses the right missing/deleted equivalence. No capacity estimate is involved.

## 5. Unique deleted terminal seat

Every missing active direction q occurs at exactly one deleted terminal seat.
The active fiber supplies its unique maximum; missing membership forces this
maximum to be deleted. Conversely, the preceding theorem accounts for every
terminal direction found at a deleted seat. There is also a unique minimum
version. Several different directions may share that unique seat.

## 6. Exact global source count

The biUnion of Q(a) over a in D equals the missing active carrier. Terminal
sets at distinct seats are pairwise disjoint, since the same prime cannot
have two different fiber maxima. Finset.card_biUnion therefore proves
missing.card = sum over D of Q(a).card, as an equality.

Both right-minimum statements are implemented. The new kernel calibration
derives exact source sums 9/8 at 297 and 48/53 at 1031 from the existing
kernel-certified 023 missing counts. Those counts are reused explicitly,
not replaced with diagnostic factor lists.

## 7. Reused product theorems

PrimorialUniverse.finitePrimeBasisProduct_dvd_of_commonMultiple supplies the
product divisibility theorem. IsFinitePrimeBasis is pointwise primality, and
finitePrimeBasisProduct is definitionally the actual Finset product.
Its proof uses coprimality of distinct primes.

Mathlib Finset.pow_card_le_prod supplies the arbitrary-base lower bound.
No new neutral product induction or FinsetProductBounds module is needed.
PrimitiveSet.RealLog's pairwise-coprime divisor APIs were audited as valid
alternatives, but their real layer is not imported. Petal's local base-2
pattern is not imported into Legendre.

## 8. Full actual support product

For every n and a, the product of actual support divides n^2+a. Support
membership already proves primality and divisibility. A genuine square offset
also makes the complete point positive, so this divisor is at most n^2+a.
The exact shell inequality n^2+a < (n+1)^2 follows from 1<=a<=2*n.

The product is the distinct-prime factor budget, not the whole factorization
with valuations. It can be strictly below the point: at n=11, a=19,
product support=70 divides point140. A separate kernel check records
5^2 dividing the n=7 point50, preventing a valuation-one interpretation.
No general rough sqrt-factorization stratum is inferred for arbitrary V.

## 9. Initial-world local power inequality

For S=primeScalesUpTo P and a in V, every actual support prime q satisfies
P<q, hence P+1<=q. This comes from survivor support containment in T and
nonmembership in primeScalesUpTo P, without a next-prime theorem.

The exact local chain is proved:
(P+1)^f(a).card <= product f(a) <= n^2+a < (n+1)^2.
It remains valid for P=0 or P=1. The general pointwise-base theorem also
handles other certified worlds when a suitable lower prime bound is supplied.

## 10. Stronger deleted-seat inequality

The full partition first gives
(P+1)^(Q.card+C.card) <= n^2+a.
On a deleted seat C.card>=1; monotonicity in the exponent then gives
(P+1)^(Q.card+1) <= n^2+a.

The general version requires only a positive base B and B<=every actual
support prime. It is implemented for both orientations. These are local
arithmetic bounds on source multiplicity, not a global missing-direction
estimate without further aggregation.

## 11. Explicit continuing-prime product

For p in C(a), p * product Q(a) divides n^2+a. Its proof takes p dividing
product C and composes with the exact terminal/continuing product divisor.
No product of arbitrary noncoprime divisors is asserted.

For initial worlds the power lower bound also proves
p * (P+1)^Q.card <= n^2+a. The full-support exponent theorem is the preferred
bound because it charges every continuing prime, not just a chosen one.

## 12. Exact Nat threshold and small-base boundary

The generic theorem states: if 1<B, B^(t+1)<=m, m<H and H<=B^(k+1), then t<k.
The strict shell endpoint saves one more unit than t<k+1. Applied to a deleted
seat with H=(n+1)^2, it proves Q.card<k, equivalently Q.card<=k-1 when such
a deleted seat exists. The right theorem has the same boundary.

Base B=1 cannot bound the exponent. A kernel regression proves
1^(t+1)<=1 for every natural t. Thus P=0 is not silently included in a
strictly increasing power-base argument. The unconditional initial inequality
still holds; a generic base-2 prime lower bound can handle its cardinality
threshold separately. No rounding or real-number comparison is used.

## 13. Logarithmic gauge

No Lean logarithmic gauge was introduced. Nat.log's exact power adjunction
was audited, but explicit thresholds suffice and keep all boundary hypotheses
visible. StructuralArithmetic.PowerGauge and Real.log are not used.
The diagnostic exponent budget is computed by exact integer multiplication;
it is computational evidence, not a separately formalized logarithmic API.

## 14. Global bounds with retained excess

Any supplied capacity(a)>=Q(a).card gives
missing.card <= sum over D of capacity(a).
A uniform capacity k gives missing.card <= D.card*k.
For a valid shell threshold B^(k+1)>=(n+1)^2 with B>1, the product-derived
uniform result is missing.card <= D.card*(k-1).

Loss consumers add retained support excess in full:
L <= sum over D of capacity(a) + retainedExcessLeft.
The right and better-loss consumers do the same. The minimum of the two
loss upper bounds can feed the existing exact 023 loss frontier. A supplied
capacity-frontier certificate implies the existing better remainder deficit;
there is no separate prime-producing route.

## 15. Formal comparison against prior excess

On a deleted seat the partition already gives Q.card<=f.card-1. A point-size
threshold also bounds the entire actual support: f.card<=k. Therefore its
single-continuation source allowance k-1 is at least f.card-1. This inequality
is formalized, including aggregation over either deleted carrier.

The complete excess splits exactly as
X = sum over D of (f.card-1) + retainedExcessLeft.
Hence X <= D.card*(k-1)+retainedExcessLeft for the product threshold; the
right statement and minimum-of-both statement are also proved. Existing
losses satisfy L=X-O<=X. The new uniform allowance cannot improve even X,
much less the exact old losses. Nonuniform allowances dominating actual
f.card-1 satisfy the same formal comparison.

There is a finer arithmetic observation in the diagnostics. Write e for the
point-size support exponent budget, s=f.card, c=C.card, t=Q.card. Then e>=s
and t=s-c, so the continuing-aware allowance is
e-c = t+(e-s) >= t. Sixty-eight such allowances are below the coarse s-1
baseline, but the exact support partition already provides t=s-c. This is
an algebraic explanation of those diagnostic flags, not a claim of a newly
proved stronger loss theorem.

## 16. Anchors and kernel reconstruction

Each kernel case verifies complete actual support, terminal and continuing
carriers, exact products, disjoint partition, product divisibility and a power
lower bound. Endpoint computation uses the actual certified town and the
proved divisibility-fiber normal form, not unverified lists of factors.

| n | seat | terminal | continuing | full support product | complete point |
| --- | --- | --- | --- | --- | --- |
| 11, odd S={3} | 19 | {5,7} | {2} | 70 | 140 |
| 297, initial | 350 | {59,79} | {19} | 88559 | 88559 |
| 297, initial | 44 | {113} | {11,71} | 88253 | 88253 |
| 1031, initial | 90 | {241,401} | {11} | 1063051 | 1063051 |

The old 297 uniform branching theorem 113->11 and 113->71 is preserved and
included in the public dependency audit. The 1031 checked seat has two
terminal sources, the largest multiplicity found in its initial-world scan.

For all 602 existing worlds, all 68813 oriented deleted-seat records include
the point, exact carriers/cards, products, lower powers, source capacities
and comparisons. Records are in [deleted-seats-024.csv](logs/deleted-seats-024.csv);
aggregate results and preserved examples are in
[discovery-024.json](logs/discovery-024.json).

The bulk initial-world diagnostics normalize cutoff P=max(S), or P=0 for
empty S. At both larger anchors this is P=7. Kernel calibrations use P=10,
which gives the same finite S and a stronger base11 power inequality. The
formal comparison holds for every valid base, including base11. For odd
worlds with S missing prime2, P+1 is not a justified lower support bound;
the diagnostics use base2. Tiny odd worlds with empty S also satisfy an
initial-cutoff presentation, which is recorded explicitly.

| Initial n | left/right source sums | max sources left/right | multi-source seats left/right | exact loss left/right | product loss upper left/right |
| --- | --- | --- | --- | --- | --- |
| 29 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 2 | 12 / 20 |
| 297 | 9 / 8 | 2 / 2 | 2 / 2 | 12 / 9 | 159 / 145 |
| 1031 | 48 / 53 | 2 / 2 | 7 / 13 | 56 / 62 | 1088 / 1119 |

These upper bounds include retained excess and use the diagnostic normalized
cutoffs. At n=29 the right missing sum is zero but retained excess is two;
source control cannot erase that term. The 29 aggregate is independently
verified diagnostics, not a new 024 kernel global-count calibration.

## 17. Right minimum mirror

Implemented: minimum-terminal carrier, exact support partition, disjointness,
active containment, continuing/deletion equivalence, missing subset, unique
deleted terminal seat, disjoint endpoint biUnion, exact source-count sum,
product divisibility, deleted power and threshold bound, capacity sums and
loss comparison. The orientation-independent full-support arithmetic is
shared. No second generic product induction is introduced.

## 18. Better loss and survivor capacity

The better upper-bound consumer retains both retained-excess terms and takes
the minimum of the two full upper bounds. All exact source residuals are
zero in the scan. There are zero simple local improvements among 68813
records. The baseline product criterion fires in 25 worlds; the 023 exact
better selector fires in 586. Every one of those 25 worlds is already detected
by 023. None of the three mandatory anchors obtains a new product criterion.

Thus no new symbolic loss frontier or finite prime endpoint was obtained.
The new local theorem and exact endpoint aggregation are useful arithmetic
interfaces, but their capacity allowance is weaker than existing excess
accounting. The formal comparison is universal within its stated hypotheses,
so this conclusion is not based only on the sample.

## 19. Smallest limitation and scope of the judgment

The smallest recorded strict weakness is n=2, odd empty S, seat2, point6:
support={2}, continuing={2}, terminal empty. The exact trivial source allowance
is support.card-1=0, whereas the base2 point budget permits one source because
4<=6<8. Actual carriers and these inequalities are kernel-checked.
Smallest means first in this recorded scan, not a universal minimality theorem.

The obstruction is structural: the complete point must accommodate all
actual support primes already present. A bound on their total count cannot
force a single-continuation allowance below that actual count minus one.
Using the exact number of continuing directions merely recovers the known
terminal count with nonnegative product-budget slack.

The distinct-prime refinement was audited. Current primorial APIs provide
products and divisibility, but no lightweight order-statistic product of the
first eligible primes above a cutoff was found. None is implemented; there
is no new prime enumeration, analytic estimate, or consecutive-source-prime
assumption. Stronger prime products would refine total factor capacity, but
still require a new geometric bridge to improve global endpoint loss.
This result does not rule out every future arithmetic method. It supplies
no universal positive U, Legendre proof, or return to valuation floor sums.

## 20. Single next theorem and implementation proposal

Attempt the terminal-product divisor theorem for a geometry-reduced cofactor.
For a full-town seat a, let m=n^2+a, Q(a) its terminal primes, W(a) the later
full-town seats b>a, and Delta(a) the product over W(a) of the positive
differences b-a. The single proposed theorem is:

product Q(a) divides m / Nat.gcd(m,Delta(a)).

For each q in Q(a), q dividing b-a would imply q divides n^2+b, contradicting
its maximum at a. Primality therefore makes product Q coprime to Delta and
to Nat.gcd(m,Delta). The already proved product-Q divisor of m should then
cancel this coprime gcd factor and descend to the positive cofactor. Existing
finite coprime-product and Nat divisor/cancellation APIs should supply the
proof without valuation-one assumptions or analytic machinery.

This cofactor divides out the whole common divisor Nat.gcd(m,Delta), including
repeated prime factors present in both m and Delta. The inferred
initial-world corollary would be (P+1)^Q.card <= m/Nat.gcd(m,Delta), a smaller
budget than the complete point when the gcd is nontrivial. That implication
is a consequence of the proposed theorem, not a result established here.

Implement later-seat exclusion as an internal bridge, lift it to product
coprimality, and prove the single cofactor divisibility target. Provide a grid
adapter retaining the signed residue phase. Calibrate on seats350 and44 at
297 and seat90 at 1031. For computation, reducing the difference product
modulo m preserves its gcd with m and avoids storing a large product.
Only after proving the bridge should one test whether these reduced budgets
give a strict aggregate improvement after retained excess is restored.
This proposal is not implemented in 024, and no global improvement is claimed.

Exploratory arithmetic in checks/proposal-cofactor-024.py reduces Delta modulo
m and records [proposed-cofactor-024.json](logs/proposed-cofactor-024.json).
At 297 seat44 the gcd is 781 and the cofactor is 113. Base11 would then allow
at most one terminal source since 11<=113<121, recovering the already known
one-source branching seat without using its continuing-card count. At 297
seat350 the cofactor is 4661; at 1031 seat90 it is 96641. These are numerical
checks of the proposed bridge, not kernel proofs of it or new prime endpoints.

Outcome C - TERMINAL PRODUCT IS EXACT BUT GLOBALLY TOO WEAK
