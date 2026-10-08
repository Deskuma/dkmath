# Report 017 - Centered quadratic shell folding

Instruction 017 is implemented. The fold geometry is an exact normalization of
CenteredPair. Least-owner folding supplies a parity constraint, and a separate
norm-and-gap dictionary supplies a new arithmetic interface for common support.
It gives exact support fibers, a mod-four restriction and consecutive-shell
support exclusion. It does not prove a uniform full-cover contradiction.

All newly written report/checkpoint artifacts use ASCII text. Algebraic bridge
code remains in CosmicFormula; Legendre does not import that half-step module.
The previous finite-difference audit was read and its negative provider judgment
is retained. Source names and positions are in
[source-inventory-017.md](source-inventory-017.md).

## 1. Identities already present

CosmicDifferenceKernel already defines delta and cosmicKernel.
CosmicDerivativePower.sub_pow_eq_u_mul_powerKernel,
cosmicKernel_pow_eq_powerKernel_of_ne_zero and
CosmicFormulaDerivativeBridge.delta_pow_two_eq_u_mul_powerKernel_two already
connect power differences to their normalized kernel. The unit specialization
already reproduces the square gnomon. No delta, power kernel or derivative API
was reimplemented. No limiting argument is used.

SquareGnomon.core_add_squareGnomon_eq_next_square and
squareGnomon_eq_mul_two_mul_add already expose the degree-two normal form.
QuadraticCenteredBridge adds only four algebraic adapters:

- quadratic_forward_factor, over a commutative ring: forward = h*(2*x+h).
- quadratic_forward_backward: forward = 2*h*x+h^2; backward = 2*h*x-h^2.
- quadratic_forward_div, over a field and h nonzero: forward/h = 2*x+h.
- quadratic_centered_half, over a characteristic-zero field: centered = 2*h*x.

These are category A. The rational steps 1, 1/2, 1/4 and 1/8 are kernel-calibrated.
SquareGnomon already imports Mathlib; the generic adapter reuses that dependency
outside the Legendre facade. No Real or analysis import was added to any new
Legendre source. The new norm module uses finite-field arithmetic from
Mathlib.NumberTheory.LegendreSymbol.Basic for its mod-four theorem.

## 2. Denominator-free half-lattice theorem

centered_doubled_square_difference proves, for every integer n:

    (2*n+1)^2 - (2*n-1)^2 = 8*n

centered_doubled_square_difference_nat proves the same equation for natural
n>0. This positivity hypothesis is necessary: at n=0, Nat truncation gives
1, whereas the right side is 0. The integer identity at n=0 gives 0 correctly.
centered_doubled_square_difference_div_four proves exact Nat division:

    ((2*n+1)^2 - (2*n-1)^2)/4 = 2*n, for n>0.

The scaled identity represents the width between squares at n-1/2 and n+1/2.
Its arithmetic content is algebraic geometry, category B.

## 3. Centered window and the ordinary open shell

centered_window_translation proves for every natural n,m:

    m in Icc(n^2-n+1, n^2+n) iff SquareCell n (m+n).

centered_window_card proves this interval has exactly 2*n elements, including
an empty interval at n=0. Translation by n matches both endpoints with the
ordinary shell n^2+1 through n^2+2*n. The midpoint of the centered interval
is n^2+1/2; the ordinary shell midpoint is n^2+n+1/2.

This is a geometric translation, not preservation of prime divisibility.
The smallest bounded old-prime counterexample is n=3,m=7,p=2:
7 translates to 10; 2 does not divide 7 but divides 10. Membership and this
failure are kernel-calibrated in translation_divisibility_counterexample.

## 4. Exact fold involution

squareOffsetFold n r is 2*n+1-r. On squareOffsets n it preserves membership,
is involutive, has no fixed point, and satisfies r+fold(r)=2*n+1.
Each orbit {r,fold(r)} has cardinality two. These statements use valid shell
membership explicitly; the total Nat subtraction function outside the shell
is not asserted to be an involution. This package is category B.

## 5. Existing CenteredPair as canonical coordinates

For j<n, centeredLeftOffset n j=n-j and centeredRightOffset n j=n+1+j are
fold partners. centeredFoldPair is their unordered two-seat Finset.
The image of range n under centeredFoldPair has cardinality n.

squareOffsetFold_pair_index gives a unique j for every valid seat orbit;
centeredFoldPair_injective proves index injection; centeredFoldPair_disjoint
proves distinct pairs are disjoint; centeredFoldPairs_union proves their
union is squareOffsets n. Thus the index-to-pair image is a bijection without
a quotient type. Existing CenteredPair coordinates and arithmetic are retained.

## 6. Exact internal odd gaps

centeredPoint_difference already gives the complete-point difference 2*j+1.
centered_offset_difference exposes the corresponding offset difference.
centeredInternalGaps_eq_odd_interval and centeredInternalGaps_card identify
its image with the odd members of Icc(1,2*n-1), of cardinality n.
At n=0 both carriers are empty. The quantities must remain distinct:

- Outer gnomon at n: 2*n+1.
- Open shell width: 2*n.
- Internal gaps: 1,3,...,2*n-1.
- Next outer gnomon: 2*n+3.

The regression reuses square_add_oddGnomon and oddGnomon_succ for the unit
forward difference and plus-two growth. It also kernel-checks
(n+2)^2+n^2=2*(n+1)^2+2. Constant curvature alone is not a Legendre provider.

## 7. Degree-two GN interpretation

centered_gap_eq_GTail reuses Gnomon.CosmicBridge.oddGnomon_eq_GTail_two_one_unit:

    rightOffset-leftOffset = oddGnomon j = GTail 2 1 1 j = 2*j+1.

These are literally the same natural number at the reparameterized index j.
The normalized unit forward square difference at x=j also equals 2*j+1.
For arbitrary square endpoints A,B, the factorization
A^2-B^2=(A-B)*(A+B) instead identifies the normalized degree-two coefficient
with A+B. Setting A=j+1 and B=j recovers 2*j+1.

It does not follow that the squares of the actual complete pair points have
difference 2*j+1: their square difference has the additional factor equal to
the sum of those points. In this checkpoint that sum is centeredFoldNorm n.
No prime-distribution content is claimed for a GN identification alone.
The Legendre adapter is category A.

## 8. Canonical owner constraint and common support

The requested conditional theorem centered_same_owner_dvd_gap follows from
centeredCommonDivisor_iff and the existing owner packet. Under cover on both
seats and equal least owners, that owner divides 2*j+1.

There is a stronger elementary fact: squareOffsetFold_owner_ne proves that
the two total minFac owners always differ, even without cover assumptions.
The sum of the complete points is odd, so one point is even and has owner 2;
the other is odd and has owner different from 2. Consequently every actual
same-covered-owner fiber is empty. The same-owner divisibility implication
is valid but vacuous for canonical least owners. No same-owner example exists.
This is category A as a consequence of the existing parity/least-owner API.

Distinct least owners do not imply disjoint common support. The first shared
old support in the bounded scan is n=6,j=2: points 40,45; gap 5; owners 2,3;
common old prime 5. six_shared_support and distinct_owner_does_not_imply_disjoint
kernel-check the example. The first scanned failure of the reverse rule
"left least owner divides gap implies equal owners" is n=8,j=7: points 65,80;
gap 15; owners 5,2. eight_reverse_owner_counterexample checks it.
Smallest means ascending anchor then pair index within the recorded finite scan;
these records are not a universal minimality theorem.

For prime gap 2*j+1>n, centered_prime_gap_support_packet reuses the existing
disjoint support theorem. The n=3,j=2 calibration gives points 10,15 and gap 5.
Its old supports are disjoint although gcd(10,15)=5, a fresh prime above 3.
The OldSupportGcd fresh-prime alternative is preserved.

The separate common-support bridge is the nontrivial addition. Define:

    N_n = centeredFoldNorm n = n^2+(n+1)^2 = 2*n*(n+1)+1.
    L = n^2+n-j; R = n^2+n+1+j; g_j = 2*j+1.
    L+R=N_n; R-L=g_j; N_n=2*L+g_j.

mem_common_centered_support_iff_norm_and_gap proves, for j<n:

    p in support(L) and support(R)
    iff p.Prime and p<=n and p divides N_n and p divides g_j.

The reverse direction cancels 2 using primality and the odd norm; it is an
exact equivalence, not only a necessary divisibility condition. Moreover
prime_dvd_centeredFoldNorm_mod_four proves every prime divisor of N_n is 1 mod 4.
The consecutive coordinates are coprime, so a prime dividing this norm yields
a nonzero solution to a square equaling the negative of another square in ZMod p.
The finite-field mod-four lemma excludes 3 mod 4; parity excludes 2.
This is a category C application bridge, not a new general theorem about sums
of squares and not a restriction on every individual owner.

## 9. Exact per-prime capacity

centeredOwnerGapCapacityIndices aliases the existing lowerPrimeAddressOffsets
p 0 n. Its members are exactly j<n with p dividing 2*j+1. No duplicate
progression abstraction is introduced. For odd prime p:

    j mod p = (p-1)/2;
    card = floor((n+(p-1)/2)/p).

For p=2 the carrier is empty. The exact cardinality is proved by a bijection
j=(p-1)/2+k*p with k in the appropriate finite range.
Actual same-owner indices embed into the gap capacity, but their cardinality
is zero. The floor count is a potential common-prime address count, not a
positive count of same least owners. Its new counted interface is category C,
without category D obstruction content.

The norm bridge gives a sharper exact actual common-support formula:

    centeredCommonSupportIndices n p
      = gapCapacity n p, if p<=n and p divides N_n;
      = empty, otherwise.

For odd prime p its card is the same floor expression when activated, otherwise
zero. Only primes 1 mod 4 can be activated. This distinguishes actual common
support from both potential support and the always-empty same-owner fiber.

## 10. Sum of capacities and full cover

centeredSameOwnerIndices_sum proves the canonical same-owner sum is zero.
Under full cover, centeredDifferentOwnerIndices equals range n and has card n.
This is an exact but tautological consequence of parity and full cover; it
does not contradict any proved capacity.

The raw potential capacity sum counts incidences with gap prime divisors;
it can overlap at a pair. It already exceeds n at n=29 (31 versus 29),
n=297 (448 versus 297) and n=1031 (1752 versus 1031). No inclusion-exclusion
or raw sum has been mistaken for a disjoint canonical partition.
The norm-filtered common-support sum is also a support-incidence sum, not a
least-owner partition, and cannot be charged as if every covered pair must
have shared support. A fully covered pair can have disjoint old supports.
There is no new full-cover capacity obstruction.

Diagnostics factor every point independently for all natural anchors 1..300
and extra anchor 1031. Instruction 016 JSON supplies only survivor comparison;
it is not used to supply current factorization, colors or supports.
Full colors, prime fibers, capacity ratios and forced-prime-gap lists are in
[discovery-017.json](evidence/MANIFEST.md#log-7e873d3d844038ff). The prime list reaches 2100,
so all internal prime gaps up to 2061 at anchor 1031 are covered.

| n | pairs | same covered owners | different covered owners | one covered seat | potential capacity sum | common support incidences |
|---|---|---|---|---|---|---|
| 5 | 5 | 0 | 3 | 2 | 3 | 0 |
| 8 | 8 | 0 | 4 | 4 | 6 | 2 |
| 11 | 11 | 0 | 7 | 4 | 9 | 2 |
| 19 | 19 | 0 | 13 | 6 | 18 | 0 |
| 29 | 29 | 0 | 21 | 8 | 31 | 0 |
| 297 | 297 | 0 | 252 | 45 | 448 | 0 |
| 1031 | 1031 | 0 | 871 | 160 | 1752 | 223 |

All pairs have different total minFac owners, including pairs with an escaping
seat. Here "different covered owners" requires both seats covered. The ratio
of actual same-owner count to positive potential capacity is zero; when the
capacity is zero the diagnostic records an undefined ratio, not a division
by zero. There are no same-owner gaps to enumerate. The full JSON records
forced prime-gap pairs individually. No asymptotic conclusion follows.

At n=297 the norm is prime 177013 above the old bound, and
near_miss_297_common_empty kernel-proves every common-support fiber empty.
At n=1031 the diagnostic factorization is 5*61*6977; activated old-prime
counts 206 and 17 are independently kernel-proved by norm1031_support_counts.
The full 223 census and all listed coloring counts remain Python diagnostics.
The inherited 1031 non-cover, at-least-18 survivor certificate and prime endpoint
are reused in preserved1031; they are not a new uniform conclusion.

## 11. Combining fold and successor restrictions

Let F_n be squareOffsetFold and T_n be successorThresholdInsert. The exact
map relation is noncommuting:

    F_(n+1)(T_n(r)) = T_n(F_n(r)) + 1.

The smallest positive-anchor mismatch is n=1,r=1: 4 versus 3.
fold_successor_common_divisor_iff says the corresponding complete points
at anchor n+1 have a common divisor q iff q=1.
fold_successor_support_disjoint derives disjoint bounded supports at these
adjacent path endpoints. This is an adjacent-point consequence, category A.
fold_lower_successor_owner_packet combines the within-shell and 016 lower-channel
least-owner changes under their explicit covered-seat hypotheses.

There is no local contradiction. compatible_covered_trajectory kernel-checks
one covered trajectory at n=13,r=6:

    old seat 6: point 175, owner 5.
    old folded seat 21: point 190, owner 2.
    inserted seat 6 at n=14: point 202, owner 2.
    fold-after-insert seat 23: point 219, owner 3.
    insert-after-fold seat 22: point 218, owner 2.

Every displayed seat is covered. All owner inequalities and the path-endpoint
support disjointness can hold together. This example certifies compatibility
of local constraints; it does not exhibit a fully covered shell.

A different category C cross-shell statement is now proved:

    Nat.Coprime N_n N_(n+1).

Their difference is 4*(n+1). A common prime would divide 4 or n+1. The first
case contradicts the odd norm; the second forces it to divide consecutive
integers n,n+1. common_centered_support_no_successor therefore forbids any
prime from being shared by a fold pair at n and also a fold pair at n+1,
for arbitrary pair indices. This is stronger than a selected trajectory
statement about common support, but it does not constrain all individual
owners or forbid full cover with changing support.

## 12. Arithmetic advance versus normalization

The geometry and GN identification alone are category B/A normalization.
The least-owner consequences are category A elementary consequences of the
016 parity/owner API. No same-owner obstruction survives the parity audit.
The new norm-and-gap support dictionary, exact activated fibers, mod-four
restriction and consecutive norm coprimality are category C interfaces.
They reach beyond an offset coordinate change by using primitive norm
arithmetic and an exact common-support equivalence. No theorem is category D.

Every new theorem, definition and calibration is classified individually in
[declaration-classification-017.md](declaration-classification-017.md), and
[declaration-coverage-017.json](evidence/MANIFEST.md#log-6ad638207d253912) is the exact
source manifest. There are 66 production declarations: 24 category A,
33 category B and 9 category C. Kernel calibration declarations are listed
separately as category A applications or explicit numeral counterexamples.
The source comparison includes CenteredPair, OldSupportGcd, support-capacity
and residue-owner APIs; no previous exact fold-norm interface was found in
the audited repository. C denotes a new application interface, not a claim
that the elementary number theory is new to mathematics.

Build, axiom, forbidden-token, header and whitespace evidence is recorded in
[validation-017.md](validation-017.md). All new production declarations are
free of sorryAx. Legendre, CosmicFormula and the DkMath root build succeeded.
No Legendre, PNT, RH, Bertrand, Jacobsthal or analytic-sieve theorem is claimed.

## 13. Single next theorem contract and implementation proposal

The next contract is the full gcd normal form, not a prime-existence provider:

    centeredPair_gcd_eq_norm_gap {n j : Nat} (hj : j<n):
      Nat.gcd (n^2+centeredLeftOffset n j)
              (n^2+centeredRightOffset n j)
      = Nat.gcd (centeredFoldNorm n) (2*j+1).

This is proposed, not implemented or counted as a current theorem.
It would upgrade the current prime-support equivalence to exact multiplicities
and retain the fresh-prime branch above n. It neither assumes nor concludes
failure of full cover. The present results do not supply an exact uniform
prime provider; this is a bounded arithmetic next step whose statement does
not hide Legendre as an assumption or conclusion.

Implement it in CenteredFoldSupportNorm using centeredPoint_difference to
replace gcd(L,R) by gcd(L,gap), then N=2*L+gap and oddness of gap to cancel 2
from the gcd. Prefer existing Nat gcd addition/multiplication and coprimality
lemmas to a new valuation theory. The regression acceptance set should include
j=0 (gap 1), n=3,j=2 (fresh gcd 5), n=6,j=2 (old gcd 5), and a repeated-prime
common divisor case. Validate its entire public dependency closure by focused
build and axiom audit before exposing any valuation corollary.

The mathematical purpose is to determine whether retaining common-support
multiplicity creates a useful input to the existing exact census, rather than
calling the coordinate normalization or a zero least-owner count a provider.
No uniform contradiction is currently obtained.

Outcome B - CENTERED FOLD PRODUCES A NEW EXACT ARITHMETIC BRIDGE
