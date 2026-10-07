# Report 034 - Three-prime witness and factor-depth stopping decision

Ordered prime triples now supply a collision-safe lower witness disjoint from
the semiprime image. Repeated factors are handled by unique factorization of
sorted prime lists. The combined mass D3 is certified below E, and one new
envelope preserves the exact ledger. It deletes the whole {343,539} residual
at n=32, kernel checked. Diagnostics recover the failed 033 anchors 210,297,
1031, but still fail at 5000. The finite gain is substantial; unbounded
factor-depth continuation would approach exact factor classification rather
than a new quantitative estimate. The stopping decision is to retain this
bounded layer and seek aggregate weighted residual control, without adding
four/five-factor enumerators automatically. The result is Outcome B.

## Implementation and source reuse

Added [GnomonCofactorThreePrime](../../../DkMath/NumberTheory/Legendre/GnomonCofactorThreePrime.lean)
and one export in the [Legendre facade](../../../DkMath/NumberTheory/Legendre.lean).
The module has 15 public declarations: five definitions and ten theorems.
Two private proof helpers extract triple facts and transport unique prime
factorization between lists. Direct imports are GnomonCofactorSemiprime,
Mathlib.Data.Nat.Factors and Mathlib.Data.List.Sort. Earlier production modules
are inspected/reused without edits. Unified headers and the immediate file
print marker are preserved. No general factor-depth hierarchy is introduced.

[Source inventory](source-inventory-034.md) records the inspected roughTriple,
strict support-wave, quotient, prime-list and sorted-list APIs. The strict
active-label triple receivers exclude repetitions and have different carrier
hypotheses. Endpoint enumeration plus the existing factorization receivers
therefore provides a smaller compatible implementation.
[Findings](findings-034.md) records the quantitative stopping decision.
[Calibration](../../../DkMathTest/NumberTheory/GnomonCofactorThreePrimeCalibration.lean)
contains nine named public checks; the
[axiom audit](../../../DkMathTest/NumberTheory/GnomonCofactorThreePrimeAxiomAudit.lean)
covers all 24 new named public declarations.

## Actual ordered carrier

For each k in Icc(2,n-1), let A=max(n^2/k,2*n), B=(n^2+2*n)/k using
natural floor quotients, and M=finitePrimeBasisProduct S. The carrier enumerates

 r prime, 2<=r<=sqrt(B), r^3<=B, gcd(r,M)=1;
 s prime, r<=s<=sqrt(B/r), gcd(s,M)=1;
 t prime, max(s,A/(r*s)+1)<=t<=B/(r*s), gcd(t,M)=1.

Thus r<=s<=t and A<r*s*t<=B. Weak ordering is essential for cubes and
repeated factors. The first two cutoffs express necessary endpoint geometry
for an ordered triple, rather than an extra rough-support assumption.
The exact complementary interval follows from positive natural division.
Every product survives the wheel and is composite, since r*s and t are
nonunits. Neither the actual composite filter, target minFac, Q nor carry-event
membership defines this carrier. Factor primality is used only as the finite
endpoint witness condition. Target factorization is used in diagnostics to
audit residuals, not to construct the witness.

## Product uniqueness, repetitions and semiprime interaction

For two equal products, Nat.primeFactorsList_unique gives a permutation
between the two three-element prime lists. Both are weakly ordered, so
List.Perm.eq_of_pairwise' forces list equality and therefore equality of all
three tuple coordinates. This proves product injectivity, including repeated
factors; no squarefree hypothesis is needed.

A semiprime product similarly gives a two-element prime list. If it equaled
a triple product, unique factorization would give a permutation between a
list of length two and one of length three. List.Perm.length_eq contradicts
that equality. The product images are therefore disjoint, kernel proved.

Let T3 be the log weight of the triple product image, and let D be the 033
semiprime mass. The combined witness is their distinct product union. The
sum_union and injective sum_image theorems prove exactly

 D3 = D + T3,             D3<=E.

No product is double charged. Squares already present in D remain included
once, and triple products add genuinely new certainly-composite mass. The
factorization theorem is a proof receiver; no complete factorization function
is used in the witness definition.

## One corrected envelope and exact budget effect

Write Z for the 033 semiprime envelope, and define

 Y=min(Z,V-D3).

For n>=3 and a basis consisting of primes at most 2*n, the kernel proves

 Q<=Y<=Z,                Y-Q=min(Z-Q,E-D3).

Y<=Z itself is unconditional. E-D3 is nonnegative because D3<=E. This is a
valid lower-mass deletion, retaining the 032 orientation warning: an upper
bound on E is not subtracted as removable mass.

The exact old ledger remains oldBudget=H+S_small+R+Q. Every higher-shell,
small-carry and repeated-carry term is retained, and the exact substitution is

 S_small+R+Y+H=oldBudget+(Y-Q).

The new conditional consumer accepts S_small+R+Y+H<log(cell), with n>=3 and
an admissible basis, then proves a prime exists in SquareCell. Since Y>=Q,
it is still at least the exact old ledger. Recovering a failed independent
envelope does not establish a new unconditional range beyond that ledger.
No universal strict premise is proved. At n=3, Y=Z is kernel checked, so
strict improvement at every admissible anchor is false.

## Required finite calibration

The entire combined carrier equals the actual surviving composite carrier
in every window at n in {9,12,31,32}, kernel checked. Hence D3=E and Y=Q
at these anchors, also kernel checked. These are calibration equalities,
not the definition of the witness or a global classification claim.

49 and 77 from n=9 and n=12 remain the prior semiprime witnesses; no additional
triple mass is needed there. The n=31 strict consumer is preserved by Y<=Z.
At n=32 the full triple carrier is exactly {(7,7,11)} in k=2 and {(7,7,7)}
in k=3, with every other triple window empty. Their products are 539 and
343, both kernel checked. The ambiguity 539=7*77=11*49 from the raw factor
cover is replaced by the single sorted prime triple (7,7,11). The cube
343 has the single ordered tuple (7,7,7). The new triple mass is
log(539)+log(343), about 12.127446, and the combined residual vanishes.

An exact integer product inequality at 32, residual*sieveProduct <
cell*combinedProduct, yields a kernel strict consumer by log monotonicity.
Its diagnostic margin is about 62.639084, compared with about 50.511638
for 033. This is a finite gain within the existing exact-ledger scope.

A further kernel regression fixes the survivor 2401=7^4 at n=69,k=2 and
proves it is absent from the combined witness. Thus the definition has not
collapsed into the complete composite carrier. Its diagnostic residual is
log(2401), about 7.783641, and the consumer still passes numerically there.
No kernel claim of global residual classification by factor count is made.

## Quantitative stopping test

[Diagnostics](logs/diagnostics-034.json) retains 300 rows: every n=3..300,
plus 1031 and 5000, with 15 direct anchor reconstructions. The 033
and 031 source digests are checked. Ordered triple products are independently
reconstructed, tested for injection, disjointness from semiprimes, and inclusion
in the composite carrier. All log weights and margins are floating diagnostics
only, never Lean premises.

| n | E-D from 033 approx | Triple mass approx | E-D3 approx | New consumer margin approx |
| --- | --- | --- | --- | --- |
| 3 | 0.000000 | 0.000000 | 0.000000 | 4.962845 |
| 9 | 0.000000 | 0.000000 | 0.000000 | 13.482188 |
| 12 | 0.000000 | 0.000000 | 0.000000 | 25.289216 |
| 31 | 0.000000 | 0.000000 | 0.000000 | 69.023587 |
| 32 | 12.127446 | 12.127446 | 0.000000 | 62.639084 |
| 69 | 35.484937 | 27.701297 | 7.783641 | 102.473447 |
| 210 | 428.038020 | 398.425570 | 29.612450 | 376.935533 |
| 297 | 699.205940 | 659.127698 | 40.078242 | 472.514475 |
| 1031 | 6266.644524 | 5506.500569 | 760.143955 | 1460.260321 |
| 5000 | 65561.859242 | 53563.881327 | 11997.977915 | -1555.778583 |

At n=210, the previous 033 residual about 428.038020 is reduced by about
398.425570 to 29.612450. The previous margin about -21.490037 becomes
about 376.935533. At 297, the remaining error falls from about 699.205940
to 40.078242; the new margin is about 472.514475. At 1031, the remaining
6266.644524 falls to 760.143955; the new margin is about 1460.260321.
These recoveries are diagnostic, not kernel-certified large-anchor inequalities.

At 5000, 4023 triple products supply about 53563.881327 of additional log
weight. The combined mass is about 169268.279864 of E's 181266.257779.
There are still 854 unremoved composite slots, with weight about 11997.977915,
exceeding the exact-ledger margin about 10442.199332. The new consumer margin
is about -1555.778583. This is a sampled numerical failure, not a kernel
counterexample to a universal theorem. Every n=3..300 and the retained 1031
passes numerically; the gap from 301 to 4999 is not fully tested. In particular
5000 is not claimed to be the first failure across all integers.

The three-prime layer therefore changes the retained frontier materially,
rather than adding negligible mass. It remains an independent finite witness
with missing products, as the 7^4 regression demonstrates. Nevertheless
continuing all factor depths would eventually reproduce E exactly and hence
Q, which is classification rather than a distribution estimate. The stopping
decision is to keep this bounded layer, stop automatic depth enumeration,
and require an aggregate quantitative provider before further production work.
This is a research-route decision, not a theorem that every deeper finite
experiment or elementary method is useless.

## Validation

Focused, Legendre facade, DkMath root and complete public axiom builds all
passed with LEAN_NUM_THREADS=2. Focused and axiom builds have no warnings.
Facade/root replay the inherited PacketCross unused-variable warning; root
also replays five inherited sorry warnings in unrelated modules whose sources
were not edited. No repository-wide absence-of-sorry claim is made.

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 7.704 | 963240 | 3 | 32429 | 0 |
| facade | 0 | 12.916 | 6747264 | 0 | 197544 | 0 |
| root | 0 | 14.029 | 7110348 | 0 | 204571 | 0 |
| axiom-audit | 0 | 13.114 | 6692328 | 0 | 199089 | 0 |

GNU time measures Lake and waited descendants. Peak RSS is process telemetry,
not a sum of concurrent allocations. No build memory failure or swap occurred.
All 15 production and nine calibration declarations have only propext,
Classical.choice and Quot.sound, with no sorryAx in that checked scope. The
two private production helpers and private calibration helpers are covered
transitively. Large finite product checks have documented scoped recursion
and heartbeat allowances and use the proved fast_choose identity, without
native evaluation axioms. Header, file-marker, forbidden-construct, import,
whitespace, source-digest, diagnostic, ASCII and Markdown-link audits passed.
Exact evidence is retained in [validation](validation-034.md).

## Next natural frontier and implementation proposal

The remaining cofactor-window problem is a useful aggregate weighted estimate
for the carrier after semiprime/triple deletion. In the exact error coordinates
closure needs min(Z-Q,E-D3)<log(cell)-oldBudget; independently the consumer
requires V-D3 or a smaller valid envelope below log(cell)-S_small-R-H.
A raw upper bound on the higher-composite error alone cannot be subtracted
with the wrong orientation to obtain a better upper bound for Q.

A bounded next investigation should compare an endpoint/residue-based upper
estimate for the corrected carrier, or an independently certified lower
composite-mass provider with controlled total error, against the retained
69,210,297,1031,5000 margins. Grouping the residual by roughness and endpoint
geometry may support an aggregate inequality, but its multiplicity and boundary
errors must be proved. The 2401 survivor should remain a regression. Do not
create four-prime, five-prime and deeper carrier APIs merely to enumerate the
missing inventory. Promote further code only if it contributes a quantitative
estimate distinct from complete target factorization.

No PNT, RH or unproved short-interval theorem is used, and no proof that
analytic prime-distribution input is unavoidable has been obtained. The
remaining weighted short-window control is an identified missing estimate.
No later checkpoint architecture or unbounded hierarchy is prescribed.

Outcome B - THREE-PRIME CORRECTION WITH A FACTOR-DEPTH STOPPING BOUNDARY
