# Report 028 - Divisor incidence and binary carry cancellation

The required finite bridges and cancellation identities are proved for n>=3:

 log(cell) = shell VM + low carry mass
 old Pascal budget = higher correction + low carry mass.

This is an exact coordinate for the existing frontier. No new universal upper
bound on total carry mass or universal shell lower provider is obtained.
Individual large labels have unique shell multiples, but their map is not
injective. Colliding large prime-power labels necessarily have the same base.

Production and validation surface:

- [Neutral DivisorIncidence](../../../DkMath/NumberTheory/DivisorIncidence.lean)
- [GnomonDivisorCarry](../../../DkMath/NumberTheory/Legendre/GnomonDivisorCarry.lean)
- [Updated facade](../../../DkMath/NumberTheory/Legendre.lean)
- [Kernel calibration](../../../DkMathTest/NumberTheory/GnomonDivisorCarryCalibration.lean)
- [Complete axiom audit](../../../DkMathTest/NumberTheory/GnomonDivisorCarryAxiomAudit.lean)
- [Source inventory](source-inventory-028.md), [findings](findings-028.md), [validation](validation-028.md).

Write base=n^2, width=2*n and top=base+width. All divisions in counts are
natural divisions, and every displayed logarithm is a natural logarithm.

## 1. Exact shell multiple-count function

GnomonShellMultipleCount, spelled gnomonShellMultipleCount in Lean, is
 top/d-base/d as a Nat subtraction. Its total value at d=0 is zero.
Arithmetic counting statements explicitly assume d>0.

## 2. Exact counting proof

Yes. gnomonShellMultipleCount_eq_card identifies this number with the card
of (Icc(base+1,top)).filter(d divides m). The neutral prefix proof reuses
Nat.Ioc_filter_dvd_card_eq_div; subtraction of nested finite prefix carriers
proves the arbitrary-shell count. There is no floating count or heuristic.

## 3. Finite divisor-incidence transpose

Yes. sum_shell_divisors_eq_floor handles an arbitrary real weight. Positive
m has exactly the divisors in Icc(1,top) that divide m. Finset.sum_comm and
the exact filter card yield the weighted floor sum. gnomonShell_divisor_incidence
instantiates this with von Mangoldt, in the requested n>=1 domain.

## 4. Exact log shell-product identity

Yes. vonMangoldt_sum expands every log(m). Real.log_prod applies because all
shell factors are positive. gnomonShell_log_prod_eq_divisor_mass retains the
full divisor interval through top and every multiplicity. The neutral theorem
also covers empty shells; no estimate of psi is imported into this argument.

## 5. Cell/factorial to VM/lower-divisor bridge

Yes. gnomonPascalCell_mul_factorial_eq_shell_prod reindexes the existing product.
Logs first give log(cell)+log(width factorial)=sum_shell log(m). For n>=3,
each base<d<=top has top<2*d and multiple count one. Splitting the full
carrier proves the required
 gnomonPascalCell_log_add_factorial_eq_shellVM_add_lowerDivisorMass.
The lower mass is nonnegative but no smallness estimate is inferred.

## 6. Generic factorial floor identity

Yes. log_factorial_eq_floor states
 log(N factorial)=sum over Icc(1,N) of (N/d)*Lambda(d), including N=0.
Its proof is the neutral base-zero incidence result and the factorial product.
log_factorial_eq_floor_cutoff allows any B>=N, since all extra quotients vanish.
No second proof through factorization was added.

## 7. Exact binary carry bit

For d>0, gnomonLowDivisorCarryBit n d is one exactly when
 d<=base%d+width%d, and zero otherwise. The total zero-divisor convention is
zero. The binary and at-most-one theorems include that convention.

## 8. Multiple count decomposition

Yes. gnomonShellMultipleCount_eq_div_add_carry states
 multipleCount=width/d+carryBit for d>0, directly from Nat.add_div and natural
subtraction cancellation. Explicit Nat casts prevent replacing floor quotients
by real division.

## 9. Exact remainder-phase condition

Yes. The positive-divisor one iff and zero iff theorems state the crossing
predicate and its strict reverse. This is a single Nat bit API; no parallel
Bool coordinate or redundant valuation framework was introduced.

## 10. Next-multiple gap

nextMultipleGap(base,d) is d-base%d for d>0 and zero for d=0. If the boundary
is aligned, its gap is d, because the next multiple is strictly later.
Carry one iff gap<=width%d is proved. If d>width, width%d=width, so it is
exactly gap<=width. No square endpoint or next-square point is included.

## 11. Lower mass equals factorial log plus carry mass

Yes. gnomonPascalLowerDivisorMass_eq_factorial_add_carry uses width<=base
for n>=3, the extended factorial cutoff, and the pointwise floor decomposition.
All uniform factorial contribution is exposed before cancellation.

## 12. Central cancellation

Yes. gnomonPascalCell_log_eq_shellVM_add_lowCarryMass cancels the common
factorial log over the reals. The resulting residual is exactly binary
lower-prime-power phase mass. This equality alone asserts no lower bound.

## 13. Exact old Pascal comparison

Yes. gnomonPascalOldLogBudget_eq_higher_add_lowCarryMass is subtraction-free.
It combines the existing old plus birth and VM equals birth plus higher
identities with the central theorem. Thus K is precisely the old budget with
the already-small higher correction removed; it is not independent information.

## 14. Prime-power event support

Yes. gnomonPascalLowCarryEvents filters Icc(1,base) by IsPrimePow and bit one.
Exact membership and low mass equals sum of Lambda on these events are proved.
Each label p^a has weight log(p), justified symbolically by vonMangoldt_apply_pow.
The bit does not retain full valuation height; distinct powers remain labels.

## 15. Agreement with choose carries

The pointwise prime-power theorem uses the same predicate as
GnomonPascalCell_factorization_carries, spelled gnomonPascalCell_factorization_carries
in Lean, after commuting the two remainders. The sum-level old comparison
accounts exactly for old labels plus higher shell powers. No additional
per-prime old-height theorem was forced. In diagnostics, every prime-coordinate
choose height was independently reconstructed by factorial floor valuations.

## 16. Small/large band decomposition

The two finite carriers filter the low events at d<=width and width<d.
Their masses sum exactly to K and feed a band-wise conditional margin provider.
Small labels keep width%d; large labels use the full width and a unique grid
hit. In the scan n=3..5000, small mass is at most 45.2681 percent of K, at n=3,
and as low as 4.9460 percent, at n=4576. The large band dominates in this finite
range; this is diagnostic evidence, not a universal theorem about dominance.

## 17. Unique large shell multiple and cofactor

Yes. gnomonNextShellMultiple n d=d*(base/d+1). The packet proves SquareCell
membership and divisibility under d>width and bit one. The uniqueness theorem
quantifies all other divisible shell integers. The cofactor base/d+1<n is
proved for every n>=3 and d>width, even before imposing the event predicate.
The distinct-base exclusion theorem shows two large prime-power divisors of
one shell integer share a prime base: otherwise their coprime product exceeds
top while dividing that integer. This does not exclude same-base chains.

## 18. Failure of label-map injectivity

No. The smallest positive-anchor collision is n=11:
 32=2^5 and 64=2^6 both map to 128.
The exact carrier memberships, images and failure of InjOn are kernel checked.
A finite kernel certificate proves all earlier positive anchors 1..10 have
injective large-label maps. General collision iff shared divisible shell
integer is proved. The largest finite multiplicity is ten at n=2896; its image
2^23 has old large labels 2^13 through 2^22. This latter complete scan result
is an integer diagnostic, not a newly added kernel certificate.

## 19. Relation of the conditional prime criteria

The carry/log-log criterion is proved exactly equivalent to
 log-log budget<shell VM, namely the existing 027 sufficient condition.
It implies the old strict criterion, but its equivalence to that old criterion
is not proved. Algebraically it requires
 birth mass>log-log budget-higher correction,
whereas oldBudget<log(cell) requires only birth mass>0. The margin difference
is nonnegative by 027. Replacing the upper budget by the exact higher correction
gives a proved exact equivalence with the old criterion. No actual anchor
counterexample to the fixed log-log converse is asserted; no converse provider
or universal strict inequality was proved.

The generic consumer also accepts K<=B and B+margin<log(cell), concluding
margin<VM. Multiplicative growth gives (base+1)^width<=cell*width factorial,
and its log form gives width*log(base+1)<=log(cell)+log(width factorial).
Any derived VM bound must still subtract K. Product growth alone supplies no
shell-prime theorem.

## 20. Diagnostics and the 297/1031 anchors

[Full data](logs/diagnostics-028.jsonl) record all n=1..5000; the
[summary](logs/diagnostics-summary-028.json) gives explicit mandatory-anchor
labels, bases, depths and complete large-image distributions. Prime labels
are losslessly encoded by prefix-summed positive deltas; each decoded prime
has base equal to its label and depth one. Higher-power triples explicitly
record label, base and depth. The image rule reconstructs every shell multiple;
each row also records its exact multiplicity histogram and maximum.

Route A factors every shell integer and enumerates its prime-power divisors.
Route B reconstructs all binary power carries by floor division. Candidate
prime support is complete because a carry implies a positive shell multiple
count. Choose heights are separately checked through factorial floor sums.
Both integer ledger identities hold at every n>=3. The n=1 central flag is
false outside this domain; n=2 happens to satisfy it. All logs, residuals and
strict-provider flags are explicitly floating diagnostics. The old Pascal
budget here is the actual valuation budget, not the 026 log-count upper budget.

| n | low labels | small | large | low mass approx | VM approx | log cell approx | maximum fiber |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 3 | 2 | 1 | 1 | 3.555348 | 4.962845 | 8.518193 | 1 |
| 5 | 5 | 1 | 4 | 10.435115 | 8.593043 | 19.028158 | 1 |
| 11 | 13 | 1 | 12 | 37.131941 | 21.876424 | 59.008366 | 2 |
| 19 | 25 | 5 | 20 | 87.132456 | 35.660027 | 122.792484 | 2 |
| 29 | 39 | 7 | 32 | 157.991794 | 54.147116 | 212.138910 | 2 |
| 297 | 384 | 46 | 338 | 3049.641111 | 512.592717 | 3562.233828 | 1 |
| 1031 | 1304 | 144 | 1160 | 12716.333826 | 2220.404276 | 14936.738102 | 3 |

At 297, K=old budget approximately 3049.641111 and higher correction is zero.
The large mass is approximately 2832.887744; all 338 large images are distinct.
At 1031, K=old budget approximately 12716.333826 and correction is again zero.
The large mass is approximately 11833.466270, with 1160 labels on 1158 images.
The largest fiber there has three labels. Empty higher correction therefore
never means empty old carry mass. The mandatory anchors are all retained.

Kernel calibration proves complete carriers at 3,5,11 and selected small/large
packets at 297 and 1031, including every requested coordinate and universal
unique-multiple statements for large labels. Inherited complete higher-empty
certificates at 19,297,1031 yield symbolic zero-correction ledger identities.
No large real-log inequality is kernel evaluated. The floating log-log provider
comparison passed all n=3..5000; this is not universal evidence.

## 21. New bound, build evidence and remaining frontier

No new universal upper bound on total K was proved. Binary support, unique
multiples, small cofactors and same-base collisions are structural theorems.
The unresolved strict estimate is K+log-log budget<log(cell) for all relevant
anchors, equivalently the unresolved 027 shell VM lower comparison. No Legendre,
PNT, RH, or short-interval Chebyshev theorem is asserted.

All 57 new public production declarations and 32 new calibration declarations
are included in the 89-declaration axiom audit. Only propext, Classical.choice
and Quot.sound occur; there are no new sorryAx dependencies or forbidden proof
constructs. The neutral module has no application or RH dependency. Facade
export was added after focused validation passed.

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 7.985 | 964772 | 0 | 34836 | 0 |
| facade | 0 | 12.78 | 6741520 | 0 | 198913 | 0 |
| root | 0 | 13.111 | 7106900 | 0 | 208923 | 0 |
| axiom-audit | 0 | 12.287 | 6684028 | 0 | 197034 | 0 |

All four final invocations used LEAN_NUM_THREADS=2 and /usr/bin/time -v.
The final focused invocation replayed already compiled targets; its RSS is
therefore not a clean-compilation peak. Facade, root and axiom outputs retain
their actual compile/replay evidence. These are Lake and waited-descendant
process metrics, not total host memory. No observed OOM, kill, timeout or manual
termination occurred. Major faults and reported swaps were zero.
The facade retains the pre-existing PacketCross unused-variable warning.
Root additionally replays five pre-existing sorry warnings in unrelated files;
none is in the new declarations' dependency audit.

## 22. Exactly one theorem proposed for instruction 029

Attempt the large-band common-base fiber-cap theorem:

 K_large(n) <= sum over occupied large shell images m of
   (Nat.log p_m(base)-Nat.log p_m(width))*log(p_m), for n>=3.

Here p_m is the unique prime base of the large labels mapping to m, well-defined
by the proved distinct-base exclusion. The natural-logarithm notation log(p_m)
and the integer cutoff Nat.log p_m are deliberately different. The right weight
uses only the anchor, the prime base and the occupied image; it does not use
carry bits or actual image valuation height. It is an upper bound on possible
same-base powers, rather than another equality renaming K.

Implementation proposal: define the occupied image and choose its common base;
show each fiber's exponents inject into Icc(Nat.log p_m(width)+1,
Nat.log p_m(base)); count that finite interval and multiply by the nonnegative
base log; sum the fiber bounds. Existing unique-multiple and common-base
lemmas discharge geometry. Keep the image itself explicit instead of silently
assuming its card is the label count.

[Candidate diagnostics](logs/fiber-cap-028.json) show cap/large mass from
1 to approximately 1.079630 over n=3..5000. At 297 the ratio is approximately
1.006433, at 1031 approximately 1.003638, and at 5000 approximately 1.000935.
It accommodates the ten-label chain at 2896. These are diagnostic values only;
this proposed bound is not implemented in 028. Even proving it will still
require control of the occupied-image prime weights before it becomes a global
provider. No claim is made that this cap alone solves the strict margin.

Outcome B - BINARY CARRY MASS IS AN EXACT RECOORDINATION OF THE OLD FRONTIER
