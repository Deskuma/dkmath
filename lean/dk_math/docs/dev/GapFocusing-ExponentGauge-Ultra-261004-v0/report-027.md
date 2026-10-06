# Report 027 - Odd-depth reciprocal budget and logarithmic compression

The independent finite reciprocal bound and Mathlib harmonic compression are
proved. For n>=3, higher correction is bounded by the new log-log-style budget,
and that budget is proved no larger than instruction 026's log-count budget.
The strict shell-mass comparison remains a hypothesis in every prime provider.
No universal lower shell-mass theorem, Legendre conjecture, PNT, RH, or formal
asymptotic Big-O theorem is asserted.

Production surface:

- [Neutral OddReciprocal module](../../../DkMath/NumberTheory/OddReciprocal.lean)
- [Extended SquareShellPrimePowerGauge](../../../DkMath/NumberTheory/Legendre/SquareShellPrimePowerGauge.lean)
- [Kernel calibration](../../../DkMathTest/NumberTheory/SquareShellReciprocalCalibration.lean)

The existing Legendre facade already imports Gauge and therefore exports this
extension. Neither that facade nor DkMath.lean needed a source edit.
[Source inventory](source-inventory-027.md), [findings](findings-027.md), and
[validation](validation-027.md) record the scope and checked evidence.

Write top=n^2+2*n and L=Nat.log 2 ((n+1)^2) throughout this report.

## 1. Exact occupied-depth carrier

shellHigherPrimePowerDepths n is the Finset image of the exact higher-event
carrier under q mapped to q.factorization q.minFac. No inverse-event selection
or extra primality predicate is introduced.

## 2. Exact image and count

mem_shellHigherPrimePowerDepths proves membership iff there exists an event q
whose canonical depth equals the requested exponent. All occupied depths are
at least three, odd, and at most L. card_shellHigherPrimePowerDepths proves the
image card equals event card using the established canonical depth injection.
This is exact finite bookkeeping, not a scan-based uniqueness claim.

## 3. Admissible odd carrier

shellOddDepths n is (Icc 3 L).filter Odd. The occupied image is a subset of this
carrier. The latter is an exponent universe, with no primality encoding.
The two need not coincide: at n=11 the occupied set is {3,7}, whereas the
admissible set is {3,5,7}. This difference is kernel calibrated.

## 4. Exact log divided by depth

shellHigherPrimePower_weight_eq_log_div_depth proves exactly
Lambda(q)=log(q)/a for each higher event, with canonical a. It reuses the
existing log-depth packet and a>=3 to justify division. No approximation or
floating logarithm appears in its premises.

## 5. Pointwise top bound

For n>=3, shellHigherPrimePower_weight_le_top_log_div_depth proves
Lambda(q)<=log(top)/a. Shell membership yields q<=top, while prime-power
positivity and canonical depth positivity justify monotone log and division.
The primary bound uses the exact last shell integer top, not the next square.

## 6. Injective reindex

Starting from the exact sum of Lambda on events, the proof applies the
pointwise bound and Finset.sum_image with canonical depth injectivity.
The result is correction<=sum over occupied depths of log(top)/a. There is no
choice of an event inverse, and no multiplicity is lost.

## 7. Independent reciprocal budget

The occupied-depth subset and nonnegative upper weights permit filling all
admissible odd depths. Factoring the constant proves

 correction(n) <= log(top) * sum over odd a in Icc 3 L of 1/a.

shellOddDepthReciprocalSum and shellHigherPrimePowerReciprocalBudget name this
finite sum and budget. The acceptance theorem
 gnomonPascalShellHigherPrimePowerMass_le_reciprocalBudget
is independent of any harmonic approximation. The neutral harmonic module
is imported by Gauge, but this particular proof uses only finite sums, exact
weights, injection, subset inclusion, and positivity.

## 8. Harmonic compression

OddReciprocal proves the neutral subset bound against the reciprocal interval
Icc 2 L, the exact identity
 sum over Icc 2 L of 1/a = (harmonic L : Real)-1,
and odd_reciprocal_sum_le_log for L>=3.
The proof coerces Mathlib's rational harmonic sum via Rat.cast_sum, Rat.cast_inv,
and Rat.cast_natCast, then applies harmonic_le_one_add_log. No harmonic function
was reimplemented. The lower harmonic bound was audited but is unnecessary
for this upper compression.

## 9. Explicit compressed correction bound

shell_binary_depth_cutoff_ge_three proves L>=3 for n>=3.
shellHigherPrimePowerLogLogBudget n is exactly log(top)*log(L).
The production theorem proves the reciprocal budget is at most this budget,
and consequently

 correction(n) <= log(n^2+2*n) * log(Nat.log 2 ((n+1)^2)).

The optional geometric presentation also proves log(top)<2*log(n+1) for n>=1,
and correction<=2*log(n+1)*log(L) for n>=3.
The budget name describes a nested logarithmic scale; it is not a proved
asymptotic O(log(n)*log(log(n))) statement.

## 10. Comparison with instruction 026

Yes, the universal comparison is proved for every n>=3:
 log-log budget <= (L+1)*log(n).
Thus the independent reciprocal budget is also below the previous budget by
transitivity. The proof uses top<=n^3, log monotonicity, and the neutral envelope
3*log(x)<=x+1 for x>0. The latter follows from log(x/3)<=x/3-1 and a proved
log(3)<=4/3 bound using the rational cube (13/9)^3>=3.
No decimal log oracle, derivative estimate, or finite comparison is used as a
premise. The theorem states no larger, not strict inequality everywhere.

In the scan both new budgets first strictly beat the old budget at n=2 and
beat it at all n=3..5000. The smallest provider-domain anchor is n=3.
The only positive-anchor exception to strict improvement in that finite range
is n=1: the reciprocal budget ties old zero, and the log-log budget is larger.
That anchor is outside the proved n>=3 comparison. No failed in-domain
comparison or smallest in-domain counterexample remains.

## 11. Sharper odd-only harmonic identity

The optional subtraction of one-half harmonic(L/2) was not implemented.
The required finite reciprocal theorem and harmonic compression already close,
and the next frontier is lower shell-mass accounting. No one-half logarithmic
coefficient or sharper odd asymptotic is claimed.

## 12. Conditional prime providers

exists_prime_squareCell_of_reciprocalBudget_lt and
exists_prime_squareCell_of_logLogBudget_lt reuse the generic correction-bound
consumer. For n>=3, either budget strictly below shell von Mangoldt mass
implies positive prime-birth mass, hence a prime strictly between the squares.
The strict comparison remains an explicit hypothesis; neither provider proves
it for every anchor.

## 13. Exact psi-difference forms

The two companion providers accept the equivalent strict comparison against
psi(top)-psi(n^2), using the previously proved exact observable identity.
The reciprocal and compressed budgets are unchanged. This connects the finite
Pascal-shell vocabulary with the classical arithmetic function without an
asymptotic argument or RH import.

## 14. Two-event shells and preserved anchors

The [diagnostics](logs/diagnostics-027.json) extend the verified exact 026
integer inventory for all 5000 shells and retain its SHA-256 digest.
Cutoffs, occupied/admissible depths, and rational reciprocal sums are exact.
All logarithmic values and strict-comparison flags are floating diagnostics.

| n | occupied depths | correction approx | old budget approx | reciprocal approx | log-log approx |
| --- | --- | --- | --- | --- | --- |
| 3 | none | 0 | 5.493061 | 0.902683 | 3.754155 |
| 5 | 3,5 | 1.791759 | 9.656627 | 1.896186 | 5.722112 |
| 7 | none | 0 | 13.621371 | 2.209672 | 7.423501 |
| 9 | none | 0 | 15.380572 | 2.450731 | 8.233350 |
| 11 | 3,7 | 2.302585 | 19.183162 | 3.355828 | 9.657250 |
| 19 | none | 0 | see full data | see full data | see full data |
| 29 | none | 0 | see full data | see full data | see full data |
| 297 | none | 0 | 96.793446 | 11.642574 | 31.591363 |
| 1031 | none | 0 | 145.703974 | 15.727895 | 41.576291 |

At n=5 the exact rational reciprocal sum is 8/15; at n=11 it is 71/105.
The reciprocal budgets are about 19.6 percent and 17.5 percent of the respective
old budgets. Multiple events with distinct depths therefore still benefit
substantially from 1/a weighting. At n=11 one admissible depth is unused, so the
all-odd reciprocal bound is looser than the occupied-depth bound.

Named kernel calibrations certify all event data and symbolic weight identities
for 8,27,32,125,128 and 2^23=8388608. Complete depth patterns are {3} at n=2,
{3,5} at n=5, {3,7} at n=11, and {23} at n=2896. At the last shell the complete
higher-event carrier is a singleton, proved with base cutoff 203 and finite
depths 3..23. The preserved 297 and 1031 depth carriers are empty by complete
026 event certificates. No giant real-log inequality is kernel evaluated.

## 15. Worst ratios and strict-comparison diagnostics

For the proved provider domain n=3..5000, the largest correction/reciprocal
ratio is about 0.944928301 at n=5. The largest correction/log-log ratio is about
0.313129048, also at n=5. The all-positive-anchor reciprocal maximum occurs
at n=2 and is mathematically one; floating rounding prints 1.0000000000000002.
This is a diagnostic rounding effect, not a counterexample.

Both new strict shell-mass comparisons passed numerically at all 4998
provider-domain anchors. The old log-count comparison failed at n=3,5,7,9.
The theta and cube-candidate comparisons also passed throughout this scan.
These observations do not certify real-log inequalities and are not hypotheses
in any production theorem. The scan has no universal lower-mass conclusion.

## 16. Build RSS and paging telemetry

All four final builds were measured with /usr/bin/time -v and
LEAN_NUM_THREADS=2. The requested process metrics are:

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 37.859 | 7495276 | 0 | 599702 | 0 |
| facade | 0 | 12.24 | 6740292 | 0 | 201388 | 0 |
| root | 0 | 13.043 | 7107420 | 0 | 201903 | 0 |
| axiom-audit | 0 | 12.294 | 6681060 | 0 | 194998 | 0 |

The largest reported peak RSS was 7495276 kbytes, about 7.148 GiB.
Major page faults and reported swap counts were zero in all four measurements.
Minor faults are reported separately in the table. GNU time measures the Lake
invocation and waited descendants; these are process measurements, not total
concurrent host memory or a complete machine-wide swap monitor. Cache replay
and actual compilation are both present. The final focused run rebuilt Gauge
and both the inherited 026 and new 027 calibrations after the module doc edit.

[Telemetry and validation](validation-027.md) retains the raw output and
structured records. The measurements do not give an upper bound for every
future repository build.

## 17. Actual OOM evidence

All final measured builds exited successfully. No process was killed, timed
out, manually terminated, or observed to fail from OOM during this checkpoint.
Two Lean threads were chosen to preserve the requested validation setup;
thread count by itself supplies no evidence of memory exhaustion.
The document's 32 GiB memory and 64 GiB swap description is environment context,
not a substitute for measured process resource usage.

## 18. Exact remaining shell lower bound

The unresolved sufficient comparison is

 log(top)*log(L) < psi(top)-psi(n^2), for every relevant n>=3.

Any stronger valid shell lower bound exceeding this budget would feed the
proved provider. Neither the compressed upper correction bound nor a favorable
finite scan supplies such a lower bound. A prime shell can also exist when a
chosen sufficient budget comparison fails; these are conditional sufficient
criteria, not equivalences for every fixed upper budget.

## 19. Best existing candidates and source audit

The best exact bridge combines
Legendre.gnomonPascalCell_mul_factorial with
ArithmeticFunction.vonMangoldt_sum. The former identifies
cell*(2*n)! with the product of the shell labels. The latter identifies log(q)
with the sum of Lambda(d) over divisors of q. It keeps lower divisors visible,
which a raw Pascal growth estimate does not do.

WallisCellGrowth.pascalCellGrowthQ_eq_cast_choose is a proved general-cell
receiver. centralBinomialWallisLowerR_le_choose and certified central intervals
provide central growth control, but the gnomon cell at column 2*n of row
n^2+2*n lies far from the center for large n. A central lower estimate needs the
full offset or prefix product before applying to that cell. It is not directly
an estimate for short-shell psi mass.

Mathlib Nat.pow_le_choose provides the general lower bound
 (N+1-k)^k/k! <= choose(N,k).
At the gnomon indices, it gives the elementary shell-product bound
 (n^2+1)^(2*n) <= cell*(2*n)!.
This lower growth is available, but lower-divisor weights still have to be
subtracted before concluding anything about shell von Mangoldt mass.

Chebyshev.psi_ge and theta_ge were read. Their global lower bounds do not
control the short increment. Combining psi_ge(top) with the global psi upper
bound at n^2 is logically valid, but yields a bound with a negative leading
quadratic coefficient, not a useful positive short-shell estimate. Subtracting
two unrelated upper bounds is invalid and was not done.

Bertrand's centralBinom_factorization_small and
centralBinom_le_of_no_bertrand_prime split central-binomial factors to prove a
prime in a doubling interval. Their scale and factor-support estimates do not
automatically transfer to intervals of width 2*n around n^2. None of these
high-level candidates was imported into Gauge to assert an unproved provider.

## 20. Single theorem proposed for instruction 028

Define a lower-divisor shell mass

 C(n) = sum over d in Icc 1 (n^2) of
   ((top/d - n^2/d : Nat) : Real) * Lambda(d).

Nat division supplies exact floor counts of multiples in this shell. Prove the
single exact bridge, provisionally named
 gnomonPascalCell_log_add_factorial_eq_shellVM_add_lowerDivisorMass:

 log(cell) + log((2*n)!) = shellVonMangoldtMass(n) + C(n), for n>=3.

This is a proposal, not an implemented theorem in 027. Proof plan: take logs of
the existing nonzero product/factorial identity, apply vonMangoldt_sum at each
shell label, swap the finite divisor sums, and count shell multiples by the
natural division difference. Split divisors at n^2. A divisor above n^2 and
at most top has only itself as a shell multiple, so that part is exactly the
shell von Mangoldt mass. Leave C as an explicit lower-divisor contribution.

The identity then converts a proved log(cell)>=G lower bound into
 shell mass >= G+log((2*n)!)-C.
A separate C<=U bound would make the strict condition
 log-log budget < G+log((2*n)!)-U
sufficient. This explicitly exposes the subtraction needed to use a Pascal
multiplicative growth lower bound; it does not pretend that a suitable U is known.

The bridge also needs a comparison with the existing ledger. If it is proved,
026's identities give
 C-log((2*n)!) = oldCarryBudget-higherCorrection.
Thus merely renaming C cannot solve the old frontier. The useful next research
question is whether exact divisor multiplicities have a provable cancellation
estimate strong enough for the remaining lower shell-mass comparison.
Do not attach a universal lower-bound claim to this identity alone, and do not
resume deletion packing, terminal cofactor, or FLT7.

Outcome A - ODD-DEPTH RECIPROCAL GAUGE COMPRESSES THE HIGHER CORRECTION
