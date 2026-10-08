# Report 026 - Square-shell von Mangoldt split and small higher-power budget

The exact classical shell split and both requested sparsity bridges are proved.
For n>=3, higher correction is bounded by theta(n), by a cube-cutoff prime sum,
and by an explicit logarithmic-count times logarithmic-weight budget.
Fixed-exponent uniqueness and the event-count bound actually hold for all n.
The strict lower comparison needed for universal prime existence is still an
explicit hypothesis. No Legendre conjecture, PNT, RH, or universal shell
prime-power existence theorem follows from this checkpoint.

Production sources:

- [SquareShellPrimePower](../../../DkMath/NumberTheory/Legendre/SquareShellPrimePower.lean)
- [SquareShellVonMangoldt](../../../DkMath/NumberTheory/Legendre/SquareShellVonMangoldt.lean)
- [SquareShellPrimePowerGauge](../../../DkMath/NumberTheory/Legendre/SquareShellPrimePowerGauge.lean)
- [Kernel calibration](../../../DkMathTest/NumberTheory/SquareShellPrimePowerCalibration.lean)

[Source inventory](source-inventory-026.md), [findings](findings-026.md), and
[validation](validation-026.md) record scope and evidence.

## 1. Exact shell observable

The definition gnomonPascalShellVonMangoldtMass n is the finite sum of
ArithmeticFunction.vonMangoldt (n^2+r) over r in squareOffsets n.
All shell values are integers strictly between consecutive squares.
Both this mass and the higher correction are nonnegative; their zero-anchor
values are explicitly zero.

## 2. Exact psi difference

Yes. gnomonPascalShellVonMangoldtMass_eq_psi_sub proves
mass = psi(n^2+2*n)-psi(n^2), with the endpoints cast from Nat to Real.
The upper endpoint is the last integer strictly below the next square.
The proof shifts finite sums and splits initial segments, including n=0.
No asymptotic estimate is used.

## 3. Pointwise split

higherPrimePowerWeight q is Lambda(q) when IsPrimePow q and not q.Prime,
and zero otherwise. vonMangoldt_eq_primeBirth_add_higher proves for every q:
Lambda(q) = pascalPrimeBirthLogMass q + higherPrimePowerWeight q.
The proof separates prime, nonprime prime power, and non-prime-power cases.
A higher power resynchronization is not identified with genuine prime birth.

## 4. Shell split

Yes. gnomonPascalShellVonMangoldtMass_eq_birth_add_higher proves exactly
shell mass = shell prime birth mass + shell higher correction.
The correction also equals the sum of Lambda over shellHigherPrimePowerEvents,
the exact finite carrier of nonprime prime-power labels in the shell.

## 5. No perfect square

not_squareCell_square excludes m^2 for every n and m. The strict inequalities
would force n<m<n+1 in Nat. Basic.lean was left unchanged; the extension lives
in the new application module, so existing foundational code is preserved.

## 6. No even exponent

not_squareCell_even_power excludes every even exponent for every natural base,
without primality or positive-depth assumptions. An even power is the square
of a lower power. This is stronger than excluding exponent two alone.

## 7. Odd depth at least three

shell_nonprime_power_depth applies to any prime-base representation in the
shell whose power is nonprime. It proves Odd a and 3<=a. Depth zero and every
even depth are excluded by the square theorem; depth one is genuine prime.

## 8. Canonical packet

shell_higher_primePower_canonical uses p=q.minFac and
 a=q.factorization q.minFac. It proves p prime, a>=3, a odd, q=p^a, p<=n,
and p^3<(n+1)^2. This packet needs no n>=3 assumption.
The equality reuses IsPrimePow.minFac_pow_factorization_eq.

## 9. Gauge gap

The exact packet proves Lambda(q)=log(p) and log(q)=a*log(p).
It gives 3*Lambda(q)<=log(q), and pascalPrimePowerLogGauge p a<=1/3.
Prime shell events have Lambda(q)=log(q) and gauge one instead.
The thin shellHigherPrimePowerResynchronizationPacket additionally records
prebirth alternation at q-1, whole-row divisibility at q, old cumulative
support, absence of base-coordinate birth, and exact gauge 1/a.
There is no continuous interpolation or identification with StructuralArithmetic.PowerGauge.

## 10. Same base uniqueness

For n>=3, squareCell_prime_power_exponent_unique proves that two shell powers
of the same prime base have equal exponents. The shell endpoint ratio is less
than two, while distinct prime-base powers differ by a factor at least two.
squareCell_primePower_minFac_injective converts this to canonical-label
injectivity. Thus the minFac image has no multiplicity in the correction sum.

## 11. Theta and cube-cutoff bounds

Yes. The exact base image is contained in Nat.primesLE n, and correction equals
the sum of log(p) on that image for n>=3. Nonnegative prime logs and
Chebyshev.theta_eq_sum_primesLE_log give correction<=theta(n).
The optional shellHigherBaseCandidates carrier further requires p^3<(n+1)^2.
Correction<=sum of candidate logs<=theta(n) is also proved.
These are finite carrier inclusions, not analytic approximations.

## 12. Fixed-exponent uniqueness

For each a>=3, a shell contains at most one natural a-th power. The theorem
squareCell_fixed_exponent_unique is proved for every n, stronger than the
requested n>=3 boundary. No primality assumptions are required.
Shell membership gives x<=n and x^(a-1)>n. The installed finite binomial
lower bound gives (x+1)^a>=x^a+a*x^(a-1), whose gap exceeds 2*n. Monotonicity
then excludes any larger base with another shell power.
No counterexample or unproved fixed-exponent bridge remains.
The exponent-indexed prime-base carrier has card<=1, and is empty at even depth.

## 13. Event count

Prime bases enforce 2^a<=p^a<(n+1)^2. Nat.le_log_of_pow_le yields
 a<=Nat.log 2 ((n+1)^2).
The canonical depth map is injective on higher events by fixed-exponent
uniqueness. Injecting into range(Nat.log 2 ((n+1)^2)+1) gives the proved bound
higherEventCarrier.card<=Nat.log 2 ((n+1)^2)+1 for all n.
The count does not assert at most one event overall: different odd depths can coexist.

## 14. Explicit mass bound

For n>=3, each base is at most n, so each event weighs at most log(n).
The proved shellHigherPrimePowerLogBudget is
 (Nat.log 2 ((n+1)^2)+1 : Real)*Real.log(n).
The correction is at most this budget. This is an explicit finite inequality;
no separate asymptotic Big-O theorem is claimed.
It gives a smaller growth-scale correction universe than all old Pascal
coordinates up to n^2. It is not asserted to beat theta(n) at every small n.

## 15. Exact psi-minus-theta increment

Yes. gnomonPascalShellHigherPrimePowerMass_eq_psi_theta_sub proves exactly
correction = (psi(top)-theta(top))-(psi(n^2)-theta(n^2)), top=n^2+2*n.
The proof combines the exact psi increment, theta birth increment, and split.

## 16. Mathlib bound audit

The global theta linear bound, psi linear bound, psi-minus-theta square-root
bound, and global exponent decomposition were audited in installed sources.
They provide no direct sharper estimate for this short-shell increment.
In particular, two unrelated global upper bounds cannot be subtracted to
bound an increment. No such subtraction was implemented. The new local bounds
come from exact shell arithmetic, exponent gaps, and finite carrier injections.
No high-level RH module was imported into production.

## 17. Conditional prime criteria

exists_prime_squareCell_of_higher_bound is the generic consumer:
if correction<=B and B<shell von Mangoldt mass, then a shell prime exists.
It uses the exact split to obtain positive birth mass and the established
birth-mass positivity equivalence. Specializations use theta(n) or the
logarithmic budget for n>=3. The generic consumer also accepts the cube budget.
The corresponding psi difference may replace the shell observable exactly.
No theorem establishes the strict comparison for all anchors.

The old instruction 025 comparison is old carry budget<log(Pascal cell).
Its old budget counts valuations from lower prime-coordinate carry events
inside a binomial coefficient. The new correction counts only labels that
are themselves nonprime prime powers in this square shell. The exact cell
log and the shell psi increment are different observables. No implication
between the two sufficient-inequality formulations was proved or assumed.
The exact positive-birth equivalences continue to describe the same local
prime-existence proposition.

## 18. Gnomon top row exclusion

For n>=3, gnomon_top_not_isPrimePow proves not IsPrimePow (n*(n+2)).
If the product were a power of one prime p, both factors would be powers of p.
Their difference forces p=2. Since n>=3, both factors would be divisible by
four, contradicting their difference two.
gnomon_top_innerCommonDivisor_eq_one then proves the common inner-row gcd at
n^2+2*n is one, reusing instruction 025. A global row gcd-one statement does
not imply a fresh factor in a selected cell.

## 19. Diagnostics and calibration

The [full exact integer scan](evidence/MANIFEST.md#log-c79c8f5cca11b656) covers n=1 through
5000; [the summary](evidence/MANIFEST.md#log-eccb85a0735e48e4) records results.
The scan took approximately 4.7 seconds. Natural logarithms, ratios, and
strict-budget comparisons are floating diagnostics only.

Maximum higher-event count is two, attained at n=5,11,46. Maximum exponent
is 23, at q=2^23 in shell n=2896. No shared exponent or shared base occurred.
The first higher event is n=2, q=8=2^3. The first multiple-event shell is n=5,
with q=27=3^3 and q=32=2^5. Universal uniqueness is proved separately in Lean;
finite scans are not used as proof.

For the theorem domain n>=3, the largest observed correction/theta ratio is
about 0.526803, the largest correction/logarithmic-budget ratio is about
0.185547, and the largest correction/cube-budget ratio is 1; all occur at n=5.
The full scan includes n=2, where the first two ratios are 1 and 0.25.
Among n=3..5000, the theta sufficient comparison passed numerically at all
4998 anchors; the logarithmic comparison passed at 4994. Its failures were
n=3,5,7,9, where direct prime witnesses still exist. These comparisons are
not certified interval-log inequalities.

Preserved anchors:

| n | shell prime count, exact scan | higher labels |
| --- | --- | --- |
| 5 | 2 | 27,32 |
| 11 | 4 | 125,128 |
| 19 | 6 | none |
| 29 | 8 | none |
| 297 | 45 | none |
| 1031 | 160 | none |

Named kernel calibrations certify the complete higher-label summaries for
these anchors, the prime-only first shell, the first cube, fifth and seventh
powers, nonempty correction logs at n=5, and exact mass=birth at n=1031.
Large anchors use small-base cube cutoffs and a bounded finite exponent check;
no giant Pascal coefficient is expanded. Prime counts above are sieve results,
not claimed as kernel-certified prime-count theorems.

## 20. What the gap buys and what remains

The exponent gap removes every even depth and forces all higher correction
labels into odd depths at least three. Fixed-depth uniqueness then makes their
number logarithmic in the shell height. The resulting explicit small budget
and conditional prime providers materially narrow the correction that must
be overcome. The cube carrier and theta budget provide additional choices.

This does not supply a universal lower bound on shell psi mass. The theorem
that this mass exceeds a valid correction budget at all relevant anchors
remains the short-interval prime frontier. We do not call it solved because
an upper bound is small or because bounded scans are favorable.
The old carry-product proposal was reassessed and deferred: without a new
consumer, it duplicates the already exact cell-log frontier. No deletion,
cofactor campaign, or second equivalent product frontier was added.

## 21. Single next theorem and implementation proposal

Attempt a finite odd-depth reciprocal budget:

 correction(n) <= log(n^2+2*n) *
   sum over odd a in Icc 3 (Nat.log 2 ((n+1)^2)) of (1/a).

This is a proposed theorem, not part of the proved API in this checkpoint.
It uses the same canonical depth injection, but weights each occupied depth
by log(q)/a instead of the uniform log(n) bound. The exact log-depth packet
and q<=top give Lambda(q)<=log(top)/a; zero weights at unused depths can then
be filled by nonnegative upper weights. This should require only finite
reindexing, log monotonicity, and positive-depth division.

Suggested implementation: add an odd-depth Finset, reindex the correction on
its occupied image, prove the exact depth-weight expression, then establish
the finite reciprocal-sum upper bound and feed it to the generic provider.
Validate focused Gauge and calibration modules, print axioms for all added
public declarations, then build the Legendre facade and DkMath root.
Only after this finite bound closes should an asymptotic harmonic estimate
be attempted. Heuristically it suggests log(n)*log(log(n)) rather than the
current logarithmic-count times log(n) scale; no asymptotic theorem is claimed.
The universal lower-mass comparison remains a separate unresolved task.

Outcome A - SQUARE-SHELL GAUGE GAP YIELDS A NEW SMALL HIGHER-POWER BUDGET
