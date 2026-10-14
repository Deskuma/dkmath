# Findings 026

## Source audit

Read the 025 report and audited the required Pascal, shell, finite-shadow and RH canonical-fold interfaces. Installed Mathlib supplies the classical von Mangoldt function, canonical minFac depth, and Chebyshev finite sums. No foundational Legendre theorem needs an RH import. Global Chebyshev upper bounds are not shell-local increment estimates.

The planned derivative gap uses pow_add_mul_le_add_pow. Fixed-exponent shell uniqueness is not assumed before its Lean proof compiles.

## Exact observable and split

SquareShellVonMangoldt focused build passed. The observable is the sum of
classical von Mangoldt weights at n^2+r for r in squareOffsets n.
A general finite initial-segment subtraction lemma gives exact psi and theta
increments, including n=0. Pointwise prime/nonprime-prime-power/other cases
sum to the exact birth plus higher correction identity. The correction is
exactly the increment of psi minus theta.

## Power-gap arithmetic

No-square, all-even-depth exclusion, odd depth at least three, canonical
minFac factorization, same-base uniqueness, and the fixed-depth gap proof
have elaborated. The fixed-depth theorem needs only a>=3; it does not need
n>=3. Its proof uses base<=n, preceding power>n, and the standard binomial
lower bound for (x+1)^a. Carrier API cleanup is being completed before the
module's final focused build and downstream use.

## Arithmetic module closed

The focused SquareShellPrimePower build passed with no warnings. The canonical
packet, all-even exclusion, same-base uniqueness for n>=3, fixed-exponent
uniqueness for every n, exponent cutoff, exponent-indexed carriers, depth
injection, and event count <= Nat.log 2 ((n+1)^2)+1 are kernel checked.

## Gauge, base injection, and budgets

The focused SquareShellPrimePowerGauge build passed. It reindexes correction
mass exactly over the minFac image and bounds it by theta(n), by the cube-cutoff
candidate sum, and by (Nat.log 2 ((n+1)^2)+1)*log(n) for n>=3.
The exact log-depth relation proves 3*Lambda(q)<=log(q) and log gauge<=1/3.
Strict theta or logarithmic-budget comparison with shell mass provides a
prime via positive birth mass. No universal strict comparison is assumed.
Thin canonical resynchronization and prime-birth packets connect instruction 025.
Two minor lint warnings are being removed before final validation.

## Chebyshev bound audit

The installed global theta, psi, and psi-minus-theta bounds do not by themselves
provide a stronger short-shell correction estimate. In particular, subtracting
two unrelated upper bounds is invalid. The production bounds use exact finite
carriers instead; no unsupported local error estimate was introduced.

## Diagnostics completed

The integer sieve and integer power scan covered n=1 through 5000. Maximum
higher-event count is two, at n=5,11,46. Maximum observed exponent is 23.
No shared exponent or shared base occurred. The first higher event is n=2,
q=8; the first multiple-event shell is n=5, q=27 and q=32. Logarithms and
criterion/sharpness comparisons are floating diagnostics, not Lean proofs.

## Gnomon row exclusion

The arithmetic exclusion of IsPrimePow (n*(n+2)) for n>=3 and the resulting
whole-row inner common gcd-one theorem compiled. The proof uses divisors of
one prime power, difference two, and the impossible simultaneous four-divisibility.
It is explicitly separated from a selected-cell fresh-prime claim.

## Calibration cost correction

Direct large-anchor depth/base evaluation was interrupted after excessive
compiler time. It has been replaced by a bounded cube-cutoff certificate:
for n=297 all contributing bases are at most 44; for n=1031 they are at most
102. The reusable bounded-exclusion theorem combines this with the exact
binary exponent cutoff. This reduces the finite computation and retains the
complete no-higher-events conclusion, rather than weakening the calibration.

## Judgment and next proposal

Outcome A is justified by the proved explicit logarithmic event-count and
mass bound and its conditional prime consumer. The universal shell lower-mass
provider is still unresolved. The next proposed theorem is an odd-depth
reciprocal-weight budget, using Lambda(q)=log(q)/a and depth injection. This
proposal is not asserted as implemented or proved. The old carry-product
proposal remains deferred because it adds no new consumer here.

## Complete kernel calibrations passed

The final focused calibration build passed with no warnings. All six preserved
higher-event carrier summaries are kernel checked. The first shell is prime-only;
n=2 has the first cube; n=5 has a cube and a fifth power; n=11 has a cube and a
seventh power. Both large no-event anchors use the bounded cube-cutoff certificate.
The exact nonempty correction at n=5 and mass=birth at n=1031 also compile.
Kernel reduction uses decide +kernel for computational finite certificates;
no native decision or external numerical oracle is used. Final production
builds contain no new lint warnings. The facade was updated only after green
focused production and calibration builds.

## Final validation completed

All three production modules, the calibration module, the Legendre facade,
the DkMath root, and the complete axiom audit passed with two Lean threads.
The final checker passed full public declaration coverage, standard-axiom-only
audit, forbidden constructs, header/file-marker conventions, whitespace checks,
5000-shell exact higher-event inventory, 21 report answers and ASCII artifacts.
Only existing unrelated facade/root warnings remain. Outcome A retains the explicit
unresolved universal lower-mass comparison.
