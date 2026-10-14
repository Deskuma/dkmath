# Findings 031 - Weighted wheel exclusion and its remaining error

## Carrier choice

Use the existing finite prime-basis product M(S), filtering the exact 030
interval Icc(A+1,B) by gcd(q,M)=1. Absolute q may exceed the wheel period,
so a one-period survivor set is not the appropriate carrier. The existing
not-reserved/coprime theorem identifies precisely the same exclusion in all
periods. Basis elements must be prime and at most width. That bound ensures
no contributing prime p>width is itself removed as a basis element.

## Estimate and exact error

The raw mass V sums log(q) over surviving integers in every cofactor window.
It contains no primality or carry membership predicate. Filtering its carrier
by primality returns exactly the 030 prime window. Hence V=Q+E, with E the
sum of log(q) over surviving nonprime slots. This E is an audit identity, not
an assumed numerical estimate. All its terms are nonnegative.

The final bound W=min(G,V) satisfies Q<=W<=G. Its exact excess is
W-Q=min(G-Q,E). The cap preserves the former envelope for arbitrary admissible
finite bases, including coarse choices. The old-ledger excess is still W-Q,
so this improves the independent 030 envelope but never lowers the actual
exact old budget. The new consumer retains small, repeated-power and higher
correction terms and requires the explicit strict margin.

## Obstruction and diagnostics

The fixed basis {2,3,5} deletes the whole (14,15] window at n=7, as well as
25,27,21 in neighboring windows. Its remaining four slots are prime, giving
zero error and a strict improvement over G. The corrected consumer passes.

The first surviving composite is n=9, k=2, q=49. Its error is log(49), while
the old repeated carry label 49 contributes log(7). These weights cannot be
identified or canceled. At n=12 the carrier also includes 77=7*11, which is
not even a prime-power carry label. This is remaining rough-composite mass,
not a new compensation created by deleting the small-prime multiples.

An independent fixed-wheel prefix calculation covers all n=3..5000; direct
gcd/factor scans check anchor windows. The first diagnostic consumer failure
is 29, with error about 59.173469 and margin about -5.026353. Later anchors
30 and 33 pass, so the failure is not a monotone threshold. Larger fixed
bases help locally but still fail at the displayed large anchors. No claim
that every finite sieve strategy must fail follows from these checks.

Kernel calibration preserves the corrected n=7 margin, first composite error
at 9 with absence at 3..8, the compound survivor 77, the fixed-wheel failure
at 29, and two endpoint pitfalls. A period-average density without boundary
error fails already on (6,7]. A basis containing 7 at n=3 deletes the desired
prime and violates the required cutoff. Equality W=G at n=3 also prevents
a claim of strict improvement at every n>=3.

## Frontier

The remaining estimate must control total rough-composite log weight or an
equivalent weighted short-window sieve bound. An exact Mobius cardinal
identity or whole-period density alone does not provide this control. A
larger complete factor-test basis can turn the carrier back into the actual
prime carrier; that is exact classification, not a distribution estimate.

A natural bounded next experiment is to group surviving composites by their
least prime factor and estimate the accumulated factor-pair weight, with
explicit endpoint and multiplicity errors. No later checkpoint architecture
or analytic assumption is introduced.

## Final validation

All four builds passed with two Lean threads. The complete 26-declaration
public axiom audit contains only standard logical axioms and no sorryAx.
Kernel checks fix the n=7 recovery, first composite at 9, survivor 77 at 12,
and fixed-wheel failure at 29. Bounded diagnostics retain 4998 anchors and
14 direct reconstructions. Inherited root warnings are documented separately.
Outcome B: independent wheel bound, exact error, no universal strict margin.
