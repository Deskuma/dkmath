# Findings 032 - Canonical least factors, overcover and oriented correction

## Structural route

A surviving composite q is greater than one. With r=minFac(q), m=q/r,
r is prime, q=r*m, r<=m, r^2<=B, both factors are coprime to the wheel product,
and A/r<m<=B/r. Every prime divisor of m is at least r. The pair reconstructs
q, hence canonical fibers are disjoint per window. A general basis excludes
its members, not necessarily every prime below its largest element.

## Independent bound and orientation

The pair cover drops the least-factor restriction on m. Its accumulated
product-log sum F bounds E by canonical injection and nonnegative extra terms.
At n=32, q=539 has both (7,77) and (11,49) in the cover, but only the first
pair is canonical. The bound is therefore more than an exact reindexing,
though its multiplicity loss is substantial at large anchors.

E<=F implies V-F<=Q. Subtracting F cannot supply a prime-mass upper bound.
The report preserves this orientation rather than silently treating an error
upper bound as removable mass. The diagonal pair products give the correct
lower witness L<=E. Deduplicating within each window, U=min(W,V-L) satisfies
Q<=U<=W and U-Q=min(W-Q,E-L). The old ledger is unchanged below U.

## Calibrations and remaining obstruction

49 at n=9 routes to (7,7), and 77 at n=12 routes to (7,11). The square
correction deletes the former but retains the latter. All 11 canonical triples
at n=29 are kernel checked. Its three squares 289,169,121 give L about
15.592116 and recover a consumer margin about 10.565763.

Independent bounded diagnostics show the first corrected failure at n=31,
followed by passes at 32 and 33. Failure minimality is diagnostic only.
At n=5000 the square witness is about 140.702 against E about 181266.258;
F is about 284403.302. Diagonal deletion does not control the nonsquare error.
No universal failure threshold or impossibility for all elementary methods
follows from these finite tests.

## Frontier

The route needs useful lower certified composite mass for deletion, or a
separate independent upper prime-weight estimate. Improving an upper bound
on E alone addresses a different inequality. A next bounded investigation
could compare collision-controlled distinct-product factor witnesses against
the remaining nonsquare error, retaining endpoint and window multiplicities.
Full product image classification or a complete factor-test wheel just
recovers the exact composite or prime carrier and is not quantitative closure.

## Final validation

Focused, facade, root and complete public axiom builds passed with two Lean
threads. No new warning or sorryAx dependency occurs in the new public surface.
Kernel checks certify the local recovery at 29 and residual failure at 31.
All inherited root warnings are scoped in validation. Outcome B: independent
factor-pair error bound and certified square deletion, without global closure.
