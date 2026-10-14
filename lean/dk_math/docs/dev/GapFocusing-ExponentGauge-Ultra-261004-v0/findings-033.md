# Findings 033 - Semiprime deletion and higher-composite residual

## Carrier and collision route

The existing endpoint factor cover is filtered by primality of its second
factor. Ordered prime pairs r<=s have injective products, proved using prime
divisibility and cancellation. The product image includes the 032 squares
and admits 77=7*11 safely. It excludes both (7,77) and (11,49), preserving
539 as a higher-composite residual rather than subtracting it twice.

## Lower mass and budget

The independent witness definition uses endpoints, factor primality and wheel
coprimality, not Q or the actual composite/carry filter. Its log mass D satisfies
L<=D<=E. The new envelope Z=min(U,V-D) satisfies Q<=Z<=U, with exact excess
Z-Q=min(U-Q,E-D). All residual ledger terms remain unchanged.

Kernel checks certify exact witness coverage at 9,12,29,31, where Z=Q. The
031/032 recoveries are retained, and the failed 032 consumer at 31 becomes
strictly passing. At 32 the remaining carrier is {539} in k=2 and {343} in
k=3, with every other residual window empty. Equality at 3 excludes strict
gain at every admissible anchor.

## Bounded limitation

Independent diagnostics cover n=3..300 and the retained anchors 1031,5000.
The first numeric consumer failure is 210; it and its minimality are diagnostic
only, not kernel-certified. Later passes show no monotone threshold.
At 5000, D is about 115704.399, leaving E-D about 65561.859 against the
available exact-ledger margin about 10442.199. Semiprime deletion supplies
substantial finite saving but does not close the large-anchor budgets.

The next mathematical issue is a useful lower certificate for higher-
composite mass, with product collisions controlled, or an independent upper
estimate for the surviving weighted carrier. Complete target factorization
would recover the exact composite inventory rather than a new estimate.

## Final validation

Focused, facade, root and all 25 named public axiom checks passed with two
Lean threads. No new warning or sorryAx occurs in the checked public surface.
Kernel checks fix complete small-anchor coverage, strict recovery at 31 and
higher-composite residual at 32. Inherited root warnings are scoped separately.
Outcome B: a distinct lower witness and stronger envelope, without global closure.
