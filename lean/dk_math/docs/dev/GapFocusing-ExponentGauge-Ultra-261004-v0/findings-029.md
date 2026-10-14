# Findings 029

## Source audit and initial route

The large-label common-base exclusion is already proved in 028 and will be
reused, not duplicated. The actual fiber should be a consecutive exponent
interval: lower cutoff from width, upper cutoff from both old labels and target
valuation. Its weight is cardinality times log(p), because every label has the
same von Mangoldt weight. A cutoff-only upper budget may be larger than the
actual 028 mass; this comparison must be proved and reported explicitly.

## Exact fiber and routing

The new production module builds. Exponents route to y iff their positive prime
power is an old large carry label with canonical next multiple y. The fiber is
exactly Icc(L+1,min(U,v)), with L=Nat.log p(width), U=Nat.log p(base) and
v=y.factorization p. Its card is min(U,v)-L with natural subtraction, and its
von Mangoldt mass is this card times log(p). No reciprocal-exponent discount
is appropriate: all labels have the same base weight.

## Collision classification

The existing large-power distinct-base exclusion is reused to prove target
projection injective on canonical (base,target) pairs. This assertion is not
label-map injectivity. Dropping the large-label restriction produces a mixed
base diagnostic at n=7, labels 3 and 17 with target 51; a kernel calibration
will preserve the hypotheses' necessity.

## Bound and 028 consumer

The cutoff-only capacity U-L bounds each fiber and gives a universal finite
large-mass upper envelope. Inserting it into the old ledger gives old budget
at most higher plus small mass plus fiber budget. The new provider retains a
strict inequality hypothesis. The envelope's entire excess is fiber budget
minus actual large mass; nonnegative excess prevents interpreting this as a
strict saving relative to the exact 028 ledger.
## Final diagnostics and route judgment

All same-base exponent fibers through n=5000 match both direct divisibility
and the exact cutoff/valuation interval. The first cutoff slack is n=6,
p=2 and target 48. The first large collision is n=11; the largest recorded
fiber has ten labels at n=2896 and is now kernel certified. Dropping the
large-label restriction first permits mixed prime bases at n=7, labels 3 and
17 with target 51; the earlier exploratory n=8 guess was corrected.

The cutoff envelope is everywhere at least the exact old budget, with exact
excess C-K_large. It therefore supplies no universal strict old-budget gain.
Large prime-base singleton fibers dominate the measured mass at 297/1031,
and a production subset theorem proves those bases have only depth one.
Outcome B is selected. The next natural frontier is an independent weighted
bound for their cofactor-window prime occupancy; no candidate useful U or
full instruction-030 architecture is manufactured.

## Final validation

Focused, facade, root and complete axiom builds pass with two Lean threads.
All 18 production and 14 calibration declarations have only standard logical
axioms. Existing root warnings remain outside the new dependency surface.
Headers, file markers, forbidden-token scans, whitespace, source digests and
ASCII artifacts are checked. Resource metrics are retained in validation-029.
