# Instruction 039 - Pooled residual-product compensation

## Mission

Continue from Instruction 038.

Instruction 038 reduced the unresolved central-binomial candidate to an exact
finite product comparison.

Let

  L(n) = product of minFac(d) over small-only prime-power coordinates,
  R(n) = product of minFac(d) over central-only prime-power coordinates.

Then the desired weighted inequality is exactly

  L(n) <= R(n).

The coordinatewise route is now known to fail.

At n=27 there is no injective map from small-only coordinates to central-only
coordinates that weakly increases each contributed prime base, even though the
total product inequality holds with a large margin.

The next question is whether the compensation has a canonical pooled-block
structure.

Do not return to pointwise carry inclusion or local phase-exclusion heuristics.

## Main research question

Can the small-only and central-only residual coordinates be partitioned or
grouped into finitely many blocks so that each left block is paid for by one
right block through a proved product inequality?

Conceptually seek blocks A_i and C_i with

  product_{d in A_i} minFac(d)
    <=
  product_{d in C_i} minFac(d)

and disjoint unions covering all residual coordinates.

The block construction must come from fixed-n arithmetic structure and must
not assume the desired global product inequality.

The exact block representation is open.

## Required calibration

Preserve the exact Instruction 038 regressions.

At n=4:

  small-only bases   = {3}
  central-only bases = {5,7,2}.

The construction should explain the compensation without requiring divisibility.

At n=27:

  small-only bases   = {5,11,19,23}
  central-only bases = {2,2,7,2,47,7,53}.

A valid block mechanism must survive the proved no-dominating-injection
obstruction.

The informal grouping

  5 <= 2*2*2,
  11 <= 7*7,
  19 <= 47,
  23 <= 53

is only calibration evidence. Do not hard-code these blocks or assume that the
same thresholds work universally.

Retain representative anchors 32,69,210,297,1031,5000.

## Search directions

Audit existing finite combinatorics before introducing new machinery.

Potential structures worth testing include:

- ordering residual coordinates by contributed prime base,
- cumulative products of sorted base multisets,
- dyadic or multiplicative size classes,
- grouping repeated powers of the same base before cross-base comparison,
- residue classes of n modulo d,
- blocks arising from central-binomial factorization intervals,
- Hall-type capacity after replacing one-coordinate capacity by logarithmic or
  multiplicative block capacity.

Let the arithmetic choose the useful structure.

Do not assume blocks have equal cardinality.

Do not require a matching if a cumulative-product or prefix-majorization theorem
is cleaner.

## A useful intermediate target

A sufficient pooled comparison may be expressed without an explicit partition.

For example, if sorted or thresholded cumulative products satisfy a family of
inequalities strong enough to imply

  L(n) <= R(n),

formalize that directly.

A theorem comparing logarithmic mass above or below multiplicative thresholds
is also acceptable if it is genuinely independent and proves the global
residual-product inequality.

The important point is that several smaller right-side prime bases may jointly
pay for one larger left-side base, and conversely one large right-side base may
pay for several left-side bases.

## Exact product currency

Reuse the exact product encoding from Instruction 038.

Do not introduce real logarithms earlier than necessary.

Prefer natural-number product inequalities when possible, then transport to
weighted log mass using the existing positive-product bridge.

Keep multiplicity of repeated prime-power coordinates exactly.

## Independence / circularity guard

The following do not count as a block-compensation theorem:

- defining one block to contain all residual coordinates and assuming L<=R,
- choosing blocks by searching until their products satisfy the target,
- using the already-computed total residual products as the block rule,
- querying Q, shell-prime existence, or oldBudget strictness,
- proving only bounded finite instances and extrapolating.

The grouping rule must be specified from independent arithmetic data.

## If pooled compensation succeeds

Prove the global residual product inequality

  L(n) <= R(n)

and therefore

  gnomonPascalSmallCarryMass n
    <=
  log (Nat.choose (2*n) n).

Then build the central correction envelope using:

  central-binomial small bound,
  repeated-large band budget,
  reciprocal higher correction.

Prove

  C_ns <= B_central

and connect the usual conditional consumer

  Q + B_central < log(cell)
    -> exists prime in SquareCell n.

Compare B_central with the proved 037 budget and 036 budget where possible.

## If pooled compensation does not close

Do not create increasingly ad hoc block heuristics.

Instead identify the precise obstruction.

Useful Outcome C information would include:

- a fixed-n configuration defeating a natural block rule,
- a failure of sorted-prefix or threshold majorization,
- evidence that compensation requires a genuinely global weighted theorem,
- or a reduction to another recognized arithmetic inequality.

The original total product conjecture may remain open.

## Quantitative interpretation

Instruction 038 diagnostics show that hypothetical central compensation would:

- improve n=297 from a negative correction-envelope margin to a positive one,
- strongly improve n=5000,
- but still leave n=69 slightly negative.

Therefore even success here does not by itself imply universal closure.

Retain the correction slack separately from Q when interpreting the result.

Do not report Q as the sole remaining frontier unless the proved budget
actually supports that conclusion.

## Stopping rule

This checkpoint should test one coherent pooled-compensation principle.

Do not start an unbounded hierarchy of block sizes or manually tuned residue
zones.

If no canonical block rule emerges, classify the route honestly and move the
frontier rather than accumulating heuristics.

Do not predesign Instruction 040.

## Validation

Use the standard branch validation:

- focused build,
- Legendre facade build,
- root build when appropriate,
- axiom audit for new production declarations,
- bounded diagnostics where useful.

## Outcome classification

Outcome A:

A pooled compensation theorem yields the central-binomial bound and, together
with existing results, a universal strict budget theorem or genuinely new
unconditional prime-existence range.

Outcome B:

A genuine uniform pooled-product theorem proves the central-binomial small-carry
bound and strengthens the correction budget, but universal closure is not
obtained.

Outcome C:

No non-circular pooled block rule proves the residual-product comparison, or a
structural counterexample defeats the investigated block principle.

All outcomes are acceptable.

## Report

Write:

  lean/dk_math/docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/report-039.md

State:

- the pooled/block structure actually investigated,
- whether it is canonical and independent of the target inequality,
- how n=4 and n=27 are handled,
- any sorted-prefix / threshold / block-product theorem or counterexample,
- status of the universal residual-product inequality,
- strongest resulting small-carry bound,
- correction-budget effect,
- diagnostics at retained anchors,
- axiom/build status,
- Outcome A/B/C,
- the next natural frontier suggested by the result.
