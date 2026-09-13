# CGE-009 closeout report

Date: 2026-09-13

## Scope

Implemented the bounded exact single-prime signed-CRT incidence layer from
`instruction-009.md`.  The attached instruction was treated as the stage
contract; no universal survivor provider, Strong Goldbach statement, analytic
limit, density claim, or prime-realization theorem was added.

## Implemented

- Added `DkMath.NumberTheory.Goldbach.BalancedSignedCRTIncidence`.
- Added `signedSingleResidues` and its membership theorem.
- Proved, for prime moduli, exact cardinality of the canonical single-prime
  representatives against `goldbachForbiddenResidues`.
- Added `goldbachSignedSingleCRTCount` and proved its exact equality with the
  cardinality of `goldbachWindowBlockedSeats` under the stated finite prime
  world, bound, anchor, and `2 ≤ n` hypotheses.
- Added the global identity
  `goldbachSignedSingleCRTSum = goldbachWindowIncidence`.
- Added the exact single/pair/triple signed budget survivor provider and the
  `primeScalesUpTo P` anchor-local `GoldbachPairAt` wrapper.
- Exported the module through `DkMath.NumberTheory.Goldbach`.
- Extended `GoldbachBalancedReflectionAudit` with executable regressions and
  axiom prints.

## Kernel-checked regressions

- For `(n,w,P)=(15,8,5)`, the single-prime counts at `r=2,3,5` are `4,3,2`,
  so the exact single sum and incidence are both `9`; pair/triple overlap
  counts are `3,0`, the window size is `9`, and
  `9 < 9 + (3 - 0)`.
- For `(n,w,P)=(50,10,7)`, the single-prime counts at `r=2,3,5,7` are
  `6,7,3,3`, giving exact single sum/incidence `19`; pair/triple counts are
  `12,2`, the window size is `11`, and the exact budget is `19 < 21`.
- The exact provider replay closes `GoldbachPairAt 15` and `GoldbachPairAt 50`
  under their explicit anchor and square-body hypotheses.

## Validation

- Focused build passed:
  `lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit`
  (`8735` jobs).
- The standalone new module build passed.
- Full build passed: `lake build DkMath` (`9858` jobs).
- A fresh full-build warning filter reported no warnings other than the
  repository's excluded sorry-declaration warning category.
- The audit's `#print axioms` output reports only the existing finite
  bookkeeping dependencies (`propext`, `Classical.choice`, `Quot.sound`);
  no `sorry`, `admit`, `native_decide`, or `unsafe` construct was introduced.
- `git diff --check` passed.

## Outcome

Outcome A: the decisive finite production identity is established.  The
single-prime signed CRT sum is now exactly the existing window incidence, and
the exact pair/triple identities feed the existing bounded Pascal provider.
The global/provider assumptions remain explicit.
