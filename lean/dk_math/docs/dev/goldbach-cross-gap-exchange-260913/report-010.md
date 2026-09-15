# CGE-010 closeout report

Date: 2026-09-13

## Scope

Implemented the bounded fourth Pascal and signed-CRT quadruple layer from
`instruction-010.md`.  The attached instruction was treated as the stage
contract; the implementation remains finite and conditional.  No universal
survivor theorem, Strong Goldbach theorem, analytic limit, density claim, or
prime-realization theorem was added.

## Implemented

- Added `DkMath.NumberTheory.Goldbach.BalancedSignedCRTQuadruple`.
- Added the local fourth multiplicity
  `Nat.choose support.card 4` and its window sum.
- Proved the bounded Pascal identity
  `k - 1 = (choose k 2 - choose k 3) + choose k 4` for `k ≤ 4`, together
  with local and window exact identities under the explicit support bound.
- Added `goldbachPrimeQuadruples` as `S.powersetCard 4`, canonical signed
  quadruple residue representatives modulo `Q.prod id`, exact per-subset
  support-seat counts, and the global quadruple double-count identity.
- Added the exact single/pair/triple/quadruple budget provider under the
  explicit support-card bound and its world-card-`≤ 4` and anchor-local
  `GoldbachPairAt` wrappers.
- Exported the module through `DkMath.NumberTheory.Goldbach`.
- Extended `GoldbachBalancedReflectionAudit` with the CGE-010 regressions and
  axiom prints.

## Kernel-checked regressions

- For `(n,w,P)=(22,9,7)`, the ten support-card values are
  `1,2,3,1,2,1,2,2,4,0`.
- The balanced window, incidence, pair, triple, quadruple, and excess values
  are respectively `10,18,13,5,1,9`; the quadruple CRT global sum is exactly
  `1`.
- The three-layer inequality fails (`18 < 10 + (13 - 5)` is false), while the
  fourth-layer inequality succeeds (`18 < 10 + ((13 - 5) + 1)`).
- The support-card-5 firewall is checked:
  `choose 5 2 = 10`, `choose 5 3 = 10`, `choose 5 4 = 5`, and the fourth
  layer is not exported as an unconditional inequality.
- The exact provider replay closes `GoldbachPairAt 22` under the explicit
  anchor, horizon, world-card, and budget hypotheses.

## Validation

- Standalone focused build passed:
  `lake build DkMath.NumberTheory.Goldbach.BalancedSignedCRTQuadruple`
  (`8724` jobs).
- Audit focused build passed:
  `lake build DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit`
  (`8736` jobs).
- Full build passed: `lake build` (`9859` jobs).
- A fresh full-build warning filter reported no warnings other than the
  repository's excluded sorry-declaration warning category.
- The audit's `#print axioms` output for the new declarations reports only
  the existing finite bookkeeping dependencies (`propext`, `Classical.choice`,
  `Quot.sound`); no `sorry`, `admit`, `native_decide`, `unsafe`, or new axiom
  was introduced.
- `git diff --check` passed.

## Outcome

Outcome A: the bounded fourth finite production identity and its exact
quadruple signed-CRT ledger are established.  The resulting provider remains
explicitly bounded and conditional at the requested checkpoint boundary.
