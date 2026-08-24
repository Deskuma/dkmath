# GWSS-001M Mellin finite-jet rank report

## Global objective

Formalize the finite Mellin jet and determine whether the actual-window
Mellin family gives an independent finite-rank transfer for the Guinand--Weil
source audit.  This report records the result of the bounded 0007 task only;
GWSS-002 is not started.

## Current GWSS stage

`GWSS-001M-A` is implemented.  The new module is
`DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteJetRankAudit`.

For the bare symmetric exponential kernel, the module proves the punctured
finite jets

* quadratic jet: `z ^ 2`;
* quartic correction: `z ^ 4 / 12`;
* sextic correction: `z ^ 6 / 360`.

The proofs use the exponential Taylor remainder as an `IsLittleO` statement,
then transport it through the real dilation parameter.  The formulas are
therefore compatible with the existing patched `τ = 0` definition while the
higher quotients are explicitly taken on `nhdsWithin 0 ({0}ᶜ)`.

## Load-bearing boundary

The implementation proves only the finite local Mellin-jet facts.  It does
not prove RH, Weil positivity, fixed-Xi defect vanishing, a prime-side sign,
horizontal decay, or any limit exchange.  The existing centered spectral
factor is retained; it is not replaced by `1`.

## Gate B: two-orbit obstruction

Before any Vandermonde generalization, the zero coordinate was checked
explicitly.  The module proves:

* `complexExpSecondDifferenceKernel_zero_coordinate`;
* `pascalCenteredXiMellinSecondDifferenceWeight_zero_coordinate`.

Thus the Mellin family annihilates `z = 0` for every `τ`, including the patched
zero-dilation branch.  No independently formalized exclusion of a zero
squared-coordinate in the actual Xi carrier is currently available.  It is
therefore invalid to insert a hidden factor `q₁ * q₂ ≠ 0` and claim an actual
two-orbit rank theorem.

## Primary classification

`MELLIN-FAMILY-RANK-OBSTRUCTION`

Part A succeeds, but the actual-window rank transfer stops at the concrete
zero-coordinate obstruction in Part B.  Parts C and D are intentionally not
started.  The next admissible input is an independent theorem excluding the
zero squared-coordinate (or a revised observable that does not annihilate it);
only then should the two-orbit determinant and the actual-window spectral
factor be revisited.

## Verification and acceptance

Focused verification succeeds with:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteJetRankAudit
```

No public aggregation import was changed, so a repository-wide build is not
part of this bounded task.  No `sorry`, `admit`, or new axiom was introduced.

