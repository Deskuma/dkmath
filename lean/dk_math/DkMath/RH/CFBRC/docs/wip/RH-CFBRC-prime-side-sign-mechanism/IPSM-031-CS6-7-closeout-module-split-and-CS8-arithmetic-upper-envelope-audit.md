# IPSM-031 — CS6/CS7 closeout, module split, and CS8 arithmetic upper-envelope audit

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: CS1–CS7 Green / source-derived smoothing control closed / CS8 independent arithmetic upper envelope open / no RH claim

## 0. Review result

The IPSM-030 implementation is Green.

The current `PascalCenteredXiPrimeSideQuadraticizationAudit.lean` now contains the following source-derived chain:

```text
common centered-Xi weighted source                         GREEN
Mellin quadratic weight adapter                            GREEN
radial weight adapter                                      GREEN
finite common-source defect sum                            GREEN
pointwise epsilon -> 0 limit density 2 * re(z)^2           GREEN
critical-axis sinc identity                                GREEN
critical-axis residual nonnegativity                       GREEN
pointwise smoothing remainder O(epsilon^2 * norm(z)^4)     GREEN
finite zero-disk smoothing envelope                        GREEN
endpoint - fixed defect absolute bound                     GREEN
smoothing envelope -> 0                                    GREEN
independent arithmetic upper envelope                      OPEN
```

The exact critical-axis source residual is nonnegative at fixed positive epsilon. Therefore the finite positive-epsilon smoothing layer must not be confused with the sign mechanism itself.

## 1. Freeze the current large audit module

`PascalCenteredXiPrimeSideQuadraticizationAudit.lean` has now grown past 3000 lines and should be treated as a completed foundation module at the IPSM-030 checkpoint.

From this point forward:

```text
DO NOT append new research phases to
PascalCenteredXiPrimeSideQuadraticizationAudit.lean
```

Exceptions:

```text
- bug fixes
- theorem statement corrections
- proof-engineering maintenance required by imports/toolchain
```

Do not move or rename the existing Green theorem surface merely for file-size cleanup. A large refactor would create unnecessary dependency and regression risk.

## 2. New module for CS8

Create:

```text
lean/dk_math/DkMath/RH/CFBRC/
  PascalCenteredXiPrimeSideArithmeticUpperEnvelopeAudit.lean
```

with the dependency:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
```

Use the same namespace:

```lean
namespace DkMath.RH.CFBRCProjection
```

This starts the import chain:

```text
PascalCenteredXiPrimeSideQuadraticizationAudit
  -> PascalCenteredXiPrimeSideArithmeticUpperEnvelopeAudit
  -> later radial/sign closure module if CS8 succeeds
```

Add the new module to the public `DkMath.RH` import surface only after it compiles independently.

## 3. CS8 mathematical target

Let conceptually:

```text
D_epsilon(W) = pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint epsilon W
D_0(W)       = pascalCenteredXiFixedSecondMomentDefectFunctional W.R
S_epsilon(W) = pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingEnvelope epsilon W.R
```

CS7 has proved, under the finite-radius smallness condition,

```text
abs (D_epsilon(W) - D_0(W)) <= S_epsilon(W)
```

and

```text
S_epsilon(W) -> 0 as epsilon -> 0+
```

This controls approximation error only.

It does not imply any sign for `D_0(W)`.

The independent CS8 target is a genuinely arithmetic upper bound of the form

```text
D_epsilon(W) <= A_epsilon(W)
```

where

```text
A_epsilon(W) -> 0 as epsilon -> 0+.
```

Combined with the already Green order adapter, this would imply

```text
D_0(W) <= 0.
```

Since the fixed Xi zero-side theory independently gives the opposite nonnegative direction only at the final fixed-defect layer, the arithmetic upper envelope must not import that fact back into CS8.

## 4. Prefer an arithmetic-source theorem, not a provider structure

Do not begin CS8 by introducing a structure whose field is already the desired endpoint inequality.

Bad first step:

```lean
structure ArithmeticUpperEnvelopeProvider ... where
  eventually_endpoint_le : ...
```

Such a structure is useful only after the mathematical source of the inequality is known.

First audit whether the finite prime/von-Mangoldt source already has one of the following mechanisms.

## 5. Route CS8-A — finite-X inequality before X -> infinity

Preferred route.

Search for a source-derived estimate on the finite arithmetic defect approximant at fixed positive epsilon and finite X.

Target shape:

```text
finite arithmetic defect <= finite nonnegative/error expression
```

with the error expression admitting, for fixed epsilon, an `X -> infinity` limit that yields a vanishing-in-epsilon endpoint envelope.

Important:

```text
X -> infinity first
then epsilon -> 0+
```

Keep the existing ordered-limit discipline. No joint limit or exchange.

If a finite-X inequality exists, transport it to `ArithmeticDefectEndpoint` only through the already established fixed-epsilon `Tendsto` theorem.

## 6. Route CS8-B — prime-source cancellation after whole-feature quadraticization

Audit whether the finite prime source behind `WholeBoxFeature` admits a decomposition

```text
arithmetic endpoint
= signed main term + nonnegative/error term
```

where the signed main term cancels by an exact prime/mirror symmetry and the remaining term is bounded by a vanishing smoothing envelope.

Do not use the two shifted whole energies merely because each is PSD.

Recall:

```text
WholeE+ >= 0
WholeE- >= 0
```

does not order `WholeE-` and `WholeE+`.

Any useful ordering must come from a new source-specific relation between the two beams.

## 7. Route CS8-C — common-source pairwise cancellation

The CS1–CS7 common-source representation suggests a more precise audit.

For each centered Xi source point `a`, the endpoint defect density is

```text
limit density 2 * a.re^2
+ smoothing remainder.
```

The smoothing remainder is small, but `2 * a.re^2` is not.

Therefore pairing `a` with its Xi symmetries cannot by itself create a vanishing upper envelope unless the arithmetic source contributes an additional signed term that cancels this off-critical density.

Audit explicitly whether the prime-side formula supplies such a signed paired contribution.

Do not assume it from zero symmetry.

## 8. Route CS8-D — contour/arithmetic completion square

A completion-square route is admissible only if the exact square is derived from the existing arithmetic integrand or contour identity.

Reject any construction that inserts the radial functional or fixed defect by definition merely to force a square.

A valid theorem must have the form:

```text
existing arithmetic quantity
= source-derived expression
= negative/nonpositive term + controlled smoothing error
```

not

```text
newly defined square := desired difference.
```

## 9. Useful immediate wrapper in the new module

Before the source audit, it is reasonable to prove a convenience theorem converting the CS7 absolute estimate into two one-sided inequalities:

```text
D_0(W) - S_epsilon(W) <= D_epsilon(W)
D_epsilon(W) <= D_0(W) + S_epsilon(W)
```

under `0 < epsilon` and `epsilon * W.R <= 1`.

This is only a smoothing wrapper. It must be documented as non-sign-producing.

A second useful theorem is that the smallness condition is eventually true along `nhdsWithin 0 (Set.Ioi 0)` for fixed finite `W.R`.

These two wrappers simplify later CS8 composition but do not count as an arithmetic provider.

## 10. CS8 acceptance condition

A successful CS8 theorem should eventually yield, without zero-side input,

```text
exists/define A_epsilon(W)
A_epsilon(W) -> 0
and eventually
ArithmeticDefectEndpoint epsilon W <= A_epsilon(W)
```

or a stronger finite-X source theorem that implies it in the prescribed limit order.

Then instantiate the existing theorem:

```lean
pascalCenteredXiFixedDefect_nonpos_of_endpoint_le_vanishingEnvelope
```

Do not re-prove the limit comparison manually.

## 11. Hard firewall

CS8 must not use any of the following as the arithmetic upper-bound source:

```text
- fixed Xi defect nonnegativity
- horizontal zero energy nonnegativity
- anti-mirror zero energy
- RH or any RH-equivalent vanishing theorem
- the final fixed-defect iff RH theorem
- reverse or joint X/epsilon limit exchange
- synthetic completion square containing the radial term by definition
```

The purpose of CS8 is precisely to discover an independent prime-side inequality.

## 12. Expected closeout possibilities

### Green-A — genuine arithmetic envelope

```text
source-derived endpoint upper envelope     GREEN
envelope -> 0                              GREEN
fixed defect <= 0                          GREEN
```

Then proceed to the final radial/sign closure layer in a new module.

### Green-B — named obstruction

If all source routes fail, add a new named gap in the new module, not the frozen 3000-line module:

```lean
inductive PascalCenteredXiPrimeSideArithmeticUpperEnvelopeGap : Prop
  | noIndependentVanishingArithmeticUpperEnvelope :
      PascalCenteredXiPrimeSideArithmeticUpperEnvelopeGap
```

This records the exact frontier without altering the already Green smoothing layer.

## 13. Validation

For the new module require:

```text
direct lake env lean
lake build DkMath.RH.CFBRC.PascalCenteredXiPrimeSideArithmeticUpperEnvelopeAudit
./lb DkMath.RH.CFBRC.PascalCenteredXiPrimeSideArithmeticUpperEnvelopeAudit
lake build DkMath.RH
git diff --check
```

The old `PascalCenteredXiPrimeSideQuadraticizationAudit.lean` should remain unchanged during CS8 unless a genuine bug is found.
