# RH-CFBRC spectral-gauge closure handoff

Date: 2026-08-05

## Closed route

The off-critical exclusion audit route is closed by:

- `EtaCriticalMirrorPairedFrameSpectralGaugeDirectionAudit`
- `EtaCriticalMirrorPairedFrameSpectralGaugeClosureDecision`

The pair-left spectral gauge depends only on the imaginary coordinate. Any predicate determined solely by one fixed gauge value is invariant under all real spectral translations and therefore cannot characterize `s.re = 1 / 2` on the whole complex plane.

Retain all earlier modules as no-go or compatibility Core. Do not resume:

- searches for an `hcollapse` provider;
- additional mirror, conjugation, or functional-equation orbit variants;
- collisions between distinct sequences with limits `±C`, `conj C`, or `-conj C`;
- attempts to derive the critical line from the spectral gauge alone.

## Build gate

Before branching, run:

```bash
cd lean/dk_math

lake build \
  DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameSpectralGaugeClosureDecision

lake build \
  DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameSpectralGaugeClosureDecision

./lean-build.sh && ./lean-test.sh
```

The closure route is complete only after this full local build is Green.

## Next branch

Create from the Green closure commit:

```text
wip/RH-CFBRC-moving-line-collision-260805-v0
```

The new route begins with the projective moving real line
`etaPairMovingRealLine(s,k) = B_k(s)⁻¹ • ℝ`, followed by two-scale projective nonresonance and an independently supplied global zero-line lock. The global line must not be defined from the endpoint itself and must not contain RH-equivalent assumptions.
