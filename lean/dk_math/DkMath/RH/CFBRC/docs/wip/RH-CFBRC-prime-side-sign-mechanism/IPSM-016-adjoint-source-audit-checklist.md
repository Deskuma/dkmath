# IPSM-016 — Adjoint source audit checklist

Date: 2026-08-14

Current continuous layer:

```text
right-edge node                 GREEN
coefficient density             GREEN
Gram feature                    GREEN
BoxFeature factorization        GREEN
aggregated feature              GREEN
continuous Gram energy          GREEN
fixed-epsilon nonnegativity     GREEN
source adjoint identity         OPEN
whole-surface bridge            OPEN
```

Keep the variables distinct:

```text
n = arithmetic mode
t = contour-height index
u = Mellin-box variable
```

## Contract note

Before using `PascalCenteredXiPrimeSideQuadraticizationContinuousAdjointProvider`, connect its provenance to a concrete mirrored source observable by equality. The current `source_derived : Prop` field alone does not encode that equality.

## Next theorem targets

### D1

Prove the right-edge coordinate identity under `t -> -t` and its conjugation consequence for the coefficient-free Gram feature.

### D2

Audit the finite PHZ cutoff for an exact right-edge conjugation identity. The finite source is built from real logarithmic coefficients and Euler prime-power modes, so this should be checked directly at finite `X`.

### D3

Audit the archimedean and elementary source terms separately for the same right-edge conjugation law. Only after all source components are available should a full vertical-amplitude conjugation theorem be stated.

### D4

Define a mirrored box feature from the existing source using `t -> -t`, aggregate it over the same finite interval, and prove its relation to the conjugate aggregated feature.

### D5

Classify the existing contour relations. Current APIs give reflection and additive pairing for left/right and top/bottom edges. Check separately whether any theorem supplies a Hermitian product relation; additive pairing alone is not such a relation.

## Boundary

The continuous Gram energy contains the vertical amplitude only. Top-horizontal and radial comparison terms remain separate.

Next sequence:

```text
D1  right-edge conjugation
D2  finite prime-cutoff conjugation
D3  correction conjugation
D4  mirrored aggregate relation
D5  additive-pairing / Hermitian-product classification
```
