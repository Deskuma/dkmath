Global objective:

zero configuration
  -> independent source
  -> off-critical detector
  -> arithmetic control
  -> centered-coordinate uniqueness
  -> RiemannHypothesis

Current GWSS stage:

`GWSS-001M-B` — q=0 discharge and exact two-/three-orbit Mellin-jet rank.

Load-bearing boundary:

No RH assumption, classical Weil positivity, Li criterion, fixed-Xi defect
vanishing provider, `T -> infinity` horizontal decay provider, limit exchange,
or prime-side sign assumption is used.  The actual-window selector remains
carrier-dependent and is not treated as an independent witness.  Jet rank is
not promoted to finite-`τ` evaluation rank.

Next unresolved Gap:

`FINITE-TAU-EVALUATION-SEPARATION-GAP`

## B0 q=0 actual-window classification

`ACTUAL-WINDOW-QZERO-OBSTRUCTION-DISCHARGED`

For `z ∈ pascalCenteredXiZeroDiskFinset R`, the module proves
`z ≠ 0` and `z ^ 2 ≠ 0`.  The proof transports membership to
`NontrivialRiemannZetaZero (criticalLineCenter + z)` and applies the existing
unconditional theorem `nontrivialRiemannZetaZero_im_ne_zero`.  No RH input is
introduced.

The generic bare-kernel theorem remains true: both
`complexExpSecondDifferenceKernel τ 0 = 0` and the corresponding specialized
Mellin-family null-coordinate theorem are preserved in the finite-jet module.
The actual Xi carrier simply excludes that coordinate.

## B1 two-orbit jet-rank result

`twoOrbitMellinJetDeterminant_eq` proves the exact identity

```text
q₁ * (q₂² / 12) - q₂ * (q₁² / 12)
  = q₁ * q₂ * (q₂ - q₁) / 12.
```

`twoOrbitMellinJetDeterminant_ne_zero` proves nonvanishing from
`q₁ ≠ 0`, `q₂ ≠ 0`, and `q₁ ≠ q₂`.  The actual-window corollary obtains the
nonzero hypotheses from B0 and only assumes distinct squared orbits; it does
not require `z₁ ≠ z₂`.

## B2 three-orbit jet-rank result

`threeOrbitMellinJetDeterminant_eq` proves by direct scalar expansion that the
first three jet rows have determinant

```text
q₁ * q₂ * q₃ * (q₂ - q₁) * (q₃ - q₁) * (q₃ - q₂) / (12 * 360).
```

The corresponding nonvanishing theorem and actual Xi-window corollary are
implemented.  This is intentionally a fixed 3-orbit identity, not a general
Vandermonde or matrix framework.

## Primary bounded-stage classification

`MELLIN-LOW-JET-ACTUAL-WINDOW-RANK-FOUND`

All B0/B1/B2 requirements are met.  This classifies only the finite local jet
coefficient rank of the actual squared-orbit carrier, not the full Mellin
family at finite parameter values.

## Spectral-factor firewall

No additional spectral-factor determinant was introduced.  The existing
centered Mellin spectral factor is not silently replaced by `1`, and no claim
of finite-`τ` evaluation separation is made.

## GWSS-002 authorization status

Not authorized and not started.  A later finite-parameter separation theorem
for the zero-independent Mellin family is still required.

## Verification

Focused build:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinLowRankAudit
```

`git diff --check` succeeds.  No `sorry`, `admit`, or new `axiom` was added.

