# RH-CFBRC Common-Kernel Second Source Roadmap

Date: 2026-08-20

Branch: `wip/RH-CFBRC-common-kernel-second-source-260820-v0`

Base: `develop` at `c29de6da5a6c180483fea6b216ad6281402396fb`

## 0. Route identity

This route begins after ZDI closed at `O-INFORMATION` and ZDSS isolated the exact same-scale cross-endpoint frontier.

The purpose is not to refine Eta endpoint asymptotics. Those asymptotics already show that an off-critical factor survives on the raw common scale.

The purpose is to search for a genuinely independent zero-derived source in which original and critical-mirror data are coupled from the beginning by one common kernel, one common measure, and one common scale.

```text
standard nontrivial zeta zero
  -> common-kernel source
  -> same-scale original/mirror coupling
  -> positive centered detector
  -> shrinking centered coordinate
  -> existing DkReal uniqueness
  -> Mathlib RiemannHypothesis
```

No RH-equivalent provider may be introduced as an assumption.

## 1. Trusted Core

Do not re-prove:

```text
endpoint pair source                 FOUND
endpoint positive scalar U-side      FOUND
exact individual tail rates          FOUND
raw common-scale dichotomy           FOUND
same-scale coupling provider         MISSING
global frequent-upper provider       RH-EQUIVALENT
DkReal completion                    READY / INACTIVE
```

For a nonreal standard zero,

```text
A_K(s) = etaPairedPartial K s
B_K(s) = etaPairedPartial K (criticalMirror s)
```

are separately zero-derived finite sources. Their difference is the old P2-F projection.

The natural positive scalar

```text
E_K(s) = ||A_K(s)||^2 + ||B_K(s)||^2
```

tends to zero, but no source-derived centered-coordinate lower bound is known.

Each endpoint has a nonzero natural normalized rate, and the raw ratio retains the horizontal factor

```text
||B_K(s)|| / ||A_K(s)|| ~ K^(2 * centeredSigma s.re).
```

ZDSS-005 proves the exact raw-ratio dichotomy and shows that a global frequent-upper-control provider is RH-equivalent.

## 2. Hard stop

Do not extend the exhausted Eta-tail route with:

```text
endpoint-specific normalizations
higher tail terms
new norms or polarizations of the same endpoint pair
new subsequence/cofinal wrappers
moving-frame or positive-density residual estimates
RH-equivalent raw-ratio provider wrappers
```

## 3. CKSS-000 — frontier consolidation

1. Verify the public `DkMath.RH` import surface.
2. Export `ZeroDerivedSameScaleCrossEndpointCouplingAudit` if missing.
3. Build the root module.
4. Record the frontier ledger above.

No new mathematics is required.

## 4. CKSS-001 — common-kernel source API audit

Audit the installed Mathlib/DkMath APIs underlying the completed-zeta functional equation.

Priority families:

```text
Hurwitz/Riemann zeta even functional-equation infrastructure
Mellin-transform representations
Jacobi-theta / theta inversion infrastructure
completed-zeta integral representations
existing DkMath Mellin kernels
```

The target is not merely a final reflected equality. Seek an actual source representation in which original and reflected data inhabit one common integration/summation object.

Preferred schematic form:

```text
C(s) = integral W(x) * Phi(x,s) dx
```

where, after

```text
s = 1/2 + delta + i*t,
```

the same variable, measure, and source kernel expose both mirror amplitudes on one scale.

Classify exactly one:

```text
COMMON-KERNEL-SOURCE-FOUND
FUNCTIONAL-EQUATION-TRANSPORT-ONLY
COMMON-KERNEL-API-GAP
```

Do not invent a heuristic approximate functional equation if no exact API exists.

## 5. CKSS-002 — centered common-kernel factorization

Proceed only after `COMMON-KERNEL-SOURCE-FOUND`.

Factor the actual source around `s = 1/2 + delta + i*t` into roles such as

```text
common radial kernel
horizontal mirror amplitude
cycle state
```

The two sides must remain on the same source variable and normalization.

## 6. CKSS-003 — source-rank audit

Before quadraticization, reject candidates that are only:

```text
conjugation
critical-mirror swap
functional-equation rewrite
nonzero scalar multiplication
invertible linear transport
fixed-Xi defect renamed
post-processing of the existing endpoint pair
```

If no genuine information gain is found, close the route with a named obstruction.

## 7. CKSS-004 — positive common-kernel detector

Only after source independence is certified, test a centered positive detector.

For `x > 1`, the canonical pointwise shape is

```text
G_x(delta) = x^delta + x^(-delta) - 2
```

with

```text
G_x(delta) = (x^(delta/2) - x^(-delta/2))^2 >= 0.
```

Audit whether the actual zero-derived source yields an integrated or finite source-matched positive scalar.

Stop if the only inequality direction is whole-integral smallness without diagonal-energy upper control.

## 8. CKSS-005 — centered coercivity

If a zero-derived positive scalar `E` is obtained, seek

```text
c * (centeredSigma s.re)^2 <= E
```

with `c > 0`, or a sequence form

```text
c_K * (centeredSigma s.re)^2 <= E_K <= epsilon_K
epsilon_K / c_K -> 0.
```

Historical prime-mirror, aggregate-Gap, or fixed-Xi energies may be used only through exact source-preserving comparison theorems.

## 9. CKSS-006 — DkReal completion

Only after a shrinking centered-coordinate bound is proved, reuse the existing DkReal uniqueness layer and existing RH wrapper.

Do not rebuild either layer.

## 10. Fixed-Xi firewall

Existing finite centered-Xi / Weil-style anti-mirror identities are representation theorems, not vanishing providers.

A CKSS result is new only if the common-kernel source supplies an independent zero-derived upper/sign relation for the positive defect.

## 11. Stop conditions

Stop and record an obstruction if:

1. the candidate is only functional-equation transport;
2. it is recoverable from the endpoint pair by invertible algebra;
3. positivity needs an unavailable reverse inequality;
4. the desired bound is assumed or RH-equivalent;
5. the route returns to endpoint-specific normalizations;
6. successive modules merely rename the same missing relation.

## 12. Immediate target

Start only with CKSS-000 and CKSS-001.

```text
A. Is ZDSS-005 exported from DkMath.RH?
B. Which exact theorem generates the completed-zeta functional equation?
C. Does it expose a common kernel before reflection, or only the final reflected equality?
```

Do not proceed to quadraticization until C is answered by an exact source theorem.
