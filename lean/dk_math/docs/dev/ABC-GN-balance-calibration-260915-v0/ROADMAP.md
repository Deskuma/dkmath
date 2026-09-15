# ABC–GN Balance / Calibration Roadmap

This roadmap is intentionally structure-first.

Numerical exponents and uniform bounds are postponed until the balance law and calibration mechanism are explicit.

## BCAL-000 — Coordinate extraction

Goal:

```text
S = fresh support mass
E = repeated valuation-depth mass
M = S + E
Q = S - E
Cal = M - ρR
```

Production target:

```text
joint pressure iff Cal <= C
```

No new arithmetic bound.

Status: **complete / Outcome A** at commit `39022f480db874c91432f4c114bb7e1c3661fa5b`.

## BCAL-001 — Outer ABC balance bridge / pointwise calibration

Place the GN calibration coordinate and the already-existing outer ABC coordinate in one bridge layer:

```text
outer imbalance:
  abcGap
  = valuationExcess(c) - log(rad(ab))
  = abcEpsilon * radLog

inner GN calibration:
  Cal = S + E - ρ*radLog
```

The pointwise calibration function is:

```text
pointwiseCorrection(T,p,ρ)
  = (Cal(T,p,ρ) + log(rad p))
      / ((p-1) * radLog(T)).
```

The checkpoint also exposes the outer ABC support/depth mass coordinates and the exact outer balance

```text
ABCOuterBalance = abcGap.
```

The GN inner balance and ABC outer balance deliberately retain opposite sign conventions and are not identified.

Status: **complete / Outcome A** at commit `748adca6ee93715ecf5d30c90ed2352f7e0d23c2`.

## BCAL-002 — Exact calibration-source decomposition

Open the checkpoint-001 safe pointwise correction and identify its exact slack sources.

The completed decomposition is:

```text
ReturnSlack
  = log GN - (p-1) log c
  >= 0

ExceptionalGaugeSlack
  = log(rad p) - log(exceptional support)
  >= 0

abcEpsilon
  = GNEpsilon + ExactCalibrationCorrection

GNPointwiseCalibrationCorrection
  = ExactCalibrationCorrection
    + normalized(ReturnSlack + ExceptionalGaugeSlack).
```

Prime-exponent lifted-radical transport is exact, so it contributes no slack on this route.
The uniform allowance `C` remains a later family-level envelope, not a source of pointwise arithmetic slack.

Status: **complete / Outcome A** at commit `670acf204798d7965f32faffb0e1ab5ac1102282`.

## BCAL-003 — Local valuation balance law

The next checkpoint studies the signed coordinate

```text
Q = S - E
```

using the already-formalized finite depth-layer decomposition.

For every fresh non-exceptional support prime `q`, write conceptually

```text
v = v_q(GN)
w = log q.
```

Then the exact local accounting should expose

```text
support contribution = w
depth contribution   = (v-1)w
local mass            = vw
local balance         = (2-v)w.
```

Thus valuation depth `v = 2` is the **local** support/depth balance pivot:

```text
v = 1  -> positive support-side contribution
v = 2  -> zero local balance
v >= 3 -> negative depth-side contribution.
```

Global targets:

```text
GNChannelMass
  = sum of local masses

GNChannelBalance
  = sum of local balances
  = first support layer - all repeated-depth layers.
```

This checkpoint identifies the local ruler of the scale. It does **not** claim that global `Q = 0` forces every valuation to equal `2`; local positive and negative contributions may cancel.

Status: **active via `instruction-003.md`**.

## BCAL-004 — Cubic shell coordinate bridge

For the cubic specialization, compare the GN balance coordinates with the shell decomposition

```text
F(a) = M_shell * S_shell
```

where `M_shell` is the complete repeated/square-full part and `S_shell` is the squarefree complement.

Introduce logarithmic shell coordinates only after exact production identities have been inventoried:

```text
shellMass    = log(M_shell) + log(S_shell)
shellBalance = log(M_shell) - log(S_shell)
```

Research question:

```text
Does an exact or monotone transport exist between
  GNChannelBalance
and
  shellBalance ?
```

The local valuation law from BCAL-003 should be used to interpret shell repeated powers before any counting estimate is attempted.

A negative result is acceptable and should be recorded precisely.

## BCAL-005 — PowerSwap / contour abstraction audit

Only if BCAL-000 through BCAL-004 reveal genuine reuse, audit whether the common pattern belongs in a generic module rather than ABC:

```text
two real components U,V
mass    M = U + V
balance Q = U - V
reconstruction U=(M+Q)/2, V=(M-Q)/2
zero contour Q=0
```

Do not force an abstraction merely for aesthetic symmetry. A generic layer is justified only if it has at least two real consumers, e.g. `PowerSwap` and `ABC`.

## BCAL-006 — Quantitative calibration frontier

Only after the structural checkpoints are stable should the project return to numerical estimates.

At that point reinterpret previous numbers as measurements of the calibrated balance region:

```text
old radical/support slopes
shell-count exponents
square-full counting exponents
moment exponents
```

The first quantitative question is not "what is the best exponent?" but:

```text
Which supporting line / contour / residual component is that exponent measuring?
```

Only then decide whether a sharper bound is mathematically meaningful.

## Global stop rule

If a checkpoint merely renames a statement equivalent to `ABCGNOddPrimeJointContract` without revealing an exact internal component, stop and report it as structural normalization.

The branch succeeds if it makes the calibration mechanism more explicit even if no new ABC-strength bound is proved.
