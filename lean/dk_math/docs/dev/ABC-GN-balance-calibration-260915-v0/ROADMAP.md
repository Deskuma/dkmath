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

The checkpoint exposed the outer ABC support/depth coordinates and the exact outer balance

```text
ABCOuterBalance = abcGap
```

while retaining the distinct inner GN sign convention and the pointwise correction built from `GNCalibrationResidual`.

Status: **complete / Outcome A** at commit `748adca6ee93715ecf5d30c90ed2352f7e0d23c2`.

## BCAL-002 — Exact calibration-source decomposition

Completed exact decomposition:

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

Status: **complete / Outcome A** at commit `670acf204798d7965f32faffb0e1ab5ac1102282`.

## BCAL-003 — Local valuation balance law

For every fresh non-exceptional support prime `q`, with `v = v_q(GN)` and `w = log q`, the exact local accounting is:

```text
support contribution = w
depth contribution   = (v-1)w
local mass            = vw
local balance         = (2-v)w.
```

Thus valuation depth `v = 2` is the local pivot:

```text
v = 1  -> positive
v = 2  -> zero
v >= 3 -> negative.
```

Global `Q = 0` is not identified with all valuations being `2`.

Status: **complete / Outcome A** at commit `d083a6a2b9752baa1524ceab80dfd5ddc58966a8`.

## BCAL-004 — Cubic shell coordinate bridge

The generic non-exceptional bridge is exact:

```text
GNChannelBalance
  = log(nonExceptionalSingleLayer)
    - log(twoTail(nonExceptionalPart)).
```

The repeated part splits as

```text
repeatedPrimePowerPart
  = piSqRad^2 * twoTail,
```

so `piSqRad^2` is the neutral valuation-two pivot and `twoTail` is precisely the over-depth tail.

The full cubic complement may additionally contain exceptional prime `3` at valuation one, so the first full-complement identification required a side condition.

Status: **complete / Outcome B — PARTIAL BRIDGE** at commit `e211e0472280515ff0adca8f2b287a387fa1e2c1`.

## BCAL-005 — Exceptional cubic gauge completion

BCAL-004's bounded mismatch is completed exactly.

For `F(a) = GN 3 a 1`:

```text
GNExceptionalSupportProduct 3 a 1
  = if 3 ∣ F(a) then 3 else 1
```

and the full complement factors exactly as

```text
GNExcessCubicComplement
  = exceptional support product
    * non-exceptional single layer.
```

The exceptional factor never enters `twoTail`, because its valuation is at most one. Therefore the unconditional full-shell bridge is:

```text
GNChannelBalance
  = log(full cubic complement)
    - log(full twoTail)
    - log(exceptional support product).
```

Rewriting the last term through BCAL-002 shows that the full-shell discrepancy is exactly the already-existing `GNExceptionalGaugeSlack` coordinate, not a new correction.

Status: **complete / Outcome A — EXACT EXCEPTIONAL COMPLETION** at commit `7aa08d384b8c6b21c5da095e73964cc5ba15d8b2`.

## BCAL-006 — Depth-step / finite Hensel transport audit

The local ruler and finite root tree are now connected without confusing exact valuation with divisibility threshold depth.

Level A proves, under the explicit exact successor hypothesis

```text
v_q(GN p a' b) = v_q(GN p a b) + 1,
```

the exact coordinate transport

```text
localMass    -> localMass + log q
localBalance -> localBalance - log q.
```

Level B proves canonical downward reduction

```text
R_(k+1) -> R_k,
r |-> r mod q^k.
```

Level C combines the existing simple-root Hensel uniqueness with that reduction to obtain successor injectivity and

```text
card R_(k+1) <= card R_k.
```

No lift-existence theorem, infinite branch, or cardinality equality is asserted.

Status: **complete / Outcome A — EXACT DEPTH TRANSPORT** at commit `f68cb617a2db3fed875655037ce966db3d659b51`.

## BCAL-007 — Two-channel / PowerSwap abstraction audit

Active via `instruction-007.md`.

The preceding checkpoints now provide two substantive consumers of the same exact linear coordinate transform.

PowerSwap:

```text
U = gapU
V = gapV
center  = (U + V)/2
balance = U - V.
```

ABC/GN:

```text
U = GNChannelSupportMass
V = GNChannelDepthMass
mass    = U + V
balance = U - V.
```

BCAL-006 additionally gives the right-channel transport instance

```text
V -> V + δ
mass    -> mass + δ
balance -> balance - δ.
```

The checkpoint first audits for an existing public abstraction. If none exists, it may extract a small dependency-neutral `DkMath.Lib.*` two-channel kernel containing only exact reconstruction, zero-contour, swap-symmetry, and one-channel transport laws.

PowerSwap and ABC/GN should consume the kernel through bridge theorems while retaining their existing domain-specific public definitions and meanings.

The goal is reuse of the linear coordinate transform, **not** an assertion that PowerSwap and ABC are the same mathematical theory.

## BCAL-008 — Quantitative calibration frontier

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
