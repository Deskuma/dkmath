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

The signed coordinate

```text
Q = S - E
```

was expanded prime by prime using the existing finite depth-layer decomposition.

For every fresh non-exceptional support prime `q`, with

```text
v = v_q(GN)
w = log q,
```

the exact local accounting is:

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

Global `Q = 0` is not identified with all valuations being `2`; cancellation remains possible.

Status: **complete / Outcome A** at commit `d083a6a2b9752baa1524ceab80dfd5ddc58966a8`.

## BCAL-004 — Cubic shell coordinate bridge

The cubic shell audit compared the BCAL signed balance with repeated-prime-power / squarefree-complement coordinates.

The generic non-exceptional bridge is exact:

```text
GNChannelBalance
  = log(nonExceptionalSingleLayer)
    - log(twoTail(nonExceptionalPart)).
```

The existing repeated part already splits as

```text
repeatedPrimePowerPart
  = piSqRad^2 * twoTail,
```

so `piSqRad^2` is the neutral valuation-two pivot and `twoTail` contains exactly the over-depth `v-2` tail.

For the cubic family, the full complement may additionally contain exceptional prime `3` at valuation one.  Therefore the full complement cannot be identified unconditionally with the BCAL non-exceptional single layer.

Status: **complete / Outcome B — PARTIAL BRIDGE** at commit `e211e0472280515ff0adca8f2b287a387fa1e2c1`.

This is a bounded information mismatch, not a failure of the generic bridge.

## BCAL-005 — Exceptional cubic gauge completion

Active via `instruction-005.md`.

The goal is to make the BCAL-004 missing exceptional single layer explicit rather than excluding it by the side condition `¬ 3 ∣ GN 3 a 1`.

Primary candidate identities:

```text
full cubic complement
  = exceptional support product
    * non-exceptional single layer
```

and

```text
GNChannelBalance
  = log(full cubic complement)
    - log(full twoTail)
    - log(exceptional support product).
```

Then reuse BCAL-002:

```text
ExceptionalGaugeSlack
  = log(rad 3) - log(exceptional support product)
```

so the cubic full-shell discrepancy is recognized as the same exceptional gauge coordinate already present in the exact calibration accounting.

No new numerical estimate or ABC-strength contract is permitted.

## BCAL-006 — Depth-step / Hensel transport audit

Only after the shell coordinate is exact, investigate whether existing valuation/Hensel APIs support a genuine transition law for a fixed prime channel.

The local balance formula suggests the formal target

```text
v -> v + 1
localMass    -> localMass + log q
localBalance -> localBalance - log q.
```

This is currently a **research target**, not an established theorem.

The checkpoint must first inventory existing Hensel / lifting / valuation-step APIs and distinguish:

- a tautological arithmetic rewrite under an explicit valuation-equality hypothesis;
- an actual arithmetic theorem producing the next valuation depth;
- a merely heuristic "mutation" interpretation.

A negative audit result is acceptable.

## BCAL-007 — PowerSwap / contour abstraction audit

Only if the preceding checkpoints reveal genuine reuse, audit whether the common pattern belongs in a generic module rather than ABC:

```text
two real components U,V
mass    M = U + V
balance Q = U - V
reconstruction U=(M+Q)/2, V=(M-Q)/2
zero contour Q=0
```

Do not force an abstraction merely for aesthetic symmetry.  A generic layer is justified only if it has at least two substantive consumers, e.g. `PowerSwap` and `ABC`.

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
