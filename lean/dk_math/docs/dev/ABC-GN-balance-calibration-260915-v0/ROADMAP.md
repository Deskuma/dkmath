# ABC–GN Balance / Calibration Roadmap

This roadmap is intentionally structure-first.

The structural/calibration campaign is now complete. Numerical optimization is not continued on this branch because BCAL-008 identified a missing deterministic bridge between aggregate quantitative estimates and the pointwise calibration budget.

## BCAL-000 — Coordinate extraction

Established

```text
S = fresh support mass
E = repeated valuation-depth mass
M = S + E
Q = S - E
Cal = M - rho*R
```

and the production calibration/budget bridge.

Status: **complete / Outcome A** at commit `39022f480db874c91432f4c114bb7e1c3661fa5b`.

## BCAL-001 — Outer ABC balance bridge / pointwise calibration

Exposed the outer ABC support/depth coordinates and exact outer balance

```text
ABCOuterBalance = abcGap
```

while retaining the distinct inner GN orientation and the pointwise correction built from `GNCalibrationResidual`.

Status: **complete / Outcome A** at commit `748adca6ee93715ecf5d30c90ed2352f7e0d23c2`.

## BCAL-002 — Exact calibration-source decomposition

Completed the exact decomposition into pointwise calibration residual, return slack, and exceptional gauge slack. Prime-exponent lifted-radical transport is exact and contributes no slack on this route.

Status: **complete / Outcome A** at commit `670acf204798d7965f32faffb0e1ab5ac1102282`.

## BCAL-003 — Local valuation balance law

For every fresh non-exceptional support prime `q`, with `v = v_q(GN)` and `w = log q`:

```text
local mass    = v*w
local balance = (2-v)*w
```

so valuation depth `v=2` is the local balance pivot.

Status: **complete / Outcome A** at commit `d083a6a2b9752baa1524ceab80dfd5ddc58966a8`.

## BCAL-004 — Cubic shell coordinate bridge

Established the exact generic non-exceptional shell bridge and isolated the only mismatch in the full cubic complement: exceptional prime `3` at single-layer depth.

Status: **complete / Outcome B — PARTIAL BRIDGE** at commit `e211e0472280515ff0adca8f2b287a387fa1e2c1`.

## BCAL-005 — Exceptional cubic gauge completion

Completed the BCAL-004 mismatch exactly. The full cubic complement is exceptional single layer times non-exceptional single layer; the exceptional term is exactly the existing BCAL-002 gauge coordinate.

Status: **complete / Outcome A — EXACT EXCEPTIONAL COMPLETION** at commit `7aa08d384b8c6b21c5da095e73964cc5ba15d8b2`.

## BCAL-006 — Depth-step / finite Hensel transport

Established:

```text
exact valuation successor:
  localMass    -> localMass + log q
  localBalance -> localBalance - log q

canonical root transport:
  depth k+1 -> depth k

simple-root uniqueness:
  successor reduction is injective
  card R_(k+1) <= card R_k
```

No lift-existence or equality of successive cardinalities is claimed.

Status: **complete / Outcome A — EXACT DEPTH TRANSPORT** at commit `f68cb617a2db3fed875655037ce966db3d659b51`.

## BCAL-007 — Two-channel / PowerSwap abstraction

Extracted the stable dependency-neutral kernel

```text
mass(u,v)    = u + v
balance(u,v) = u - v
center(u,v)  = (u + v)/2
```

with exact PowerSwap and ABC/GN consumer bridges while preserving the existing domain APIs.

Status: **complete / Outcome A — GENERIC KERNEL JUSTIFIED** at commit `7c4a1137c92c21d83a3803f46eaec062b30cf718`.

## BCAL-008 — Quantitative calibration frontier audit

The existing quantitative interfaces were classified by population, measured quantity, normalization, and current coordinate class (`S`, `E`, `M`, `Q`, `Cal`, or aggregate/proxy).

The audit established:

```text
historical 0.435 route
  != current pointwise M/Cal theorem

count / average / moment / shell exponents
  != pointwise calibration slopes without an explicit bridge

current pointwise frontier:
  conditional M <= rho*R + C
  <-> Cal <= C

current aggregate frontier:
  finite Hensel layer/depth averages
  + cubic realized shell/incidence/moment bounds
```

The missing ingredient is a deterministic selector / cover / compensation theorem that converts the aggregate information into compatible pointwise `S` and `E` bounds in the same `R` normalization.

No exponent improvement, new constant, density-to-pointwise promotion, or ABC conclusion was introduced.

Status: **complete / Outcome A — CALIBRATED QUANTITATIVE MAP COMPLETE** at commit `6dcf3f7c5051a898d7233a6d79648d1cbacc1849`.

## Campaign closeout

This branch is closed as a structural/calibration success.

The final closeout is recorded in:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/FINAL_REPORT.md
```

A future quantitative campaign should begin only from the explicit missing bridge:

```text
aggregate counting / layer / incidence / moment control
        ↓
deterministic selector / cover / compensation
        ↓
pointwise S and E budgets in one R-normalization
        ↓
M <= rho*R + C
        <->
Cal <= C
```

Historical constants and exponents must remain classified by their actual theorem population and quantity until such a bridge exists.

## Global stop rule

The branch must not be extended by merely renaming a statement equivalent to `ABCGNOddPrimeJointContract`, by optimizing incompatible exponents, or by inferring pointwise bounds from density/average statements.

**Campaign status: CLOSED / STRUCTURAL-CALIBRATION COMPLETE.**
