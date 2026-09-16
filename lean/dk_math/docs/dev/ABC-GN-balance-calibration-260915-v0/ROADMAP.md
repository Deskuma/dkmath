# ABC–GN Balance / Calibration Roadmap

This roadmap is intentionally structure-first.

Numerical exponents and uniform bounds were postponed until the balance law and calibration mechanism became explicit.

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

Established three distinct levels:

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

A genuine two-consumer abstraction was found and extracted as a stable dependency-neutral kernel:

```text
mass(u,v)    = u + v
balance(u,v) = u - v
center(u,v)  = (u + v)/2
```

with reconstruction, swap symmetry, and left/right channel transports.

Exact consumer bridges now identify:

```text
PowerSwap:
  gapP = center(gapU,gapV)
  gapQ = balance(gapU,gapV)

ABC/GN:
  GNChannelMass    = mass(S,E)
  GNChannelBalance = balance(S,E)
```

Existing domain definitions and direct proofs remain intact.

Status: **complete / Outcome A — GENERIC KERNEL JUSTIFIED**.

## BCAL-008 — Quantitative calibration frontier

Active via `instruction-008.md`.

The structural phase is now sufficiently explicit to revisit historical quantitative estimates without conflating their dimensions.

This checkpoint audits actual theorem statements and classifies each estimate by:

```text
population
measured quantity
normalization
statement type
coordinate class:
  support / depth / mass / balance / calibration residual / proxy
```

Historical constants such as `0.435`, `0.20`, `0.23`, and `0.005` must be interpreted by what their Lean theorems actually prove. Matching decimal arithmetic is not evidence that constants are composable.

The checkpoint must distinguish at least:

```text
pointwise mass/calibration bounds
counting bounds
average bounds
moment bounds
shell-count exponents
asymptotic exceptional-set estimates
```

and identify the strongest currently existing pointwise endpoint separately from the strongest counting/average endpoint.

No exponent improvement or new ABC-strength contract is part of this checkpoint.

## After BCAL-008

If the quantitative audit identifies a dimensionally valid and nontrivial numerical frontier, open a new campaign for optimization rather than extending this structural branch indefinitely.

If instead the existing quantitative route still lacks a deterministic bridge from counting/average control to pointwise calibration, record that frontier explicitly and close this branch as a structural/calibration success.

## Global stop rule

If a checkpoint merely renames a statement equivalent to `ABCGNOddPrimeJointContract` without revealing an exact internal component, stop and report it as structural normalization.

The branch succeeds if it makes the calibration mechanism and the status of the quantitative frontier explicit even if no new ABC-strength bound is proved.
