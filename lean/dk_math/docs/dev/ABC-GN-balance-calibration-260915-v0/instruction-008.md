# instruction-008 — Quantitative calibration frontier audit

## 0. Purpose

BCAL-000 through BCAL-007 extracted exact coordinates, exact slack sources, local valuation balance, shell bridges, finite depth transport, and a reusable two-channel kernel.

Only now return to the older quantitative ABC/GN estimates.

This checkpoint is **not** an exponent-improvement campaign.  Its purpose is to classify existing quantitative theorems by the exact structural coordinate they measure and to determine which numerical constants are dimensionally compatible with the current calibration picture.

Primary question:

> What exact coordinate / residual / supporting line was each historical exponent measuring?

Do not optimize constants before answering that question.

## 1. Required repository-first audit

Inventory the existing production and archived quantitative APIs relevant to at least the following families:

- historical `0.435` route and `delta_0435_final`;
- support/radical growth bounds;
- valuation-excess / `piSqRad` / `twoTail` bounds;
- shell-count and square-full / repeated-part bounds;
- fixed-prime Hensel residue counting / finite layer-cake bounds;
- realized shell / dyadic / incidence / moment bounds from the later cubic campaign;
- any theorem currently feeding `GNNonExceptionalChannelMassBudgetAffine`, odd-prime joint pressure, or equivalent budget statements.

Read the actual theorem statements, not just old prose summaries.

For each numerical theorem, record:

1. theorem name and source file;
2. quantified population (`all triples`, fixed prime, interval `[0,X]`, shell, average, etc.);
3. measured quantity;
4. normalization / scale;
5. theorem type: pointwise, counting, average, moment, asymptotic, or finite exact;
6. whether it controls `support`, `depth`, `mass`, `balance`, `calibration residual`, or only a proxy;
7. whether its constant can legally be added to another constant without an additional bridge theorem.

## 2. Current exact coordinate dictionary

Use the current production coordinates as the reference frame.

For the non-exceptional GN channel:

```text
S = GNChannelSupportMass
E = GNChannelDepthMass
M = GNChannelMass    = S + E
Q = GNChannelBalance = S - E
Cal = M - rho * R
R = Triple.radLog
```

Generic two-channel reconstruction:

```text
S = (M + Q)/2
E = (M - Q)/2
```

Local prime law:

```text
v = v_q(GN)
w = log q
localMass    = v*w
localBalance = (2-v)*w
```

Shell bridge:

```text
Q = log(single layer) - log(twoTail)
```

with the cubic exceptional correction already completed in BCAL-005.

Calibration source decomposition:

```text
abcEpsilon
  = GNEpsilon + ExactCalibrationCorrection

PointwiseSafeCorrection
  = ExactCalibrationCorrection
    + normalized(ReturnSlack + ExceptionalGaugeSlack)
```

These exact identities are the coordinate system into which old estimates must be translated.

## 3. Historical `0.435` route

Audit `delta_0435_final` and every production theorem on which its intended use depended.

Do **not** assume that

```text
0.435 = 0.20 + 0.23 + 0.005
```

represents a legitimate current `M = S + E` bound merely because the decimal sum matches.

Determine exactly what each component controls:

```text
0.20
0.23
0.005
```

and whether they are:

- log-mass slopes;
- support-count exponents;
- exceptional-set cardinality exponents;
- tail-probability exponents;
- shell-count exponents;
- or something else.

If quantities live in different dimensions/populations, state explicitly that the constants are not directly additive.

The wrapper `delta_0435_final` itself must be classified by what it actually proves in Lean, not by historical intended narrative.

## 4. Quantitative theorem taxonomy

Create a documented taxonomy with at least these coordinate classes.

### A. Support-side estimates

Controls only `S` or a quantity exactly identified with `S`.

### B. Depth-side estimates

Controls only `E`, `piSqRad`, `twoTail`, valuation layers, or an exact equivalent.

Distinguish second-layer (`v>=2`) from over-depth (`v>=3`) where relevant.

### C. Total channel mass estimates

Controls `M=S+E` directly or can be converted to `M` using exact production equalities.

### D. Balance estimates

Controls `Q=S-E`, shell single-vs-over-depth difference, or an exact equivalent.

Do not infer a `Q` bound from separate `S` and `E` counts unless a valid quantitative bridge is available.

### E. Calibration residual estimates

Controls

```text
Cal = M - rho*R
```

or an equivalent affine budget.

This is the class directly relevant to the existing ABC epsilon consumer.

### F. Counting / density / moment statements

These measure populations of inputs, not pointwise channel mass.

They must not be silently promoted to pointwise `Cal <= C` statements.

Record precisely what deterministic bridge would be required for such a promotion.

## 5. Supporting-line interpretation

For every theorem that truly gives an affine mass bound of the form

```text
M <= rho*R + C
```

or equivalent, record it as a supporting-line statement in the `(R,M)` plane.

For every theorem that instead controls `Q`, interpret it in the `(M,Q)` / two-channel plane.

Do not merge these two geometries.

If an old exponent is only a count/moment exponent, do not call it a slope in `(R,M)` space.

## 6. Production implementation policy

This checkpoint may be mostly audit/documentation.

Add production Lean code **only** when there is a small exact bridge that is genuinely missing and needed to classify an existing theorem.

Good candidates:

- exact rewrite from a legacy quantity to `S`, `E`, `M`, `Q`, or `Cal`;
- a theorem exposing that a historical wrapper is weaker than / equivalent to a current coordinate statement;
- dimensional separation lemmas with no new estimate.

Do not create placeholder structures merely to hold metadata.

Do not rewrite old quantitative proof files unless required for a minimal exact bridge.

## 7. Forbidden strengthening

Do not:

- improve `0.435` or any other numerical exponent;
- prove a new uniform `C`;
- prove `ABCGNOddPrimeJointContract`;
- infer pointwise bounds from density/counting estimates;
- claim ABC;
- assert shell-count exponents are channel-mass slopes without an exact bridge;
- add Hensel lift existence;
- claim `Q=0` is optimal;
- claim any current exponent is best possible.

If a historical quantitative route is dimensionally invalid or too weak for the current exact target, report that cleanly.

## 8. Deliverables

Create:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-008.md
```

The report must contain a table with columns at least:

```text
theorem / source
population
raw measured quantity
current coordinate class
normalization
statement type
constant/exponent
directly composable? yes/no
required bridge / limitation
```

Then give:

1. the status of the `0.435` route under current coordinates;
2. the strongest currently existing **pointwise** theorem in `Cal` / `M` coordinates;
3. the strongest currently existing **counting/average** theorem, clearly separated;
4. the exact missing deterministic bridge, if one remains;
5. whether returning to numerical optimization is now justified.

## 9. Outcome classes

### Outcome A — CALIBRATED QUANTITATIVE MAP COMPLETE

The historical and current quantitative APIs are successfully classified in the exact BCAL coordinate system, and the remaining quantitative frontier is identified without dimensional ambiguity.

No exponent improvement is required.

### Outcome B — PARTIAL MAP / MISSING EXACT BRIDGE

Most estimates are classified, but one or more legacy quantities cannot yet be translated exactly into current coordinates.  Add only the minimal exact bridges that are justified; otherwise record the gap.

### Outcome C — HISTORICAL ROUTE NOT COMPOSABLE

The old numerical route mixes incompatible populations/dimensions and cannot support the intended current pointwise budget without new mathematics.  Preserve the result as an audit conclusion; do not repair it by assumption.

## 10. Validation

If production Lean files are changed:

```text
focused module build
lake build DkMath.ABC
axiom audit
forbidden-token scan
git diff --check
```

If the checkpoint is documentation-only, still run `git diff --check` and verify every cited theorem exists in the current branch.

## 11. Central rule

The numerical question is no longer

> "Can these exponents be made smaller?"

but

> "Which exact coordinate is each exponent measuring, and is that coordinate the one consumed by the ABC calibration bridge?"

Only after that classification may a later campaign optimize a numerical frontier.
