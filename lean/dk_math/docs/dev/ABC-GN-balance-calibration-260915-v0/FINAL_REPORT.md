# ABC/GN Balance Calibration — Final Closeout Report

## Status

Campaign: `ABC-GN-balance-calibration-260915-v0`

Working branch:

```text
research/ABC-GN-balance-calibration-260915-v0
```

Base `develop` commit:

```text
5bba76f07a966e23eba7d0fbf7c70f1133d7e90e
```

Final research status: **STRUCTURAL / CALIBRATION CAMPAIGN COMPLETE**.

The campaign does **not** prove the ABC conjecture, does not provide a new unconditional numerical `rho` or `C`, and does not promote density or average estimates to a pointwise ABC/GN contract.

At closeout the branch is ahead of `develop` by 35 commits and behind by 0 commits.  The branch adds nine production modules plus facade exports and the full BCAL-000 through BCAL-008 instruction/report trail.

## Checkpoint summary

| checkpoint | result | primary content |
|---|---|---|
| BCAL-000 | Outcome A | extracted `S`, `E`, `M=S+E`, `Q=S-E`, `Cal=M-rho*R` |
| BCAL-001 | Outcome A | outer ABC balance bridge and pointwise calibration coordinates |
| BCAL-002 | Outcome A | exact return slack and exceptional gauge slack decomposition |
| BCAL-003 | Outcome A | prime-local law `localBalance=(2-v_q) log q`; local pivot `v_q=2` |
| BCAL-004 | Outcome B | exact generic cubic shell bridge; exceptional prime `3` isolated as the only full-complement mismatch |
| BCAL-005 | Outcome A | exceptional cubic completion; mismatch identified with existing gauge coordinate |
| BCAL-006 | Outcome A | exact valuation-step transport, canonical downward residue reduction, simple-root injectivity, `card R_(k+1) <= card R_k` |
| BCAL-007 | Outcome A | dependency-neutral `DkMath.Lib.TwoChannel` kernel with PowerSwap and ABC/GN consumers |
| BCAL-008 | Outcome A | calibrated quantitative map; deterministic counting/average-to-pointwise bridge identified as the remaining frontier |

The implementation commits recorded by the campaign are:

```text
BCAL-000  39022f480db874c91432f4c114bb7e1c3661fa5b
BCAL-001  748adca6ee93715ecf5d30c90ed2352f7e0d23c2
BCAL-002  670acf204798d7965f32faffb0e1ab5ac1102282
BCAL-003  d083a6a2b9752baa1524ceab80dfd5ddc58966a8
BCAL-004  e211e0472280515ff0adca8f2b287a387fa1e2c1
BCAL-005  7aa08d384b8c6b21c5da095e73964cc5ba15d8b2
BCAL-006  f68cb617a2db3fed875655037ce966db3d659b51
BCAL-007  7c4a1137c92c21d83a3803f46eaec062b30cf718
BCAL-008  6dcf3f7c5051a898d7233a6d79648d1cbacc1849
```

## Final exact coordinate picture

For the non-exceptional GN channel:

```text
S = fresh support mass
E = repeated valuation-depth mass
M = S + E
Q = S - E
Cal = M - rho*R
```

For a support prime `q`, with `v = v_q(GN)`:

```text
localMass    = v * log q
localBalance = (2 - v) * log q
```

Hence:

```text
v = 1  support-heavy
v = 2  exact local pivot
v >= 3 depth-heavy
```

An exact valuation successor `v -> v+1` changes the local coordinates by:

```text
localMass    -> localMass + log q
localBalance -> localBalance - log q
```

This algebraic step is kept separate from the arithmetic question of whether a successor lift exists.

## Cubic shell completion

The repeated-prime-power shell separates into the neutral square layer and the over-depth tail.  The generic non-exceptional balance can be written as the logarithm of the single layer minus the logarithm of `twoTail`.

For the cubic family, the only full-complement mismatch is exceptional prime `3` at valuation zero or one.  BCAL-005 proves that the full complement is exactly exceptional single layer times non-exceptional single layer and that the exceptional factor does not enter `twoTail`.

The resulting full-shell discrepancy is exactly the already-existing `GNExceptionalGaugeSlack` coordinate from BCAL-002.  No independent cubic correction is needed.

## Finite Hensel / depth-tree result

BCAL-006 distinguishes exact valuation from threshold divisibility.

Existing finite simple-root uniqueness combines with canonical reduction to give:

```text
R_(k+1) -> R_k
r |-> r mod q^k
```

with injectivity on the successor root set, and therefore:

```text
card R_(k+1) <= card R_k.
```

This says that under the stated non-exceptional simple-root hypotheses deeper canonical branches cannot split and multiply.  It does not prove lift existence, an infinite branch, or equality of successive cardinalities.

## Generic two-channel kernel

BCAL-007 extracts the shared linear coordinate transform into `DkMath.Lib.TwoChannel`:

```text
mass(u,v)    = u + v
balance(u,v) = u - v
center(u,v)  = (u + v)/2
```

The kernel contains only exact reconstruction, zero-balance, swap-symmetry, and left/right channel transport identities.

Two substantive consumers are now connected by exact bridges:

```text
PowerSwap:
  gapP = center(gapU,gapV)
  gapQ = balance(gapU,gapV)

ABC/GN:
  GNChannelMass    = mass(S,E)
  GNChannelBalance = balance(S,E)
```

This is reuse of a common linear coordinate transform, not an identification of the two mathematical theories.

## Quantitative frontier

BCAL-008 classifies the existing quantitative APIs by coordinate and population.  The important conclusion is negative but precise:

- the historical `0.435` route is not currently a Lean proof of a pointwise `M` or `Cal` budget;
- shell-count, incidence, moment, and density exponents remain aggregate/proxy quantities until a theorem connects them to the same pointwise affine `R` normalization;
- the current strongest pointwise interface is the conditional channel-mass/calibration budget;
- the current strongest relevant aggregate interfaces include finite Hensel layer-cake depth averages and cubic realized shell/moment bounds.

The missing deterministic bridge must, for every relevant triple or through a justified selector/cover mechanism:

1. convert the aggregate shell/layer/incidence information to pointwise `E` control;
2. provide compatible pointwise `S` control;
3. combine both in the same `R` normalization to obtain `M <= rho*R + C`, equivalently `Cal <= C`.

No such theorem exists in the audited source.  Therefore numerical optimization of `rho`, `C`, `0.435`, `3/8`, or related exponents is not justified on this branch.

## Production additions

The campaign adds these production modules:

```text
DkMath/ABC/GNBalanceCalibration.lean
DkMath/ABC/ABCBalanceCalibrationBridge.lean
DkMath/ABC/ABCCalibrationSourceDecomposition.lean
DkMath/ABC/GNBalanceDepthLayers.lean
DkMath/ABC/GNBalanceCubicShell.lean
DkMath/ABC/GNBalanceDepthTransport.lean
DkMath/ABC/GNBalanceTwoChannelBridge.lean
DkMath/Lib/TwoChannel.lean
DkMath/PowerSwap/TwoChannelBridge.lean
```

and exports them through the existing ABC, Lib, and PowerSwap facades.

The production checkpoints report successful focused/facade builds and axiom audits with only the standard axioms already present in this development (`propext`, `Classical.choice`, `Quot.sound`).  BCAL-008 is documentation-only and makes no production Lean change.

## Closeout decision

This branch has reached its intended structural goal.  Extending it with numerical optimization would mix a new research problem into a completed coordinate/calibration campaign.

The next quantitative campaign, if opened, should start from the explicit frontier:

```text
aggregate counting / layer / incidence / moment control
        ↓
missing deterministic selector / cover / compensation theorem
        ↓
pointwise S and E budgets in one R-normalization
        ↓
M <= rho*R + C
        ↔
Cal <= C
```

Until that middle bridge is supplied, historical exponents must remain classified by their actual population and quantity rather than being combined as if they were pointwise calibration slopes.

**Campaign closed successfully as a structural/calibration result.**
