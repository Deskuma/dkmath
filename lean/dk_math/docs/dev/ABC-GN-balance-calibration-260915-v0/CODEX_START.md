# Codex Start — ABC/GN Balance Calibration

Work only on:

```text
repository: Deskuma/dkmath
branch: research/ABC-GN-balance-calibration-260915-v0
```

Accepted checkpoints:

```text
BCAL-000 — Outcome A
commit: 39022f480db874c91432f4c114bb7e1c3661fa5b

BCAL-001 — Outcome A
commit: 748adca6ee93715ecf5d30c90ed2352f7e0d23c2

BCAL-002 — Outcome A
commit: 670acf204798d7965f32faffb0e1ab5ac1102282

BCAL-003 — Outcome A
commit: d083a6a2b9752baa1524ceab80dfd5ddc58966a8

BCAL-004 — Outcome B / PARTIAL BRIDGE
commit: e211e0472280515ff0adca8f2b287a387fa1e2c1

BCAL-005 — Outcome A / EXACT EXCEPTIONAL COMPLETION
commit: 7aa08d384b8c6b21c5da095e73964cc5ba15d8b2

BCAL-006 — Outcome A / EXACT DEPTH TRANSPORT
commit: f68cb617a2db3fed875655037ce966db3d659b51

BCAL-007 — Outcome A / GENERIC KERNEL JUSTIFIED
```

Read in this order:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-007.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/instruction-008.md
```

Then execute `instruction-008.md` repository-first.

Current core rule:

```text
BCAL-007 justified and extracted a dependency-neutral TwoChannel kernel.
The structural phase is now mature enough to revisit old numerical estimates.
Do not optimize exponents yet.
Classify every existing quantitative theorem by the exact coordinate and population it measures.
Keep pointwise, counting, average, moment, and asymptotic statements separate.
Do not silently add constants from incompatible dimensions.
Do not construct a new ABC contract.
```

Established exact coordinate frame:

```text
S = support mass
E = depth mass
M = S + E
Q = S - E
Cal = M - rho*R

TwoChannel:
  mass(u,v)    = u+v
  balance(u,v) = u-v
  center(u,v)  = (u+v)/2

local prime:
  localMass    = v_q(GN) * log q
  localBalance = (2-v_q(GN)) * log q

shell:
  Q = log(single layer) - log(twoTail)
  with exact cubic exceptional correction

calibration:
  abcEpsilon = GNEpsilon + ExactCalibrationCorrection
  safe correction = exact correction + normalized(return + gauge slacks)
```

Checkpoint 008 is the quantitative calibration frontier audit.  Audit the actual current theorem statements behind historical constants such as `0.435`, classify what they really measure, and identify the strongest existing pointwise and counting/average endpoints separately.

Write results and any minimal exact bridge evidence to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-008.md
```
