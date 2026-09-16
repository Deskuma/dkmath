# Codex Start — ABC/GN Balance Calibration

Repository:

```text
Deskuma/dkmath
```

Branch:

```text
research/ABC-GN-balance-calibration-260915-v0
```

Campaign status:

```text
CLOSED / STRUCTURAL-CALIBRATION COMPLETE
```

There is no active implementation instruction on this branch.

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
commit: 7c4a1137c92c21d83a3803f46eaec062b30cf718

BCAL-008 — Outcome A / CALIBRATED QUANTITATIVE MAP COMPLETE
commit: 6dcf3f7c5051a898d7233a6d79648d1cbacc1849
```

Read the final state in this order:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/FINAL_REPORT.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/ROADMAP.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-008.md
```

Final exact coordinate frame:

```text
S = support mass
E = depth mass
M = S + E
Q = S - E
Cal = M - rho*R

localMass(q)    = v_q(GN) * log q
localBalance(q) = (2-v_q(GN)) * log q
```

The campaign also established:

```text
cubic shell:
  single / neutral pivot / over-depth decomposition
  + exact exceptional prime-3 gauge completion

finite depth transport:
  exact valuation +1 -> mass +log q, balance -log q
  canonical depth k+1 -> k reduction
  simple-root successor injectivity
  card R_(k+1) <= card R_k

generic kernel:
  DkMath.Lib.TwoChannel
  with PowerSwap and ABC/GN consumers
```

The quantitative audit found no theorem that turns the existing counting, average, shell, incidence, or moment estimates into a uniform pointwise calibration budget.

Do **not** continue on this branch by:

```text
optimizing 0.435, 3/8, rho, or C
adding count/moment exponents as if they were pointwise slopes
promoting density or average statements to pointwise bounds
constructing a new ABC contract from the current aggregate estimates
claiming an ABC theorem
```

The next quantitative research campaign, if created, must begin with the missing deterministic frontier:

```text
aggregate counting / layer / incidence / moment control
        ↓
selector / cover / compensation theorem
        ↓
pointwise S and E in one R-normalization
        ↓
M <= rho*R + C
        <->
Cal <= C
```

Until that bridge is supplied, stop here.
