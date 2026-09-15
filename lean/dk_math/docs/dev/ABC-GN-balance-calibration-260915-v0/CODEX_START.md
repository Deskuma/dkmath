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
```

Read in this order:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-006.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/instruction-007.md
```

Then execute `instruction-007.md` repository-first.

Current core rule:

```text
BCAL-006 completed the bounded local/depth transport audit.
Do not pursue lift existence here.
Audit whether the exact two-channel linear coordinate transform deserves a stable DkMath.Lib kernel.
Require real reuse by both PowerSwap and ABC/GN.
Preserve existing public APIs and dependency direction.
Do not return to exponent optimization.
Do not construct a new ABC contract.
```

Established exact structures now include:

```text
PowerSwap:
  U = gapU
  V = gapV
  gapP = (U + V)/2
  gapQ = U - V

ABC/GN:
  U = GNChannelSupportMass
  V = GNChannelDepthMass
  GNChannelMass    = U + V
  GNChannelBalance = U - V

BCAL-006 right-channel step:
  V -> V + δ
  M -> M + δ
  Q -> Q - δ
```

Checkpoint 007 should first search for an existing generic replacement. If none exists and extraction is dependency-neutral, add only a small stable two-channel coordinate kernel and exact consumer bridges.

Do not claim that PowerSwap and ABC are the same mathematics. The shared object under audit is only the linear sum/difference coordinate transform.

Write results and build/audit evidence to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-007.md
```
