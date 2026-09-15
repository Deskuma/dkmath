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
```

Read in this order:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-002.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/instruction-003.md
```

Then execute `instruction-003.md` repository-first.

Current core rule:

```text
Calibration sources are now exactly separated.
Do not return to exponent optimization yet.
Now expose the signed GN balance prime by prime and identify its local valuation pivot.
Do not prove global monotonicity.
Do not prove a uniform calibration bound.
Do not construct a new ABC contract.
```

Checkpoint 002 established:

```text
abcEpsilon
  = GNEpsilon + ExactCalibrationCorrection

PointwiseSafeCorrection
  = ExactCalibrationCorrection
    + normalized(ReturnSlack + ExceptionalGaugeSlack)
```

with nonnegative return and gauge slacks and no lift-radical slack on the prime-exponent route.

Checkpoint 003 should use the existing depth-layer API to expose:

```text
S = sum fresh log q
E = sum (v_q - 1) log q
M = S + E
Q = S - E
```

and the local exact law

```text
localBalance(q) = (2 - v_q(GN)) * log q.
```

The key structural landmark is the **local** valuation pivot `v_q = 2`.
Do not turn that into an unsupported global characterization of `Q = 0`.

Write results and build/audit evidence to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-003.md
```
