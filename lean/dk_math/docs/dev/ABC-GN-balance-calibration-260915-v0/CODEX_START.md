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
```

Read in this order:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-000.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-001.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/instruction-002.md
```

Then execute `instruction-002.md` repository-first.

Current core rule:

```text
The inner GN mass/balance coordinates and the outer ABC balance now exist.
The actual pointwise correction also exists.
Now open that correction and identify exactly which terms are genuine arithmetic slack.
Do not improve exponents.
Do not prove a uniform calibration bound.
Do not construct a new ABC contract.
Do not claim a balance contour is globally optimal.
```

Checkpoint 001 established:

```text
GNPointwiseCalibrationCorrection
  = (Cal + log(rad p)) / ((p-1) * radLog)

ABCOuterBalance
  = output depth - input support
  = abcGap
  = abcEpsilon * radLog
```

Checkpoint 002 should distinguish the exact odd-prime accounting from the safe envelope by extracting:

```text
ReturnSlack
  = log GN - (p-1) log c

ExceptionalGaugeSlack
  = log(rad p) - log(exceptional support)

ExactCalibrationCorrection
```

and should aim for the exact identities

```text
abcEpsilon
  = GNEpsilon + ExactCalibrationCorrection

GNPointwiseCalibrationCorrection
  = ExactCalibrationCorrection
    + normalized(ReturnSlack + ExceptionalGaugeSlack).
```

Reuse existing production identities. Do not rebuild GN support or return proofs.

Write results and build/audit evidence to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-002.md
```
