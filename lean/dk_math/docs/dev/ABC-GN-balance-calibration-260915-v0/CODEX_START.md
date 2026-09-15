# Codex Start — ABC/GN Balance Calibration

Work only on:

```text
repository: Deskuma/dkmath
branch: research/ABC-GN-balance-calibration-260915-v0
```

Read in this order:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/instruction-000.md
```

Then execute `instruction-000.md` repository-first.

Core rule:

```text
This checkpoint extracts exact coordinates only.
Do not improve exponents.
Do not prove a uniform calibration bound.
Do not construct a new ABC contract.
Do not claim the balance contour is globally optimal.
```

The intended new coordinates are:

```text
S = fresh non-exceptional support log mass
E = non-exceptional valuation depth mass
M = S + E
Q = S - E
Cal(T,p,ρ) = M - ρ * radLog(T)
```

The load-bearing target is the exact equivalence

```text
odd-prime joint pressure
  iff
GNCalibrationResidual T p ρ <= C.
```

Reuse the existing production theorem

```lean
Triple.oddPrimeJointPressure_iff_nonExceptionalChannelMass
```

rather than rebuilding the GN accounting proof.

Write results and build/audit evidence to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-000.md
```
