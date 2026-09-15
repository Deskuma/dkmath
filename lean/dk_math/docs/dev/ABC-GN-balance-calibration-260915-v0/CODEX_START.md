# Codex Start — ABC/GN Balance Calibration

Work only on:

```text
repository: Deskuma/dkmath
branch: research/ABC-GN-balance-calibration-260915-v0
```

Current accepted checkpoint:

```text
BCAL-000 — Outcome A
commit: 39022f480db874c91432f4c114bb7e1c3661fa5b
```

Read in this order:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/README.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-000.md
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/instruction-001.md
```

Then execute `instruction-001.md` repository-first.

Current core rule:

```text
The balance coordinates already exist.
Now expose the actual pointwise calibration function before any uniform bound.
Do not improve exponents.
Do not prove a uniform calibration bound.
Do not construct a new ABC contract.
Do not claim either zero contour is globally optimal.
```

Checkpoint 000 established:

```text
S = fresh non-exceptional support log mass
E = non-exceptional valuation depth mass
M = S + E
Q = S - E
Cal(T,p,ρ) = M - ρ * radLog(T)

odd-prime joint pressure
  iff
Cal(T,p,ρ) <= C
```

Checkpoint 001 must extract:

```text
pointwise calibration correction
  := (Cal(T,p,ρ) + log(rad p)) / ((p-1) * radLog(T))

outer ABC balance
  := valuationExcess(T.c) - log(rad(T.a*T.b))
  = abcGap(T)
```

Reuse existing production bridges. Do not rebuild the GN accounting or epsilon proof.

Write results and build/audit evidence to:

```text
lean/dk_math/docs/dev/ABC-GN-balance-calibration-260915-v0/report-001.md
```
