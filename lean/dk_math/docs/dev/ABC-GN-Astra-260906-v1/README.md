# ABC–GN Astra Campaign 260906 v1

cid: 6a9d5951-68dc-83ee-b422-0b21f77bac4a

## Purpose

This directory is the mathematical restart and production-freeze hub after the completed v0 ABC–GN reduction campaign.

The v0 capstone remains:

```text
DkMath.ABC.GNExcessCubicResearchFrontier
```

with the provider-free reduction:

```text
explicit realized dyadic shell-count bounds
-> cubic 3/8 excess-sum bound.
```

The open arithmetic object remains the realized cubic shell count.

ABC is not proved.

---

## Branch

```text
branch: wip/ABC-GN-astra-260906-v1
predecessor:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
```

On 2026-09-12 this branch was fast-forwarded to the current `develop` head after the FLT prime-generalization / DkMath.Lib promotion work.

The current campaign therefore includes:

```text
ABC-GN v1 production checkpoints
+
latest DkMath.Lib promotion
+
latest odd-prime FLT TraceOne architecture.
```

---

## Mathematical frontier

For the canonical cubic value

```text
F(a) = a^2 + 3*a + 3 = GN 3 a 1,
```

a realized large repeated modulus M has a witness a with canonical coordinates

```text
M*S = a^2 + 3*a + 3
M = u^2*r^3
T = r*S
y = 2*a+3
y^2 + 3 = 4*T*d^2.
```

Production now also freezes:

```text
fixed (T,r) + one dyadic shell
-> at most one witness;

inside one shell:
a |-> (r,S) is injective;

D^2*T^3 < 54*(X+1)^6;

shell witness count
= represented (r,S) pair count;

shell witness count
= sum over represented (S,u)
    of exact Mordell-coordinate image cards;

Y^2 + 48*S^2*u^4 = Z^3
for every production Mordell image point.
```

No integral-point counting theorem is included in production.

---

## Eisenstein production surface

LUNA-006/007 added a neutral Eisenstein coordinate presentation backed by

```text
TraceOneInt (-1).
```

The current production facts include:

```text
Norm(m+n*omega) = m^2-m*n+n^2;

beta*gamma^2 exact coordinate formulas;

coefficient-one
-> IsCoprime of the square coefficients;

a^2+3*a+3 = Norm((a+2)+omega);

IF beta*gamma^2 = (a+2)+omega,
THEN the exact coordinate equations,
     coprimality,
     and norm-factor identity hold.
```

The factorization-existence hypothesis itself is not proved.

---

## Result of SOL-000 / ASTRA-001

SOL-000 and ASTRA-001 isolated the shell-count mechanism and validated the elementary deterministic layer.

Research-only analytic deductions include:

```text
elementary hybrid moment improvement;
Helfgott–Venkatesh-based O_epsilon(X^(31/24+epsilon)) route;
balanced-box represented-pair sparsity target.
```

These remain outside production Lean.

The balanced-box research target is still conceptually:

```text
Q(B) << B^(2-delta+epsilon)
```

for a useful positive delta.

---

## DkMath.Lib / FLT-prime-generalization reconciliation

The repository has since promoted reusable arithmetic into:

```text
DkMath.Lib.NumberTheory.*
```

including:

```text
PadicValNat
PowerFactor
IdealPowerFactor
PrincipalIdealPower
UnitPowerSector.
```

The odd-prime FLT architecture now runs through generic TraceOne coordinates, principal-ideal power extraction, and generic unit-sector normalization.

The ABC-GN v1 Eisenstein core predates that promotion and currently lives at:

```text
DkMath.NumberTheory.EisensteinCoordinates.
```

The reconciliation task is recorded in:

```text
reconciliation-008.md
instruction-008.md.
```

Target state:

```text
DkMath.Lib.NumberTheory.EisensteinCoordinates
  = canonical reusable owner;

DkMath.NumberTheory.EisensteinCoordinates
  = compatibility facade;

ABC Eisenstein modules
  -> import Lib owner directly.
```

---

## p=3 TraceOne / Eisenstein contact

The FLT prime-generalization closeout records a p=3 carrier/API boundary.

The concrete implementation shows:

```text
EisensteinInt := TraceOneInt (-1)
```

and the generic signed-prime parameter specializes to

```text
signedPrimeParameter 3 = -1.
```

Thus there is no mathematical carrier mismatch.

The remaining compatibility work is:

```text
omega/tau coordinate convention;
namespace/API ownership;
unit-sector packaging.
```

Existing FLT3 cube-unit sectors can be packaged through the new generic:

```text
UnitPowerSectorSystem (TraceOneInt (-1)) 3.
```

This is an API reconciliation only; it does not by itself establish a new generic FLT p=3 theorem.

---

## Regression barriers

Still active:

```text
a -> M is not injective;
fixed S can have infinitely many witnesses;
independent paired exact depths exist;
both paired repeated parts can be arbitrarily large;
Hensel uniqueness alone does not imply global rarity;
mod-49 state normalization is not a density theorem.
```

Known regressions such as M=169, M=8281, and the complement-3 Pell family remain mandatory tests.

---

## Research / production boundary

### Production-proved

```text
v0 deterministic reduction;
realized profile/fiber machinery;
cubic complement / Pell / squareful packets;
paired orientation / seven-state normalization;
shell fiber card <= 1;
shell (r,S) injectivity;
Pell parameter height bound;
Mordell exact transport and finite incidence ledger;
neutral Eisenstein coordinate algebra;
conditional explicit beta*gamma^2 consequences.
```

### Research-only / open

```text
actual beta*gamma^2 factorization existence for ABC shell witnesses;
factor counting;
Mordell integral-point bounds in Lean;
Helfgott–Venkatesh specialization in production;
balanced-box power saving;
near-linear shell count;
ABC closure.
```

---

## Model roles

```text
Sol:
  mathematical attacker / route design.

Astra:
  expensive independent referee / branch pruner.

Luna:
  production implementation of already validated deterministic facts.
```

Do not use Luna to invent the missing counting theorem.

---

## Key files

```text
ROADMAP.md

instruction-000.md / report-000.md
  SOL shell-count attack

instruction-001.md / report-001.md
  ASTRA adversarial review

instruction-002.md ... instruction-007.md
report-002.md ... report-007.md
  deterministic production freeze

reconciliation-008.md
  delta against new Lib / FLT-prime-generalization architecture

instruction-008.md
  Lib promotion and p=3 Eisenstein API reconciliation
```

---

## Current status

```text
v0 deterministic reduction:
  COMPLETE

SOL-000:
  COMPLETE / Outcome B

ASTRA-001:
  COMPLETE / Outcome B

LUNA-002 ... LUNA-007:
  COMPLETE / APPROVED

branch sync to develop:
  COMPLETE

LUNA-008 Lib / p=3 API reconciliation:
  READY / ACTIVE TASK

ABC:
  NOT PROVED

current mathematical frontier:
  actual Eisenstein factorization existence/counting
  and/or
  balanced-box represented-pair power saving.
```
