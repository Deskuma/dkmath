# ROADMAP — ABC–GN Astra Campaign 260906 v1

## 0. Current campaign state

The original v1 research attack is complete through SOL-000 / ASTRA-001, and the validated deterministic consequences have been frozen through LUNA-007.

LUNA-008 has now completed the bounded DkMath.Lib promotion and p=3 Eisenstein API reconciliation checkpoint.

This branch is closed for further implementation and proposed for merge to `develop`.

ABC remains unproved.

---

## 1. Fixed production chain

Treat the following as infrastructure:

```text
v0 shell-count reduction
-> realized profile/fiber machinery
-> cubic complement / Pell / squareful packets
-> paired orientation / seven-state normalization
-> fixed-(T,r) shell fiber card <= 1
-> shell-local a |-> (r,S) injective
-> D^2*T^3 < 54*(X+1)^6
-> exact represented (r,S) pair ledger
-> Pell-to-Mordell exact transport
-> fixed-(S,u) Mordell incidence ledger
-> neutral Eisenstein coordinate algebra
-> explicit beta*gamma^2 consequence API
-> Lib-owned Eisenstein coordinate API
-> p=3 TraceOne / FLT3 carrier-coordinate-sector reconciliation.
```

No asymptotic counting theorem is hidden in this chain.

---

## 2. Current mathematical frontier

Two closely related ABC research routes remain open:

### A — balanced-box represented-pair sparsity

Target conceptually:

```text
Q(B) << B^(2-delta+epsilon)
```

for a useful positive `delta`.

### B — actual Eisenstein factorization existence/counting

Production proves only:

```text
IF
  beta*gamma^2 = (a+2)+omega
THEN
  exact coordinate equations,
  coefficient-one Bezout relation,
  coprimality,
  and norm-factor identities.
```

It does not prove the IF hypothesis.

---

## 3. Research-only analytic route

ASTRA-001 derived, outside production Lean, a Helfgott–Venkatesh-based shell-moment improvement of rough order

```text
O_epsilon(X^(31/24+epsilon)).
```

This remains research-only.

Do not formalize it merely as a provider or axiom.

---

## 4. DkMath.Lib context

The reusable generic number-theory layer now includes:

```text
DkMath.Lib.NumberTheory.PadicValNat
DkMath.Lib.NumberTheory.PowerFactor
DkMath.Lib.NumberTheory.IdealPowerFactor
DkMath.Lib.NumberTheory.PrincipalIdealPower
DkMath.Lib.NumberTheory.UnitPowerSector
DkMath.Lib.NumberTheory.EisensteinCoordinates.
```

The odd-prime FLT architecture exposes the generic chain:

```text
ideal p-th power
-> principalization hypothesis
-> unit * element^p
-> unit-sector normalization.
```

This does not automatically solve the ABC-side factorization problem, but it removes the need to rebuild downstream ideal/unit machinery if the required ABC ideal-power statement is found later.

---

## 5. Eisenstein promotion — COMPLETE

LUNA-008 completed the migration:

```text
DkMath.Lib.NumberTheory.EisensteinCoordinates
  = canonical implementation

DkMath.NumberTheory.EisensteinCoordinates
  = compatibility facade

ABC Eisenstein modules
  -> import Lib owner directly.
```

The theorem content was preserved; this was an API ownership refactor, not new ABC mathematics.

---

## 6. p=3 TraceOne / Eisenstein reconciliation — COMPLETE

The generic odd-prime carrier is:

```text
TraceOneInt (signedPrimeParameter p).
```

Production now proves:

```text
signedPrimeParameter 3 = -1.
```

FLT3 already defines:

```text
abbrev EisensteinInt := TraceOneInt (-1).
```

LUNA-008 also records the omega/tau sign bridge and packages the existing three FLT3 cube-unit sectors as:

```text
UnitPowerSectorSystem (TraceOneInt (-1)) 3.
```

Thus the former carrier/API mismatch is closed at this bounded interface.

Do not claim full generic odd-prime p=3 facade integration from this alone.

---

## 7. LUNA-008 validation

See:

```text
reconciliation-008.md
instruction-008.md
report-008.md
validation-008.txt.
```

Completed deliverables:

```text
A. Lib-owned Eisenstein coordinate core;
B. old-path compatibility facade;
C. ABC direct Lib migration;
D. DkMath.Lib entry-point update;
E. signedPrimeParameter_three;
F. omega/tau coordinate bridge;
G. FLT3 cube sectors packaged as UnitPowerSectorSystem.
```

Focused builds and aggregators recorded in `validation-008.txt` succeeded. Forbidden and warning scans are clean for the checkpoint.

---

## 8. Hard boundaries

Do not infer any of the following from the new Lib layer:

```text
actual ABC Eisenstein factorization existence;
uniqueness of beta/gamma;
factor counting;
class-group torsion-freeness for the ABC problem;
Mordell integral-point bounds;
balanced-box power saving;
ABC closure.
```

Likewise, do not claim the whole generic odd-prime FLT architecture now specializes to p=3 merely because the carrier and unit-sector APIs align.

---

## 9. Regression barriers

Mandatory checks remain:

```text
M=169 collisions;
M=8281 four-witness collision;
complement-3 Pell family;
independent paired exact depths;
arbitrarily large coprime paired repeated parts;
arbitrary finite Hensel lifting;
all mod-49 seven states.
```

---

## 10. Independent research extracted from this branch

A broader, non-ABC-specific research direction emerged after LUNA-008:

```text
multi-gauge GN divisibility
-> Norm divisibility
-> coordinate divisibility
-> integer-lattice landing
-> power/Core-image landing.
```

It is recorded in:

```text
docs/not_implements/260912-MultiGauge-Divisibility-Norm-Lattice-Landing.md
```

This should continue as generic DkMath research, not as LUNA-009 on this ABC branch.

---

## 11. Model roles

```text
Sol:
  new mathematics / proof-route design.

Astra:
  expensive adversarial review and branch pruning.

Luna:
  implementation of already validated deterministic facts and refactors.
```

No further Luna sequence is opened here.

---

## 12. Closeout status

```text
v0 deterministic reduction:
  COMPLETE

SOL-000:
  COMPLETE / Outcome B

ASTRA-001:
  COMPLETE / Outcome B

LUNA-002 ... LUNA-007:
  COMPLETE / APPROVED

LUNA-008 Lib / p=3 reconciliation:
  COMPLETE / APPROVED

ABC-GN Astra v1:
  CLOSED / MERGE CANDIDATE

ABC:
  NOT PROVED

remaining ABC frontier:
  balanced-box sparsity
  and/or
  Eisenstein factorization existence/counting

new independent DkMath frontier:
  multi-gauge divisibility / Norm-lattice landing.
```
