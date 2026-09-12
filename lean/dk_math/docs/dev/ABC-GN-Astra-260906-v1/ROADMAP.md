# ROADMAP — ABC–GN Astra Campaign 260906 v1

## 0. Current campaign state

The original v1 research attack is complete through SOL-000 / ASTRA-001, and the validated deterministic consequences have been frozen through LUNA-007.

The branch has now been fast-forwarded to the current `develop` after the FLT prime-generalization and DkMath.Lib promotion work.

Current task:

```text
LUNA-008
  Lib promotion + p=3 Eisenstein API reconciliation.
```

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
-> explicit beta*gamma^2 consequence API.
```

No asymptotic counting theorem is hidden in this chain.

---

## 2. Current mathematical frontier

Two closely related research routes remain open:

### A — balanced-box represented-pair sparsity

Target conceptually:

```text
Q(B) << B^(2-delta+epsilon)
```

for a useful positive `delta`.

### B — actual Eisenstein factorization existence/counting

Production currently proves only:

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

## 4. New DkMath.Lib context

The current `develop` now contains reusable generic number-theory components:

```text
DkMath.Lib.NumberTheory.PadicValNat
DkMath.Lib.NumberTheory.PowerFactor
DkMath.Lib.NumberTheory.IdealPowerFactor
DkMath.Lib.NumberTheory.PrincipalIdealPower
DkMath.Lib.NumberTheory.UnitPowerSector.
```

The odd-prime FLT architecture now exposes the generic chain:

```text
ideal p-th power
-> principalization hypothesis
-> unit * element^p
-> unit-sector normalization.
```

This does not automatically solve the ABC-side factorization problem, but it removes the need to rebuild downstream ideal/unit machinery if the required ABC ideal-power statement is found later.

---

## 5. Eisenstein promotion gap

ABC-GN v1 currently owns reusable Eisenstein coordinates at:

```text
DkMath.NumberTheory.EisensteinCoordinates.
```

The preferred stable owner is now:

```text
DkMath.Lib.NumberTheory.EisensteinCoordinates.
```

Migration target:

```text
Lib owner
  -> canonical implementation

old NumberTheory path
  -> compatibility facade

ABC
  -> imports Lib owner directly.
```

This is LUNA-008 Part I–IV.

---

## 6. p=3 TraceOne / Eisenstein reconciliation

The generic odd-prime carrier is:

```text
TraceOneInt (signedPrimeParameter p).
```

At p=3:

```text
signedPrimeParameter 3 = -1.
```

FLT3 defines:

```text
abbrev EisensteinInt := TraceOneInt (-1).
```

Therefore the former p=3 carrier boundary is not a mathematical type-equivalence problem.

The remaining reconciliation is only:

```text
1. API ownership;
2. omega/tau coordinate convention;
3. unit-sector packaging.
```

The coordinate conversion is:

```text
standard omega coordinates:  (m,n)
trace-one tau coordinates:   (m,-n)

tau = -omega.
```

FLT3 already classifies units modulo cubes into the three sectors:

```text
1, tau, tau^2.
```

LUNA-008 should package these as:

```text
UnitPowerSectorSystem (TraceOneInt (-1)) 3.
```

Do not claim full generic p=3 FLT facade integration from this alone.

---

## 7. LUNA-008 implementation gate

See:

```text
reconciliation-008.md
instruction-008.md.
```

Required deliverables:

```text
A. Lib-owned Eisenstein coordinate core;
B. old-path compatibility facade;
C. ABC direct Lib migration;
D. DkMath.Lib entry-point update;
E. signedPrimeParameter_three;
F. omega/tau coordinate bridge;
G. FLT3 cube sectors packaged as UnitPowerSectorSystem.
```

This is a refactor / API-alignment checkpoint only.

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

## 10. Model roles

```text
Sol:
  new mathematics / proof-route design.

Astra:
  expensive adversarial review and branch pruning.

Luna:
  implementation of already validated deterministic facts and refactors.
```

LUNA-008 belongs entirely to the third category.

---

## 11. Next research phase after reconciliation

After LUNA-008, pause implementation again unless another already-validated deterministic fact is identified.

Next genuine mathematics should return to one of:

```text
balanced-box represented-pair sparsity;

or

actual Eisenstein factorization existence/counting for shell witnesses.
```

The new Lib principal-ideal and unit-sector APIs should be treated as reusable downstream tools, not as proof of either research target.

---

## 12. Current status

```text
v0 deterministic reduction:
  COMPLETE

SOL-000:
  COMPLETE / Outcome B

ASTRA-001:
  COMPLETE / Outcome B

LUNA-002 ... LUNA-007:
  COMPLETE / APPROVED

sync with latest develop:
  COMPLETE

LUNA-008 Lib / p=3 reconciliation:
  ACTIVE TASK

ABC:
  NOT PROVED

next mathematical frontier:
  balanced-box sparsity
  and/or
  Eisenstein factorization existence/counting.
```
