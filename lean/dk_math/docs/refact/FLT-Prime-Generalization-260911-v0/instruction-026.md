# FLT prime-generalization Phase 26 — conditional odd-prime descent endpoint and branch closure

## Goal

Phase 25 completed the actual front/middle arithmetic chain from a
`PrimeAdicFactorPacket` and an arbitrary-prime TraceOne coordinate packet to a
nonzero ideal `p`-th power:

```text
PrimeAdicFactorPacket
  -> PrimeTraceOneCoordinatePacket
  -> primitive TraceOne parent coordinates
  -> one discriminant-axis strip
  -> primitive terminal residual
  -> coprime conjugate principal ideals
  -> span(residual) = idealRoot^p, idealRoot != 0.
```

Phase 26 must **not** introduce a new number-theoretic assumption or claim a
general FLT theorem. Its purpose is to compose the already-green Phase
15/16/18/19/20 principalization and unit-sector layers with the Phase-25
packet, producing the strongest honest *conditional* odd-prime descent
endpoint.

This should be treated as the final integration phase of
`refact/FLT-Prime-Generalization-260911-v0`. After it, write a branch summary
that clearly separates the completed generic architecture from the two
remaining arithmetic research obligations.

## Current inputs

Use the exact checked-out declarations, not reconstructed copies:

- `DkMath.FLT.Prime.PrimeTraceOneStrippedIdealPacket`
- `DkMath.FLT.Prime.nonempty_primeTraceOneStrippedIdealPacket`
- packet fields
  - `residual`
  - `idealRoot`
  - `idealRoot_nonzero`
  - `residual_span_eq`
  - `residual_norm_pow`
  - `residual_conj_ideal_coprime`
- `DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt`
- `exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt`
- `exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt`
- `traceOnePrimeRealFinSectorSystem`
- `traceOnePrimeReal_exists_sector_mul_pow_of_span_eq_pow`
- `traceOnePrimeImaginarySingletonSectorSystem`
- `traceOnePrimeImaginary_exists_eq_pow_of_span_eq_pow`

Do not duplicate the class-group or unit-sector proofs.

## Part A — test-first API audit

Add a focused audit file, suggested:

```text
DkMathTest/FLT/Prime/PrimeTraceOneConditionalDescentApiAudit.lean
```

Pin the exact signatures and required local instances for:

1. the Phase-25 packet constructor and fields;
2. `classGroupPTorsionFreeAt`;
3. the neutral principalization/unit theorem;
4. the generic `UnitPowerSectorSystem` endpoint;
5. the real `Fin p` sector system and real conditional endpoint;
6. the imaginary singleton/exact-power endpoint;
7. the Phase-17 `TraceOneRat` field/Dedekind instances.

Also audit the p=3 carrier situation. Do not assume that the existing
Eisenstein unit-sector theorem is already a production
`UnitPowerSectorSystem (TraceOneInt (-1)) 3`. If a neutral production adapter
already exists, reuse it. Otherwise record p=3 as an explicit exceptional
carrier/API boundary rather than fabricating an equivalence.

## Part B — generic conditional principalization endpoint

Add a small FLT-prime orchestration module, suggested:

```text
DkMath/FLT/Prime/PrimeTraceOneConditionalDescent.lean
```

It may import the Phase-25 packet, neutral unit-sector API, and
`TraceOnePrimeUnitSectors`, but should not import specialized FLT3/5/7 theorem
stacks merely to obtain the generic result.

First prove a theorem with the conceptual shape:

```lean
PrimeTraceOneStrippedIdealPacket ... ->
classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p ->
∃ u gamma,
  IsUnit u ∧
  residual = u * gamma^p
```

or expose an equivalent associated-power form if that better matches the
existing API. Prefer direct composition of
`exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt` using
`idealRoot_nonzero` and `residual_span_eq`.

This theorem is the branch-independent conditional endpoint. It must keep the
unit explicit.

Suggested status:

```text
PGEN-PRIME-TRACEONE-CLASSGROUP-CONDITIONAL-GREEN
```

## Part C — generic sector endpoint

For an arbitrary supplied

```lean
S : UnitPowerSectorSystem
      (TraceOneInt (signedPrimeParameter p)) p
```

compose Phase 25 directly with the neutral Phase-18 theorem and prove:

```text
classGroupPTorsionFreeAt R p
  -> exists sector s and delta,
       residual = S.rep s * delta^p.
```

This theorem should not know whether the field is real or imaginary.

Suggested status:

```text
PGEN-PRIME-TRACEONE-SECTOR-CONDITIONAL-GREEN
```

## Part D — imaginary branch specialization

For

```text
p prime
7 <= p
p % 4 = 3
```

use the already proved singleton unit system / exact-power theorem. Starting
from the actual Phase-25 packet and only the explicit assumption

```lean
classGroupPTorsionFreeAt
  (TraceOneInt (signedPrimeParameter p)) p
```

prove the actual endpoint

```text
exists delta,
  packet.residual = delta^p.
```

Do not reprove that all units are `±1`.

Suggested status:

```text
PGEN-PRIME-TRACEONE-IMAGINARY-EXACT-POWER-CONDITIONAL-GREEN
```

The wording **conditional** is mandatory: this phase does not prove the
class-group hypothesis.

## Part E — real branch specialization

For

```text
p prime
p % 4 = 1
```

use `traceOnePrimeRealFinSectorSystem` and prove from the actual Phase-25
packet plus the explicit class-group hypothesis:

```text
exists i : Fin p, exists delta,
  packet.residual =
    (traceOnePrimeRealFinSectorSystem hp hmod).rep i * delta^p.
```

No sector is eliminated here.

Suggested status:

```text
PGEN-PRIME-TRACEONE-REAL-FIN-SECTOR-CONDITIONAL-GREEN
```

## Part F — p=3 boundary

Keep p=3 honest.

The signed-prime parameter is the Eisenstein case, but Phase 19 intentionally
kept p=3 outside the `p >= 7` singleton theorem because its unit group has
nontrivial cube sectors.

Do one of the following, in preference order:

1. If the current checkout already has a clean production adapter providing a
   `UnitPowerSectorSystem (TraceOneInt (-1)) 3`, compose it with Phase 25 and
   record the resulting three-sector conditional endpoint.
2. If only `EisensteinInt`-carrier sector results exist, record the carrier
   mismatch and do not invent an equivalence in this phase.

p=3 is not allowed to block the p>=5 arbitrary-prime integration.

## Part G — finite regressions

Add a focused probe, suggested:

```text
DkMathTest/FLT/Prime/PrimeTraceOneConditionalDescentProbe.lean
```

Check architecture at:

```text
p=3   exceptional sector/carrier audit
p=5   real Fin 5 conditional sector endpoint
p=7   imaginary conditional exact-power endpoint
p=11  imaginary conditional exact-power endpoint
p=13  real Fin 13 conditional sector endpoint
```

These are conditional theorem/API regressions only. Do not assert FLT5,
FLT7, FLT11, or FLT13 from the new module.

Where practical, compare p=7 with the existing specialized seventh-power
normal form to ensure the generic conditional route points at the same
mathematical shape, without rewriting the specialized proof.

## Part H — axiom and source audit

Add:

```text
DkMathTest/FLT/Prime/PrimeTraceOneConditionalDescentAxiomAudit.lean
```

Print axioms for:

- generic class-group conditional endpoint;
- generic sector conditional endpoint;
- real `Fin p` specialization;
- imaginary exact-power specialization;
- any p=3 adapter added in this phase.

Require:

- no new `sorry` / `sorryAx` / `admit`;
- no explicit `axiom`;
- no `unsafe`;
- no hidden theorem that asserts `classGroupPTorsionFreeAt` for arbitrary p;
- no hidden sector elimination assumption;
- `git diff --check` clean.

## Part I — report

Create:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-026.md
```

The report must answer explicitly:

1. Does the Phase-25 ideal-root packet compose directly with Phase 16/18?
2. What is the strongest branch-independent conditional element statement?
3. For `p % 4 = 3, p >= 7`, is the only remaining hypothesis before an exact
   residual p-th power exactly `classGroupPTorsionFreeAt`?
4. For `p % 4 = 1`, is the endpoint exactly a `Fin p` sector times a p-th
   power under the same class-group hypothesis?
5. What is the precise p=3 carrier/sector status?
6. Which assumptions are mathematical obligations rather than missing API?
7. Which parts of the chain are now fully generic for arbitrary odd primes?
8. What remains before an unconditional FLT contradiction?

## Part J — branch closure summary

If Parts B-E are GREEN, also create a concise branch closure document:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md
```

It should summarize the proved chain without calling it a general FLT proof:

```text
PrimeAdicFactorPacket
  -> GTail exact p-adic split
  -> arbitrary-prime QR/QNR TraceOne coordinates
  -> primitive coordinates
  -> prime-discriminant maximal order / Dedekind domain
  -> discriminant-axis strip
  -> conjugate-coprime residual ideals
  -> residual principal ideal = idealRoot^p
  -> [classGroupPTorsionFreeAt]
  -> unit * element^p
  -> unit-sector normalization
```

Then state the remaining research frontier as two explicit categories:

```text
A. class-group p-torsion/principalization hypothesis
B. real-branch nonzero unit-sector elimination
```

For the imaginary `p % 4 = 3, p >= 7` branch, note that B disappears because
the unit sector is singleton; do **not** infer that A is automatically true.

The closure summary should recommend that these two problems be studied on a
new research branch rather than extending this refactor branch indefinitely.

## Suggested focused validation

At minimum build:

```text
lake build DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal \
  DkMath.Lib.NumberTheory.IdealPowerFactor \
  DkMath.Lib.NumberTheory.PrincipalIdealPower \
  DkMath.Lib.NumberTheory.UnitPowerSector \
  DkMath.NumberTheory.TraceOnePrimeUnitSectors \
  DkMath.FLT.Prime.PrimeTraceOneConditionalDescent \
  DkMathTest.FLT.Prime.PrimeTraceOneConditionalDescentApiAudit \
  DkMathTest.FLT.Prime.PrimeTraceOneConditionalDescentProbe \
  DkMathTest.FLT.Prime.PrimeTraceOneConditionalDescentAxiomAudit \
  DkMath.FLT.Seven
```

and run `git diff --check` plus the forbidden-source scan.

## Non-goals

Do not in Phase 26:

- prove `classGroupPTorsionFreeAt` for arbitrary prime-discriminant fields;
- prove a class-number theorem or regular-prime theorem;
- eliminate nonzero real unit sectors;
- refactor all FLT3/5/7 endpoints onto the new generic API;
- assert an unconditional arbitrary-prime FLT theorem;
- claim that the historical/general FLT proof has been replaced.

The intended result is a **complete conditional odd-prime descent
architecture**, with the remaining mathematical obstructions exposed rather
than hidden.
