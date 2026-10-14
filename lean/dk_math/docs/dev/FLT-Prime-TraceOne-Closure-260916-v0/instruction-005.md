# Instruction-005 — p=3 generic TraceOne/Eisenstein sector closure

## Working branch

Work only on:

```text
repository: Deskuma/dkmath
branch: research/FLT-Prime-TraceOne-Closure-260916-v0
```

Read first:

```text
README.md
AGENT.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/README.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/ROADMAP.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-000.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-001.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-002.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-003.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-004.md
DkMath/FLT/Three/EisensteinSubstrate.lean
DkMath/FLT/Three/EisensteinEuclidean.lean
DkMath/FLT/Three/EisensteinUnitSectors.lean
DkMath/FLT/Three/EisensteinLibBridge.lean
DkMath/FLT/Prime/PrimeTraceOneConditionalDescent.lean
DkMath/Lib/NumberTheory/ClassGroupTorsionBridge.lean
DkMath/Lib/NumberTheory/UnitPowerSector.lean
```

This checkpoint is deliberately narrow.

**Do not re-prove FLT3, duplicate the Eisenstein carrier, or invent a second unit-sector system.**

The current repository already contains the critical adapter:

```lean
DkMath.FLT.Three.eisensteinCubeUnitPowerSectorSystem :
  UnitPowerSectorSystem (TraceOneInt (-1)) 3
```

and the carrier alignment

```text
EisensteinInt = TraceOneInt (-1)
signedPrimeParameter 3 = -1
```

is already represented in production.  Therefore the intended work is to audit and compose existing pieces, not to recreate them.

---

## 0. Repository-first API audit

Before editing production code, record the exact current declarations and import paths for:

```lean
DkMath.FLT.Three.eisensteinCubeUnitPowerSectorSystem
DkMath.FLT.Three.eisensteinCubeUnitPowerSectorSystem_complete
DkMath.FLT.Three.traceOneNegOneEuclideanDomain
DkMath.FLT.Three.traceOneInt_signedPrimeParameter_three_type

DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_isPrincipalIdealRing
DkMath.Lib.NumberTheory.exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt

DkMath.FLT.Prime.exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket
```

Also locate the exact theorem proving/computing:

```text
signedPrimeParameter 3 = -1
```

and determine whether the existing sector system can be passed to the generic prime theorem by definitional reduction / `simpa`, or whether a tiny theorem-level cast is required.

Do not introduce a new carrier equivalence for definitionally identical types.

Create and maintain:

```text
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-005.md
```

The report must include exact API evidence, failed probes, import direction, and whether any adapter beyond existing `EisensteinLibBridge` was actually necessary.

---

## 1. Focused API audit

Add a focused audit file, suggested:

```text
DkMathTest/FLT/Prime/PrimeTraceOneThreeSectorClosureApiAudit.lean
```

Use `#check`, `#synth`, and local examples to establish all of the following:

1. `EisensteinInt` is definitionally `TraceOneInt (-1)`.
2. `signedPrimeParameter 3 = -1` is available by an existing theorem or direct computation.
3. `EuclideanDomain (TraceOneInt (-1))` synthesizes the principal-ideal structure required by the FPTC-000 class-group bridge.
4. Therefore

```lean
classGroupPTorsionFreeAt (TraceOneInt (-1)) 3
```

is derivable structurally, without any class-number hypothesis.
5. The existing

```lean
eisensteinCubeUnitPowerSectorSystem
```

can serve the generic p=3 TraceOne carrier after signed-parameter normalization.

Do not leave exploratory local examples in production unless they become purposeful regression theorems.

---

## 2. p=3 structural class-group closure

If not already present under an appropriate reusable name, add an FLT-side theorem of conceptual form:

```lean
classGroupPTorsionFreeAt_traceOneNegOne_three :
  classGroupPTorsionFreeAt (TraceOneInt (-1)) 3
```

Its proof must use only the existing Euclidean/PID structure plus the neutral FPTC-000 bridge, e.g. conceptually:

```text
EuclideanDomain (TraceOneInt (-1))
  -> IsPrincipalIdealRing (TraceOneInt (-1))
  -> trivial class group
  -> classGroupPTorsionFreeAt ... 3
```

Do not use `fermatThree_no_positive_solution`, `FLT_d3_unconditional`, or any completed FLT3 contradiction theorem.

Suggested status:

```text
FPTC-P3-CLASSGROUP-DISCHARGED-GREEN
```

---

## 3. Compose the existing Eisenstein sector system with the generic prime endpoint

The principal production target of this checkpoint is a p=3 specialization of the **branch-independent** generic theorem:

```lean
DkMath.FLT.Prime.exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket
```

Do **not** use

```lean
exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
```

because that theorem intentionally assumes `7 ≤ p` and belongs to the p >= 7 imaginary singleton-sector route.

Suggested production module:

```text
DkMath/FLT/Prime/PrimeTraceOneThreeSectorClosure.lean
```

Suggested theorem shape, adjusted to the actual current API:

```lean
exists_eisensteinSector_mul_cube_of_primeTraceOneStrippedIdealPacket_three
```

with conceptual content:

```text
P0 : PrimeAdicFactorPacket 3 g u x
P  : PrimeTraceOneCoordinatePacket L 3 ζ hζ
Q  : PrimeTraceOneStrippedIdealPacket L P0 P

------------------------------------------

∃ sector : EisensteinUnitSector,
∃ delta : TraceOneInt (-1),
  Q.residual =
    (eisensteinCubeUnitPowerSectorSystem.rep sector : TraceOneInt (-1)) *
      delta ^ 3
```

If the exact type of `Q.residual` is written as

```text
TraceOneInt (signedPrimeParameter 3)
```

normalize it explicitly with the existing signed-parameter theorem.  Prefer theorem-level `simpa`/rewriting to a new structure or duplicated adapter.

The proof should:

1. call the existing generic sector theorem;
2. supply `eisensteinCubeUnitPowerSectorSystem`;
3. discharge `3 != 2` trivially;
4. discharge the class-group hypothesis structurally using Part 2;
5. normalize `signedPrimeParameter 3 = -1` only as needed.

Do not duplicate ideal principalization, sector completeness, or the FLT3 unit classification.

Suggested status:

```text
FPTC-P3-GENERIC-SECTOR-CLOSURE-GREEN
```

---

## 4. Audit the next coordinate-consumer boundary — report first

FPTC-003 now provides:

```lean
traceOne_pow_core_landing_iff
```

For the p=3 result above, the natural next consumer would use

```text
beta = sector representative
r = 3
alpha = Q.residual
```

and derive exact coordinate equations for

```text
Q.residual * conj(sector representative)
```

scaled by the norm of the representative.

However, **do not force this into production in FPTC-005 unless it is genuinely a very small corollary with no new arithmetic argument**.

Audit and report:

1. whether `norm (S.rep sector : TraceOneInt (-1)) != 0` follows immediately from its unit status;
2. whether the sector representatives have norm exactly `1` in the existing API;
3. whether `traceOne_pow_core_landing_iff` therefore yields a clean coordinate receiver without re-proving Eisenstein arithmetic;
4. whether such a receiver would add useful information beyond the already specialized FLT3 development.

If this is not completely trivial, defer it.  The required Outcome A for FPTC-005 is the generic p=3 sector closure, not a coordinate contradiction.

---

## 5. No duplicate adapter rule

The current repository already contains:

```lean
noncomputable def eisensteinCubeUnitPowerSectorSystem :
  UnitPowerSectorSystem (TraceOneInt (-1)) 3
```

Therefore:

- do not create `eisensteinCubeUnitPowerSectorSystem2` or equivalent;
- do not create a ring equivalence between `EisensteinInt` and `TraceOneInt (-1)` when they are definitionally identical;
- do not copy FLT3 unit-sector proofs into `DkMath.FLT.Prime`;
- do not move FLT3-specific unit classification into `DkMath.Lib` merely for convenience.

The intended dependency direction is:

```text
DkMath.Lib.NumberTheory.*
        ↓
DkMath.FLT.Three.EisensteinLibBridge
        ↓
DkMath.FLT.Prime.PrimeTraceOneThreeSectorClosure
```

The generic Prime module may depend on the specialized p=3 adapter for this fixed-exponent regression, but neutral Lib code must not depend on FLT3.

---

## 6. Validation

Run focused builds first, adjusted to actual module names if necessary:

```text
lake build DkMath.FLT.Three.EisensteinEuclidean
lake build DkMath.FLT.Three.EisensteinLibBridge
lake build DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
lake build DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
lake build DkMath.FLT.Prime.PrimeTraceOneThreeSectorClosure
lake build DkMathTest.FLT.Prime.PrimeTraceOneThreeSectorClosureApiAudit
```

Add a focused axiom audit, suggested:

```text
DkMathTest/FLT/Prime/PrimeTraceOneThreeSectorClosureAxiomAudit.lean
```

Print axioms for the load-bearing p=3 class-group theorem and generic sector-closure theorem.

Also run:

```text
lake build DkMath.Lib
git diff --check
```

and the repository-standard forbidden-source scan.  New production/test sources must contain no new:

```text
sorry
sorryAx
admit
explicit axiom
unsafe
```

Standard Lean/Mathlib dependencies such as `propext`, `Classical.choice`, and `Quot.sound` are acceptable if inherited; report the exact output.

---

## 7. Outcome classification

Use exactly one primary outcome:

```text
Outcome A — P3 GENERIC EISENSTEIN SECTOR CLOSURE GREEN
Outcome B — EXISTING SECTOR ADAPTER GREEN, GENERIC P3 COMPOSITION BLOCKED BY API/INSTANCE BOUNDARY
Outcome C — P3 CARRIER/SECTOR ASSUMPTION MISMATCH IDENTIFIED
```

Outcome A requires all of:

```text
- confirmation that no new carrier adapter is necessary;
- structural p=3 class-group discharge;
- reuse of the existing `eisensteinCubeUnitPowerSectorSystem`;
- successful composition with the branch-independent generic stripped-ideal sector endpoint;
- no use of the specialized FLT3 final contradiction theorem;
- focused build and axiom audit success;
- report-005.md with exact API evidence.
```

---

## 8. Hard boundaries

Do not in FPTC-005:

- prove FLT3 again;
- call `FLT_d3_unconditional` or `fermatThree_no_positive_solution` to obtain the generic result;
- claim that a sector-weighted cube is automatically an exact cube;
- eliminate Eisenstein unit sectors unless that is already an existing theorem being merely restated;
- prove any new class-number theorem;
- change the generic `p >= 7` imaginary theorem to admit `p = 3` artificially;
- implement the p=5 Golden/TraceOne bridge;
- reopen q-adic global descent;
- claim a general FLT theorem;
- duplicate an existing unit-sector system or carrier.

The desired result is a clean proof that the generic prime stripped-ideal machinery can consume the already completed FLT3 Eisenstein infrastructure at `p = 3`, with the remaining unit sector kept explicit and mathematically honest.
