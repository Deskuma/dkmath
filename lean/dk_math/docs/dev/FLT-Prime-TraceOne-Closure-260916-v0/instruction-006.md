# Instruction-006 — p=5 Golden/TraceOne bridge and generic sector closure audit

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
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-005.md
lean/dk_math/docs/refact/FLT-Prime-Generalization-260911-v0/report-019.md
lean/dk_math/DkMath/FLT/Five/GoldenOrder.lean
lean/dk_math/DkMath/FLT/Five/TraceOneBridge.lean
lean/dk_math/DkMath/FLT/Five/GoldenDivisibility.lean
lean/dk_math/DkMath/FLT/Five/GoldenEuclidean.lean
lean/dk_math/DkMath/FLT/Five/GoldenCoprimeFactor.lean
lean/dk_math/DkMath/FLT/Five/SignedGoldenUnitClasses.lean
lean/dk_math/DkMath/FLT/Five/GoldenUnitClassification.lean
lean/dk_math/DkMath/FLT/Prime/PrimeTraceOneConditionalDescent.lean
lean/dk_math/DkMath/Lib/NumberTheory/UnitPowerSector.lean
lean/dk_math/DkMath/Lib/NumberTheory/ClassGroupTorsionBridge.lean
```

This checkpoint is bounded.

**Do not prove FLT5 again, do not import a completed FLT5 contradiction theorem as a black box, and do not eliminate real nonzero sectors here.**

The purpose is to determine whether the existing explicit golden-order infrastructure can be transported honestly to the generic `TraceOneInt 1` carrier and then consumed by the generic prime endpoint at `p = 5`.

---

## 0. Repository-first audit

Before editing production code, record the exact current declarations and imports for:

```lean
DkMath.FLT.Five.GoldenInt
DkMath.FLT.Five.goldenToTraceOne
DkMath.FLT.Five.goldenNorm_eq_traceOneNorm_one
DkMath.FLT.Five.goldenEuclideanDomain
DkMath.FLT.Five.goldenUnit_iff_isUnit
DkMath.FLT.Five.goldenUnitClassesModFifth
DkMath.FLT.Five.goldenPhi

DkMath.NumberTheory.PrimeQuadraticDiscriminant.signedPrimeParameter
DkMath.NumberTheory.PrimeQuadraticDiscriminant.signedPrimeParameter_five

DkMath.Lib.NumberTheory.UnitPowerSectorSystem
DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_isPrincipalIdealRing

DkMath.FLT.Prime.exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket
DkMath.FLT.Prime.exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket
DkMath.NumberTheory.TraceOnePrimeUnitSectors.traceOnePrimeRealFinSectorSystem
```

Also audit the current Mathlib API for transporting across a ring equivalence:

```text
RingEquiv
Units.map
IsUnit.map
IsPrincipalIdealRing transport under RingEquiv
EuclideanDomain / PID transport if available
ClassGroup transport or principal-ideal consequences
```

Do not assume theorem names from memory.

Create and maintain:

```text
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-006.md
```

The report must separate facts already present from new production declarations.

---

## 1. Exact carrier equivalence audit

The coordinate operations currently show:

```text
GoldenInt multiplication:
  (a,b) * (c,d) = (ac + bd, ad + bc + bd)

TraceOneInt 1 multiplication:
  (a,b) * (c,d) = (ac + bd, ad + bc + bd)
```

The existing `goldenToTraceOne : GoldenInt -> TraceOneInt 1` preserves coordinates but is not yet a `RingEquiv`.

First prove in an audit file that the coordinate identity really preserves:

```text
0, 1, +, -, *, nat/int casts, powers
```

and has the obvious coordinate inverse.

If this is clean, add an FLT5 bridge theorem/definition, suggested names:

```lean
traceOneToGolden
goldenTraceOneRingEquiv : GoldenInt ≃+* TraceOneInt 1
```

or names matching repository style.

The equivalence should be coordinate-preserving.  Do not introduce a field-level isomorphism, `AdjoinRoot`, `Zsqrtd 5`, or a new algebraic carrier merely to prove the ring equivalence.

Required regressions should include:

```text
Golden -> TraceOne -> Golden = id
TraceOne -> Golden -> TraceOne = id
map goldenPhi = tau 1
map goldenConj = TraceOne conj
map goldenNorm = TraceOne norm
map (x^n) = map(x)^n
```

Use only those compatibility lemmas that are useful downstream; do not create a large duplicate API.

Suggested status if successful:

```text
FPTC-P5-GOLDEN-TRACEONE-RING-EQUIV-GREEN
```

---

## 2. Unit predicate / unit-group bridge

The specialized FLT5 theorem is stated using the predicate:

```lean
GoldenUnit x
```

while the neutral sector API uses actual units:

```lean
Rˣ
```

The repository already contains:

```lean
goldenUnit_iff_isUnit : GoldenUnit x ↔ IsUnit x
```

Use that theorem rather than re-proving unit classification.

Audit and, only if needed, add the thinnest helper converting an actual
`GoldenIntˣ` into the existing `GoldenUnit` theorem and back into a unit after applying the ring equivalence.

Do not introduce a second notion of golden unit.

---

## 3. Explicit golden fifth-power sector system on `TraceOneInt 1`

If Part 1 and Part 2 are green, build an explicit unit-sector system whose representatives are the transported golden powers:

```text
Sector := Fin 5
rep(i) := image of goldenPhi^i in (TraceOneInt 1)ˣ
```

Suggested conceptual API:

```lean
goldenTraceOneFifthUnitPowerSectorSystem :
  UnitPowerSectorSystem (TraceOneInt 1) 5
```

Its completeness must come from the already proved

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

through the actual ring equivalence and `goldenUnit_iff_isUnit`.

Do not re-run the elementary golden unit descent.  Do not use the generic real Dirichlet sector theorem to prove the golden classification.

Expose, if clean, the representative compatibility theorem:

```text
(goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1)
  = goldenToTraceOne (goldenPhi ^ i.val)
```

This theorem is important because later sector arithmetic may need to identify the generic sector index with the existing FLT5 `phi^i` arithmetic.

Suggested status:

```text
FPTC-P5-EXPLICIT-GOLDEN-SECTOR-SYSTEM-GREEN
```

---

## 4. Transport the structural class-group discharge to `TraceOneInt 1`

`GoldenInt` already has a Euclidean-domain instance.

Audit the cleanest way to obtain the corresponding principal-ideal consequence for `TraceOneInt 1` through the ring equivalence.

Preferred endpoint:

```lean
classGroupPTorsionFreeAt_traceOneOne_five :
  classGroupPTorsionFreeAt (TraceOneInt 1) 5
```

The proof should be structural:

```text
GoldenInt Euclidean/PID
   + RingEquiv GoldenInt (TraceOneInt 1)
        -> principal ideal structure on TraceOneInt 1
        -> classGroupPTorsionFreeAt (TraceOneInt 1) 5
```

Do not prove a separate class-number estimate if equivalence transport already gives PID/class-group triviality.

Do not add a global typeclass instance if it creates an instance diamond with the generic TraceOne number-field/Dedekind construction.  A theorem-local `let` / local instance or theorem-level proof is preferable if needed.

If Mathlib does not expose a clean principal-ideal transport API, stop and report the exact missing bridge rather than rebuilding ideal theory by hand.

Suggested status:

```text
FPTC-P5-CLASSGROUP-DISCHARGED-GREEN
```

---

## 5. Compose with the generic `p = 5` prime endpoint

If Parts 3 and 4 are green, compose them with the branch-independent generic theorem:

```lean
exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket
```

at `p = 5`.

Use the production fact:

```text
signedPrimeParameter 5 = 1
```

and the explicit transported golden sector system.

Preferred conceptual result:

```lean
exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five
```

with conclusion equivalent to:

```text
∃ i : Fin 5, ∃ delta : TraceOneInt 1,
  Q.residual =
    (goldenTraceOneFifthUnitPowerSectorSystem.rep i : TraceOneInt 1) *
      delta ^ 5
```

No caller-supplied class-group hypothesis should remain if Part 4 is green.

This is a **generic-route p=5 structural closure theorem**, not the specialized FLT5 final contradiction.

Do not eliminate `i ≠ 0` in this checkpoint.

Suggested status:

```text
FPTC-P5-GENERIC-SECTOR-CLOSURE-GREEN
```

---

## 6. Compare with the existing generic real `Fin 5` sector system — audit only

The current generic real branch already has:

```lean
traceOnePrimeRealFinSectorSystem
```

Audit the relationship between:

```text
A. transported explicit golden system
B. generic Dirichlet-derived real Fin 5 system
```

Do not assert that their representatives are definitionally equal or indexed identically unless kernel-checked.

Record whether a unit-sector equivalence/reindexing theorem would be useful later.  Such a theorem is optional in FPTC-006 and should not block Outcome A if the explicit golden system already composes with the branch-independent endpoint.

---

## 7. Specialized FLT5 arithmetic reuse boundary — report only

Inspect the existing modules:

```text
SignedGoldenUnitClasses
SignedGoldenSectorArithmetic
SignedGoldenZeroSector
SignedGoldenZeroSectorDescent
```

and record which theorems are phrased purely in terms of:

```text
phi^i * gamma^5
```

versus specialized FLT5 packets.

The purpose is to identify whether FPTC-008 can later reuse nonzero-sector elimination after translating the generic `Q.residual` through the ring equivalence.

Do not import or invoke the final `FLT_d5`/counterexample contradiction theorem in production for this checkpoint.

Do not add a new contradiction theorem now.

---

## 8. Production placement

Preferred placement is FLT5/FLT-prime adapter code, not neutral `DkMath.Lib`, because one side of the equivalence is the specialized `GoldenInt` carrier.

Possible files:

```text
DkMath/FLT/Five/TraceOneBridge.lean
DkMath/FLT/Prime/PrimeTraceOneFiveSectorClosure.lean
```

Keep the dependency direction one-way:

```text
GoldenInt infrastructure
      -> FLT5 TraceOne bridge
      -> FLT Prime p=5 specialization
```

Do not make `DkMath.Lib.NumberTheory` depend on `DkMath.FLT.Five`.

---

## 9. Focused audits

Add focused API and axiom audits, suggested:

```text
DkMathTest/FLT/Prime/PrimeTraceOneFiveSectorClosureApiAudit.lean
DkMathTest/FLT/Prime/PrimeTraceOneFiveSectorClosureAxiomAudit.lean
```

The API audit should at minimum check:

```text
signedPrimeParameter 5 = 1
ring equivalence synthesis / map formulas
GoldenInt EuclideanDomain
TraceOneInt 1 principal-ideal consequence if obtained
explicit Golden Fin 5 sector completeness
p=5 generic sector endpoint
```

Include representative regressions for `i = 0,1,2,3,4` when inexpensive.

---

## 10. Validation

Run focused builds first, adjusted to actual module names:

```text
lake build DkMath.FLT.Five.TraceOneBridge
lake build DkMath.FLT.Five.GoldenEuclidean
lake build DkMath.FLT.Five.GoldenUnitClassification
lake build DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
lake build DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure
lake build DkMathTest.FLT.Prime.PrimeTraceOneFiveSectorClosureApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneFiveSectorClosureAxiomAudit
```

If the new production module is exported through an existing facade, build that facade as well.

Also run:

```text
git diff --check
```

and the repository-standard forbidden-source scan.  New production/test sources must add no:

```text
sorry
sorryAx
admit
explicit axiom
unsafe
```

Print axioms for the ring equivalence or its key structural theorem, the p=5 class-group discharge, the explicit sector completeness theorem, and the generic p=5 sector endpoint.

---

## 11. Outcome classification

Use exactly one primary outcome:

```text
Outcome A — P5 GOLDEN/TRACEONE GENERIC SECTOR CLOSURE GREEN
Outcome B — RING EQUIV GREEN, UNIT/PID TRANSPORT BOUNDARY REMAINS
Outcome C — GOLDEN/TRACEONE CARRIER EQUIVALENCE MISMATCH IDENTIFIED
```

Outcome A requires all of:

```text
- kernel-checked ring equivalence GoldenInt ≃+* TraceOneInt 1;
- reuse of existing golden unit classification, not duplication;
- explicit Fin 5 UnitPowerSectorSystem on TraceOneInt 1 with golden representatives;
- structural class-group discharge at p=5, with no class-number assumption;
- generic branch-independent p=5 sector endpoint with no caller class-group hypothesis;
- no use of the specialized FLT5 final contradiction theorem;
- focused builds and axiom audits green;
- report-006.md records exact transport APIs and remaining boundaries.
```

Outcome B is appropriate if the ring equivalence is fully proved but current Mathlib/DkMath API makes either unit-group completeness transport or principal-ideal transport nontrivial enough that it should be isolated as the next bounded task.

---

## 12. Hard boundaries

Do not in FPTC-006:

- prove FLT5 again;
- call a completed FLT5 final contradiction theorem;
- eliminate nonzero `Fin 5` sectors;
- claim the generic real Dirichlet sector representatives equal the golden `phi^i` representatives without proof;
- prove arbitrary real-prime class-number results;
- extend the p=5 result to p=13 or all `p % 4 = 1`;
- reopen q-adic global descent;
- modify the neutral TraceOne power recurrence/landing API unless a genuine bug is found;
- create a second GoldenInt carrier or a field-level isomorphism just to avoid a simple ring equivalence.

The desired result is a precise calibration point:

```text
specialized FLT5 golden arithmetic
        <-> exact ring-equivalent TraceOneInt 1 carrier
        -> explicit golden Fin 5 unit sectors
        -> generic p=5 stripped-ideal sector endpoint.
```
