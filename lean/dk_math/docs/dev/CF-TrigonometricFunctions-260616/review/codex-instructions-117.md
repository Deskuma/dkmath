# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by finishing the finite `Fin 4` observation API around fixed-`q2` level points and the closed shifted four-level path. Do not introduce a continuous quotient phase parameter yet unless the finite observation layer finishes completely and the quotient design is obvious.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is finite cyclic observation on the fixed `q2` boundary, not Euclidean interpretation.

Context:
The finite `Fin 4` cyclic wrapper is implemented. `finFourSucc` has named small-step facts and a four-cycle theorem. Finite shifted edges expose endpoint aliases and center-to-successor-base compatibility. The closed shifted four-level path has source and target aliases.

Part A:
Add finite base level-point wrappers.

There is already an indexed base level point:

```lean id="cdxp7y"
shiftedSemanticIndexedBaseLevelPoint
```

Add a finite wrapper:

```lean id="nhminp"
def shiftedSemanticFinBaseLevelPoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    LevelSet ℝ (Vec.q2 z) :=
  shiftedSemanticIndexedBaseLevelPoint r z i.val
```

Add simp bridge theorem if useful:

```lean id="teb4gh"
@[simp]
theorem shiftedSemanticFinBaseLevelPoint_eq_indexed
    ...
```

Part B:
Use the finite base level point in center theorems.

Add a finite-shaped center theorem:

```lean id="qfqq9b"
theorem shiftedSemanticFinLevelEdge_center_eq_succ_base_level_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinLevelEdge hcore z i phaseCenter =
      shiftedSemanticFinBaseLevelPoint r z (finFourSucc i)
```

This should be a wrapper around the existing indexed-level theorem. The `i = 3` case may need the core-zero four-step return theorem. If proof noise is high, prove by `fin_cases i`.

Part C:
Add finite source/target aliases for the finite closed path alias.

Candidate theorem names:

```lean id="mrt1fs"
theorem shiftedSemanticFinFourLevelPath_source
    ...

theorem shiftedSemanticFinFourLevelPath_target
    ...
```

These should wrap `shiftedSemanticFourLevelPath_source` and `shiftedSemanticFourLevelPath_target`.

Part D:
Add finite closed-path boundary observation theorem if convenient.

Candidate theorem shape:

```lean id="z5yrg2"
theorem shiftedSemanticFinFourLevelPath_q2
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (t : unitInterval) :
    Vec.q2 ((shiftedSemanticFinFourLevelPath hcore z t).1) = Vec.q2 z
```

If this is awkward because `shiftedSemanticFinFourLevelPath` is already a path inside `LevelSet`, then use the subtype property or add a short theorem exposing it.

Part E:
Add finite seam sequence aliases at the path endpoint level only if they improve readability.

The endpoint aliases already exist for finite right/left level endpoints. Do not duplicate too much unless downstream path concatenation needs named forms.

Part F:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="xyhf32"
implemented:
  finite base level-point wrapper
  finite center-to-successor-base level theorem
  finite closed path source/target aliases
  optional fixed-q2 observation theorem for the finite closed path

remaining:
  continuous cyclic quotient parameter
  Euclidean one-eighth reading later
```

Part G:
Do not start the continuous cyclic quotient in this checkpoint unless all above is finished and the quotient design is completely obvious.

Required checks:

```text id="mye253"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
