# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by adding a finite cyclic-index wrapper for the shifted closed path layer. The four-level path is already implemented. Now expose the same structure through `Fin 4` where useful, but do not introduce a continuous quotient phase parameter yet unless it is extremely straightforward.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is finite cyclic indexing and downstream readability, not Euclidean interpretation.

Context:
`shiftedSemanticFourLevelPath` is implemented as a closed fixed-`q2` path object by concatenating the first four indexed shifted normalized level paths. The indexed edge family already has adjacent seam compatibility and core-zero four-step return.

Part A:
Add `Fin 4` wrappers for the indexed shifted structures.

Candidate definitions:

```lean id="covr9r"
def shiftedSemanticFinBase
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) : Vec ℝ :=
  shiftedSemanticIndexedBase r z i.val

def shiftedSemanticFinEdge
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) (t : ℝ) : Vec ℝ :=
  shiftedSemanticIndexedEdge r z i.val t
```

Also add level-set versions if they are not too noisy:

```lean id="bvlku0"
def shiftedSemanticFinLevelEdge
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : ℝ) : LevelSet ℝ (Vec.q2 z) :=
  shiftedSemanticIndexedLevelEdge hcore z i.val t
```

Part B:
Add bridge theorems between `Fin 4` wrappers and indexed API.

Candidate theorem names:

```lean id="xzbr33"
theorem shiftedSemanticFinBase_eq_indexed
    ...

theorem shiftedSemanticFinEdge_eq_indexed
    ...

theorem shiftedSemanticFinLevelEdge_eq_indexed
    ...
```

If these are definitional equalities, mark useful ones as simp.

Part C:
Add q2 and center compatibility wrappers for `Fin 4`.

Candidate theorem shapes:

```lean id="hhfthi"
theorem shiftedSemanticFinEdge_q2_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) (t : ℝ) :
    Vec.q2 (shiftedSemanticFinEdge r z i t) = Vec.q2 z

theorem shiftedSemanticFinEdge_center_eq_next_base_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinEdge r z i phaseCenter =
      shiftedSemanticIndexedBase r z (i.val + 1)
```

Do not over-engineer the successor target yet. If a clean cyclic successor on `Fin 4` is easy, add it. Otherwise use the indexed `i.val + 1` target.

Part D:
Try to define a simple cyclic successor for `Fin 4`.

Candidate definition:

```lean id="i0zrj4"
def finFourSucc (i : Fin 4) : Fin 4 :=
  ⟨(i.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩
```

Then prove small cases or a value theorem:

```lean id="cwllkn"
theorem finFourSucc_val (i : Fin 4) :
    (finFourSucc i).val = (i.val + 1) % 4
```

If this becomes noisy, keep it minimal and leave deeper cyclic successor facts for later.

Part E:
If Part D succeeds, add cyclic seam compatibility in `Fin 4` language.

Candidate theorem shape:

```lean id="to7me8"
theorem shiftedSemanticFinEdge_right_eq_succ_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    ...
```

This may be easier at the level-set endpoint level. If proof noise is high, do not force it. The Nat-indexed seam theorems are already sufficient.

Part F:
Do not redefine `shiftedSemanticFourLevelPath` unless the `Fin 4` wrappers make it cleaner. If a Fin-based alias is useful, add only a wrapper:

```lean id="jukow8"
def shiftedSemanticFinFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0)
      (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0) :=
  shiftedSemanticFourLevelPath hcore z
```

Part G:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="uupivy"
implemented:
  Fin 4 wrappers for shifted cyclic index
  bridge to Nat-indexed API
  q2 and center facts if added

remaining:
  continuous cyclic quotient parameter
  Euclidean one-eighth reading later
```

Required checks:

```text id="a2h8ze"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
