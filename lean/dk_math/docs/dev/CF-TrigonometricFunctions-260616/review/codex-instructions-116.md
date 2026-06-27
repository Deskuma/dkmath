# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by strengthening the finite `Fin 4` cyclic API and the observation API for the closed shifted four-level path. Do not introduce a continuous quotient phase parameter yet unless the required facts become completely trivial.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is finite cyclic readability and closed fixed-`q2` path observation, not Euclidean interpretation.

Context:
The shifted closed fixed-`q2` path is implemented as `shiftedSemanticFourLevelPath`. The finite cyclic wrapper layer is implemented with `finFourSucc`, `shiftedSemanticFinBase`, `shiftedSemanticFinEdge`, `shiftedSemanticFinPath`, `shiftedSemanticFinLevelEdge`, `shiftedSemanticFinLevelPath`, and `shiftedSemanticFinRightLevelEndpoint_eq_succ_left`.

Part A:
Add small API facts for `finFourSucc`.

Candidate theorem names:

```lean id="xe9jzv"
@[simp] theorem finFourSucc_zero :
    finFourSucc ⟨0, by norm_num⟩ = ⟨1, by norm_num⟩

@[simp] theorem finFourSucc_one :
    finFourSucc ⟨1, by norm_num⟩ = ⟨2, by norm_num⟩

@[simp] theorem finFourSucc_two :
    finFourSucc ⟨2, by norm_num⟩ = ⟨3, by norm_num⟩

@[simp] theorem finFourSucc_three :
    finFourSucc ⟨3, by norm_num⟩ = ⟨0, by norm_num⟩
```

If exact `Fin` literal syntax is noisy, use `fin_cases` or value-level theorems instead.

Also consider:

```lean id="lv5ypc"
theorem finFourSucc_four_cycle (i : Fin 4) :
    finFourSucc (finFourSucc (finFourSucc (finFourSucc i))) = i
```

Only add it if it is easy.

Part B:
Add finite endpoint aliases for readability.

Candidate theorem names:

```lean id="uwc0xp"
theorem shiftedSemanticFinEdge_leftEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinEdge r z i 0 =
      shiftedSemanticLeftEndpoint r (shiftedSemanticFinBase r z i)

theorem shiftedSemanticFinEdge_rightEndpoint
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinEdge r z i 1 =
      shiftedSemanticRightEndpoint r (shiftedSemanticFinBase r z i)
```

These are wrappers over the indexed or normalized endpoint theorems.

Part C:
Add finite center-to-successor-base compatibility.

There is already a theorem that the finite edge center reaches the indexed base at `i.val + 1`. Add a successor-shaped theorem if it is clean.

Candidate theorem:

```lean id="b0l0bh"
theorem shiftedSemanticFinEdge_center_eq_succ_base_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) (i : Fin 4) :
    shiftedSemanticFinEdge r z i phaseCenter =
      shiftedSemanticFinBase r z (finFourSucc i)
```

This may require the four-step return theorem in the `i = 3` case. If proof becomes noisy, prove it by `fin_cases i`.

Also add the level-set version if straightforward:

```lean id="cdxgq9"
theorem shiftedSemanticFinLevelEdge_center_eq_succ_base_of_core_eq_zero
    ...
```

Part D:
Add source/target aliases for the closed four-level path.

Candidate theorem names:

```lean id="iafbfl"
theorem shiftedSemanticFourLevelPath_source
    ...

theorem shiftedSemanticFourLevelPath_target
    ...
```

If these are already `rfl` or simp, add only if they improve downstream readability.

Part E:
Optionally expose the four seam sequence in docs or theorem aliases.

Candidate theorem aliases:

```lean id="s564j0"
shiftedSemanticFinRightLevelEndpoint_zero_eq_one_left
shiftedSemanticFinRightLevelEndpoint_one_eq_two_left
shiftedSemanticFinRightLevelEndpoint_two_eq_three_left
shiftedSemanticFinRightLevelEndpoint_three_eq_zero_left
```

These can be wrappers around `shiftedSemanticFinRightLevelEndpoint_eq_succ_left`.

Part F:
Do not start the continuous cyclic quotient yet unless the above finishes cleanly and the quotient design is obvious. If not, update docs saying that the finite cyclic skeleton is implemented and the continuous quotient remains a later design layer.

Part G:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="tw72lu"
implemented:
  finFourSucc small API
  finite endpoint aliases
  finite center-to-successor-base compatibility

implemented if successful:
  four-cycle theorem for finFourSucc
  finite seam sequence aliases

remaining:
  continuous cyclic quotient parameter
  Euclidean one-eighth reading later
```

Required checks:

```text id="v86jo0"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
