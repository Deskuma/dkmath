# Codex instructions

Target:
DkMath.Analysis.DkReal.SemanticCF2DPhaseShift

Goal:
Continue checkpoint 104 by preparing and, if feasible, packaging the four indexed shifted normalized level paths into a single closed fixed-`q2` path object. Do not introduce Euclidean angle language.

Principle:
Keep this layer pre-geometric. Do not use angle, arc, degree, circle, rotation, piOverFour, or fortyFive in Lean theorem names. The goal is four-edge shifted concatenation on a fixed `q2` boundary.

Context:
`shiftedSemanticIndexedLevelPath` is implemented. Indexed shifted edges use semantic action iterates as bases. Adjacent indexed shifted edges share endpoints. Under the core-zero hypothesis, indexed bases and edge functions repeat after four steps.

Part A:
Add explicit endpoint compatibility facts for four indexed level paths.

Use existing theorem:

```lean id="mkxmb2"
shiftedSemanticIndexedRightLevelEndpoint_eq_next_left
```

Add wrappers for the first three seams if useful:

```lean id="ef8lxr"
theorem shiftedSemanticIndexedLevelEndpoint_0_1
    ...

theorem shiftedSemanticIndexedLevelEndpoint_1_2
    ...

theorem shiftedSemanticIndexedLevelEndpoint_2_3
    ...
```

These should specialize `k = 0`, `k = 1`, and `k = 2`.

Part B:
Prove the closing seam from edge 3 back to edge 0 under core-zero.

Candidate theorem:

```lean id="qk0u48"
theorem shiftedSemanticIndexedRightLevelEndpoint_three_eq_zero_left
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    shiftedSemanticIndexedRightLevelEndpoint hcore z 3 =
      shiftedSemanticIndexedLeftLevelEndpoint hcore z 0
```

Expected route:
Use adjacent compatibility from `k = 3` to identify right endpoint of edge 3 with left endpoint of edge 4, then use the four-step return theorem for indexed bases or endpoints to rewrite edge 4 back to edge 0.

If this theorem is easier at the `Vec ℝ` level, prove it there first, then lift with `Subtype.ext`.

Part C:
Prepare path concatenation helpers.

Try to concatenate the four fixed-level paths:

```lean id="ofcuri"
shiftedSemanticIndexedLevelPath hcore z 0
shiftedSemanticIndexedLevelPath hcore z 1
shiftedSemanticIndexedLevelPath hcore z 2
shiftedSemanticIndexedLevelPath hcore z 3
```

If `Path.trans` requires exact endpoint types, use the endpoint equality theorems to cast/rewrite. Inspect existing path concatenation patterns in the project before inventing a new wrapper.

Candidate final object if feasible:

```lean id="kgob87"
def shiftedSemanticFourLevelPath
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (z : Vec ℝ) :
    Path
      (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0)
      (shiftedSemanticIndexedLeftLevelEndpoint hcore z 0) :=
  ...
```

This should be a closed fixed-`q2` path object.

Part D:
If full path concatenation is too noisy, stop at theorem-level closed chain.

At minimum, prove:

```lean id="esaxsi"
edge 0 target = edge 1 source
edge 1 target = edge 2 source
edge 2 target = edge 3 source
edge 3 target = edge 0 source
```

Then add a TODO saying that the only remaining work is packaging those compatible paths by `Path.trans` or a project-specific path concatenation wrapper.

Part E:
Optionally add function-level four-period facts for level edges if they are easy.

Candidate theorem:

```lean id="v95s44"
theorem shiftedSemanticIndexedLevelEdge_add_four_of_core_eq_zero
    ...
```

Do not spend much effort here if it is only a wrapper.

Part F:
Update docs.

Update `DkReal.lean` and `design-phase-center-shift-104.md`.

Record clearly:

```text id="b4h3gc"
implemented:
  four endpoint compatibility facts

implemented if successful:
  shiftedSemanticFourLevelPath

remaining:
  cyclic quotient parameter
  Euclidean one-eighth reading later
```

Required checks:

```text id="h3bbyk"
lake build DkMath.Analysis.DkReal.SemanticCF2DPhaseShift
lake build DkMath.Analysis.DkReal
git diff --check
```
