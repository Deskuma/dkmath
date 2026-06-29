# Design: DkPath Layer Map

## Purpose

This note records the optimization map extracted from the shifted cyclic path
work in `DkMath.Analysis.DkReal.SemanticCF2DPhaseShift`.

The current route used Mathlib `Path` directly. It succeeded, but the proof
history shows which parts were mathematical and which parts were dependent
path bookkeeping. A future `DkPath` layer should keep the mathematical route
short by making that bookkeeping reusable.

## Completed Observation

The quotient-side closed shifted path, after endpoint casting, is equal to the
existing fixed-`q2` finite four-level path.

The comparison is purely path packaging:

```text
Path.map
Path.trans
Path.cast
seam proof irrelevance
```

No circle, angle, arc, Euclidean metric, or pi vocabulary is used in this
layer.

## Long Route

The implemented route was:

```text
1. build finite shifted level paths;
2. build a finite chart and seam relation;
3. quotient the chart by generated seam equivalence;
4. descend semantic evaluation to the quotient;
5. package quotient edge paths;
6. glue the four quotient edges;
7. observe the glued quotient path in the fixed boundary;
8. compare each observed edge with the finite level edge;
9. standardize four-edge gluing with explicit seams;
10. prove seam proof irrelevance for the standardized gluing;
11. prove map-through-gluing;
12. compare the endpoint-cast observed quotient path with the finite path.
```

The mathematical content is concentrated in steps 1--8. Steps 9--12 are
path-normalization infrastructure.

## Short Route

The optimized route for future developments should be:

```text
1. define edge traces and endpoint labels;
2. declare seam witnesses;
3. build a four-edge path package;
4. map the package through a continuous observation;
5. use generic normalization theorems to compare packages;
6. project to Mathlib Path only when topology is required.
```

The key improvement is to avoid rediscovering `Path.cast` and seam-proof
normalization inside every semantic module.

## Validated Minimum API

The following theorem shapes have already been validated in the current
Mathlib-backed implementation:

```text
cast_apply
map_cast
map_trans
cast_proof_irrel
four_concat_congr
four_concat_congr_cast_irrel
four_concat_map
```

In the current implementation these correspond to:

```text
shiftedPath_cast_apply
shiftedPath_map_cast
shiftedPath_map_trans
shiftedPath_cast_proof_irrel
shiftedFourPathConcatWithSeams_congr
shiftedFourPathConcatWithSeams_congr_cast_irrel
shiftedFourPathConcatWithSeams_map
```

## Three-Layer Separation

A future DkPath layer should separate the following concerns.

```text
trace:
  the parameterized value over unitInterval

endpoint labels:
  source and target labels used for dependent typing

seam witnesses:
  proof terms used to type concatenation
```

The trace and endpoint labels carry the public mathematical content. Seam
witnesses are necessary for dependent typing, but should be proof-irrelevant
at the public API level.

## Bridge Policy

`DkPath` should not replace Mathlib `Path`.

Instead:

```text
DkPath:
  DkMath-facing package for traces, endpoint labels, and seam normalization

Mathlib Path:
  external topology bridge for continuity and standard path theorems
```

The intended workflow is:

```text
construct and normalize as DkPath
  -> convert to Mathlib Path when topology is needed
  -> return to DkPath-level names for reusable semantic comparisons
```

## Prototype Boundary

A future isolated prototype may use a namespace such as:

```text
DkPathPrototype
```

The first useful object is likely a four-edge package:

```text
FourPathPackage:
  four component paths
  four seam witnesses
  toPath
  map
  toPath_map
```

This should remain isolated until it proves that it reduces production proof
noise. The current phase-shift module should keep using the validated
Mathlib-backed theorems until that prototype earns its way into the API.

## Next Step

Do not start the Euclidean one-eighth reading from this note.

The next stable step is to extract a small reusable path-packaging namespace
or module only if it can preserve the current theorem statements and shorten
future proofs.
