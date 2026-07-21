# FLT5 standalone v4.33.0 and Lean4Web milestone

- Date: 2026-07-22
- Status: recorded milestone; Comparator Live validation deferred
- Branch: `feature/FLT35-essence-260722-v0`

## Reached

The FLT5 Mathlib-only standalone source has reached the following externally tested state:

- a build-passing Lean/Mathlib v4.33.0 compatibility diff was obtained;
- the resulting standalone source built successfully under Lean v4.33.0;
- the full standalone source passed Lean4Web;
- the v4.33.0-successful standalone state has been preserved.

This establishes that the complete standalone proof is accepted by a v4.33.0 Lean environment. It is a compatibility result for the standalone artifact and does not change the repository-wide v4.29.0 production baseline.

## Preserved boundary

The accepted v4.29.0 provenance artifact remains the fixed original certificate:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
SHA-256: 400935756c2468577582e6e9b87db2e5a2194a127855e3eb9bea312ff79b8dbd
```

The v4.33.0-compatible source is a version-compatibility derivative. It must not silently replace or redefine the v4.29.0 provenance original.

## Comparator Live observation

The complete standalone source does not currently initialize in Comparator Live and returns:

```text
Unexpected error initializing verification
No output generated
```

Lean4Web accepts the same complete proof. Comparator Live begins producing Lean errors after enough executable declarations are removed. Increasing or decreasing comment volume alone does not resolve the initialization failure. The remaining task is therefore to construct a smaller executable declaration bundle, not merely to minify text.

The established DkMath tool for this later task is:

```text
lean/dk_math/theorem_picker.md
```

The intended Comparator-specific artifact will be assembled declaration by declaration from the dependency route ending at:

```lean
theorem fermatFive_no_positive_solution
    (x y z : ℕ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    ¬ Fermat5Equation x y z
```

## Deferred work

Comparator Live validation is not claimed at this milestone. Producing the minimal theorem bundle is postponed and must not block the current FLT3/FLT5 essence work.

Current accepted stopping point:

```text
v4.29.0 provenance standalone: fixed and preserved
v4.33.0 compatible standalone: build success fixed
Lean4Web: PASS
Comparator Live full standalone: initialization failure
Comparator Live minimal theorem bundle: deferred
```
