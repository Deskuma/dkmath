# Collatz Package Structure

## Current Files

The package currently consists of:

```text
DkMath.Collatz.Basic
DkMath.Collatz.V2
DkMath.Collatz.Accelerated
DkMath.Collatz.Shift
DkMath.Collatz.PetalBridge
DkMath.Collatz.Collatz2K26
```

There is also a `python/` directory for numerical experiments and historical
exploration scripts.

## `Basic.lean`

This file provides the lowest-level Collatz vocabulary.

Important names:

```lean
C
OddNat
threeNPlusOne
```

The later accelerated map is built over `OddNat`, so that the main dynamics
stay on odd states.

## `V2.lean`

This file contains the 2-adic valuation layer used by Collatz.

Important names:

```lean
v2
v2_3n_plus_1_ge_1
v2_shift_invariant
```

The main mathematical role is to describe the power of two peeled from
`3n + 1`.

The theorem `v2_3n_plus_1_ge_1` is the local reason why every accelerated odd
Collatz step has height at least one.

## `Accelerated.lean`

This file defines the accelerated odd-state dynamics.

Important names:

```lean
s
T
iterateT
sumS
driftReal
```

The theorem work in `PetalBridge` uses `iterateT` to form finite orbit windows
and `sumS` to connect local height profiles to accumulated Collatz peeling.

## `Shift.lean`

This file belongs to an older but still relevant proof approach:

```text
block shift / petal cartography
```

The idea is to compare an odd state `n` with shifted states of the form:

```text
n + 2^k * m
```

and ask when the 2-adic valuation behavior stays invariant.

This approach is still useful because it points toward the same structural
theme that later appears in `PetalBridge`:

```text
differences concentrate around 2-adic boundaries and singular residue ridges
```

## `PetalBridge.lean`

This is the current active bridge layer.

It packages the accelerated orbit as a Petal-style finite observation window:

```lean
OrbitWindow
oddOrbitLabel
orbitWindowHeight
orbitWindowHeightSeq
```

It then introduces count surfaces:

```lean
orbitWindowHeightCountEq
orbitWindowHeightCountGe
orbitWindowResidueCountPow2
orbitWindowResidueCountPow2Tail
```

and the No.100 finite channel-flow aliases:

```lean
sourcePow2Distribution_total
tailPow2Distribution_total
pow2ChannelFlow_of_pointwise
```

This file is where Collatz dynamics are read as finite channel movement.

## `Collatz2K26.lean`

This is the integration file for the 2026 Collatz cartography route.

It imports:

```lean
DkMath.Collatz.Basic
DkMath.Collatz.V2
DkMath.Collatz.Accelerated
DkMath.Collatz.Shift
DkMath.Collatz.PetalBridge
```

Use this file when checking that the package-level surface still compiles.

## Historical Proof Approaches

### Direct accelerated dynamics

The direct route studies:

```text
s(n)
T(n)
sumS n k
driftReal
```

This is the most classical Collatz-facing part of the package.

### Shift invariance / block cartography

The shift route studies how behavior changes under power-of-two block offsets.

It is documented in:

```text
docs/CollatzCartography.md
docs/CollatzCartography-ja.md
```

The guiding concepts are:

```text
block size 2^k
petal self-similarity
singular ridges
first divergence under offsets
```

### PetalBridge finite windows

The current route does not start from global convergence.

It starts from finite verified observations:

```text
finite window
height profile
residue occupation
source/tail distribution
channel flow
```

This is deliberately local.  It avoids making probabilistic or asymptotic
claims before the finite theorem surface is stable.

## Python Experiments

The `python/` directory contains numerical scripts for cartography-style
experiments.

These scripts are not formal proofs.  They help identify patterns such as:

```text
where residue differences arise
how long shift invariance persists
which finite windows show concentrated behavior
```

The Lean side then decides which observations are real theorem candidates.

## Suggested Reading Order

For current development:

```text
1. README.md
2. docs/Collatz-Overview.md
3. docs/Collatz-Package-Structure.md
4. docs/Collatz-FiniteChannelFlow-100.md
5. docs/Collatz-PetalBridge-Guide.md
6. docs/Collatz-PetalBridge-Status.md
```

For historical context:

```text
docs/CollatzCartography.md
docs/IMPLEMENTATION_REPORT_20260130.md
docs/SORRY_CLEANUP_PROGRESS_20260130.md
```
