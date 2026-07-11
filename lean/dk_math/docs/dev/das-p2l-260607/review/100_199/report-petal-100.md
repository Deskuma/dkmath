# Report Petal 100: Collatz Finite Channel-Flow Documentation Checkpoint

## Checkpoint

This checkpoint follows `__next_implementation-100.md` and the conductor's
additional instruction:

```text
make No.100 a documentation-heavy consolidation checkpoint
```

The main work was to document the Collatz package, the recent finite
channel-flow layer, and the Petal-Collatz bridge in a way that remains useful
after the development context has been forgotten.

## Lean Surface Added

Added three thin conceptual aliases in `DkMath.Collatz.PetalBridge`:

```lean
theorem sourcePow2Distribution_total
theorem tailPow2Distribution_total
theorem pow2ChannelFlow_of_pointwise
```

These do not add new mathematical burden.  They expose the No.100 theorem
chain with conceptual names:

```text
source distribution conservation
tail distribution conservation
pointwise transition -> finite channel flow
```

They wrap:

```lean
orbitWindowResidueCountPow2_sum_eq_window
orbitWindowResidueCountPow2Tail_sum_eq_window
orbitWindowResidueCountPow2_le_tail_of_pointwise
```

## Documentation Created

### Collatz package entry

Created:

```text
lean/dk_math/DkMath/Collatz/README.md
```

Purpose:

```text
module entry document
package map
current milestone summary
reading order
future direction
```

It introduces the package as:

```text
odd state dynamics
  -> 2-adic height
  -> residue channels
  -> finite observation windows
  -> source/tail distributions
  -> finite channel flow
```

### Collatz overview

Created:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-Overview.md
```

Purpose:

```text
mathematical overview of the accelerated odd-state map
height and residue interpretation
finite observation windows
distribution conservation
channel flow
```

### Package structure

Created:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-Package-Structure.md
```

Purpose:

```text
file-by-file package explanation
older proof approaches
current PetalBridge route
Python experiment role
suggested reading order
```

It explicitly records older routes:

```text
direct accelerated dynamics
shift invariance / block cartography
finite PetalBridge windows
```

### Finite channel-flow checkpoint

Created:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteChannelFlow-100.md
```

Purpose:

```text
No.100 theorem chain summary
source/tail distribution conservation
channel-flow helper
recursive two-adic Petal instances
next Nat-ratio layer
later odd factor carrier layer
```

This is the central math explanation document for the checkpoint.

### PetalBridge guide

Created:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
```

Purpose:

```text
how to use PetalBridge
what each major definition means
how to add new channel theorems
why pow2ChannelFlow_of_pointwise should be preferred
```

### Petal-side bridge

Created:

```text
lean/dk_math/DkMath/Petal/docs/Petal-CollatzBridge.md
```

Purpose:

```text
Petal-facing explanation of Collatz.PetalBridge
finite range / occupation / channel-flow reading
what is connected now
what remains separate
```

## Documentation Updated

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
```

The status document now includes the No.100 conceptual aliases and points to
the new entry documents.

The Petal overview now points to the new Petal-Collatz bridge document.

## Mathematical State After No.100

The current theorem chain is:

```text
Residue arithmetic:
  labels have computable 2-adic residue behavior

Orbit-label transition:
  source residue condition implies shifted-tail residue condition

Source distribution:
  sum source cells = k

Tail distribution:
  sum tail cells = k

Channel-flow helper:
  pointwise source-to-tail transition
    -> source occupation <= tail occupation

Recursive two-adic Petal instances:
  recovery source <= outward-retention tail
  continuation source <= next-retention tail
```

The conceptual aliases make this readable:

```lean
sourcePow2Distribution_total
tailPow2Distribution_total
pow2ChannelFlow_of_pointwise
```

## Inference

No.100 should be treated as the closure of the first Collatz/Petal finite
channel-flow chapter.

The current layer is deliberately finite:

```text
no limits
no probability
no real-valued density
no odd prime carrier yet
```

This is a strength, not a gap.  It means later ratio and factor layers can be
attached to exact finite conservation laws rather than informal numerical
distribution language.

## Next Implementation Candidates

The next layer should be a finite ratio witness layer, but still in `Nat`.

Recommended first definitions or theorem style:

```text
2 * count <= k
countA + countB <= k
m <= count
```

Avoid introducing `ℚ` or `ℝ` until the Nat inequality API shows repeated need.

Candidate next documents or definitions:

```text
FiniteRatioWitness
RetentionMass(depth r)
RecoverySiblingMass(depth r)
ContinuationSiblingMass(depth r)
```

The odd factor carrier layer should remain a later chapter:

```text
same two-adic cell
  -> next odd core
  -> new odd prime factor event
```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
git diff --check -- <touched files>
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

The `rg` check found no `sorry` in `DkMath.Collatz.PetalBridge`.

Known upstream warning remains unchanged:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```
