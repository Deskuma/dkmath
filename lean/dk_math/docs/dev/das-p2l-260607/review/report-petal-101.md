# Report Petal 101: Finite Ratio Witness And Retention Mass

## Checkpoint

This checkpoint follows `__next_implementation-101.md`.

The requested direction was to start the next layer after finite channel flow:

```text
finite channel-flow
  -> finite ratio witness
  -> retention mass
  -> depth refinement
```

The implementation deliberately avoids `ℚ` and `ℝ` frequency definitions.
The new ratio layer is encoded by natural-number inequalities.

## Implemented Lean Surface

Added in `DkMath.Collatz.PetalBridge`:

```lean
def AtMostHalf (count k : Nat) : Prop
def AtMostRatioNat (num den count k : Nat) : Prop

theorem atMostHalf_of_count_le_half
theorem atMostRatioNat_refl
theorem atMostHalf_iff_atMostRatioNat_one_two
theorem atMostRatioNat_one_one_of_le
```

The intended reading is:

```text
AtMostHalf count k
  means 2 * count <= k

AtMostRatioNat num den count k
  means den * count <= num * k
```

So `AtMostRatioNat num den count k` is the division-free form of:

```text
count / k <= num / den
```

## Retention And Sibling Mass

Added source and tail retention mass names:

```lean
noncomputable def orbitWindowRetentionMassPow2
noncomputable def orbitWindowRetentionMassPow2Tail
```

Added source sibling mass names:

```lean
noncomputable def orbitWindowRecoverySiblingMassPow2
noncomputable def orbitWindowContinuationSiblingMassPow2
```

Added shifted-tail sibling mass names:

```lean
noncomputable def orbitWindowRecoverySiblingMassPow2Tail
noncomputable def orbitWindowContinuationSiblingMassPow2Tail
```

Added basic window bounds:

```lean
theorem orbitWindowRetentionMassPow2_le_window
theorem orbitWindowRetentionMassPow2Tail_le_window
theorem orbitWindowRecoverySiblingMassPow2_le_window
theorem orbitWindowContinuationSiblingMassPow2_le_window
```

## Mass-Name Channel Flow

The existing recursive two-adic Petal channel-flow theorems now have mass-name
readings:

```lean
theorem orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
theorem orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
theorem orbitWindowContinuationSiblingMassPow2Tail_eq_retentionMassTail_succ
```

These make the next stage easier to read:

```text
Recovery sibling mass flows to the shifted-tail recovery sibling mass.

Continuation sibling mass flows to shifted-tail retention mass at the next
depth.
```

## Documentation Created

Created:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-FiniteRatioRetention-101.md
```

This document explains:

```text
division-free ratio witnesses
retention mass
recovery sibling mass
continuation sibling mass
mass-name channel flow
deferred split theorem
```

## Documentation Updated

Updated:

```text
lean/dk_math/DkMath/Collatz/README.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
```

## Inference

Checkpoint 101 establishes the vocabulary needed to talk about retention
without repeatedly exposing raw residue-count expressions.

The current stack is now:

```text
source/tail distribution
  -> channel-flow helper
  -> recursive channel instances
  -> retention/sibling mass names
  -> division-free finite ratio witness
```

This is the correct place to introduce ratio language because the total mass
conservation law was already proved at checkpoint 100.

## Deferred Experiment

The main theorem not yet implemented is the depth-refinement split:

```lean
theorem orbitWindowResidueCountPow2_refine_succ
    (n : OddNat) (k depth residue : Nat)
    (hres : residue < 2 ^ depth) :
    orbitWindowResidueCountPow2 n k depth residue =
      orbitWindowResidueCountPow2 n k (depth + 1) residue +
        orbitWindowResidueCountPow2 n k (depth + 1) (residue + 2 ^ depth)
```

The retention-specific version would be:

```lean
theorem orbitWindowRetentionMass_split
    (n : OddNat) (k r : Nat) (hr : 1 <= r) :
    orbitWindowRetentionMassPow2 n k r =
      orbitWindowRecoverySiblingMassPow2 n k r +
        orbitWindowContinuationSiblingMassPow2 n k r
```

This is the natural No.102 target.  The recommended route is:

```text
1. prove a pointwise residue refinement lemma
2. lift it to counts using successor formulas
3. specialize to the retention residue
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
