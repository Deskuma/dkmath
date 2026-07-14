# Report Petal 093: Recursive Two-Adic Petal Raw Layer

## Checkpoint

This checkpoint follows `__next_implementation-093.md` and
`discus-petal-093.md`.

The question was whether the narrowing Collatz residue cylinder is only a list
of fixed congruence observations, or whether it has a recursive Petal structure.

The answer at the raw arithmetic layer is now:

```text
yes, no-sorry Lean proof passed for the expanded general form.
```

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

Recursive Petal naming layer:

```lean
twoAdicRetentionResidue
twoAdicRecoverySiblingResidue
twoAdicContinuationSiblingResidue
```

Structural identities:

```lean
twoAdicRecoverySiblingResidue_eq_retentionResidue
twoAdicContinuationSiblingResidue_eq_retentionResidue_succ
```

General expanded raw transition theorems:

```lean
next_recovery_residue_expanded
next_continuation_residue_expanded
```

## Main Theorems

Recovery sibling:

```lean
theorem next_recovery_residue_expanded
    (r t : ℕ) :
    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 1) - 1)) + 1) / 2) %
        (2 ^ (r + 1)) = 2 ^ r - 1
```

Continuation sibling:

```lean
theorem next_continuation_residue_expanded
    (r t : ℕ) :
    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 2) - 1)) + 1) / 2) %
        (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
```

## Petal Reading

The naming layer fixes the recursive shape:

```text
RetentionResidue r
  = 2^r - 1

RecoverySibling r
  = 2^r - 1

ContinuationSibling r
  = 2^(r + 1) - 1
```

The key identity is:

```lean
theorem twoAdicContinuationSiblingResidue_eq_retentionResidue_succ
    (r : ℕ) :
    twoAdicContinuationSiblingResidue r =
      twoAdicRetentionResidue (r + 1)
```

Reading:

```text
continuation sibling at level r
  = retention cell at level r + 1
```

This is the minimal formal anchor for the nested Petal interpretation.

## Arithmetic Reading

The expanded recovery theorem says:

```text
m = 2^(r+2) * t + (2^(r+1) - 1)

one visible height-one step:
  (3m + 1) / 2

lands at:
  2^r - 1 mod 2^(r+1)
```

The expanded continuation theorem says:

```text
m = 2^(r+2) * t + (2^(r+2) - 1)

one visible height-one step:
  (3m + 1) / 2

lands at:
  2^(r+1) - 1 mod 2^(r+1)
```

Thus every refined retention cell splits into:

```text
recovery sibling:
  returns outward by one residue depth

continuation sibling:
  becomes the next inner retention cell
```

This is precisely the recursive Petal structure discussed in
`discus-petal-093.md`.

## Proof Notes

The direct `omega` attempt did not close the expanded general theorem because
the proof contains both natural subtraction and products involving `t * 2^r`.

The successful proof shape was:

```text
1. rewrite powers:
   2^(r+1) = 2 * 2^r
   2^(r+2) = 2 * 2^(r+1)

2. split the predecessor term:
   2 * p - 1 = p + (p - 1)

3. prove the numerator is exactly twice the intended quotient

4. eliminate division by Nat.mul_div_right

5. reduce modulo with Nat.add_mul_mod_self_left
```

This proof route is useful for the next `hm`-style theorem because it shows
where the hard part is: not the modular reduction, but normalizing the
natural-number predecessor around `/ 2`.

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
recursive Petal naming layer
ContinuationSibling r = RetentionResidue (r + 1)
expanded recovery raw theorem
expanded continuation raw theorem
```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
```

The targeted build still reports the existing upstream warning:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean: declaration uses `sorry`
```

No new `sorry` was introduced in this checkpoint.

## What Was Not Done Yet

The practical `hm` form was not implemented in this checkpoint:

```lean
theorem next_recovery_residue_of_mod
theorem next_continuation_residue_of_mod
```

Reason:

```text
expanded form is now closed;
hm form requires rewriting m through Nat.mod_add_div before applying it.
```

That is the next natural bridge.

## Next Implementation Candidates

Candidate A: `hm` form for recovery.

```lean
theorem next_recovery_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ r - 1
```

Candidate B: `hm` form for continuation.

```lean
theorem next_continuation_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
```

Candidate C: derive selected fixed raw anchors from the expanded general theorem.

This would reduce future duplication, but it is lower priority than the `hm`
form because the fixed anchors already pass.

Candidate D: once `hm` form passes, promote the general raw theorem to the
orbit-label layer.

That will require proving that the source residue also guarantees exact
height-one, then using the existing `T_val_eq_three_mul_add_one_div_two_of_s_eq_one`.
