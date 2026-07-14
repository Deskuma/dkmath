# Report Petal 092: Mod 64 Recovery and Raw Cylinder Data to Mod 512

## Checkpoint

This checkpoint follows `__next_implementation-092.md`.

The requested Lean step was to split the `31 mod 32` retention-continuation
channel at mod `64`.  The additional instruction asked for a wider numerical
lookahead instead of returning only one rung at a time.

Therefore this checkpoint does two things:

```text
1. Promote the mod 64 rung to Lean orbit-label and drift theorems.
2. Record raw arithmetic anchors up to mod 512, backed by a Python check.
```

## Python Numerical Check

The following table was checked directly by Python using:

```text
((3 * residue + 1) // 2) % previous_mod
```

Result:

```text
mod 16:
  7 mod 16 -> 3 mod 8
  15 mod 16 -> 7 mod 8

mod 32:
  15 mod 32 -> 7 mod 16
  31 mod 32 -> 15 mod 16

mod 64:
  31 mod 64 -> 15 mod 32
  63 mod 64 -> 31 mod 32

mod 128:
  63 mod 128 -> 31 mod 64
  127 mod 128 -> 63 mod 64

mod 256:
  127 mod 256 -> 63 mod 128
  255 mod 256 -> 127 mod 128

mod 512:
  255 mod 512 -> 127 mod 256
  511 mod 512 -> 255 mod 256
```

The pattern remains stable through the requested lookahead.

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

Full mod `64` rung:

```lean
next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone
next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree

oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree

orbitWindowNextNextNextNextHeight_two_le_of_mod_sixtyfour_eq_thirtyone
sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
```

Raw arithmetic anchors beyond mod `64`:

```lean
next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_sixtythree
next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven

next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_onehundredtwentyseven
next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_twohundredfiftyfive

next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive
next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven
```

These raw anchors are intentionally not expanded into orbit-label and drift
bridges yet.  They serve as formal waypoints for the next generalization
discussion.

## Main Reading

The mod `64` split is:

```text
31 mod 64:
  next label is 15 mod 32
  recovery branch

63 mod 64:
  next label is 31 mod 32
  retention-continuation branch
```

The new drift theorem says:

```lean
theorem sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 64 = 31) :
    6 ≤ sumS n 5
```

Reading:

```text
31 mod 64
  -> 15 mod 32
  -> 7 mod 16
  -> 3 mod 8
  -> next height >= 2

therefore:
  sumS over five steps >= 1 + 1 + 1 + 1 + 2 = 6
```

## Ladder So Far

The verified drift ladder is now:

```text
3 mod 8:
  2 steps, sumS >= 3

7 mod 16:
  3 steps, sumS >= 4

15 mod 32:
  4 steps, sumS >= 5

31 mod 64:
  5 steps, sumS >= 6
```

The continuation branch keeps narrowing:

```text
7 mod 8
15 mod 16
31 mod 32
63 mod 64
127 mod 128
255 mod 256
511 mod 512
```

Thus a long exact-height-one path is being forced toward the 2-adic point
`-1`.  This is still an observation ladder, not a Collatz convergence proof.
But the local obstruction has become clearer: every additional retention step
requires one more exact binary address bit.

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
mod 64 orbit-label split
mod 64 five-step recovery
raw arithmetic anchors through mod 512
narrowing-cylinder interpretation
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

## Next Implementation Candidates

Candidate A: promote the raw `mod 128` rung to orbit-label and drift form.

Expected theorem:

```lean
theorem sumS_six_steps_ge_seven_of_mod_onehundredtwentyeight_eq_sixtythree
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 128 = 63) :
    7 ≤ sumS n 6
```

Candidate B: stop adding fixed rungs and design the general raw arithmetic
lemma.

Observed raw form:

```text
recovery sibling:
  (2^r - 1) mod 2^(r+1)
  maps to (2^(r-1) - 1) mod 2^r

continuation sibling:
  (2^(r+1) - 1) mod 2^(r+1)
  maps to (2^r - 1) mod 2^r
```

The fixed raw anchors through mod `512` make this a reasonable next research
target, but the Lean proof will likely need power-of-two modular arithmetic
rather than only `omega`.

Candidate C: introduce a small doc-only naming layer for:

```text
RetentionCylinder
RecoverySibling
ContinuationSibling
```

This should remain doc-only unless a downstream theorem needs the definitions.
