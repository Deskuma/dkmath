/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.Accelerated
import DkMath.Collatz.Shift
import DkMath.Collatz.GnomonEvaluation
import DkMath.Petal.RangeFamily

#print "file: DkMath.Collatz.PetalBridge.Basic"

namespace DkMath.Collatz

/--
Raw 2-adic height observation for a natural state.

This is the address-like Collatz quantity:

```text
n -> v2 (3n + 1)
```

For an odd state it is exactly the accelerated Collatz observation `s`.
-/
def rawHeightLabel (n : ℕ) : ℕ :=
  v2 (3 * n + 1)

/--
The finite observation window for the first `k` accelerated Collatz states.

This is intentionally just `Finset.range k`; the point is to give the Collatz
side a named window that can later carry address, height, or statistical
observations.
-/
def OrbitWindow (_n : OddNat) (k : ℕ) : Finset ℕ :=
  Finset.range k

/--
The natural-number label of the `i`-th accelerated Collatz odd state.

This is the Collatz-facing candidate for a Petal `qOf i` label.  It deliberately
forgets the proof that the state is odd and keeps only the observed address
value.
-/
noncomputable def oddOrbitLabel (n : OddNat) (i : ℕ) : ℕ :=
  (iterateT i n).1

/--
The 2-adic height observed at the `i`-th accelerated Collatz odd state.

This is the first address-like label attached to the Collatz observation window.
-/
noncomputable def orbitWindowHeight (n : OddNat) (i : ℕ) : ℕ :=
  rawHeightLabel (oddOrbitLabel n i)

/--
The ordered height profile observed in the first `k` accelerated Collatz
states.

This keeps order, unlike a finite support/image view.  It is the window-level
form of the sequence summed by `sumS`.
-/
noncomputable def orbitWindowHeightSeq (n : OddNat) (k : ℕ) : List ℕ :=
  (List.range k).map (orbitWindowHeight n)

/--
Residual shape extracted at the `i`-th accelerated Collatz odd-state label.

This is a window-level lift of `RawGnomonResidualShape`; the low-level gnomon
vocabulary stays in `GnomonEvaluation`, while this definition records the
finite-window observation.
-/
noncomputable def orbitWindowResidualShape (n : OddNat) (i : ℕ) : ℕ :=
  RawGnomonResidualShape (oddOrbitLabel n i)

/--
The ordered residual-shape profile observed in the first `k` accelerated
Collatz states.

Checkpoint 127 reads the orbit window as a finite chain of residual-shape
extractions.
-/
noncomputable def orbitWindowResidualShapeSeq (n : OddNat) (k : ℕ) : List ℕ :=
  (List.range k).map (orbitWindowResidualShape n)

/--
Low-bit all-ones depth of a natural residual shape.

This is the direct Lean counterpart of the checkpoint-132 scan observable:

```text
all_ones_depth x = v2 (x + 1)
```

It measures how long the low-bit suffix of `x` stays in the all-ones channel:
`1`, `3`, `7`, `15`, `31`, ...
-/
def ResidualAllOnesDepth (x : ℕ) : ℕ :=
  v2 (x + 1)

/--
All-ones depth of the residual shape at a window index.

This keeps the time index `i` separate from pressure depth `j`.  It is an
observable profile, not a pressure-prefix theorem.
-/
noncomputable def orbitWindowResidualAllOnesDepth
    (n : OddNat) (i : ℕ) : ℕ :=
  ResidualAllOnesDepth (orbitWindowResidualShape n i)

/--
Ordered all-ones-depth profile of the residual shapes in a finite orbit window.

Checkpoint 132 adds this thin profile before introducing any heavier grid:
the current experiment asks whether positive pressure blocks are explained by
concentration in deep all-ones residual channels.
-/
noncomputable def orbitWindowResidualAllOnesDepthSeq
    (n : OddNat) (k : ℕ) : List ℕ :=
  (List.range k).map (orbitWindowResidualAllOnesDepth n)

/--
First failed power-of-two alignment depth at the `i`-th observed odd label.

This is the window-level version of `FirstFailedPow2Depth`.
-/
noncomputable def orbitWindowFirstFailedPow2Depth (n : OddNat) (i : ℕ) : ℕ :=
  FirstFailedPow2Depth (oddOrbitLabel n i)

/--
The first `k` accelerated Collatz odd-state labels are pairwise separated.

This is the Collatz-specific spelling of the RangeFamily pairwise condition:
different in-range times have different observed odd states.
-/
def OddOrbitLabelsPairwiseSeparated (n : OddNat) (k : ℕ) : Prop :=
  ∀ i, i < k → ∀ j, j < k → i ≠ j → oddOrbitLabel n i ≠ oddOrbitLabel n j

/--
Window-level spelling of pairwise separation for accelerated Collatz labels.
-/
def OrbitWindowSeparated (n : OddNat) (k : ℕ) : Prop :=
  OddOrbitLabelsPairwiseSeparated n k

/--
Window-level collision: two distinct in-window times have the same accelerated
odd-state label.

For Petal/ABC this blocks independent range counting.  For Collatz dynamics it
is the observable merge/fold/cycle signal.
-/
def OrbitWindowCollision (n : OddNat) (k : ℕ) : Prop :=
  ∃ i j, i < k ∧ j < k ∧ i ≠ j ∧ oddOrbitLabel n i = oddOrbitLabel n j

/--
The named Collatz observation window is definitionally the range window.
-/
theorem orbitWindow_eq_range (n : OddNat) (k : ℕ) :
    OrbitWindow n k = Finset.range k := rfl

/--
Raw height agrees with the existing Collatz observation `s` on odd states.
-/
theorem rawHeightLabel_eq_s (n : OddNat) :
    rawHeightLabel n.1 = s n := rfl

/--
Window height is the raw gnomon alignment height of the observed odd label.

This is the PetalBridge lift of the checkpoint-126 residual-shape vocabulary:
the finite window still uses `orbitWindowHeight`, but it can now be read as
`RawGnomonHeight` pointwise.
-/
theorem orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel
    (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i =
      RawGnomonHeight (oddOrbitLabel n i) := by
  unfold orbitWindowHeight rawHeightLabel RawGnomonHeight
  rw [rawGnomonStep_eq_three_mul_add_one]

/--
The window height is the existing Collatz observation `s` applied to the
corresponding accelerated state.
-/
theorem orbitWindowHeight_eq_s_iterateT (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i = s (iterateT i n) := rfl


end DkMath.Collatz
