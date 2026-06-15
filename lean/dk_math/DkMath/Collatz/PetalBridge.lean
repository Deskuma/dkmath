/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.Accelerated
import DkMath.Collatz.Shift
import DkMath.Petal.RangeFamily

#print "file: DkMath.Collatz.PetalBridge"

/-!
# Collatz Petal Bridge

This file is a small observation window between the accelerated Collatz
dynamics and the Petal range-family API.

The bridge is intentionally thin.  It does not claim any Collatz convergence
or nontrivial cycle theorem.  It only fixes the common language:

```text
accelerated Collatz orbit segment
  -> range-indexed labels
  -> either pairwise separated, or a collision closes that route as False
```

For Petal/ABC routes, a repeated label means that a proposed independent
range-family cannot be counted as `k` independent carriers.  For Collatz
dynamics, the same collision is not merely a failure: it is the observable
shape of a merge, fold, or cycle candidate.
-/

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
The window height is the existing Collatz observation `s` applied to the
corresponding accelerated state.
-/
theorem orbitWindowHeight_eq_s_iterateT (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i = s (iterateT i n) := rfl

/--
Block shifts preserve the raw height when the observed height is below the
block exponent.

This is `v2_shift_invariant` in the observation-window vocabulary.  It is the
first stable bridge from Collatz shift invariance to a Petal-style address
reading: inside a sufficiently large `2^k` block, the height label is conserved.
-/
theorem rawHeightLabel_shift_eq
    (k m n : ℕ)
    (hk : rawHeightLabel n < k) :
    rawHeightLabel (shift k m n) = rawHeightLabel n :=
  v2_shift_invariant k m n hk

/--
Pairwise separated Collatz orbit labels give the Petal range-label injectivity
condition.
-/
theorem oddOrbitLabel_injOn_of_pairwiseSeparated
    (n : OddNat) {k : ℕ}
    (hsep : OddOrbitLabelsPairwiseSeparated n k) :
    Set.InjOn (oddOrbitLabel n) ↑(Finset.range k) :=
  DkMath.Petal.rangeLabel_injOn_of_pairwise_ne hsep

/--
Equal Collatz odd-state labels identify the accelerated states themselves.

Since `OddNat` is a subtype of natural numbers, equality of the stored natural
value is equality of the subtype state.
-/
theorem iterateT_eq_of_oddOrbitLabel_eq
    {n : OddNat} {i j : ℕ}
    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
    iterateT i n = iterateT j n := by
  apply Subtype.ext
  exact hlabel

/--
False/obstruction window for Collatz orbit labels.

If an orbit segment is assumed pairwise separated but two distinct in-range
times have the same odd-state label, the independent Petal range route closes
as `False`.
-/
theorem oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
    {n : OddNat} {k i j : ℕ}
    (hsep : OddOrbitLabelsPairwiseSeparated n k)
    (hi : i < k) (hj : j < k)
    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j)
    (hne : i ≠ j) :
    False :=
  DkMath.Petal.rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
    hsep hi hj hlabel hne

/--
Collision observation form.

When two different in-range Collatz times have the same label, they are the
same accelerated odd state.  This theorem does not call that good or bad:
Petal/ABC reads it as an independence obstruction, while Collatz reads it as a
merge/fold/cycle candidate.
-/
theorem same_iterateT_of_oddOrbitLabel_collision
    {n : OddNat} {k i j : ℕ}
    (_hi : i < k) (_hj : j < k)
    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
    iterateT i n = iterateT j n :=
  iterateT_eq_of_oddOrbitLabel_eq hlabel

/--
A window collision identifies the two accelerated Collatz states at the
colliding times.
-/
theorem exists_same_iterateT_of_orbitWindowCollision
    {n : OddNat} {k : ℕ}
    (hcollision : OrbitWindowCollision n k) :
    ∃ i j, i < k ∧ j < k ∧ i ≠ j ∧ iterateT i n = iterateT j n := by
  rcases hcollision with ⟨i, j, hi, hj, hne, hlabel⟩
  exact ⟨i, j, hi, hj, hne, iterateT_eq_of_oddOrbitLabel_eq hlabel⟩

/--
Separated windows have no collision.
-/
theorem not_orbitWindowCollision_of_separated
    {n : OddNat} {k : ℕ}
    (hsep : OrbitWindowSeparated n k) :
    ¬ OrbitWindowCollision n k := by
  intro hcollision
  rcases hcollision with ⟨i, j, hi, hj, hne, hlabel⟩
  exact (hsep i hi j hj hne) hlabel

/--
A collision closes the separated-window route as `False`.
-/
theorem orbitWindowSeparated_contradiction_of_collision
    {n : OddNat} {k : ℕ}
    (hsep : OrbitWindowSeparated n k)
    (hcollision : OrbitWindowCollision n k) :
    False :=
  not_orbitWindowCollision_of_separated hsep hcollision

/--
Finite observation split: an accelerated Collatz window is either pairwise
separated, or it contains a collision.

This is not a convergence statement.  It only names the two basic observation
modes for a finite window.
-/
theorem orbitWindowSeparated_or_collision
    (n : OddNat) (k : ℕ) :
    OrbitWindowSeparated n k ∨ OrbitWindowCollision n k := by
  classical
  by_cases hsep : OrbitWindowSeparated n k
  · exact Or.inl hsep
  · right
    unfold OrbitWindowSeparated OddOrbitLabelsPairwiseSeparated at hsep
    push Not at hsep
    rcases hsep with ⟨i, hi, j, hj, hne, hlabel⟩
    exact ⟨i, j, hi, hj, hne, hlabel⟩

end DkMath.Collatz
