/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.Accelerated

#print "file: DkMath.Collatz.GnomonEvaluation"

/-!
# Collatz Gnomon Evaluation

This file starts the checkpoint-125 refactor layer.

`DkMath.Collatz.PetalBridge` has grown into a large observation surface.  New
low-level vocabulary should not be added there by default.  This file is the
new lower layer for the revised reading:

```text
Odd Gnomon correction
  n -> n + (2n+1) = 3n+1

Pow2 alignment evaluation
  v2 (3n+1)

Residual shape extraction
  (3n+1) / 2^height

Relative scale update
  the residual odd shape becomes the next odd state
```

The important shift is linguistic and structural.  We no longer treat the
Collatz odd step merely as "multiply by three and add one".  We expose it as
an odd square-gnomon correction followed by a power-of-two alignment
evaluation.

Keep this file integer-valued.  Do not introduce `Real.log` here.  Logarithmic
drift belongs to the final translation layer, after the integer shape and
margin surfaces have been stabilized.
-/

namespace DkMath.Collatz

/--
The odd gnomon layer at `n`.

This is the square-difference layer

```text
(n+1)^2 - n^2 = 2n+1.
```
-/
def OddGnomonLayer (n : ℕ) : ℕ :=
  2 * n + 1

/--
The raw Collatz odd-step numerator read as a gnomon correction.

Instead of starting from `3n+1`, this definition records the decomposition

```text
n + (2n+1).
```
-/
def RawGnomonStep (n : ℕ) : ℕ :=
  n + OddGnomonLayer n

/-- The raw gnomon step is the usual `3n+1` numerator. -/
theorem rawGnomonStep_eq_three_mul_add_one
    (n : ℕ) :
    RawGnomonStep n = 3 * n + 1 := by
  unfold RawGnomonStep OddGnomonLayer
  ring

/-- Bridge to the existing base definition `threeNPlusOne`. -/
theorem rawGnomonStep_eq_threeNPlusOne
    (n : ℕ) :
    RawGnomonStep n = threeNPlusOne n := by
  rw [rawGnomonStep_eq_three_mul_add_one]
  rfl

/--
The next square is obtained by adding the odd gnomon layer.

This fixes the geometric source of `OddGnomonLayer` without introducing any
real or Euclidean geometry.
-/
theorem square_succ_eq_square_add_oddGnomonLayer
    (n : ℕ) :
    (n + 1) ^ 2 = n ^ 2 + OddGnomonLayer n := by
  unfold OddGnomonLayer
  ring

/-- The first `n` odd gnomon layers sum to `n^2`. -/
theorem sum_oddGnomonLayer_eq_square
    (n : ℕ) :
    (Finset.range n).sum OddGnomonLayer = n ^ 2 := by
  induction n with
  | zero =>
      simp [OddGnomonLayer]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold OddGnomonLayer
      ring

/--
The classical odd-number sum form.

This alias is useful for callers that do not want the named
`OddGnomonLayer` vocabulary.
-/
theorem sum_odd_eq_square
    (n : ℕ) :
    (Finset.range n).sum (fun i => 2 * i + 1) = n ^ 2 := by
  simpa [OddGnomonLayer] using sum_oddGnomonLayer_eq_square n

/--
A shifted gnomon band from `P` of length `u`.

This is the integer bridge between a single gap `u` and `u` unit gnomon
layers.  It is the square-growth form that later connects Collatz gnomon
correction to the Petal/cosmic `Gap = 1` viewpoint.
-/
theorem square_add_eq_square_add_gnomon_sum
    (P u : ℕ) :
    (P + u) ^ 2 =
      P ^ 2 + (Finset.range u).sum (fun i => 2 * (P + i) + 1) := by
  induction u with
  | zero =>
      simp
  | succ u ih =>
      rw [Finset.sum_range_succ]
      calc
        (P + (u + 1)) ^ 2 = (P + u) ^ 2 + (2 * (P + u) + 1) := by
          ring
        _ = P ^ 2 + (Finset.range u).sum (fun i => 2 * (P + i) + 1) +
            (2 * (P + u) + 1) := by
          rw [ih]
        _ = P ^ 2 +
            ((Finset.range u).sum (fun i => 2 * (P + i) + 1) +
              (2 * (P + u) + 1)) := by
          ring

/--
Power-of-two alignment height of the raw gnomon step.

This is the revised name for the old observation `v2 (3n+1)`: it measures how
deeply the gnomon-corrected raw value aligns with the power-of-two grid.
-/
noncomputable def RawGnomonHeight (n : ℕ) : ℕ :=
  v2 (RawGnomonStep n)

/--
Residual shape after removing the visible power-of-two alignment.

For odd Collatz states, this is the natural-number value underlying the next
accelerated odd state.  The exact bridge to `T` is intentionally left for a
later file/checkpoint, because it should use the existing maximality lemmas for
`padicValNat` rather than ad-hoc division reasoning.
-/
noncomputable def RawGnomonResidualShape (n : ℕ) : ℕ :=
  RawGnomonStep n / 2 ^ RawGnomonHeight n

/-- Existing Collatz observation `s` is the raw gnomon alignment height. -/
theorem rawGnomonHeight_eq_s
    (n : OddNat) :
    RawGnomonHeight n.1 = s n := by
  unfold RawGnomonHeight s
  rw [rawGnomonStep_eq_threeNPlusOne]

/-- Remainder profile of the raw gnomon step at a power-of-two depth. -/
def RawGnomonRemainderAtDepth (n j : ℕ) : ℕ :=
  RawGnomonStep n % 2 ^ j

/--
First depth after the visible power-of-two alignment.

For later shape analysis, depths `j <= RawGnomonHeight n` are fully aligned;
`RawGnomonHeight n + 1` is the first depth where the residual odd shape is
visible.
-/
noncomputable def FirstFailedPow2Depth (n : ℕ) : ℕ :=
  RawGnomonHeight n + 1

/--
At every depth up to the alignment height, the raw gnomon step has zero
remainder.

This is the first formal reading of `RawGnomonHeight` as a power-of-two
alignment depth.
-/
theorem rawGnomonRemainderAtDepth_eq_zero_of_le_height
    (n j : ℕ)
    (hj : j ≤ RawGnomonHeight n) :
    RawGnomonRemainderAtDepth n j = 0 := by
  unfold RawGnomonRemainderAtDepth
  have htop : 2 ^ RawGnomonHeight n ∣ RawGnomonStep n := by
    unfold RawGnomonHeight
    simpa [v2] using
      (pow_padicValNat_dvd (p := 2) (n := RawGnomonStep n))
  have hdiv : 2 ^ j ∣ RawGnomonStep n :=
    dvd_trans (pow_dvd_pow 2 hj) htop
  exact Nat.dvd_iff_mod_eq_zero.mp hdiv

/--
The residual shape is exactly the natural value of the existing accelerated
Collatz map.

This closes the checkpoint-126 bridge:

```text
RawGnomonStep      = existing `threeNPlusOne`
RawGnomonHeight    = existing `s`
RawGnomonResidualShape = existing `(T n).1`
```

After this theorem, the new gnomon vocabulary is not merely explanatory; it is
definitionally connected to the core accelerated odd-state dynamics.
-/
theorem rawGnomonResidualShape_eq_T_val
    (n : OddNat) :
    RawGnomonResidualShape n.1 = (T n).1 := by
  unfold RawGnomonResidualShape RawGnomonHeight T
  rw [rawGnomonStep_eq_threeNPlusOne]
  rfl

/--
The residual shape is odd.

The proof intentionally uses `rawGnomonResidualShape_eq_T_val`: oddness is
already carried by the `OddNat` result of `T`, so we do not duplicate the
`padicValNat` maximality proof here.
-/
theorem rawGnomonResidualShape_odd
    (n : OddNat) :
    RawGnomonResidualShape n.1 % 2 = 1 := by
  rw [rawGnomonResidualShape_eq_T_val n]
  exact (T n).2

/--
The raw gnomon step factors into its visible power-of-two alignment and its
residual shape.

This is the multiplicative counterpart of the residual-shape bridge.
-/
theorem rawGnomonStep_eq_pow_height_mul_residualShape
    (n : OddNat) :
    RawGnomonStep n.1 =
      2 ^ RawGnomonHeight n.1 * RawGnomonResidualShape n.1 := by
  unfold RawGnomonResidualShape
  have hdiv : 2 ^ RawGnomonHeight n.1 ∣ RawGnomonStep n.1 := by
    unfold RawGnomonHeight
    simpa [v2] using
      (pow_padicValNat_dvd (p := 2) (n := RawGnomonStep n.1))
  exact (Nat.mul_div_cancel' hdiv).symm

/--
The next power after the alignment height does not divide the raw gnomon step.

This is the formal "first failed depth" boundary: height is maximal.
-/
theorem two_pow_succ_rawGnomonHeight_not_dvd
    (n : OddNat) :
    ¬ 2 ^ (RawGnomonHeight n.1 + 1) ∣ RawGnomonStep n.1 := by
  have hpos : RawGnomonStep n.1 ≠ 0 := by
    rw [rawGnomonStep_eq_three_mul_add_one]
    omega
  unfold RawGnomonHeight
  simpa [v2] using
    (pow_succ_padicValNat_not_dvd hpos)

/--
At the first failed depth, the raw gnomon remainder is nonzero.

Together with `rawGnomonRemainderAtDepth_eq_zero_of_le_height`, this pins down
the exact boundary:

```text
j <= height     -> remainder = 0
j = height + 1  -> remainder != 0
```
-/
theorem rawGnomonRemainderAtDepth_firstFailed_ne_zero
    (n : OddNat) :
    RawGnomonRemainderAtDepth n.1 (FirstFailedPow2Depth n.1) ≠ 0 := by
  unfold RawGnomonRemainderAtDepth FirstFailedPow2Depth
  intro h
  have hdiv :
      2 ^ (RawGnomonHeight n.1 + 1) ∣ RawGnomonStep n.1 :=
    Nat.dvd_iff_mod_eq_zero.mpr h
  exact two_pow_succ_rawGnomonHeight_not_dvd n hdiv

end DkMath.Collatz
