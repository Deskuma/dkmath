/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.Residues

#print "file: DkMath.Collatz.PetalBridge.Profiles"

namespace DkMath.Collatz


/--
The ordered height profile has length equal to the window size.
-/
theorem orbitWindowHeightSeq_length (n : OddNat) (k : ℕ) :
    (orbitWindowHeightSeq n k).length = k := by
  simp [orbitWindowHeightSeq]

/--
The sum of the ordered height profile is exactly the existing Collatz `sumS`.

This connects the Petal-style finite observation window with the existing
Collatz drift/statistics API.
-/
theorem orbitWindowHeightSeq_sum_eq_sumS (n : OddNat) (k : ℕ) :
    (orbitWindowHeightSeq n k).sum = sumS n k := by
  induction k with
  | zero =>
      simp [orbitWindowHeightSeq, sumS]
  | succ k ih =>
      have ih' :
          (List.map (orbitWindowHeight n) (List.range k)).sum = sumS n k := by
        simpa [orbitWindowHeightSeq] using ih
      simp [orbitWindowHeightSeq, List.range_succ, sumS,
        orbitWindowHeight_eq_s_iterateT, ih']

/--
If every height in the window is at least `threshold`, then the accumulated
Collatz height is at least `k * threshold`.

This is the integer threshold form of an average-height lower bound.  It avoids
real logarithms and keeps the bridge on the combinatorial side.
-/
theorem orbitWindowHeightSeq_sum_ge_of_forall_ge
    (n : OddNat) {k threshold : ℕ}
    (h : ∀ i, i < k → threshold ≤ orbitWindowHeight n i) :
    k * threshold ≤ sumS n k := by
  induction k with
  | zero =>
      simp [sumS]
  | succ k ih =>
      have hprefix : ∀ i, i < k → threshold ≤ orbitWindowHeight n i := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self k))
      have hlast : threshold ≤ orbitWindowHeight n k := h k (Nat.lt_succ_self k)
      have ih' : k * threshold ≤ sumS n k := ih hprefix
      rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
      rw [Nat.succ_mul]
      exact Nat.add_le_add ih' hlast

/--
The prefix of the ordered height profile has sum `sumS n r`, as long as the
prefix length `r` lies inside the ambient window `k`.
-/
theorem orbitWindowHeightSeq_take_sum_eq_sumS
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    ((orbitWindowHeightSeq n k).take r).sum = sumS n r := by
  rw [← orbitWindowHeightSeq_sum_eq_sumS n r]
  simp [orbitWindowHeightSeq, ← List.map_take, List.take_range, Nat.min_eq_left hr]

/--
The prefix of length `r` has length `r` when `r` lies inside the window.
-/
theorem orbitWindowHeightSeq_take_length
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    ((orbitWindowHeightSeq n k).take r).length = r := by
  simp [orbitWindowHeightSeq_length, Nat.min_eq_left hr]

/--
Reading the ordered height profile at an in-window time recovers the pointwise
height observation.
-/
theorem orbitWindowHeightSeq_get?_eq_some
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowHeightSeq n k)[i]? = some (orbitWindowHeight n i) := by
  simp [orbitWindowHeightSeq, hi]

/--
Reading a prefix of the ordered height profile recovers the same pointwise
height observation while the index remains inside the prefix.
-/
theorem orbitWindowHeightSeq_take_get?_eq_some
    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
    ((orbitWindowHeightSeq n k).take r)[i]? = some (orbitWindowHeight n i) := by
  rw [List.getElem?_take_of_lt hi]
  exact orbitWindowHeightSeq_get?_eq_some n (Nat.lt_of_lt_of_le hi hr)

/--
The ordered residual-shape profile has length equal to the window size.
-/
theorem orbitWindowResidualShapeSeq_length (n : OddNat) (k : ℕ) :
    (orbitWindowResidualShapeSeq n k).length = k := by
  simp [orbitWindowResidualShapeSeq]

/--
Reading the ordered residual-shape profile at an in-window time recovers the
pointwise residual shape.
-/
theorem orbitWindowResidualShapeSeq_get?_eq_some
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowResidualShapeSeq n k)[i]? =
      some (orbitWindowResidualShape n i) := by
  simp [orbitWindowResidualShapeSeq, hi]

/--
The prefix of length `r` in the residual-shape profile has length `r` when
`r` lies inside the window.
-/
theorem orbitWindowResidualShapeSeq_take_length
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    ((orbitWindowResidualShapeSeq n k).take r).length = r := by
  simp [orbitWindowResidualShapeSeq_length, Nat.min_eq_left hr]

/--
Reading a prefix of the residual-shape profile recovers the same pointwise
residual shape while the index remains inside the prefix.
-/
theorem orbitWindowResidualShapeSeq_take_get?_eq_some
    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
    ((orbitWindowResidualShapeSeq n k).take r)[i]? =
      some (orbitWindowResidualShape n i) := by
  rw [List.getElem?_take_of_lt hi]
  exact orbitWindowResidualShapeSeq_get?_eq_some n (Nat.lt_of_lt_of_le hi hr)

/--
The ordered all-ones-depth residual profile has length equal to the window
size.
-/
theorem orbitWindowResidualAllOnesDepthSeq_length
    (n : OddNat) (k : ℕ) :
    (orbitWindowResidualAllOnesDepthSeq n k).length = k := by
  simp [orbitWindowResidualAllOnesDepthSeq]

/--
Reading the all-ones-depth residual profile at an in-window time recovers the
pointwise all-ones-depth observation.
-/
theorem orbitWindowResidualAllOnesDepthSeq_get?_eq_some
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowResidualAllOnesDepthSeq n k)[i]? =
      some (orbitWindowResidualAllOnesDepth n i) := by
  simp [orbitWindowResidualAllOnesDepthSeq, hi]

/--
The prefix of the all-ones-depth residual profile has length `r` when `r` lies
inside the window.
-/
theorem orbitWindowResidualAllOnesDepthSeq_take_length
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    ((orbitWindowResidualAllOnesDepthSeq n k).take r).length = r := by
  simp [orbitWindowResidualAllOnesDepthSeq_length, Nat.min_eq_left hr]

/--
Reading a prefix of the all-ones-depth residual profile recovers the same
pointwise observation while the index remains inside the prefix.
-/
theorem orbitWindowResidualAllOnesDepthSeq_take_get?_eq_some
    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
    ((orbitWindowResidualAllOnesDepthSeq n k).take r)[i]? =
      some (orbitWindowResidualAllOnesDepth n i) := by
  rw [List.getElem?_take_of_lt hi]
  exact orbitWindowResidualAllOnesDepthSeq_get?_eq_some n
    (Nat.lt_of_lt_of_le hi hr)

/-
Checkpoint 133 keeps the post-refactor source of truth in code comments.

The experimental Python scan says that positive pressure blocks are better
predicted by a deep all-ones excursion somewhere in the residual-shape window
than by the first or modal residual.  The following names deliberately stay on
the time-profile axis.  They do not mention pressure depth, do not assert a
pressure prefix theorem, and do not introduce the future ShapePressureGrid.
-/

/--
The finite window contains a residual all-ones excursion at threshold `d`.

This is the thin profile-level predicate suggested by checkpoint 133.  It is
existential on the time axis `i`; it does not claim that any pressure-depth
block follows without additional retention/continuation hypotheses.
-/
def WindowHasResidualAllOnesDepthAtLeast
    (n : OddNat) (k d : ℕ) : Prop :=
  ∃ i, i < k ∧ d ≤ orbitWindowResidualAllOnesDepth n i

/--
Meaning-name alias for a deep residual all-ones excursion.

The alias is intentionally separate from pressure vocabulary.  Future pressure
bridges should consume this predicate together with a decay or retention
condition, rather than smuggling in a pressure-prefix assumption.
-/
def WindowHasDeepResidualAllOnesExcursion
    (n : OddNat) (k d : ℕ) : Prop :=
  WindowHasResidualAllOnesDepthAtLeast n k d

/-- Build a window all-ones-depth witness from an explicit in-window time. -/
theorem windowHasResidualAllOnesDepthAtLeast_of_lt
    (n : OddNat) (k d i : ℕ)
    (hi : i < k)
    (hdepth : d ≤ orbitWindowResidualAllOnesDepth n i) :
    WindowHasResidualAllOnesDepthAtLeast n k d :=
  ⟨i, hi, hdepth⟩

/--
Lower the all-ones-depth threshold of an existing window excursion.
-/
theorem windowHasResidualAllOnesDepthAtLeast_of_le
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e)
    (h : WindowHasResidualAllOnesDepthAtLeast n k e) :
    WindowHasResidualAllOnesDepthAtLeast n k d := by
  rcases h with ⟨i, hi, he⟩
  exact ⟨i, hi, le_trans hde he⟩

/-- Constructor spelling for the deep-excursion alias. -/
theorem windowHasDeepResidualAllOnesExcursion_of_lt
    (n : OddNat) (k d i : ℕ)
    (hi : i < k)
    (hdepth : d ≤ orbitWindowResidualAllOnesDepth n i) :
    WindowHasDeepResidualAllOnesExcursion n k d :=
  windowHasResidualAllOnesDepthAtLeast_of_lt n k d i hi hdepth

/-- Lower the threshold of the deep-excursion alias. -/
theorem windowHasDeepResidualAllOnesExcursion_of_le
    (n : OddNat) (k d e : ℕ)
    (hde : d ≤ e)
    (h : WindowHasDeepResidualAllOnesExcursion n k e) :
    WindowHasDeepResidualAllOnesExcursion n k d :=
  windowHasResidualAllOnesDepthAtLeast_of_le n k d e hde h

/--
First-failed-depth profile over the first `k` observed odd labels.
-/
noncomputable def orbitWindowFirstFailedPow2DepthSeq
    (n : OddNat) (k : ℕ) : List ℕ :=
  (List.range k).map (orbitWindowFirstFailedPow2Depth n)

/--
The first-failed-depth profile has length equal to the window size.
-/
theorem orbitWindowFirstFailedPow2DepthSeq_length
    (n : OddNat) (k : ℕ) :
    (orbitWindowFirstFailedPow2DepthSeq n k).length = k := by
  simp [orbitWindowFirstFailedPow2DepthSeq]

/--
Reading the ordered first-failed-depth profile at an in-window time recovers
the pointwise first-failed depth.
-/
theorem orbitWindowFirstFailedPow2DepthSeq_get?_eq_some
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowFirstFailedPow2DepthSeq n k)[i]? =
      some (orbitWindowFirstFailedPow2Depth n i) := by
  simp [orbitWindowFirstFailedPow2DepthSeq, hi]

/--
Window first-failed depth is exactly one more than the observed window height.
-/
theorem orbitWindowFirstFailedPow2Depth_eq_height_add_one
    (n : OddNat) (i : ℕ) :
    orbitWindowFirstFailedPow2Depth n i = orbitWindowHeight n i + 1 := by
  unfold orbitWindowFirstFailedPow2Depth FirstFailedPow2Depth
  rw [orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel]

/--
Reading the ordered first-failed-depth profile also recovers the observed height
plus one.
-/
theorem orbitWindowFirstFailedPow2DepthSeq_get?_eq_some_height_add_one
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowFirstFailedPow2DepthSeq n k)[i]? =
      some (orbitWindowHeight n i + 1) := by
  rw [orbitWindowFirstFailedPow2DepthSeq_get?_eq_some n hi]
  rw [orbitWindowFirstFailedPow2Depth_eq_height_add_one]

/--
The prefix of length `r` in the first-failed-depth profile has length `r` when
`r` lies inside the window.
-/
theorem orbitWindowFirstFailedPow2DepthSeq_take_length
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    ((orbitWindowFirstFailedPow2DepthSeq n k).take r).length = r := by
  simp [orbitWindowFirstFailedPow2DepthSeq_length, Nat.min_eq_left hr]

/--
Reading a prefix of the first-failed-depth profile recovers the same pointwise
first-failed depth while the index remains inside the prefix.
-/
theorem orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some
    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
    ((orbitWindowFirstFailedPow2DepthSeq n k).take r)[i]? =
      some (orbitWindowFirstFailedPow2Depth n i) := by
  rw [List.getElem?_take_of_lt hi]
  exact orbitWindowFirstFailedPow2DepthSeq_get?_eq_some n
    (Nat.lt_of_lt_of_le hi hr)

/--
Reading a prefix of the first-failed-depth profile also recovers the observed
height plus one.
-/
theorem orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some_height_add_one
    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
    ((orbitWindowFirstFailedPow2DepthSeq n k).take r)[i]? =
      some (orbitWindowHeight n i + 1) := by
  rw [orbitWindowFirstFailedPow2DepthSeq_take_get?_eq_some n hi hr]
  rw [orbitWindowFirstFailedPow2Depth_eq_height_add_one]

/--
The three time-profile lists are aligned at every in-window index.

This is a deliberately one-dimensional observation theorem.  It keeps the time
axis `i` separate from the pressure-depth axis `j`; a later
`ShapePressureGrid` should combine those axes explicitly rather than hiding
that distinction in one index.
-/
theorem orbitWindow_threeProfiles_get?_eq_some
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowHeightSeq n k)[i]? = some (orbitWindowHeight n i) ∧
      (orbitWindowResidualShapeSeq n k)[i]? =
        some (orbitWindowResidualShape n i) ∧
      (orbitWindowFirstFailedPow2DepthSeq n k)[i]? =
        some (orbitWindowFirstFailedPow2Depth n i) := by
  constructor
  · exact orbitWindowHeightSeq_get?_eq_some n hi
  constructor
  · exact orbitWindowResidualShapeSeq_get?_eq_some n hi
  · exact orbitWindowFirstFailedPow2DepthSeq_get?_eq_some n hi

/--
The integer threshold lower bound also applies to prefixes.
-/
theorem orbitWindowHeightSeq_prefix_sum_ge_of_forall_ge
    (n : OddNat) {r k threshold : ℕ} (hr : r ≤ k)
    (h : ∀ i, i < r → threshold ≤ orbitWindowHeight n i) :
    r * threshold ≤ ((orbitWindowHeightSeq n k).take r).sum := by
  rw [orbitWindowHeightSeq_take_sum_eq_sumS n hr]
  exact orbitWindowHeightSeq_sum_ge_of_forall_ge n h

/--
Equal Collatz orbit labels have equal height observations.
-/
theorem orbitWindowHeight_eq_of_oddOrbitLabel_eq
    {n : OddNat} {i j : ℕ}
    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
    orbitWindowHeight n i = orbitWindowHeight n j := by
  simp [orbitWindowHeight, hlabel]

/--
A label collision forces equality of the height observations at the colliding
times.

If the orbit has returned to the same odd state, then the next `v2` height read
from that state is also the same.
-/
theorem orbitWindowHeight_eq_of_collision
    {n : OddNat} {k i j : ℕ}
    (_hi : i < k) (_hj : j < k)
    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
    orbitWindowHeight n i = orbitWindowHeight n j :=
  orbitWindowHeight_eq_of_oddOrbitLabel_eq hlabel

/--
Equal accelerated Collatz states have equal height observations.
-/
theorem orbitWindowHeight_eq_of_same_iterateT
    {n : OddNat} {i j : ℕ}
    (hstate : iterateT i n = iterateT j n) :
    orbitWindowHeight n i = orbitWindowHeight n j :=
  orbitWindowHeight_eq_of_oddOrbitLabel_eq (congrArg Subtype.val hstate)


end DkMath.Collatz
