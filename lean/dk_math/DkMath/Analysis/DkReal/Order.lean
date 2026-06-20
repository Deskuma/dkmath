/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.DkNNRealQ

#print "file: DkMath.Analysis.DkReal.Order"

/-!
# Asymptotic order for DkReal representations

For two interval representations `x` and `y`, define the order defect at stage
`n` by

`max 0 (x.lo n - y.lo n)`.

The relation `x ≤ y` means that this positive defect tends to zero. It is a
preorder on representations. Mutual order is equivalent to vanishing
lower-endpoint distance and therefore implies `DkReal.Equiv`.

The relation is invariant under `Equiv` in both arguments, so it descends to a
partial order on `DkNNRealQ`.

[TODO] Prove totality, or identify the additional representation theorem needed
to derive it.

Addition is monotone for this order. The corresponding results for
multiplication by nonnegative values and natural powers remain prerequisites
for ordered-semiring typeclasses.
-/

namespace DkMath.Analysis.DkReal

/-- Positive lower-endpoint order defect at approximation stage `n`. -/
def orderDefect
    (x y : DkMath.Analysis.DkReal) (n : ℕ) : ℚ :=
  max 0 ((x.interval n).lo - (y.interval n).lo)

/--
Asymptotic order on interval representations.

`Le x y` states that any positive excess of the lower endpoint of `x` over
that of `y` vanishes with increasing precision.
-/
def Le (x y : DkMath.Analysis.DkReal) : Prop :=
  Filter.Tendsto (orderDefect x y) Filter.atTop (nhds 0)

/-- Asymptotic order is reflexive. -/
theorem le_refl (x : DkMath.Analysis.DkReal) : Le x x := by
  unfold Le orderDefect
  simp only [sub_self, max_self]
  exact tendsto_const_nhds

/-- Representation equivalence implies asymptotic order. -/
theorem equiv_le
    {x y : DkMath.Analysis.DkReal} (hxy : Equiv x y) :
    Le x y := by
  have hlo := equiv_tendsto_lo_sub_zero hxy
  simpa only [Le, orderDefect, max_comm] using
    hlo.max tendsto_const_nhds

/-- Asymptotic order is transitive. -/
theorem le_trans
    {x y z : DkMath.Analysis.DkReal} (hxy : Le x y) (hyz : Le y z) :
    Le x z := by
  have hupper :
      Filter.Tendsto
        (fun n => orderDefect x y n + orderDefect y z n)
        Filter.atTop (nhds 0) := by
    simpa only [zero_add] using hxy.add hyz
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun n => le_max_left 0 _)
    (fun n => by
      simp only [orderDefect]
      have hxy' :
          (x.interval n).lo - (y.interval n).lo ≤
            max 0 ((x.interval n).lo - (y.interval n).lo) :=
        le_max_right _ _
      have hyz' :
          (y.interval n).lo - (z.interval n).lo ≤
            max 0 ((y.interval n).lo - (z.interval n).lo) :=
        le_max_right _ _
      apply max_le
      · exact add_nonneg (le_max_left _ _) (le_max_left _ _)
      · linarith)

/-- Mutual asymptotic order implies representation equivalence. -/
theorem equiv_of_le_of_le
    {x y : DkMath.Analysis.DkReal} (hxy : Le x y) (hyx : Le y x) :
    Equiv x y := by
  have hsum :
      Filter.Tendsto
        (fun n => orderDefect x y n + orderDefect y x n)
        Filter.atTop (nhds 0) := by
    simpa only [zero_add] using hxy.add hyx
  have habs :
      Filter.Tendsto
        (fun n => |(x.interval n).lo - (y.interval n).lo|)
        Filter.atTop (nhds 0) := by
    convert hsum using 1
    · funext n
      simp only [orderDefect]
      by_cases h :
          0 ≤ (x.interval n).lo - (y.interval n).lo
      · rw [abs_of_nonneg h, max_eq_right h]
        have hneg :
            (y.interval n).lo - (x.interval n).lo ≤ 0 := by linarith
        simp [hneg]
      · have hneg :
            (x.interval n).lo - (y.interval n).lo ≤ 0 := le_of_not_ge h
        have hrev :
            0 ≤ (y.interval n).lo - (x.interval n).lo := by linarith
        rw [abs_of_nonpos hneg]
        simp [hneg, hrev]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds habs
    (fun n => (x.interval n).separation_nonneg (y.interval n))
    (fun n => (x.interval n).separation_le_abs_lo_sub_lo (y.interval n))

/-- Equivalent replacement of either argument preserves asymptotic order. -/
theorem le_congr
    {x x' y y' : DkMath.Analysis.DkReal}
    (hxx' : Equiv x x') (hyy' : Equiv y y') :
    Le x y ↔ Le x' y' := by
  constructor
  · intro hxy
    exact le_trans (equiv_le (equiv_symm hxx'))
      (le_trans hxy (equiv_le hyy'))
  · intro hx'y'
    exact le_trans (equiv_le hxx')
      (le_trans hx'y' (equiv_le (equiv_symm hyy')))

/--
Stagewise addition is monotone for asymptotic order.

The positive defect of the sum is bounded by the sum of the two positive
defects, and the latter tends to zero.
-/
theorem add_le_add
    {x y z w : DkMath.Analysis.DkReal}
    (hxy : Le x y) (hzw : Le z w) :
    Le (add x z) (add y w) := by
  have hupper :
      Filter.Tendsto
        (fun n => orderDefect x y n + orderDefect z w n)
        Filter.atTop (nhds 0) := by
    simpa only [zero_add] using hxy.add hzw
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun n => le_max_left 0 _)
    (fun n => by
      simp only [orderDefect, add_interval, addApprox, GapInterval.add]
      apply max_le
      · exact add_nonneg (le_max_left _ _) (le_max_left _ _)
      · have hxy' :
            (x.interval n).lo - (y.interval n).lo ≤
              max 0 ((x.interval n).lo - (y.interval n).lo) :=
          le_max_right _ _
        have hzw' :
            (z.interval n).lo - (w.interval n).lo ≤
              max 0 ((z.interval n).lo - (w.interval n).lo) :=
          le_max_right _ _
        linarith)

end DkMath.Analysis.DkReal

namespace DkMath.Analysis.DkNNReal

/-- Asymptotic order lifted to nonnegative representation wrappers. -/
def Le (x y : DkNNReal) : Prop :=
  DkReal.Le x.val y.val

/-- Wrapper equivalence preserves asymptotic order in both arguments. -/
theorem le_congr
    {x x' y y' : DkNNReal} (hxx' : Equiv x x') (hyy' : Equiv y y') :
    Le x y ↔ Le x' y' :=
  DkReal.le_congr hxx' hyy'

/-- Addition of nonnegative representatives is monotone in both arguments. -/
theorem add_le_add
    {x y z w : DkNNReal} (hxy : Le x y) (hzw : Le z w) :
    Le (add x z) (add y w) :=
  DkReal.add_le_add hxy hzw

end DkMath.Analysis.DkNNReal

namespace DkMath.Analysis.DkNNRealQ

/-- Quotient order induced by asymptotic order on representatives. -/
def le (x y : DkNNRealQ) : Prop :=
  Quotient.liftOn₂ x y DkNNReal.Le
    (by
      intro a a' b b' haa' hbb'
      exact propext (DkNNReal.le_congr haa' hbb'))

instance : LE DkNNRealQ where
  le := le

/-- The quotient order is a partial order. -/
instance : PartialOrder DkNNRealQ where
  le_refl x := by
    refine Quotient.inductionOn x ?_
    intro a
    exact DkReal.le_refl a.val
  le_trans x y z := by
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c hab hbc
    exact DkReal.le_trans hab hbc
  le_antisymm x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro a b hab hba
    exact Quotient.sound (DkReal.equiv_of_le_of_le hab hba)

/-- Quotient addition is monotone in both arguments. -/
theorem add_le_add
    {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
    x + z ≤ y + w := by
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro a b hab
  refine Quotient.inductionOn₂ z w ?_ hzw
  intro c d hcd
  exact DkNNReal.add_le_add hab hcd

end DkMath.Analysis.DkNNRealQ
