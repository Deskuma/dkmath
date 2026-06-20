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

Addition, multiplication on nonnegative representations, and natural powers
are monotone for this order, and zero is the least quotient value. The
quotient therefore carries Mathlib's `IsOrderedRing` predicate, whose name is
historical: its algebraic assumption is only `Semiring`. No canonical-order,
strict-order, or linear-order structure is claimed.
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
The rational zero approximation is below every nonnegative representation.

At every stage its lower endpoint is zero, so the order defect is identically
zero by nonnegativity of the other lower endpoint.
-/
theorem zero_le
    {x : DkMath.Analysis.DkReal} (hx : Nonnegative x) :
    Le (DkMath.Analysis.DkReal.ofRat 0) x := by
  unfold Le orderDefect
  simp only [ofRat_interval, GapInterval.singleton_lo, zero_sub]
  have hzero :
      (fun n => max 0 (-(x.interval n).lo)) = fun _ => (0 : ℚ) := by
    funext n
    exact max_eq_left (neg_nonpos.mpr (hx n))
  rw [hzero]
  exact tendsto_const_nhds

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

/--
Nonnegative multiplication is monotone for asymptotic order.

The positive defect of a product is bounded by

`x.lo * defect(z,w) + w.lo * defect(x,y)`.

Both lower-endpoint sequences are uniformly bounded, while both defects tend
to zero.
-/
theorem mulNonneg_le_mulNonneg
    {x y z w : DkMath.Analysis.DkReal}
    (hx : Nonnegative x) (hy : Nonnegative y)
    (hz : Nonnegative z) (hw : Nonnegative w)
    (hxy : Le x y) (hzw : Le z w) :
    Le (mulNonneg x z hx hz) (mulNonneg y w hy hw) := by
  have hleft :
      Filter.Tendsto
        (fun n => (x.interval n).lo * orderDefect z w n)
        Filter.atTop (nhds 0) := by
    simpa only [mul_comm] using
      hzw.zero_mul_isBoundedUnder_le (isBoundedUnder_norm_lo x hx)
  have hright :
      Filter.Tendsto
        (fun n => (w.interval n).lo * orderDefect x y n)
        Filter.atTop (nhds 0) := by
    simpa only [mul_comm] using
      hxy.zero_mul_isBoundedUnder_le (isBoundedUnder_norm_lo w hw)
  have hupper :
      Filter.Tendsto
        (fun n =>
          (x.interval n).lo * orderDefect z w n +
            (w.interval n).lo * orderDefect x y n)
        Filter.atTop (nhds 0) := by
    simpa only [zero_add] using hleft.add hright
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun n => le_max_left 0 _)
    (fun n => by
      simp only [orderDefect, mulNonneg_interval, mulNonnegApprox,
        GapInterval.mulNonneg_lo]
      apply max_le
      · exact add_nonneg
          (mul_nonneg (hx n) (le_max_left _ _))
          (mul_nonneg (hw n) (le_max_left _ _))
      · have hzw' :
            (z.interval n).lo - (w.interval n).lo ≤
              max 0 ((z.interval n).lo - (w.interval n).lo) :=
          le_max_right _ _
        have hxy' :
            (x.interval n).lo - (y.interval n).lo ≤
              max 0 ((x.interval n).lo - (y.interval n).lo) :=
          le_max_right _ _
        nlinarith [hx n, hw n])

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

/-- Zero is below every nonnegative representative. -/
theorem zero_le (x : DkNNReal) : Le zero x :=
  DkReal.zero_le x.nonnegative

/-- Addition of nonnegative representatives is monotone in both arguments. -/
theorem add_le_add
    {x y z w : DkNNReal} (hxy : Le x y) (hzw : Le z w) :
    Le (add x z) (add y w) :=
  DkReal.add_le_add hxy hzw

/-- Multiplication of nonnegative representatives is monotone in both arguments. -/
theorem mul_le_mul
    {x y z w : DkNNReal} (hxy : Le x y) (hzw : Le z w) :
    Le (mul x z) (mul y w) :=
  DkReal.mulNonneg_le_mulNonneg
    x.nonnegative y.nonnegative z.nonnegative w.nonnegative hxy hzw

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

/-- Zero is the least value of the nonnegative quotient. -/
theorem zero_le (x : DkNNRealQ) : 0 ≤ x := by
  refine Quotient.inductionOn x ?_
  intro a
  exact DkNNReal.zero_le a

/-- Zero is below one. -/
theorem zero_le_one : (0 : DkNNRealQ) ≤ 1 :=
  zero_le 1

/-- Quotient addition is monotone in both arguments. -/
theorem add_le_add
    {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
    x + z ≤ y + w := by
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro a b hab
  refine Quotient.inductionOn₂ z w ?_ hzw
  intro c d hcd
  exact DkNNReal.add_le_add hab hcd

/-- Addition by a fixed right summand preserves order. -/
theorem add_le_add_left
    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
    x + z ≤ y + z :=
  add_le_add hxy (le_refl z)

/-- Addition by a fixed left summand preserves order. -/
theorem add_le_add_right
    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
    z + x ≤ z + y :=
  add_le_add (le_refl z) hxy

/-- Quotient multiplication is monotone in both arguments. -/
theorem mul_le_mul
    {x y z w : DkNNRealQ} (hxy : x ≤ y) (hzw : z ≤ w) :
    x * z ≤ y * w := by
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro a b hab
  refine Quotient.inductionOn₂ z w ?_ hzw
  intro c d hcd
  exact DkNNReal.mul_le_mul hab hcd

/-- Multiplication by a fixed left factor preserves order. -/
theorem mul_le_mul_of_nonneg_left
    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
    z * x ≤ z * y :=
  mul_le_mul (le_refl z) hxy

/-- Multiplication by a fixed right factor preserves order. -/
theorem mul_le_mul_of_nonneg_right
    {x y : DkNNRealQ} (hxy : x ≤ y) (z : DkNNRealQ) :
    x * z ≤ y * z :=
  mul_le_mul hxy (le_refl z)

/--
Natural powers are monotone.

The proof is algebraic: the successor step combines the induction hypothesis
with monotonicity of multiplication.
-/
theorem pow_le_pow
    {x y : DkNNRealQ} (hxy : x ≤ y) (d : ℕ) :
    x ^ d ≤ y ^ d := by
  induction d with
  | zero =>
      rw [pow_zero, pow_zero]
  | succ d ih =>
      rw [pow_succ_eq, pow_succ_eq]
      exact mul_le_mul ih hxy

/--
Ordered-semiring compatibility for the quotient.

Despite its historical name, Mathlib's `IsOrderedRing` requires only a
`Semiring`, a partial order, monotone addition, `0 ≤ 1`, and monotonicity of
multiplication by nonnegative factors. Every quotient value is nonnegative,
so the stronger two-variable multiplication theorem supplies both one-sided
fields.
-/
instance : IsOrderedRing DkNNRealQ where
  add_le_add_left _ _ h z := add_le_add_left h z
  zero_le_one := zero_le_one
  mul_le_mul_of_nonneg_left := by
    intro a _ b c hbc
    exact mul_le_mul_of_nonneg_left hbc a
  mul_le_mul_of_nonneg_right := by
    intro c _ a b hab
    exact mul_le_mul_of_nonneg_right hab c

end DkMath.Analysis.DkNNRealQ
