/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.Pow

#print "file: DkMath.Analysis.DkReal.Arithmetic"

/-!
# Nonnegative arithmetic for DkReal

This file lifts exact rational interval addition and multiplication to
nonnegative `DkReal` approximations.

The constructions remain computable. Their interval endpoints use only
rational addition and multiplication; real analysis appears only in proof
fields certifying that the rational widths tend to zero.
-/

namespace DkMath.Analysis.DkReal

/-!
## I. Addition

For nested intervals `[aₙ,bₙ]` and `[cₙ,dₙ]`, their Minkowski sums
`[aₙ+cₙ,bₙ+dₙ]` are nested and have width

`(bₙ-aₙ) + (dₙ-cₙ)`.

Thus closure under addition follows directly from closure of limits under
finite sums.
-/

/-- Stagewise Minkowski sum of two `DkReal` approximations. -/
def addApprox (x y : DkMath.Analysis.DkReal) (n : ℕ) : GapInterval :=
  (x.interval n).add (y.interval n)

/-- Stagewise interval sums remain nested. -/
theorem addApprox_nested (x y : DkMath.Analysis.DkReal) :
    ∀ n,
      (addApprox x y n).lo ≤ (addApprox x y (n + 1)).lo ∧
        (addApprox x y (n + 1)).hi ≤ (addApprox x y n).hi := by
  intro n
  exact ⟨add_le_add (x.lo_le_succ_lo n) (y.lo_le_succ_lo n),
    add_le_add (x.succ_hi_le_hi n) (y.succ_hi_le_hi n)⟩

/-- Widths of stagewise sums tend to zero. -/
theorem tendsto_addApprox_width_zero (x y : DkMath.Analysis.DkReal) :
    Filter.Tendsto (fun n => (addApprox x y n).width)
      Filter.atTop (nhds 0) := by
  simpa only [addApprox, GapInterval.add_width, add_zero] using
    x.tendsto_width_zero.add y.tendsto_width_zero

/-- Addition of `DkReal` approximations by stagewise interval addition. -/
def add (x y : DkMath.Analysis.DkReal) : DkMath.Analysis.DkReal where
  interval := addApprox x y
  nested := addApprox_nested x y
  width_tends_zero := tendsto_addApprox_width_zero x y

/-- Intervals of a `DkReal` sum are the stagewise Minkowski sums. -/
@[simp]
theorem add_interval (x y : DkMath.Analysis.DkReal) (n : ℕ) :
    (add x y).interval n = addApprox x y n := rfl

/-- Addition preserves nonnegativity. -/
theorem nonnegative_add
    {x y : DkMath.Analysis.DkReal} (hx : Nonnegative x) (hy : Nonnegative y) :
    Nonnegative (add x y) := by
  intro n
  exact add_nonneg (hx n) (hy n)

/-- Addition agrees stagewise with rational addition on embedded rationals. -/
@[simp]
theorem add_ofRat_interval (p q : ℚ) (n : ℕ) :
    (add (DkMath.Analysis.DkReal.ofRat p)
        (DkMath.Analysis.DkReal.ofRat q)).interval n
      = GapInterval.singleton (p + q) := by
  apply GapInterval.ext <;> simp [add, addApprox]

/-- Adding the embedded rational zero leaves every interval unchanged. -/
@[simp]
theorem add_zero_interval (x : DkMath.Analysis.DkReal) (n : ℕ) :
    (add x (DkMath.Analysis.DkReal.ofRat 0)).interval n = x.interval n := by
  apply GapInterval.ext <;> simp [add, addApprox]

/-!
## II. Multiplication on the nonnegative quadrant

For nonnegative nested intervals, endpoint multiplication is isotone. The
product width has the exact decomposition

`bₙ dₙ - aₙ cₙ = bₙ (dₙ-cₙ) + cₙ (bₙ-aₙ)`.

Each width tends to zero. The endpoint factors are bounded by the initial
upper endpoints, so both products tend to zero and hence so does their sum.
-/

/-- Stagewise product of two nonnegative `DkReal` approximations. -/
def mulNonnegApprox
    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y)
    (n : ℕ) : GapInterval :=
  (x.interval n).mulNonneg (y.interval n) (hx n) (hy n)

/-- Stagewise nonnegative interval products remain nested. -/
theorem mulNonnegApprox_nested
    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y) :
    ∀ n,
      (mulNonnegApprox x y hx hy n).lo
          ≤ (mulNonnegApprox x y hx hy (n + 1)).lo ∧
        (mulNonnegApprox x y hx hy (n + 1)).hi
          ≤ (mulNonnegApprox x y hx hy n).hi := by
  intro n
  constructor
  · change
      (x.interval n).lo * (y.interval n).lo
        ≤ (x.interval (n + 1)).lo * (y.interval (n + 1)).lo
    calc
      (x.interval n).lo * (y.interval n).lo
          ≤ (x.interval (n + 1)).lo * (y.interval n).lo :=
        mul_le_mul_of_nonneg_right (x.lo_le_succ_lo n) (hy n)
      _ ≤ (x.interval (n + 1)).lo * (y.interval (n + 1)).lo :=
        mul_le_mul_of_nonneg_left (y.lo_le_succ_lo n) (hx (n + 1))
  · change
      (x.interval (n + 1)).hi * (y.interval (n + 1)).hi
        ≤ (x.interval n).hi * (y.interval n).hi
    calc
      (x.interval (n + 1)).hi * (y.interval (n + 1)).hi
          ≤ (x.interval n).hi * (y.interval (n + 1)).hi :=
        mul_le_mul_of_nonneg_right (x.succ_hi_le_hi n)
          ((hy (n + 1)).trans (y.interval (n + 1)).le_lo_hi)
      _ ≤ (x.interval n).hi * (y.interval n).hi :=
        mul_le_mul_of_nonneg_left (y.succ_hi_le_hi n)
          ((hx n).trans (x.interval n).le_lo_hi)

/-- Upper endpoints of a nonnegative `DkReal` form a bounded norm sequence. -/
theorem isBoundedUnder_norm_hi
    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (norm ∘ fun n => (x.interval n).hi) := by
  apply Filter.isBoundedUnder_of_eventually_le
    (a := (((x.interval 0).hi : ℚ) : ℝ))
  filter_upwards
  intro n
  have hhi : 0 ≤ (x.interval n).hi :=
    (hx n).trans (x.interval n).le_lo_hi
  rw [Function.comp_apply, ← Rat.norm_cast_real, Real.norm_eq_abs,
    abs_of_nonneg (Rat.cast_nonneg.mpr hhi)]
  exact_mod_cast x.hi_antitone (Nat.zero_le n)

/-- Lower endpoints of a nonnegative `DkReal` form a bounded norm sequence. -/
theorem isBoundedUnder_norm_lo
    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (norm ∘ fun n => (x.interval n).lo) := by
  apply Filter.isBoundedUnder_of_eventually_le
    (a := (((x.interval 0).hi : ℚ) : ℝ))
  filter_upwards
  intro n
  rw [Function.comp_apply, ← Rat.norm_cast_real, Real.norm_eq_abs,
    abs_of_nonneg (Rat.cast_nonneg.mpr (hx n))]
  exact_mod_cast
    (x.interval n).le_lo_hi.trans (x.hi_antitone (Nat.zero_le n))

/-- Widths of stagewise nonnegative products tend to zero. -/
theorem tendsto_mulNonnegApprox_width_zero
    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y) :
    Filter.Tendsto (fun n => (mulNonnegApprox x y hx hy n).width)
      Filter.atTop (nhds 0) := by
  have hleft :
      Filter.Tendsto
        (fun n => (x.interval n).hi * (y.interval n).width)
        Filter.atTop (nhds 0) :=
    by
      simpa only [mul_comm] using
        y.tendsto_width_zero.zero_mul_isBoundedUnder_le
          (isBoundedUnder_norm_hi x hx)
  have hright :
      Filter.Tendsto
        (fun n => (y.interval n).lo * (x.interval n).width)
        Filter.atTop (nhds 0) :=
    by
      simpa only [mul_comm] using
        x.tendsto_width_zero.zero_mul_isBoundedUnder_le
          (isBoundedUnder_norm_lo y hy)
  simpa only [mulNonnegApprox, GapInterval.mulNonneg_width_eq, add_zero] using
    hleft.add hright

/-- Multiplication of nonnegative `DkReal` approximations. -/
def mulNonneg
    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y) :
    DkMath.Analysis.DkReal where
  interval := mulNonnegApprox x y hx hy
  nested := mulNonnegApprox_nested x y hx hy
  width_tends_zero := tendsto_mulNonnegApprox_width_zero x y hx hy

/-- Intervals of a nonnegative product are the stagewise endpoint products. -/
@[simp]
theorem mulNonneg_interval
    (x y : DkMath.Analysis.DkReal) (hx : Nonnegative x) (hy : Nonnegative y)
    (n : ℕ) :
    (mulNonneg x y hx hy).interval n = mulNonnegApprox x y hx hy n := rfl

/-- Multiplication preserves nonnegativity. -/
theorem nonnegative_mulNonneg
    {x y : DkMath.Analysis.DkReal} (hx : Nonnegative x) (hy : Nonnegative y) :
    Nonnegative (mulNonneg x y hx hy) := by
  intro n
  exact mul_nonneg (hx n) (hy n)

/-- Nonnegative multiplication agrees stagewise with rational multiplication. -/
@[simp]
theorem mulNonneg_ofRat_interval
    {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) (n : ℕ) :
    (mulNonneg
        (DkMath.Analysis.DkReal.ofRat p)
        (DkMath.Analysis.DkReal.ofRat q)
        (nonnegative_ofRat hp) (nonnegative_ofRat hq)).interval n
      = GapInterval.singleton (p * q) := by
  apply GapInterval.ext <;> simp [mulNonneg, mulNonnegApprox]

/-- Multiplication by the embedded zero produces the zero singleton interval. -/
@[simp]
theorem mulNonneg_zero_interval
    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (mulNonneg x (DkMath.Analysis.DkReal.ofRat 0) hx
        (nonnegative_ofRat le_rfl)).interval n
      = GapInterval.singleton 0 := by
  apply GapInterval.ext <;> simp [mulNonneg, mulNonnegApprox]

/-- Multiplication by the embedded one leaves every interval unchanged. -/
@[simp]
theorem mulNonneg_one_interval
    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (mulNonneg x (DkMath.Analysis.DkReal.ofRat 1) hx
        (nonnegative_ofRat zero_le_one)).interval n
      = x.interval n := by
  apply GapInterval.ext <;> simp [mulNonneg, mulNonnegApprox]

end DkMath.Analysis.DkReal
