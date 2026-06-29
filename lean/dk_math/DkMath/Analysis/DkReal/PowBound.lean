/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.DkReal.Pow

#print "file: DkMath.Analysis.DkReal.PowBound"

/-!
# Bounds for nonnegative DkReal power approximations

This file proves that the exact `gapGN` factors occurring in a nested
nonnegative rational interval sequence are uniformly bounded.

The proof uses the finite binomial-tail expansion. It does not appeal to real
analysis or a mean-value theorem.
-/

namespace DkMath.Analysis.DkReal

/-!
## I. Positivity and isotonicity of the exact correction kernel

For nonnegative variables, every term in the finite binomial expansion of
`gapGN` is nonnegative. Coordinatewise order of the base and increment is
therefore transported through the kernel.
-/

/-- `gapGN` is nonnegative when both its base and increment are nonnegative. -/
theorem gapGN_nonneg_of_nonneg
    (d : ℕ) {base delta : ℚ} (hbase : 0 ≤ base) (hdelta : 0 ≤ delta) :
    0 ≤ gapGN d base delta := by
  rw [gapGN_eq_GN, DkMath.CosmicFormulaBinom.GN_eq_sum]
  positivity

/--
On the nonnegative quadrant, `gapGN` is monotone in both the base and the
increment.
-/
theorem gapGN_le_of_nonneg_of_le
    (d : ℕ) {base₁ base₂ delta₁ delta₂ : ℚ}
    (hbase₁ : 0 ≤ base₁) (hbase : base₁ ≤ base₂)
    (hdelta₁ : 0 ≤ delta₁) (hdelta : delta₁ ≤ delta₂) :
    gapGN d base₁ delta₁ ≤ gapGN d base₂ delta₂ := by
  have hbase₂ : 0 ≤ base₂ := hbase₁.trans hbase
  have hdelta₂ : 0 ≤ delta₂ := hdelta₁.trans hdelta
  rw [gapGN_eq_GN, gapGN_eq_GN,
    DkMath.CosmicFormulaBinom.GN_eq_sum,
    DkMath.CosmicFormulaBinom.GN_eq_sum]
  apply Finset.sum_le_sum
  intro k hk
  gcongr

/-!
## II. Order bounds supplied by nested rational intervals

If `Iₙ = [aₙ,bₙ]` is nested, then `aₙ ≤ bₙ ≤ b₀`. Under nonnegativity,
the width `wₙ = bₙ - aₙ` also satisfies `0 ≤ wₙ ≤ b₀`. These inequalities
place both arguments of `gapGN d aₙ wₙ` in a fixed nonnegative box.
-/

/-- Every lower endpoint is bounded above by the initial upper endpoint. -/
theorem lo_le_initial_hi
    (x : DkMath.Analysis.DkReal) (n : ℕ) :
    (x.interval n).lo ≤ (x.interval 0).hi := by
  exact (x.interval n).le_lo_hi.trans (x.hi_antitone (Nat.zero_le n))

/-- Every interval width is bounded above by the initial upper endpoint when `x` is nonnegative. -/
theorem width_le_initial_hi
    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (x.interval n).width ≤ (x.interval 0).hi := by
  calc
    (x.interval n).width
        = (x.interval n).hi - (x.interval n).lo := rfl
    _ ≤ (x.interval n).hi := sub_le_self _ (hx n)
    _ ≤ (x.interval 0).hi := x.hi_antitone (Nat.zero_le n)

/--
Uniform pointwise bound for the `gapGN` factors along a nested nonnegative
approximation.
-/
theorem gapGN_le_initial_hi
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    gapGN d (x.interval n).lo (x.interval n).width
      ≤ gapGN d (x.interval 0).hi (x.interval 0).hi := by
  exact gapGN_le_of_nonneg_of_le d
    (hx n) (lo_le_initial_hi x n)
    (x.interval n).width_nonneg (width_le_initial_hi x hx n)

/-!
## III. Uniform boundedness and propagation of vanishing width

The powered width factors exactly as

`wₙ * gapGN d aₙ wₙ`.

The first factor tends to zero by the definition of `DkReal`; the second is
uniformly bounded by its value at `(b₀,b₀)`. Hence powered widths also tend to
zero. This is the closure mechanism for natural powers.
-/

/-- The `gapGN` sequence along a nested nonnegative approximation is uniformly bounded. -/
theorem gapGN_bounded_on_nonnegative_nested
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (norm ∘ fun n =>
        gapGN d (x.interval n).lo (x.interval n).width) := by
  apply Filter.isBoundedUnder_of_eventually_le
    (a := ((gapGN (R := ℚ) d (x.interval 0).hi (x.interval 0).hi : ℚ) : ℝ))
  filter_upwards
  intro n
  have hnonneg :
      0 ≤ gapGN d (x.interval n).lo (x.interval n).width :=
    gapGN_nonneg_of_nonneg d (hx n) (x.interval n).width_nonneg
  rw [Function.comp_apply, ← Rat.norm_cast_real, Real.norm_eq_abs,
    abs_of_nonneg (Rat.cast_nonneg.mpr hnonneg)]
  exact_mod_cast gapGN_le_initial_hi d x hx n

/-- Natural powers of nonnegative `DkReal` approximations form a `DkReal`. -/
def powNonneg
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
    DkMath.Analysis.DkReal :=
  powNonnegOfGapGNBounded d x hx
    (gapGN_bounded_on_nonnegative_nested d x hx)

/-!
## IV. Computable natural-power closure

`powNonneg` transforms rational endpoints stage by stage and packages the
nestedness and vanishing-width proofs. No evaluation into Mathlib's `ℝ` is
used, so this construction remains computable.
-/

/-- The intervals of `powNonneg` are the pointwise powered intervals. -/
@[simp]
theorem powNonneg_interval
    (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (powNonneg d x hx).interval n = powNonnegApprox d x hx n := rfl

/-- Natural power of an embedded nonnegative rational is its powered singleton interval. -/
@[simp]
theorem powNonneg_ofRat_interval
    (d : ℕ) {q : ℚ} (hq : 0 ≤ q) (n : ℕ) :
    (powNonneg d (DkMath.Analysis.DkReal.ofRat q) (nonnegative_ofRat hq)).interval n
      = GapInterval.singleton (q ^ d) := by
  apply GapInterval.ext <;> simp [powNonneg, powNonnegApprox]

/-- Zeroth power produces the singleton interval at `1` at every stage. -/
@[simp]
theorem powNonneg_zero_interval
    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (powNonneg 0 x hx).interval n = GapInterval.singleton 1 := by
  apply GapInterval.ext <;> simp [powNonneg, powNonnegApprox]

/-- First power leaves every approximation interval unchanged. -/
@[simp]
theorem powNonneg_one_interval
    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
    (powNonneg 1 x hx).interval n = x.interval n := by
  apply GapInterval.ext <;> simp [powNonneg, powNonnegApprox]

/-- Natural powers of a nonnegative `DkReal` remain nonnegative. -/
theorem nonnegative_powNonneg
    (d : ℕ) {x : DkMath.Analysis.DkReal} (hx : Nonnegative x) :
    Nonnegative (powNonneg d x hx) := by
  intro n
  exact pow_nonneg (hx n) d

end DkMath.Analysis.DkReal
