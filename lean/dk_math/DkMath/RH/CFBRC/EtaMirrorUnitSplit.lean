/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Algebra.MetallicRatioCore
import DkMath.RH.CFBRC.EtaMirrorAmplitudeDecoder

#print "file: DkMath.RH.CFBRC.EtaMirrorUnitSplit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Algebra.MetallicRatioCore
open DkMath.RH.Weave.Analytic

/-!
# Eta mirror unit split

This module is the thin observation layer from complex eta terms into the
generic square-core framework.

There are two related pairs.

* `etaMirrorAmplitudePair` keeps the two genuine eta magnitudes.
* `etaMirrorUnitPair` keeps only their positive ratio and splits it into a
  reciprocal pair with product one.

The second pair is therefore eligible for the framework identity
`Big = Gap + 4`.  No critical-line conclusion is assumed here.
-/

/--
The genuine mirror/original eta magnitudes, observed as a real scalar pair.
The mirror magnitude is the first coordinate so that `x / u` is exactly the
existing mirror-amplitude ratio.
-/
noncomputable def etaMirrorAmplitudePair (s : ℂ) (m : ℕ) : UnitPair ℝ :=
  UnitPair.observe norm
    (etaSignedVector (criticalMirror s) m)
    (etaSignedVector s m)

@[simp] theorem etaMirrorAmplitudePair_x (s : ℂ) (m : ℕ) :
    (etaMirrorAmplitudePair s m).x =
      ‖etaSignedVector (criticalMirror s) m‖ := rfl

@[simp] theorem etaMirrorAmplitudePair_u (s : ℂ) (m : ℕ) :
    (etaMirrorAmplitudePair s m).u =
      ‖etaSignedVector s m‖ := rfl

/-- Raw square of the sum of the two eta magnitudes. -/
noncomputable def etaMirrorAmplitudeBig (s : ℂ) (m : ℕ) : ℝ :=
  (etaMirrorAmplitudePair s m).big

/-- Raw square Gap between the two eta magnitudes. -/
noncomputable def etaMirrorAmplitudeGap (s : ℂ) (m : ℕ) : ℝ :=
  (etaMirrorAmplitudePair s m).gap

/-- Product of the two genuine eta magnitudes. -/
noncomputable def etaMirrorAmplitudeProduct (s : ℂ) (m : ℕ) : ℝ :=
  (etaMirrorAmplitudePair s m).product

@[simp] theorem etaMirrorAmplitudeBig_eq (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeBig s m =
      (‖etaSignedVector (criticalMirror s) m‖ +
        ‖etaSignedVector s m‖) ^ 2 := by
  rfl

@[simp] theorem etaMirrorAmplitudeGap_eq (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeGap s m =
      (‖etaSignedVector (criticalMirror s) m‖ -
        ‖etaSignedVector s m‖) ^ 2 := by
  rfl

@[simp] theorem etaMirrorAmplitudeProduct_eq (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeProduct s m =
      ‖etaSignedVector (criticalMirror s) m‖ *
        ‖etaSignedVector s m‖ := by
  rfl

/-- The generic square-core decomposition, specialized to genuine eta data. -/
theorem etaMirrorAmplitudeBig_eq_gap_add_four_mul_product
    (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeBig s m =
      etaMirrorAmplitudeGap s m +
        4 * etaMirrorAmplitudeProduct s m := by
  simpa [etaMirrorAmplitudeBig, etaMirrorAmplitudeGap,
    etaMirrorAmplitudeProduct] using
      (etaMirrorAmplitudePair s m).big_eq_gap_add_four_mul_product

/-- The raw eta Gap vanishes exactly when the two eta magnitudes agree. -/
theorem etaMirrorAmplitudeGap_eq_zero_iff
    (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeGap s m = 0 ↔
      ‖etaSignedVector (criticalMirror s) m‖ =
        ‖etaSignedVector s m‖ := by
  simpa [etaMirrorAmplitudeGap, etaMirrorAmplitudePair] using
    (etaMirrorAmplitudePair s m).gap_eq_zero_iff

/-- Every eta term magnitude in this finite model is strictly positive. -/
theorem norm_etaSignedVector_pos (s : ℂ) (m : ℕ) :
    0 < ‖etaSignedVector s m‖ := by
  rw [norm_etaSignedVector_eq_rpow]
  positivity

/-- The existing mirror-amplitude ratio is the quotient of the observed pair. -/
theorem etaMirrorAmplitudeRatio_eq_pair_div
    (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeRatio s m =
      (etaMirrorAmplitudePair s m).x /
        (etaMirrorAmplitudePair s m).u := by
  rfl

/-- Equality of the two raw magnitudes is equivalent to unit ratio. -/
theorem etaMirrorAmplitudeGap_eq_zero_iff_ratio_eq_one
    (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeGap s m = 0 ↔
      etaMirrorAmplitudeRatio s m = 1 := by
  rw [etaMirrorAmplitudeGap_eq_zero_iff]
  constructor
  · intro hmag
    rw [etaMirrorAmplitudeRatio, hmag]
    exact div_self (ne_of_gt (norm_etaSignedVector_pos s m))
  · intro hratio
    have hden : ‖etaSignedVector s m‖ ≠ 0 :=
      ne_of_gt (norm_etaSignedVector_pos s m)
    calc
      ‖etaSignedVector (criticalMirror s) m‖ =
          (‖etaSignedVector (criticalMirror s) m‖ /
            ‖etaSignedVector s m‖) * ‖etaSignedVector s m‖ := by
              field_simp
      _ = 1 * ‖etaSignedVector s m‖ := by
            rw [← etaMirrorAmplitudeRatio, hratio]
      _ = ‖etaSignedVector s m‖ := one_mul _

/-- The mirror-amplitude ratio is positive. -/
theorem etaMirrorAmplitudeRatio_pos (s : ℂ) (m : ℕ) :
    0 < etaMirrorAmplitudeRatio s m := by
  rw [etaMirrorAmplitudeRatio_eq_rpow]
  positivity

/--
Unit-product split of the positive mirror-amplitude ratio.

Its coordinates are `sqrt(r)` and `sqrt(r)⁻¹`, where `r` is the genuine
mirror/original eta-amplitude ratio.
-/
noncomputable def etaMirrorUnitPair (s : ℂ) (m : ℕ) : UnitPair ℝ :=
  ⟨Real.sqrt (etaMirrorAmplitudeRatio s m),
    (Real.sqrt (etaMirrorAmplitudeRatio s m))⁻¹⟩

@[simp] theorem etaMirrorUnitPair_x (s : ℂ) (m : ℕ) :
    (etaMirrorUnitPair s m).x =
      Real.sqrt (etaMirrorAmplitudeRatio s m) := rfl

@[simp] theorem etaMirrorUnitPair_u (s : ℂ) (m : ℕ) :
    (etaMirrorUnitPair s m).u =
      (Real.sqrt (etaMirrorAmplitudeRatio s m))⁻¹ := rfl

/-- The normalized mirror split has product exactly one. -/
theorem etaMirrorUnitPair_product_eq_one (s : ℂ) (m : ℕ) :
    (etaMirrorUnitPair s m).product = 1 := by
  have hsqrt : Real.sqrt (etaMirrorAmplitudeRatio s m) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (etaMirrorAmplitudeRatio_pos s m))
  exact mul_inv_cancel₀ hsqrt

/-- The first unit-split coordinate is nonnegative. -/
theorem etaMirrorUnitPair_x_nonneg (s : ℂ) (m : ℕ) :
    0 ≤ (etaMirrorUnitPair s m).x := by
  exact Real.sqrt_nonneg _

/-- The reciprocal unit-split coordinate is nonnegative. -/
theorem etaMirrorUnitPair_u_nonneg (s : ℂ) (m : ℕ) :
    0 ≤ (etaMirrorUnitPair s m).u := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- Normalized square of the sum of the reciprocal eta coordinates. -/
noncomputable def etaMirrorUnitBig (s : ℂ) (m : ℕ) : ℝ :=
  (etaMirrorUnitPair s m).big

/-- Normalized square Gap of the reciprocal eta coordinates. -/
noncomputable def etaMirrorUnitGap (s : ℂ) (m : ℕ) : ℝ :=
  (etaMirrorUnitPair s m).gap

/-- The normalized eta split satisfies `Big = Gap + 4`. -/
theorem etaMirrorUnitBig_eq_gap_add_four (s : ℂ) (m : ℕ) :
    etaMirrorUnitBig s m = etaMirrorUnitGap s m + 4 := by
  simpa [etaMirrorUnitBig, etaMirrorUnitGap] using
    (etaMirrorUnitPair s m).big_eq_gap_add_four_of_product_eq_one
      (etaMirrorUnitPair_product_eq_one s m)

/-- In the normalized split, `Big = 4` exactly when `Gap = 0`. -/
theorem etaMirrorUnitBig_eq_four_iff_gap_eq_zero
    (s : ℂ) (m : ℕ) :
    etaMirrorUnitBig s m = 4 ↔ etaMirrorUnitGap s m = 0 := by
  simpa [etaMirrorUnitBig, etaMirrorUnitGap] using
    (etaMirrorUnitPair s m).big_eq_four_iff_gap_eq_zero_of_product_eq_one
      (etaMirrorUnitPair_product_eq_one s m)

/-- Zero normalized Gap forces both reciprocal coordinates to be one. -/
theorem etaMirrorUnitPair_eq_one_of_gap_eq_zero
    (s : ℂ) (m : ℕ)
    (hgap : etaMirrorUnitGap s m = 0) :
    (etaMirrorUnitPair s m).x = 1 ∧
      (etaMirrorUnitPair s m).u = 1 := by
  apply (etaMirrorUnitPair s m).eq_one_of_nonneg_of_product_eq_one_of_gap_eq_zero
    (etaMirrorUnitPair_x_nonneg s m)
    (etaMirrorUnitPair_u_nonneg s m)
    (etaMirrorUnitPair_product_eq_one s m)
  exact hgap

/-- Zero normalized Gap is equivalent to unit mirror-amplitude ratio. -/
theorem etaMirrorUnitGap_eq_zero_iff_ratio_eq_one
    (s : ℂ) (m : ℕ) :
    etaMirrorUnitGap s m = 0 ↔ etaMirrorAmplitudeRatio s m = 1 := by
  constructor
  · intro hgap
    have hone := etaMirrorUnitPair_eq_one_of_gap_eq_zero s m hgap
    have hsqrt : Real.sqrt (etaMirrorAmplitudeRatio s m) = 1 := by
      simpa [etaMirrorUnitPair] using hone.1
    have hsquare :=
      Real.sq_sqrt (le_of_lt (etaMirrorAmplitudeRatio_pos s m))
    calc
      etaMirrorAmplitudeRatio s m =
          (Real.sqrt (etaMirrorAmplitudeRatio s m)) ^ 2 := hsquare.symm
      _ = 1 := by rw [hsqrt]; norm_num
  · intro hratio
    unfold etaMirrorUnitGap etaMirrorUnitPair UnitPair.gap
      unitAttachedCoreNeg
    rw [hratio]
    norm_num

/-- Raw and normalized eta Gaps have the same zero locus. -/
theorem etaMirrorUnitGap_eq_zero_iff_amplitudeGap_eq_zero
    (s : ℂ) (m : ℕ) :
    etaMirrorUnitGap s m = 0 ↔ etaMirrorAmplitudeGap s m = 0 := by
  rw [etaMirrorUnitGap_eq_zero_iff_ratio_eq_one,
    etaMirrorAmplitudeGap_eq_zero_iff_ratio_eq_one]

end DkMath.RH.CFBRCProjection
