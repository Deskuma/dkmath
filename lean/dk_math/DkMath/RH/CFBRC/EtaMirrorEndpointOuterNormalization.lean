/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaMirrorEndpointPairEnergy
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaMirrorEndpointOuterNormalization"

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-!
# Paired outer normalization for eta mirror endpoints

The absolute endpoint Big and endpoint Gap both collapse when the original and
critical-mirror endpoints tend to zero.  This file therefore keeps them as one
comparison pair and measures each component against their shared outer Big.

The old endpoint Big is re-read as the inner Core, while the old endpoint Gap
is re-read as the inner Gap core.  Neither component is normalized against a
separately chosen denominator.
-/

/-- The inner comparison pair: endpoint Big as Core, endpoint Gap as Gap core. -/
noncomputable def etaMirrorEndpointCoreGapPair
    (N : ℕ) (s : ℂ) : ℝ × ℝ :=
  (etaMirrorEndpointBig N s, etaMirrorEndpointGap N s)

/-- Inner Core coordinate of the paired endpoint comparison. -/
noncomputable def etaMirrorEndpointCore (N : ℕ) (s : ℂ) : ℝ :=
  (etaMirrorEndpointCoreGapPair N s).1

/-- Inner Gap-core coordinate of the paired endpoint comparison. -/
noncomputable def etaMirrorEndpointGapCore (N : ℕ) (s : ℂ) : ℝ :=
  (etaMirrorEndpointCoreGapPair N s).2

/-- Shared outer Big used as the denominator for both inner coordinates. -/
noncomputable def etaMirrorEndpointOuterBig (N : ℕ) (s : ℂ) : ℝ :=
  etaMirrorEndpointCore N s + etaMirrorEndpointGapCore N s

/-- The paired normalized coordinates, both measured by the same outer Big. -/
noncomputable def etaMirrorEndpointSharePair
    (N : ℕ) (s : ℂ) : ℝ × ℝ :=
  (etaMirrorEndpointCore N s / etaMirrorEndpointOuterBig N s,
    etaMirrorEndpointGapCore N s / etaMirrorEndpointOuterBig N s)

/-- Core occupancy inside the shared outer Big. -/
noncomputable def etaMirrorEndpointCoreShare (N : ℕ) (s : ℂ) : ℝ :=
  (etaMirrorEndpointSharePair N s).1

/-- Gap-core occupancy inside the shared outer Big. -/
noncomputable def etaMirrorEndpointGapShare (N : ℕ) (s : ℂ) : ℝ :=
  (etaMirrorEndpointSharePair N s).2

@[simp] theorem etaMirrorEndpointCore_eq
    (N : ℕ) (s : ℂ) :
    etaMirrorEndpointCore N s = etaMirrorEndpointBig N s := by
  rfl

@[simp] theorem etaMirrorEndpointGapCore_eq
    (N : ℕ) (s : ℂ) :
    etaMirrorEndpointGapCore N s = etaMirrorEndpointGap N s := by
  rfl

@[simp] theorem etaMirrorEndpointCoreShare_eq
    (N : ℕ) (s : ℂ) :
    etaMirrorEndpointCoreShare N s =
      etaMirrorEndpointCore N s / etaMirrorEndpointOuterBig N s := by
  rfl

@[simp] theorem etaMirrorEndpointGapShare_eq
    (N : ℕ) (s : ℂ) :
    etaMirrorEndpointGapShare N s =
      etaMirrorEndpointGapCore N s / etaMirrorEndpointOuterBig N s := by
  rfl

/-- The outer Big is exactly the sum of the paired inner coordinates. -/
theorem etaMirrorEndpointOuterBig_eq_core_add_gapCore
    (N : ℕ) (s : ℂ) :
    etaMirrorEndpointOuterBig N s =
      etaMirrorEndpointCore N s + etaMirrorEndpointGapCore N s := by
  rfl

/-- The outer Big is twice the total original/mirror endpoint energy. -/
theorem etaMirrorEndpointOuterBig_eq_two_mul_totalEnergy
    (N : ℕ) (s : ℂ) :
    etaMirrorEndpointOuterBig N s =
      2 * etaMirrorEndpointTotalEnergy N s := by
  exact etaMirrorEndpointBig_add_gap_eq_two_mul_totalEnergy N s

/-- The inner Core is nonnegative. -/
theorem etaMirrorEndpointCore_nonneg (N : ℕ) (s : ℂ) :
    0 ≤ etaMirrorEndpointCore N s := by
  change 0 ≤ Complex.normSq
    (etaPartialEndpoint N s + etaPartialEndpoint N (criticalMirror s))
  exact Complex.normSq_nonneg _

/-- The inner Gap core is nonnegative. -/
theorem etaMirrorEndpointGapCore_nonneg (N : ℕ) (s : ℂ) :
    0 ≤ etaMirrorEndpointGapCore N s := by
  change 0 ≤ Complex.normSq
    (etaPartialEndpoint N s - etaPartialEndpoint N (criticalMirror s))
  exact Complex.normSq_nonneg _

/-- The shared outer Big is nonnegative. -/
theorem etaMirrorEndpointOuterBig_nonneg (N : ℕ) (s : ℂ) :
    0 ≤ etaMirrorEndpointOuterBig N s := by
  rw [etaMirrorEndpointOuterBig_eq_core_add_gapCore]
  exact add_nonneg
    (etaMirrorEndpointCore_nonneg N s)
    (etaMirrorEndpointGapCore_nonneg N s)

/-- With a nonzero common denominator, the two shares exhaust the outer Big. -/
theorem etaMirrorEndpointCoreShare_add_gapShare
    (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s ≠ 0) :
    etaMirrorEndpointCoreShare N s + etaMirrorEndpointGapShare N s = 1 := by
  rw [etaMirrorEndpointCoreShare_eq, etaMirrorEndpointGapShare_eq,
    ← add_div]
  rw [← etaMirrorEndpointOuterBig_eq_core_add_gapCore]
  exact div_self hOuter

/-- Both normalized coordinates are nonnegative when the outer Big is positive. -/
theorem etaMirrorEndpointShares_nonneg
    (N : ℕ) (s : ℂ)
    (hOuter : 0 < etaMirrorEndpointOuterBig N s) :
    0 ≤ etaMirrorEndpointCoreShare N s ∧
      0 ≤ etaMirrorEndpointGapShare N s := by
  constructor
  · rw [etaMirrorEndpointCoreShare_eq]
    exact div_nonneg (etaMirrorEndpointCore_nonneg N s) (le_of_lt hOuter)
  · rw [etaMirrorEndpointGapShare_eq]
    exact div_nonneg (etaMirrorEndpointGapCore_nonneg N s) (le_of_lt hOuter)

/-- On the critical line, the finite endpoint Gap core vanishes identically. -/
theorem etaMirrorEndpointGapCore_eq_zero_of_re_eq_half
    (N : ℕ) {s : ℂ} (hre : s.re = (1 : ℝ) / 2) :
    etaMirrorEndpointGapCore N s = 0 := by
  have hmirror : criticalMirror s = s :=
    (criticalMirror_eq_self_iff_re_eq_half s).2 hre
  simp [etaMirrorEndpointGapCore, etaMirrorEndpointCoreGapPair,
    etaMirrorEndpointGap, hmirror]

/-- On the critical line, the outer Big reduces to the inner Core. -/
theorem etaMirrorEndpointOuterBig_eq_core_of_re_eq_half
    (N : ℕ) {s : ℂ} (hre : s.re = (1 : ℝ) / 2) :
    etaMirrorEndpointOuterBig N s = etaMirrorEndpointCore N s := by
  rw [etaMirrorEndpointOuterBig_eq_core_add_gapCore,
    etaMirrorEndpointGapCore_eq_zero_of_re_eq_half N hre, add_zero]

/-- On the critical line, the normalized Gap share is zero at every stage. -/
theorem etaMirrorEndpointGapShare_eq_zero_of_re_eq_half
    (N : ℕ) {s : ℂ} (hre : s.re = (1 : ℝ) / 2) :
    etaMirrorEndpointGapShare N s = 0 := by
  rw [etaMirrorEndpointGapShare_eq,
    etaMirrorEndpointGapCore_eq_zero_of_re_eq_half N hre]
  exact zero_div _

/-- On the critical line and away from zero total energy, the Core share is one. -/
theorem etaMirrorEndpointCoreShare_eq_one_of_re_eq_half
    (N : ℕ) {s : ℂ} (hre : s.re = (1 : ℝ) / 2)
    (hOuter : etaMirrorEndpointOuterBig N s ≠ 0) :
    etaMirrorEndpointCoreShare N s = 1 := by
  have hsum := etaMirrorEndpointCoreShare_add_gapShare N s hOuter
  rw [etaMirrorEndpointGapShare_eq_zero_of_re_eq_half N hre, add_zero] at hsum
  exact hsum

end DkMath.RH.CFBRCProjection
