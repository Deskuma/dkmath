/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaKUSState
import DkMath.RH.CFBRC.EtaMirrorUnitSplit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaKUSMirrorUnitBridge"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Algebra.MetallicRatioCore
open DkMath.KUS
open DkMath.RH.Weave.Analytic
open DkMath.RH.Weave.Finite

/-!
# Eta mirror unit split carried by KUS

The visible KUS coefficient may be replaced by zero, while the structural unit
still retains the complex observation point.  This module reads the original
and critical-mirror eta amplitudes from that retained point and sends them into
the generic `UnitPair` square-core framework.

The resulting mirror pair, Big, and Gap therefore depend on KUS support only;
coefficient zeroization preserves them definitionally.
-/

/-- Raw original/mirror eta amplitudes reconstructed from a retained KUS point. -/
noncomputable def etaKUSMirrorAmplitudePair
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) (m : ℕ) : UnitPair ℝ :=
  etaMirrorAmplitudePair x.unit.point m

/-- Unit-product original/mirror eta split reconstructed from a retained KUS point. -/
noncomputable def etaKUSMirrorUnitPair
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) (m : ℕ) : UnitPair ℝ :=
  etaMirrorUnitPair x.unit.point m

/-- KUS-carried normalized mirror Big. -/
noncomputable def etaKUSMirrorUnitBig
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) (m : ℕ) : ℝ :=
  (etaKUSMirrorUnitPair x m).big

/-- KUS-carried normalized mirror Gap. -/
noncomputable def etaKUSMirrorUnitGap
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) (m : ℕ) : ℝ :=
  (etaKUSMirrorUnitPair x m).gap

@[simp] theorem etaKUSMirrorAmplitudePair_eq
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) (m : ℕ) :
    etaKUSMirrorAmplitudePair x m =
      etaMirrorAmplitudePair x.unit.point m := rfl

@[simp] theorem etaKUSMirrorUnitPair_eq
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) (m : ℕ) :
    etaKUSMirrorUnitPair x m = etaMirrorUnitPair x.unit.point m := rfl

/-- The KUS-carried reciprocal mirror pair has product one. -/
theorem etaKUSMirrorUnitPair_product_eq_one
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) (m : ℕ) :
    (etaKUSMirrorUnitPair x m).product = 1 := by
  exact etaMirrorUnitPair_product_eq_one x.unit.point m

/-- The generic normalized square-core identity survives the KUS lift. -/
theorem etaKUSMirrorUnitBig_eq_gap_add_four
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) (m : ℕ) :
    etaKUSMirrorUnitBig x m = etaKUSMirrorUnitGap x m + 4 := by
  simpa [etaKUSMirrorUnitBig, etaKUSMirrorUnitGap,
    etaKUSMirrorUnitPair] using
      etaMirrorUnitBig_eq_gap_add_four x.unit.point m

/-- KUS-carried normalized Gap vanishes exactly at unit amplitude ratio. -/
theorem etaKUSMirrorUnitGap_eq_zero_iff_ratio_eq_one
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) (m : ℕ) :
    etaKUSMirrorUnitGap x m = 0 ↔
      etaMirrorAmplitudeRatio x.unit.point m = 1 := by
  exact etaMirrorUnitGap_eq_zero_iff_ratio_eq_one x.unit.point m

/-- At eta index one, zero unit Gap is exactly zero centered real coordinate. -/
theorem etaMirrorUnitGap_one_eq_zero_iff_centeredSigma_eq_zero
    (s : ℂ) :
    etaMirrorUnitGap s 1 = 0 ↔ centeredSigma s.re = 0 := by
  rw [etaMirrorUnitGap_eq_zero_iff_ratio_eq_one]
  constructor
  · intro hratio
    have hdecoder : etaMirrorAmplitudeDecoder s = 0 := by
      rw [etaMirrorAmplitudeDecoder, hratio]
      norm_num
    rwa [etaMirrorAmplitudeDecoder_eq_centeredSigma] at hdecoder
  · intro hcenter
    rw [etaMirrorAmplitudeRatio_one_eq_two_rpow, hcenter]
    norm_num

/-- At eta index one, zero unit Gap is exactly membership on the critical line. -/
theorem etaMirrorUnitGap_one_eq_zero_iff_re_eq_half
    (s : ℂ) :
    etaMirrorUnitGap s 1 = 0 ↔ s.re = (1 : ℝ) / 2 := by
  rw [etaMirrorUnitGap_one_eq_zero_iff_centeredSigma_eq_zero]
  exact centeredSigma_eq_zero_iff s.re

/-- KUS form of the centered-coordinate zero selector. -/
theorem etaKUSMirrorUnitGap_one_eq_zero_iff_centeredSigma_eq_zero
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) :
    etaKUSMirrorUnitGap x 1 = 0 ↔
      centeredSigma x.unit.point.re = 0 := by
  exact etaMirrorUnitGap_one_eq_zero_iff_centeredSigma_eq_zero x.unit.point

/-- KUS form of the critical-line selector. -/
theorem etaKUSMirrorUnitGap_one_eq_zero_iff_re_eq_half
    (x : GKUS ℂ EtaKUSUnit EtaKUSBlueprint) :
    etaKUSMirrorUnitGap x 1 = 0 ↔
      x.unit.point.re = (1 : ℝ) / 2 := by
  exact etaMirrorUnitGap_one_eq_zero_iff_re_eq_half x.unit.point

/--
Replacing an arbitrary visible coefficient by zero preserves the mirror unit
pair because both states retain exactly the same KUS support.
-/
theorem etaKUSMirrorUnitPair_mkGWith_eq_gZeroState
    (c : ℂ) (S : US EtaKUSUnit EtaKUSBlueprint) (m : ℕ) :
    etaKUSMirrorUnitPair (mkGWith c S) m =
      etaKUSMirrorUnitPair (gZeroState (C := ℂ) S) m := by
  rfl

/-- Coefficient zeroization preserves mirror Big for every eta KUS support. -/
theorem etaKUSMirrorUnitBig_mkGWith_eq_gZeroState
    (c : ℂ) (S : US EtaKUSUnit EtaKUSBlueprint) (m : ℕ) :
    etaKUSMirrorUnitBig (mkGWith c S) m =
      etaKUSMirrorUnitBig (gZeroState (C := ℂ) S) m := by
  rfl

/-- Coefficient zeroization preserves mirror Gap for every eta KUS support. -/
theorem etaKUSMirrorUnitGap_mkGWith_eq_gZeroState
    (c : ℂ) (S : US EtaKUSUnit EtaKUSBlueprint) (m : ℕ) :
    etaKUSMirrorUnitGap (mkGWith c S) m =
      etaKUSMirrorUnitGap (gZeroState (C := ℂ) S) m := by
  rfl

@[simp] theorem etaKUSMirrorUnitPair_etaKUSState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0)
    (m : ℕ) :
    etaKUSMirrorUnitPair (etaKUSState N s ω hTotal) m =
      etaMirrorUnitPair s m := by
  rfl

@[simp] theorem etaKUSMirrorUnitPair_etaKUSZeroState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0)
    (m : ℕ) :
    etaKUSMirrorUnitPair (etaKUSZeroState N s ω hTotal) m =
      etaMirrorUnitPair s m := by
  rfl

/-- The concrete eta state and its structural zero carry the same mirror pair. -/
theorem etaKUSMirrorUnitPair_state_eq_zeroState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0)
    (m : ℕ) :
    etaKUSMirrorUnitPair (etaKUSState N s ω hTotal) m =
      etaKUSMirrorUnitPair (etaKUSZeroState N s ω hTotal) m := by
  rfl

/-- The concrete eta state and its structural zero carry the same mirror Gap. -/
theorem etaKUSMirrorUnitGap_state_eq_zeroState
    (N : ℕ) (s ω : ℂ)
    (hTotal :
      projectedMassTotal (Finset.range N) (etaSignedVector s) ω ≠ 0)
    (m : ℕ) :
    etaKUSMirrorUnitGap (etaKUSState N s ω hTotal) m =
      etaKUSMirrorUnitGap (etaKUSZeroState N s ω hTotal) m := by
  rfl

@[simp] theorem etaKUSMirrorUnitGap_etaUnitKUSState
    (N : ℕ) (s : ℂ) (m : ℕ) :
    etaKUSMirrorUnitGap (etaUnitKUSState N s) m =
      etaMirrorUnitGap s m := by
  rfl

@[simp] theorem etaKUSMirrorUnitGap_etaUnitKUSZeroState
    (N : ℕ) (s : ℂ) (m : ℕ) :
    etaKUSMirrorUnitGap (etaUnitKUSZeroState N s) m =
      etaMirrorUnitGap s m := by
  rfl

/-- Unit-rotation coefficient zeroization preserves the mirror Gap exactly. -/
theorem etaKUSMirrorUnitGap_etaUnit_state_eq_zeroState
    (N : ℕ) (s : ℂ) (m : ℕ) :
    etaKUSMirrorUnitGap (etaUnitKUSState N s) m =
      etaKUSMirrorUnitGap (etaUnitKUSZeroState N s) m := by
  rfl

end DkMath.RH.CFBRCProjection
