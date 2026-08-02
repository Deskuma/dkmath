/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaProjectedEnergyBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaUnitRotationBridge"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/--
The zeroth signed eta vector is the fixed positive unit vector.  This term is
present in every support `range (N + 1)`.
-/
@[simp] theorem etaSignedVector_zero (s : ℂ) :
    etaSignedVector s 0 = 1 := by
  simp [etaSignedVector, etaUnsignedVector]

/--
Under the unit observation rotation, every nonempty eta support has strictly
positive projected positive mass.  The zeroth term alone contributes one, and
all other summands are nonnegative.
-/
theorem positiveProjectedMass_eta_unitRotation_pos
    (N : ℕ) (s : ℂ) :
    0 < positiveProjectedMass
      (Finset.range (N + 1)) (etaSignedVector s) 1 := by
  unfold positiveProjectedMass
  apply Finset.sum_pos'
  · intro i hi
    exact le_max_right _ _
  · refine ⟨0, ?_⟩
    simp

/-- The zeroth eta vector gives at least one unit of positive projected mass. -/
theorem one_le_positiveProjectedMass_eta_unitRotation
    (N : ℕ) (s : ℂ) :
    1 ≤ positiveProjectedMass
      (Finset.range (N + 1)) (etaSignedVector s) 1 := by
  unfold positiveProjectedMass
  have hmem : 0 ∈ Finset.range (N + 1) := by
    simp
  calc
    1 = max (((1 : ℂ) * etaSignedVector s 0).re) 0 := by simp
    _ ≤ (Finset.range (N + 1)).sum
          (fun i : ℕ => max (((1 : ℂ) * etaSignedVector s i).re) 0) := by
      exact Finset.single_le_sum
        (s := Finset.range (N + 1))
        (f := fun i : ℕ => max (((1 : ℂ) * etaSignedVector s i).re) 0)
        (fun i hi => le_max_right _ _)
        hmem

/-- Every negative projected-mass summand is nonnegative. -/
theorem negativeProjectedMass_eta_unitRotation_nonneg
    (N : ℕ) (s : ℂ) :
    0 ≤ negativeProjectedMass
      (Finset.range (N + 1)) (etaSignedVector s) 1 := by
  unfold negativeProjectedMass
  exact Finset.sum_nonneg fun i hi => le_max_right _ _

/-- The unit-rotation projected total mass is uniformly bounded below by one. -/
theorem one_le_projectedMassTotal_eta_unitRotation
    (N : ℕ) (s : ℂ) :
    1 ≤ projectedMassTotal
      (Finset.range (N + 1)) (etaSignedVector s) 1 := by
  unfold projectedMassTotal
  exact
    (one_le_positiveProjectedMass_eta_unitRotation N s).trans
      (le_add_of_nonneg_right
        (negativeProjectedMass_eta_unitRotation_nonneg N s))

/--
The unit rotation makes the projected eta total mass strictly positive at every
finite stage `N + 1`; no eventual nonvanishing hypothesis is needed.
-/
theorem projectedMassTotal_eta_unitRotation_pos
    (N : ℕ) (s : ℂ) :
    0 < projectedMassTotal
      (Finset.range (N + 1)) (etaSignedVector s) 1 :=
  zero_lt_one.trans_le (one_le_projectedMassTotal_eta_unitRotation N s)

/-- The projected eta total mass under unit rotation never vanishes. -/
theorem projectedMassTotal_eta_unitRotation_ne_zero
    (N : ℕ) (s : ℂ) :
    projectedMassTotal
      (Finset.range (N + 1)) (etaSignedVector s) 1 ≠ 0 :=
  ne_of_gt (projectedMassTotal_eta_unitRotation_pos N s)

/--
Projected-energy realization with the observation rotation fixed to `1`.

The zeroth eta vector discharges projected-total nonvanishing automatically,
so the remaining mathematical obligations are exactly the three asymptotic
statements: normalized energy vanishes, normalized center identifies the
critical centered coordinate, and normalized transverse displacement vanishes.
-/
structure EtaUnitRotationCFBRCBridge (Zero : ℂ → Prop) where
  d : ℕ
  hd : 0 < d
  phase : ℂ → ℝ
  normalizedEnergy_tendsto_zero : ∀ {s : ℂ}, Zero s →
    Tendsto
      (fun N : ℕ => normalizedEtaProjectedEnergy (N + 1) s 1)
      atTop (nhds 0)
  centerOffset_tendsto_centeredSigma : ∀ {s : ℂ}, Zero s →
    Tendsto
      (fun N : ℕ =>
        normalizedProjectedCenterOffset
          (Finset.range (N + 1)) (etaSignedVector s) 1)
      atTop (nhds (centeredSigma s.re))
  transverseGap_tendsto_zero : ∀ {s : ℂ}, Zero s →
    Tendsto
      (fun N : ℕ => normalizedEtaTransverseGap (N + 1) s 1)
      atTop (nhds 0)

/-- The unit-rotation model supplies the general projected-energy bridge. -/
def EtaUnitRotationCFBRCBridge.toEtaProjectedEnergyCFBRCBridge
    {Zero : ℂ → Prop} (bridge : EtaUnitRotationCFBRCBridge Zero) :
    EtaProjectedEnergyCFBRCBridge Zero where
  d := bridge.d
  hd := bridge.hd
  phase := bridge.phase
  rotation := fun _ _ => 1
  projectedMassTotal_ne_zero := fun {s} _hs N =>
    projectedMassTotal_eta_unitRotation_ne_zero N s
  normalizedEnergy_tendsto_zero := bridge.normalizedEnergy_tendsto_zero
  centerOffset_tendsto_centeredSigma :=
    bridge.centerOffset_tendsto_centeredSigma
  transverseGap_tendsto_zero := bridge.transverseGap_tendsto_zero

/-- The unit-rotation realization supplies the existing zero-to-CFBRC bridge. -/
def EtaUnitRotationCFBRCBridge.toZeroToCFBRCBridge
    {Zero : ℂ → Prop} (bridge : EtaUnitRotationCFBRCBridge Zero) :
    ZeroToCFBRCBridge Zero :=
  bridge.toEtaProjectedEnergyCFBRCBridge.toZeroToCFBRCBridge

/-- Every selected zero in the unit-rotation realization lies on the critical line. -/
theorem re_eq_half_of_etaUnitRotationCFBRCBridge
    {Zero : ℂ → Prop} (bridge : EtaUnitRotationCFBRCBridge Zero)
    {s : ℂ} (hs : Zero s) :
    s.re = (1 : ℝ) / 2 := by
  exact re_eq_half_of_zeroToCFBRCBridge bridge.toZeroToCFBRCBridge hs

/-- Standard-zeta specialization of the unit-rotation eta-energy bridge. -/
abbrev StandardZetaEtaUnitRotationCFBRCBridge :=
  EtaUnitRotationCFBRCBridge NontrivialRiemannZetaZero

/-- A standard-zeta unit-rotation realization proves Mathlib's formal RH. -/
theorem riemannHypothesis_of_standardZetaEtaUnitRotationCFBRCBridge
    (bridge : StandardZetaEtaUnitRotationCFBRCBridge) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_standardZetaToCFBRCBridge
    bridge.toZeroToCFBRCBridge

end DkMath.RH.CFBRCProjection
