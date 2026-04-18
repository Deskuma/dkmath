/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Mass.Core

#print "file: DkMath.CosmicFormula.Mass.Decompose"

namespace DkMath.CosmicFormula.Mass

open CosmicMassAPI
open CosmicResidualMassAPI

section CoreBeamGap

variable {R : Type _} [CommSemiring R]

/-- `CoreBeamGap` version of `Big = Body + Gap`. -/
theorem mass_big_eq_mass_body_add_mass_gap_of_coreBeamGap
    (d : ℕ) (x u : R) :
    (ofCoreBeamGap R).massBig d x u =
      (ofCoreBeamGap R).massBody d x u + (ofCoreBeamGap R).massGap d x u := by
  simpa [ofCoreBeamGap] using
    DkMath.CosmicFormula.CoreBeamGap.big_eq_body_add_gap (d := d) (x := x) (u := u)

/-- `CoreBeamGap` version of `Body = Core + Beam`. -/
theorem mass_body_eq_mass_core_add_mass_beam_of_coreBeamGap
    {d : ℕ} (hd : 0 < d) (x u : R) :
    (ofCoreBeamGap R).massBody d x u =
      (ofCoreBeamGap R).massCore d x u + (ofCoreBeamGap R).massBeam d x u := by
  simpa [ofCoreBeamGap] using
    DkMath.CosmicFormula.CoreBeamGap.body_eq_core_add_beam (d := d) hd x u

/-- `CoreBeamGap` version of `Big = Core + Beam + Gap`. -/
theorem mass_big_eq_mass_core_add_mass_beam_add_mass_gap_of_coreBeamGap
    {d : ℕ} (hd : 0 < d) (x u : R) :
    (ofCoreBeamGap R).massBig d x u =
      (ofCoreBeamGap R).massCore d x u +
        (ofCoreBeamGap R).massBeam d x u +
        (ofCoreBeamGap R).massGap d x u := by
  simpa [ofCoreBeamGap] using
    DkMath.CosmicFormula.CoreBeamGap.big_eq_core_beam_gap (d := d) hd x u

end CoreBeamGap

section ResidualNat

/-- `ResidualNat` version of `Big = Body + Gap`. -/
theorem mass_big_eq_mass_body_add_mass_gap_of_residualNat
    (d x u : ℕ) :
    ofResidualNat.massBig d x u =
      ofResidualNat.massBody d x u + ofResidualNat.massGap d x u := by
  simpa [ofResidualNat] using
    DkMath.CosmicFormula.big_eq_body_add_gap d x u

/--
`ResidualNat` version of `Body = Core + Beam`.

Because `beam` is defined by truncated subtraction on `ℕ`, the caller must
provide the honest side condition `core ≤ body`.
-/
theorem mass_body_eq_mass_core_add_mass_beam_of_residualNat
    (d x u : ℕ)
    (hcore : ofResidualNat.massCore d x u ≤ ofResidualNat.massBody d x u) :
    ofResidualNat.massBody d x u =
      ofResidualNat.massCore d x u + ofResidualNat.massBeam d x u := by
  simpa [ofResidualNat] using
    (DkMath.CosmicFormula.core_add_beam_eq_body d x u hcore).symm

/--
`ResidualNat` version of `Big = Core + Beam + Gap`.

As above, the `ℕ` proof keeps the side condition explicit.
-/
theorem mass_big_eq_mass_core_add_mass_beam_add_mass_gap_of_residualNat
    (d x u : ℕ)
    (hcore : ofResidualNat.massCore d x u ≤ ofResidualNat.massBody d x u) :
    ofResidualNat.massBig d x u =
      ofResidualNat.massCore d x u +
        ofResidualNat.massBeam d x u +
        ofResidualNat.massGap d x u := by
  simpa [ofResidualNat] using
    DkMath.CosmicFormula.big_eq_core_add_beam_add_gap d x u hcore

/-- `ResidualNat` version of `residual = gap`. -/
theorem mass_residual_eq_mass_gap_of_residualNat
    (d x u : ℕ) :
    ofResidualNat.massResidual d x u = ofResidualNat.massGap d x u := by
  simpa [ofResidualNat] using
    DkMath.CosmicFormula.residual_eq_gap d x u

end ResidualNat

section ResidualInt

/-- `ResidualInt` version of `Big = Body + Gap`. -/
theorem mass_big_eq_mass_body_add_mass_gap_of_residualInt
    (d : ℕ) (x u : ℤ) :
    ofResidualInt.massBig d x u =
      ofResidualInt.massBody d x u + ofResidualInt.massGap d x u := by
  exact DkMath.CosmicFormula.bigInt_eq_bodyInt_add_gapInt d x u

/-- `ResidualInt` version of `Body = Core + Beam`. -/
theorem mass_body_eq_mass_core_add_mass_beam_of_residualInt
    (d : ℕ) (x u : ℤ) :
    ofResidualInt.massBody d x u =
      ofResidualInt.massCore d x u + ofResidualInt.massBeam d x u := by
  exact (DkMath.CosmicFormula.coreInt_add_beamInt_eq_bodyInt d x u).symm

/-- `ResidualInt` version of `Big = Core + Beam + Gap`. -/
theorem mass_big_eq_mass_core_add_mass_beam_add_mass_gap_of_residualInt
    (d : ℕ) (x u : ℤ) :
    ofResidualInt.massBig d x u =
      ofResidualInt.massCore d x u +
        ofResidualInt.massBeam d x u +
        ofResidualInt.massGap d x u := by
  exact DkMath.CosmicFormula.bigInt_eq_coreInt_add_beamInt_add_gapInt d x u

/-- `ResidualInt` version of `residual = gap`. -/
theorem mass_residual_eq_mass_gap_of_residualInt
    (d : ℕ) (x u : ℤ) :
    ofResidualInt.massResidual d x u = ofResidualInt.massGap d x u := by
  exact DkMath.CosmicFormula.residualInt_eq_gapInt d x u

end ResidualInt

end DkMath.CosmicFormula.Mass
