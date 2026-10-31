/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelNodalReduction

#print "file: DkMathTest.FLT.FreyFiniteKernelNodalReduction"

/-!
# Regression use for the residue singular-centre bridge

The example keeps the critical centre and tangent direction explicit.  It
checks that the concrete valuation model exposes a `SingularCentre` over the
residue field, while making no characteristic-zero rationality claim.
-/

namespace DkMathTest.FLT.FreyFiniteKernelNodalReduction

open DkMath.FLT.Frey
open DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open DkMath.Lib.NumberTheory.EllipticCriticalCentre
open DkMath.Lib.NumberTheory.EllipticTangentDirections
open DkMath.Lib.NumberTheory.EllipticNodalTorsion.NodalTorsion
open DkMath.Lib.NumberTheory.EllipticNodalSmoothCard
open DkMath.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion
open DkMath.Lib.NumberTheory.EllipticGoodReductionSeparation
open DkMath.Lib.NumberTheory.EllipticSmoothReduction
open DkMath.Lib.NumberTheory.ValuationInertia
open DkMath.Lib.Algebra
open WeierstrassCurve IsLocalRing

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
noncomputable local instance {A : ValuationSubring (AlgebraicClosure ℚ)} :
    DecidableEq (ResidueField A) := Classical.decEq _

example (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C) :
    DkMath.Lib.NumberTheory.EllipticNodalSmoothCard.SingularCentre
      ((S.valuationModel A).map (IsLocalRing.residue A)) :=
  S.valuationModel_residue_singularCentre_of_geometry A C D

#print axioms DkMath.FLT.Frey.Source.valuationModel_residue_singularCentre_of_geometry

example (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C) :
    Frame ((S.residualValuationKernelModel L hl hq hqp A hA).map (IsLocalRing.residue A))
        (IsLocalRing.residue A ⟨C.x, C.x_mem⟩)
        (IsLocalRing.residue A ⟨C.y, C.y_mem⟩)
        (IsLocalRing.residue A ⟨D.α, D.α_mem⟩) ∧
      IsLocalRing.residue A ⟨D.α, D.α_mem⟩ ≠
        -((S.residualValuationKernelModel L hl hq hqp A hA).map
          (IsLocalRing.residue A)).a₁ - IsLocalRing.residue A ⟨D.α, D.α_mem⟩ :=
  S.residualValuationKernelModel_residue_frame_of_disjoint L hl hq hqp A hA hd C D

#print axioms DkMath.FLT.Frey.Source.residualValuationKernelModel_residue_frame_of_disjoint

example (hp2 : p ≠ 2) (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C) :
    SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (IsLocalRing.residue A)) :=
  S.residualValuationKernelModel_residue_singularCentre_of_smooth
    hp2 L hl hq hqp A hA hle C D

#print axioms DkMath.FLT.Frey.Source.residualValuationKernelModel_residue_singularCentre_of_smooth

example {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)] (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (C : SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (IsLocalRing.residue A))) :
    Nat.card ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (IsLocalRing.residue A)).toAffine.Point ≤ Fintype.card (ResidueField A) + 1 :=
  S.residualValuationKernelModel_residue_pointCard_le hq hqp A hA L hl C

#print axioms DkMath.FLT.Frey.Source.residualValuationKernelModel_residue_pointCard_le

example (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (C : SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (IsLocalRing.residue A))) :
    Nat.card ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (IsLocalRing.residue A)).toAffine.Point < p :=
  S.residualValuationKernelModel_residue_pointCard_lt_of_prime_lt
    hp5 hq hqp A hA hresidueCard hqp' L hl C

example (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (C : SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (IsLocalRing.residue A))) :
    ¬ p ∣ Nat.card ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (IsLocalRing.residue A)).toAffine.Point :=
  S.residualValuationKernelModel_residue_pointCard_not_dvd_of_prime_lt
    hp5 hq hqp A hA hresidueCard hqp' L hl C

#print axioms DkMath.FLT.Frey.Source.residualValuationKernelModel_residue_pointCard_lt_of_prime_lt
#print axioms DkMath.FLT.Frey.Source.residualValuationKernelModel_residue_pointCard_not_dvd_of_prime_lt

example (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (C : SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (IsLocalRing.residue A)))
    {R : ((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA) R ∧
      p ∣ Nat.card (((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point ⧸
        zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA)) :=
  by
    let : DecidableEq (ResidueField A) := Classical.decEq _
    exact S.residualValuationKernelModel_component_prime_dvd_of_residue_centre
      hp5 hq hqp A hA hresidueCard hqp' L hl C hR

#print axioms DkMath.FLT.Frey.Source.residualValuationKernelModel_component_prime_dvd_of_residue_centre

example (hp5 : 5 ≤ p) (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    {R : ((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA) R ∧
      p ∣ Nat.card (((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point ⧸
        zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA)) := by
  let : DecidableEq (ResidueField A) := Classical.decEq _
  exact S.residualValuationKernelModel_component_prime_dvd_of_smooth_branch
    hp5 hp2 L hl hq hqp A hA hle hresidueCard hqp' C D hR

#print axioms DkMath.FLT.Frey.Source.residualValuationKernelModel_component_prime_dvd_of_smooth_branch

example (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (hd : Disjoint L (S.residualZeroComponent A))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    {R : ((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA) R ∧
      p ∣ Nat.card (((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point ⧸
        zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA)) := by
  let : DecidableEq (ResidueField A) := Classical.decEq _
  exact S.residualValuationKernelModel_component_prime_dvd_of_disjoint_branch
    hp5 L hl hq hqp A hA hresidueCard hqp' hd C D hR

#print axioms DkMath.FLT.Frey.Source.residualValuationKernelModel_component_prime_dvd_of_disjoint_branch

example (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    {R : ((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA) R ∧
      p ∣ Nat.card (((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point ⧸
        zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA)) := by
  let : DecidableEq (ResidueField A) := Classical.decEq _
  exact S.residualValuationKernelModel_component_prime_dvd_of_geometry
    hp5 L hl hq hqp A hA hresidueCard hqp' C D hR

#print axioms DkMath.FLT.Frey.Source.residualValuationKernelModel_component_prime_dvd_of_geometry

example (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (C : SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (IsLocalRing.residue A)))
    {R : ((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    2 • R ∉ zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA) := by
  let : DecidableEq (ResidueField A) := Classical.decEq _
  exact S.residualValuationKernelModel_two_nsmul_not_mem_zeroComponent_of_geometry
    hp5 hq hqp A hA hresidueCard hqp' L hl C hR

#print axioms DkMath.FLT.Frey.Source.residualValuationKernelModel_two_nsmul_not_mem_zeroComponent_of_geometry

example (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C) :
    DkMath.Lib.NumberTheory.EllipticNodalSmoothCard.SingularCentre
      ((S.residualValuationKernelModel L hl hq hqp A hA).map (IsLocalRing.residue A)) :=
  S.residualValuationKernelModel_residue_singularCentre_of_disjoint
    L hl hq hqp A hA hd C D

#print axioms DkMath.FLT.Frey.Source.residualValuationKernelModel_residue_singularCentre_of_disjoint

end
end DkMathTest.FLT.FreyFiniteKernelNodalReduction
