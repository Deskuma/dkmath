/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerEquivariance
import DkMath.Lib.NumberTheory.CyclotomicKummerUnitEquivariance

/-!
# 同じ Frey 定数から非零 ω² 単元類への条件付き還元

元の Selmer 所属と類群像の零化を明示し、同じ定数の単元倍冪表示と
その同じ非零単元類の固有性を返す。開核・共役則・単元側の同変性は内部供給する。
局所算術、類群・単元の消滅、共鳴住所と巡回塔の反復は未完である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight
open KummerSelmer KummerSelmerExact DkMath.Lib.RepresentationTheory

set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicKummerUnitEquivariance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldUnitEquivariance : NumberField (rootField ζ) := rootField_numberField ζ

variable (v : TorsionPreimageQuotient.Quotient p K)
    (P : (letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
      Presentation p (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)))

include hline hcofixed hstable hm hcard hbase

/-- 元の同じ表示と非零ベクトルを保ち、同じ非自明な単元類に実際の ω² 条件を戻す。
`hval` と `hzero` は別々の未解決算術入力であり、単元固有性は入力にしない。 -/
theorem residual_kummer_unit_weight_square
    (hsurj : Function.Surjective
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v))
    (hval : constantVector
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ P ∈
        valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p)
    (hzero : CyclotomicKummerClassMap.classImage
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ P hval = 1) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    letI := extensionAlgebra ψ hζ
    ∃ (u : (NumberField.RingOfIntegers (rootField ζ))ˣ) (c : (rootField ζ)ˣ),
      P.constant = algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ) u * (c : rootField ζ) ^ p ∧
      constantVector ψ hζ P = Additive.ofMul
        ((Units.map (algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ)).toMonoidHom u :
          (rootField ζ)ˣ) : KummerClass (rootField ζ) p) ∧
      CyclotomicKummerUnitEquivariance.unitImage ψ hζ P hval hzero = (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) ∧
      (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) ≠ 1 ∧
      ∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        KummerSelmerUnitEquivariance.unitClassLinearMap p (CyclotomicKummerEquivariance.integerAut γ)
            (Additive.ofMul (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p)) =
          (baseCharacter hζ γ : ZMod p) ^ 2 •
            Additive.ofMul (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) :=
  CyclotomicKummerUnitEquivariance.unit_of_classImage_eq_one_weight_square _ hζ P hval hzero hsurj
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    (S.residual_cyclic_extension_character_conjugate L hline hcofixed K hstable hm hcard hbase v)

end
end DkMath.FLT.Frey.Source
