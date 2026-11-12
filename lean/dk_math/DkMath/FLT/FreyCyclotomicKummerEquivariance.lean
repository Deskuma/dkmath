/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerClassMap
import DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance

/-!
# 同じ Frey Selmer 類の実際の類群像の二乗則

指標の開核と共役則は既存の同じ巡回塔から内部供給する。
非分裂時に得る指標の全射性 `hsurj` と元の同じベクトルの所属 `hval` を明示する。
所属、類群成分の消滅、共鳴住所の吸収、塔の反復は未完であり、一般 hno を閉じない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight
open KummerSelmer KummerSelmerExact DkMath.Lib.RepresentationTheory

set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicKummerEquivariance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldEquivariance : NumberField (rootField ζ) := rootField_numberField ζ

variable (v : TorsionPreimageQuotient.Quotient p K)
    (P : (letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
      Presentation p (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)))

include hline hcofixed hstable hm hcard hbase

/-- 元の同じ Frey 表示の類群像を、実際の Galois 作用の `ω²` 成分へ移す。
同変性の provider や類群像の零化を入力に追加しない。像は零の場合も含む。 -/
theorem residual_kummer_classImage_weight_square
    (hsurj : Function.Surjective
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v))
    (hval : constantVector
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ P ∈
        valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p)
    (γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ)) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    (CyclotomicKummerEquivariance.integerAut γ).classTorsionLinearMap p
        (Additive.ofMul (CyclotomicKummerClassMap.classImage ψ hζ P hval)) =
      (baseCharacter hζ γ : ZMod p) ^ 2 •
        Additive.ofMul (CyclotomicKummerClassMap.classImage ψ hζ P hval) :=
  CyclotomicKummerEquivariance.classImage_weight_square _ hζ P hval hsurj
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    (S.residual_cyclic_extension_character_conjugate L hline hcofixed K hstable hm hcard hbase v) γ

end
end DkMath.FLT.Frey.Source
