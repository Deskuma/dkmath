/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerUnitEquivariance
import DkMath.Lib.NumberTheory.CyclotomicClassVanishing

#print "file: DkMath.FLT.FreyCyclotomicClassVanishing"

/-!
# 実際の類群冪商の消滅から同じ Frey 単元類への条件付き還元

元の hval と商側の算術的消滅を明示する。有限群の消滅移送により同じ類群像の
零化を内部で導き、以前の同じ単元還元へ接続する。一般 hno は未完成である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight
open KummerSelmer KummerSelmerExact DkMath.Lib.RepresentationTheory

set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicClassVanishing : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldClassVanishing : NumberField (rootField ζ) := rootField_numberField ζ

variable (v : TorsionPreimageQuotient.Quotient p K)
    (P : (letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
      Presentation p (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)))

include hline hcofixed hstable hm hcard hbase

/-- 元の同じ類群像を、実際の冪商側の消滅から零化する。商側の算術的消滅は明示入力。 -/
theorem residual_kummer_classImage_eq_one_of_quotient_vanishing
    (hsurj : Function.Surjective
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v))
    (hval : constantVector
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ P ∈
        valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p)
    (hvanish : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0) :
    CyclotomicKummerClassMap.classImage
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ P hval = 1 :=
  CyclotomicClassVanishing.classImage_eq_one_of_quotient_weight_square_vanishing hζ _ P hval hsurj
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    (S.residual_cyclic_extension_character_conjugate L hline hcofixed K hstable hm hcard hbase v) hvanish

/-- 元の同じ定数・表示・単元類を保つ。hzero は内部導出し、hval と商の消滅を明示する。 -/
theorem residual_kummer_unit_weight_square_of_quotient_vanishing
    (hsurj : Function.Surjective
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v))
    (hval : constantVector
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ P ∈
        valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p)
    (hvanish : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    letI := extensionAlgebra ψ hζ
    ∃ (u : (NumberField.RingOfIntegers (rootField ζ))ˣ) (c : (rootField ζ)ˣ),
      P.constant = algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ) u * (c : rootField ζ) ^ p ∧
      constantVector ψ hζ P = Additive.ofMul
        ((Units.map (algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ)).toMonoidHom u :
          (rootField ζ)ˣ) : KummerClass (rootField ζ) p) ∧
      (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) ≠ 1 ∧
      ∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        KummerSelmerUnitEquivariance.unitClassLinearMap p (CyclotomicKummerEquivariance.integerAut γ)
            (Additive.ofMul (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p)) =
          (baseCharacter hζ γ : ZMod p) ^ 2 •
            Additive.ofMul (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) := by
  have hz := S.residual_kummer_classImage_eq_one_of_quotient_vanishing
    L hline hcofixed K hstable hm hcard hbase hζ v P hsurj hval hvanish
  obtain ⟨u, c, he, hw, _, hne, hweight⟩ := S.residual_kummer_unit_weight_square
    L hline hcofixed K hstable hm hcard hbase hζ v P hsurj hval hz
  exact ⟨u, c, he, hw, hne, hweight⟩

end
end DkMath.FLT.Frey.Source
