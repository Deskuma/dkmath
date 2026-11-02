/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicClassVanishing
import DkMath.Lib.NumberTheory.CyclotomicKummerSelmer

#print "file: DkMath.FLT.FreyCyclotomicKummerSelmer"

/-!
# 元の Frey Kummer ベクトルの条件付き Selmer 所属

同じ S,L,K,m,v,P を保ち、p 上の分解群固定性と p 外の慣性固定性を合わせる。
有限慣性の持ち上げと付値・分岐指数の比較により、元の同じ hval を内部で供給する。
共鳴住所の hbad は元のまま明示する。局所 p 乗や算術的消滅は主張しない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight
open KummerSelmer KummerSelmerExact DkMath.Lib.RepresentationTheory

set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicKummerSelmer : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldKummerSelmer : NumberField (rootField ζ) := rootField_numberField ζ

variable (v : TorsionPreimageQuotient.Quotient p K)
    (P : (letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
      Presentation p (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)))

include hline hcofixed hstable hm hcard hbase

/-- 共鳴住所の吸収を保ち、元の同じ Kummer ベクトルの全素点の付値条件を内部供給する。 -/
theorem residual_kummer_mem_valuationSpace
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    : constantVector
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ P ∈
        valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p := by
  apply CyclotomicKummerSelmer.constantVector_mem_valuationSpace_of_absolute_inertia
    (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    (S.residual_cyclic_extension_character_conjugate L hline hcofixed K hstable hm hcard hbase v) P
  intro q hq A hA g hg
  by_cases hqp : q = p
  · subst q
    exact S.residual_kummer_radical_decomposition_fixed_at_p L hline hcofixed K hstable hm hcard hbase
      hζ v P hp5 A hA g ((ValuationTameCharacter.TameCharacter.mem_inertiaSubgroupIn_iff.mp hg).1)
  · exact S.residual_kummer_radical_inertia_fixed_away L hline hcofixed K hstable hm hcard hbase
      hζ v P hp5 hbad hq hqp A hA g hg

/-- 同じ条件を Mathlib の実際の空集合支持 Selmer 群の所属として読む。 -/
theorem residual_kummer_mem_selmer
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    : constantClass
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ P ∈
        KummerSelmerClassMap.Selmer (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ) p :=
  (mem_valuationSpace_iff_selmer p _).mp
    (S.residual_kummer_mem_valuationSpace L hline hcofixed K hstable hm hcard hbase hζ v P hp5 hbad)

/-- 同じ単元還元への入口。hval と hzero は内部導出し、hbad と商側の消滅を明示する。 -/
theorem residual_kummer_unit_weight_square_of_resonant_absorption
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (hsurj : Function.Surjective
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v))
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
  have hval := S.residual_kummer_mem_valuationSpace
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5 hbad
  exact S.residual_kummer_unit_weight_square_of_quotient_vanishing
    L hline hcofixed K hstable hm hcard hbase hζ v P hsurj hval hvanish

end
end DkMath.FLT.Frey.Source
