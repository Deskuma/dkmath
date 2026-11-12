/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerWeight
import DkMath.Lib.NumberTheory.CyclotomicKummerArithmetic

#print "file: DkMath.FLT.FreyCyclotomicKummerArithmetic"

/-!
# Frey の同じ非零 Kummer ベクトルの整数化

同じ固定体内で根・定数の両方を整数環の実際の非零元にする。
元のベクトルとの等式、非零性、円分二乗固有性、全素点の付値剰余を保つ。
整数化から Selmer 所属や単数性を結論しない。局所算術と消滅は残る。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight CyclicKummerIntegral
open IsDedekindDomain DkMath.Lib.RepresentationTheory

set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicKummerArithmetic : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)

include hline hcofixed hstable hm hcard hbase

/-- 非分裂から得た同じベクトルを整数化する。
整数環の元・分母・元のベクトルとの一致・固有性を内部で供給する。
付値条件への所属を新しい provider として入力しない。 -/
theorem residual_nonsplit_has_integral_weight_two_kummer_model (hp5 : 5 ≤ p)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hns : ¬ ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D) :
    ∃ v : TorsionPreimageQuotient.Quotient p K,
      Function.Surjective (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) ∧
      (let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
       letI := extensionAlgebra ψ hζ
       letI := rootField_numberField ζ
       ∃ (P : Presentation p (rootField ζ)
           (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)) (D : IntegralModel P),
         D.constant ≠ 0 ∧ D.radical ≠ 0 ∧
         constantVector ψ hζ D.presentation = constantVector ψ hζ P ∧
         constantVector ψ hζ D.presentation ≠ 0 ∧
         (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
           classLinearMap p γ.toRingHom (constantVector ψ hζ D.presentation) =
             (baseCharacter hζ γ : ZMod p) ^ 2 • constantVector ψ hζ D.presentation) ∧
         (∀ v : HeightOneSpectrum (NumberField.RingOfIntegers (rootField ζ)),
           KummerSelmer.valuationLinear p v (constantVector ψ hζ D.presentation) =
             KummerSelmer.valuationLinear p v (constantVector ψ hζ P))) := by
  obtain ⟨v, hv, P, _, hn, hw⟩ := S.residual_nonsplit_has_weight_two_kummer_class
    L hline hcofixed K hstable hm hcard hbase hp5 hζ hns
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let := extensionAlgebra ψ hζ
  let := rootField_numberField ζ
  obtain ⟨D, he⟩ := CyclotomicKummerArithmetic.exists_integral_model_same_vector ψ hζ P
  refine ⟨v, hv, P, D, D.constant_ne_zero, D.radical_ne_zero, he, ?_, ?_, ?_⟩
  · exact he ▸ hn
  · intro γ
    rw [he]
    exact (hw γ).2
  · intro v
    exact congrArg (KummerSelmer.valuationLinear p v) he

end
end DkMath.FLT.Frey.Source
