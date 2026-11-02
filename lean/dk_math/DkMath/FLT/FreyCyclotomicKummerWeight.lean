/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummer
import DkMath.Lib.NumberTheory.CyclotomicKummerWeight

#print "file: DkMath.FLT.FreyCyclotomicKummerWeight"

/-!
# Frey の非分裂から、非自明な円分二乗 Kummer 類へ

同じ巡回段・同じ指標・同じ核の固定体の同じ Kummer 表示を保つ。
元の加法指標の逆円分共役則から、底体の全自己同型について
`γ[b]=[b]^(ω(γ)^2)` を導く。非零類・重み・持ち上げの provider は要求しない。
類群・単数の消滅、整数化、共鳴住所と巡回塔の反復は未実装であり、一般 `hno` は未完成。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight DkMath.Lib.RepresentationTheory

set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicKummerWeight : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)

include hline hcofixed hstable hm hcard hbase

/-- 非分裂なら、同じ構成体の表示が実際の非自明な `ω²` Kummer 類を与える。
`P` の定数そのものの固有性ではなく、`p` 乗を法とした同じ類の等式を返す。 -/
theorem residual_nonsplit_has_weight_two_kummer_class (hp5 : 5 ≤ p)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hns : ¬ ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D) :
    ∃ v : TorsionPreimageQuotient.Quotient p K,
      Function.Surjective (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) ∧
      (let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
       letI := extensionAlgebra ψ hζ
       ∃ P : Presentation p (rootField ζ)
           (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v),
         constantClass ψ hζ P ≠ 1 ∧
         constantVector ψ hζ P ≠ 0 ∧
         ∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
           classMap p γ.toRingHom (constantClass ψ hζ P) =
             constantClass ψ hζ P ^ ((baseCharacter hζ γ : ZMod p) ^ 2).val ∧
           classLinearMap p γ.toRingHom (constantVector ψ hζ P) =
             (baseCharacter hζ γ : ZMod p) ^ 2 • constantVector ψ hζ P) := by
  obtain ⟨v, hv, ⟨P⟩⟩ := S.residual_nonsplit_has_kummer_presentation
    L hline hcofixed K hstable hm hcard hbase hp5 hζ hns
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let := extensionAlgebra ψ hζ
  refine ⟨v, hv, P, constantClass_ne_one ψ hζ P, constantVector_ne_zero ψ hζ P, ?_⟩
  intro γ
  have ho := S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v
  have hw := S.residual_cyclic_extension_character_conjugate L hline hcofixed K hstable hm hcard hbase v
  exact ⟨constantClass_weight_square ψ hζ P hv ho hw γ,
    constantVector_weight_square ψ hζ P hv ho hw γ⟩

end
end DkMath.FLT.Frey.Source
