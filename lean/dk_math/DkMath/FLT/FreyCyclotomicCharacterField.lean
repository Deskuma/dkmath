/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicExtensionCharacter
import DkMath.Lib.NumberTheory.CyclotomicCharacterField

#print "file: DkMath.FLT.FreyCyclotomicCharacterField"

/-!
# 大域非分裂から、実際の円分体上の巡回 `p` 拡大へ

同じ逆像商の実際の指標の核の固定体を構成する。
非分裂なら一つの全射指標を選び、円分体を含む有限 Galois 拡大と相対次数 `p`、
巡回 Galois 群を得る。`p` 上の分解群・`p` 外の慣性の作用も同じ固定体で消える。
類群・単数への写像、Kummer の omega 二乗への捩り、大域消滅は未実装である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField CyclotomicCharacterField
open ValuationInertia DkMath.Lib.RepresentationTheory

set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicCharacterField : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)

include hline hcofixed hstable hm hcard hbase

/-- 同じ指標の同じ核の固定体。 -/
abbrev residualCharacterField (v : TorsionPreimageQuotient.Quotient p K) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  characterField (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v)

/-- 大域非分裂なら、同じ代数閉包内に実際の巡回 `p` 拡大が現れる。
根の選択は明示し、拡大体・有限性・Galois 性・次数の provider は残さない。 -/
theorem residual_nonsplit_has_cyclotomic_cyclic_extension (hp5 : 5 ≤ p)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hns : ¬ ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D) :
    ∃ v : TorsionPreimageQuotient.Quotient p K,
      Function.Surjective (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) ∧
      FiniteDimensional ℚ (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v) ∧
      IsGalois ℚ (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v) ∧
      rootField ζ ≤ S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v ∧
      Module.finrank ℚ (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v) = p * (p - 1) ∧
      (letI := extensionAlgebra
        (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ
       Module.finrank (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v) = p ∧
       IsGalois (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v) ∧
       Nat.card ((S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v) ≃ₐ[rootField ζ]
         (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)) = p ∧
       IsCyclic ((S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v) ≃ₐ[rootField ζ]
         (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v))) := by
  obtain ⟨v, hv⟩ := S.residual_cyclic_extension_nonsplit_has_surjective_character
    L hline hcofixed K hstable hm hcard hbase hp5 hns
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  have hopen := S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v
  have hw := S.residual_cyclic_extension_character_conjugate L hline hcofixed K hstable hm hcard hbase v
  have hc := card_torsionImage_of_cyclic S.rationalCurve K hm hcard
  refine ⟨v, hv, characterField_finite ψ hopen, characterField_isGalois ψ hopen hw,
    rootField_le_characterField ψ hζ, ?_, ?_⟩
  · exact (characterField_finrank ψ hopen hv).trans (congrArg (fun n => n * (p - 1)) hc)
  · let := extensionAlgebra ψ hζ
    exact ⟨(relative_finrank ψ hζ hopen hv).trans hc, relative_isGalois ψ hζ hopen hw,
      (relative_card_aut ψ hζ hopen hv hw).trans hc, relative_isCyclic ψ hζ hopen hv hc hw⟩

/-- `p` 上では、円分体上の実際の分解群が同じ構成体の全元を固定する。 -/
theorem residual_characterField_decomposition_fixed_at_p (hp5 : 5 ≤ p)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (v : TorsionPreimageQuotient.Quotient p K)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p)
    (g : (cyclotomicCharacter (K := ℚ) p).ker)
    (hg : kernelEquiv hζ g ∈ A.decompositionSubgroup (rootField ζ))
    (x : S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v) :
    kernelEquiv hζ g x.val = x.val := by
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  have hψ : ψ g = 1 := S.residual_cyclic_extension_character_at_p L hline hcofixed K hstable
    hm hcard hbase hp5 A hA v g ((kernelEquiv_mem_decomposition_iff hζ A g).mp hg)
  have hH := (mem_kernelInGalois ψ g).mpr hψ
  exact (IntermediateField.mem_fixedField_iff (kernelInGalois ψ) x.val).mp x.property g.val hH

/-- `p` 外の円分体上の慣性も同じ構成体を固定する。
未実装の共鳴住所の吸収は、元のまま明示して保つ。 -/
theorem residual_characterField_inertia_fixed_away (hp5 : 5 ≤ p)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (v : TorsionPreimageQuotient.Quotient p K)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (g : (cyclotomicCharacter (K := ℚ) p).ker)
    (hg : kernelEquiv hζ g ∈ inertiaSubgroupIn A (rootField ζ))
    (x : S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v) :
    kernelEquiv hζ g x.val = x.val := by
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  have hψ : ψ g = 1 := S.residual_cyclic_extension_character_inertia_away L hline hcofixed K hstable
    hm hcard hbase hp5 hbad hq hqp A hA v g ((kernelEquiv_mem_inertia_iff hζ A g).mp hg)
  have hH := (mem_kernelInGalois ψ g).mpr hψ
  exact (IntermediateField.mem_fixedField_iff (kernelInGalois ψ) x.val).mp x.property g.val hH

end
end DkMath.FLT.Frey.Source
