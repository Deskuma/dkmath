/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummer
import DkMath.Lib.NumberTheory.CyclotomicKummerDecomposition

#print "file: DkMath.FLT.FreyCyclotomicKummerDecomposition"

/-!
# 同じ Frey Kummer 拡大の p 上の有限分解群は自明

同じ S,L,K,m,v,P を保ち、p 上の絶対分解群固定性を有限整数環の素点へ移す。
共鳴住所の吸収 hbad、類群消滅 hvanish、指標の全射性 hsurj は要求しない。
同じ有限拡大に対する D_w=1 と e=f=1 を結論する。
完備化への降下と局所 p 乗性は次の比較の課題である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight
open KummerDecomposition DkMath.Lib.RepresentationTheory
open scoped NumberField Pointwise

set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicKummerDecomposition : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldKummerDecomposition : NumberField (rootField ζ) := rootField_numberField ζ

variable (v : TorsionPreimageQuotient.Quotient p K)
    (P : (letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
      Presentation p (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)))

include hline hcofixed hstable hm hcard hbase P

/-- 同じ p 上の有限分解群は同じ生成根を固定する。
数体構造も既存の開核定理から内部で供給する。 -/
theorem residual_kummer_finite_decomposition_fixes_radical_at_p (hp5 : 5 ≤ p) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    let : NumberField (characterField ψ) := characterField_numberField ψ
      (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    let := extensionAlgebra ψ hζ
    ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ))),
      (p : 𝓞 (characterField ψ)) ∈ w.asIdeal →
      ∀ τ : (characterField ψ) ≃ₐ[rootField ζ] (characterField ψ),
        τ ∈ MulAction.stabilizer ((characterField ψ) ≃ₐ[rootField ζ] (characterField ψ)) w.asIdeal →
          τ P.radical = P.radical := by
  dsimp only
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let : NumberField (characterField ψ) := characterField_numberField ψ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
  let := extensionAlgebra ψ hζ
  intro w hpw
  apply CyclotomicKummerDecomposition.finite_decomposition_fixes_radical_at_p ψ hζ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    (S.residual_cyclic_extension_character_conjugate L hline hcofixed K hstable hm hcard hbase v) P ?_ w hpw
  exact S.residual_kummer_radical_decomposition_fixed_at_p
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5

/-- p 上の実際の有限分解群が自明であることを、同じ根の生成性で証明する。 -/
theorem residual_kummer_decomposition_eq_bot_at_p (hp5 : 5 ≤ p) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    let : NumberField (characterField ψ) := characterField_numberField ψ
      (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    let := extensionAlgebra ψ hζ
    ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ))),
      (p : 𝓞 (characterField ψ)) ∈ w.asIdeal →
      MulAction.stabilizer ((characterField ψ) ≃ₐ[rootField ζ] (characterField ψ)) w.asIdeal = ⊥ := by
  dsimp only
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let : NumberField (characterField ψ) := characterField_numberField ψ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
  let := extensionAlgebra ψ hζ
  intro w hpw
  exact subgroup_eq_bot_of_fixes_radical P _
    (S.residual_kummer_finite_decomposition_fixes_radical_at_p
      L hline hcofixed K hstable hm hcard hbase hζ v P hp5 w hpw)

/-- p 上の同じ v,w について分岐指数と剰余次数がともに1。
hbad や Selmer 所属を経由せず、分解群固定性から直接導く。 -/
theorem residual_kummer_ramification_and_inertiaDeg_eq_one_at_p (hp5 : 5 ≤ p) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    let : NumberField (characterField ψ) := characterField_numberField ψ
      (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    let := extensionAlgebra ψ hζ
    ∀ (vF : IsDedekindDomain.HeightOneSpectrum (𝓞 (rootField ζ)))
      (w : IsDedekindDomain.HeightOneSpectrum (𝓞 (characterField ψ))),
      w.asIdeal.LiesOver vF.asIdeal → (p : 𝓞 (rootField ζ)) ∈ vF.asIdeal →
      vF.asIdeal.ramificationIdx' w.asIdeal = 1 ∧ w.asIdeal.inertiaDeg (𝓞 (rootField ζ)) = 1 := by
  dsimp only
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let : NumberField (characterField ψ) := characterField_numberField ψ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
  let := extensionAlgebra ψ hζ
  intro vF w hvw hpv
  apply CyclotomicKummerDecomposition.ramification_and_inertiaDeg_eq_one_at_p ψ hζ
    (S.residual_cyclic_extension_character_kernel_isOpen L hline hcofixed K hstable hm hcard hbase v)
    (S.residual_cyclic_extension_character_conjugate L hline hcofixed K hstable hm hcard hbase v) P ?_ vF w hvw hpv
  exact S.residual_kummer_radical_decomposition_fixed_at_p
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5

end
end DkMath.FLT.Frey.Source
