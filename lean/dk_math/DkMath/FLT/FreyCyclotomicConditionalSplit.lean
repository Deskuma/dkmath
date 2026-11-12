/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerLocalPower
import DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence

#print "file: DkMath.FLT.FreyCyclotomicConditionalSplit"

/-!
# 同じ Frey 単元の3次合同と、算術仮定を明示した非分裂排除

同じ非零 ω² 単元類を、実際の局所冪核の部分空間へ入れる。
同じ原始根の素点で u^(p−1)−1∈(ζ−1)^3 も証明する。
局所条件付き単元空間の消滅を明示入力とすると、その同じ非零類から矛盾する。
非分裂から v と P を内部構成し、同じ元の extension の安定補空間を得る。
hbad、実際の類群商の消滅、局所条件付き単元空間の消滅は未解決の入力である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight
open KummerLocalPower NumberFieldCompletionComparison KummerSelmer KummerSelmerExact
open CyclotomicPrimaryUnitSpace CyclotomicPrimaryCongruence
open DkMath.Lib.RepresentationTheory
open scoped NumberField Pointwise

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicConditionalSplit : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldConditionalSplit : NumberField (rootField ζ) := rootField_numberField ζ

section Presentation

variable (v : TorsionPreimageQuotient.Quotient p K)
    (P : (letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
      Presentation p (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)))

include hline hcofixed hstable hm hcard hbase P

/-- 同じ単元類が局所冪核と ω² 固有空間の交差に属し、同じ根の素点で3次合同を満たす。 -/
theorem residual_kummer_primary_unit_witness
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (hsurj : Function.Surjective
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v))
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    letI := extensionAlgebra ψ hζ
    ∃ (u : (𝓞 (rootField ζ))ˣ) (c : (rootField ζ)ˣ),
      P.constant = algebraMap (𝓞 (rootField ζ)) (rootField ζ) u * (c : rootField ζ) ^ p ∧
      constantVector ψ hζ P = Additive.ofMul
        ((Units.map (algebraMap (𝓞 (rootField ζ)) (rootField ζ)).toMonoidHom u :
          (rootField ζ)ˣ) : KummerClass (rootField ζ) p) ∧
      (u : UnitClass (𝓞 (rootField ζ)) p) ≠ 1 ∧
      Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) ∈ primaryWeightSquareSpace hζ ∧
      (u : 𝓞 (rootField ζ)) ^ (p - 1) - 1 ∈ ramifiedIdeal (baseRoot_primitive hζ) ^ 3 := by
  obtain ⟨u, c, hdec, hvec, hnz, heig, hloc⟩ :=
    S.residual_kummer_unit_weight_square_and_local_power
      L hline hcofixed K hstable hm hcard hbase hζ v P hp5 hbad hsurj hclass
  have hmem := (mk_mem_primaryWeightSquareSpace_iff hζ u).mpr ⟨heig, hloc⟩
  refine ⟨u, c, hdec, hvec, hnz, hmem, ?_⟩
  let : IsCyclotomicExtension {p} ℚ (rootField ζ) := rootField_isCyclotomic hζ
  exact pow_sub_one_mem_ramifiedIdeal_cube_of_local_power (baseRoot_primitive hζ) hp5 u hmem.2

/-- 同じ非零単元類を使う条件付き矛盾。単元空間消滅自体は hunit に明示する。 -/
theorem residual_kummer_impossible_of_primary_unit_vanishing
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (hsurj : Function.Surjective
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v))
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hunit : primaryWeightSquareSpace hζ = ⊥) : False := by
  obtain ⟨u, _, _, _, hnz, hmem, _⟩ := S.residual_kummer_primary_unit_witness
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5 hbad hsurj hclass
  exact hnz (unitClass_eq_one_of_space_eq_bot hζ hunit u hmem)

end Presentation

include hline hcofixed hstable hm hcard hbase

/-- 元の extension の非分裂から同じ v と P を内部で供給し、条件付きで排除する。 -/
theorem residual_cyclic_extension_nonsplit_impossible
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hunit : primaryWeightSquareSpace hζ = ⊥)
    (hns : ¬ ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D) : False := by
  obtain ⟨v, hsurj, hP⟩ := S.residual_nonsplit_has_kummer_presentation
    L hline hcofixed K hstable hm hcard hbase hp5 hζ hns
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let := extensionAlgebra ψ hζ
  obtain ⟨P⟩ := hP
  exact S.residual_kummer_impossible_of_primary_unit_vanishing
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5 hbad hsurj hclass hunit

/-- 算術仮定を保ったまま、同じ巡回段の商表現に実際の大域安定な補空間を得る。 -/
theorem residual_cyclic_extension_has_stable_complement
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hunit : primaryWeightSquareSpace hζ = ⊥) :
    ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D := by
  classical
  by_contra hns
  exact S.residual_cyclic_extension_nonsplit_impossible
    L hline hcofixed K hstable hm hcard hbase hζ hp5 hbad hclass hunit hns

end
end DkMath.FLT.Frey.Source
