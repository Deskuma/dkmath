/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicConditionalSplit
import DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace

#print "file: DkMath.FLT.FreyCyclotomicUnitSplit"

/-!
# 単元算術を内部供給した、類群・共鳴素点条件付きの同じ Frey 分裂

同じ ω² 射影子の実際の trace=1 と、同じ単元の非零検出から単元消滅を内部供給する。
公開入口には hrank/htrace/hunit/hdetect を要求しない。
hbad・hclass・同じ巡回段の全条件は保持する。一般 hno や巡回塔はまだ未完成。
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
local instance instIsEllipticUnitSplit : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldUnitSplit : NumberField (rootField ζ) := rootField_numberField ζ

include hline hcofixed hstable hm hcard hbase

/-- 単元側の算術入力を除去した同じ安定補空間。hbad と実際の hclass は保持する。 -/
theorem residual_cyclic_extension_has_stable_complement_of_class_vanishing
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0) :
    ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D := by
  exact S.residual_cyclic_extension_has_stable_complement
    L hline hcofixed K hstable hm hcard hbase hζ hp5 hbad hclass
    (CyclotomicOmegaSquareTrace.primaryWeightSquareSpace_eq_bot hζ hp5)

end
end DkMath.FLT.Frey.Source
