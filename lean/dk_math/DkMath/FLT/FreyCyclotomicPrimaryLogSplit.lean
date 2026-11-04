/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicConditionalSplit
import DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero

#print "file: DkMath.FLT.FreyCyclotomicPrimaryLogSplit"

/-!
# 同じ円分単元の非零検出を内部供給した、次元1条件付き大域分裂

hunit や hdetect を入力しない。実際の単元空間の次元1を入力し、
証明済みの実際の Λ の非零評価から hunit を構成して既存の分裂定理に渡す。
hbad・hclass・同じ巡回段の全条件は保持する。次元1・一般 hno は未証明。
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
local instance instIsEllipticPrimaryLogSplit : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldPrimaryLogSplit : NumberField (rootField ζ) := rootField_numberField ζ

include hline hcofixed hstable hm hcard hbase

/-- hdetect と hunit を内部供給する。残る単元算術入力は同じ固有空間の次元1。 -/
theorem residual_cyclic_extension_has_stable_complement_of_unit_rank_one
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
    (hrank : Module.finrank (ZMod p) (weightSquareSpace hζ) = 1) :
    ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D := by
  exact S.residual_cyclic_extension_has_stable_complement
    L hline hcofixed K hstable hm hcard hbase hζ hp5 hbad hclass
    (CyclotomicPrimaryLogNonzero.primaryWeightSquareSpace_eq_bot_of_rank_one hζ hp5 hrank)

end
end DkMath.FLT.Frey.Source
