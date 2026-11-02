/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerArithmetic
import DkMath.Lib.NumberTheory.CyclotomicKummerClassMap

#print "file: DkMath.FLT.FreyCyclotomicKummerClassMap"

/-!
# 同じ Frey Kummer 類の類群像から単元へ戻る条件付き接続

元の同じ表示 `P` を保ち、Selmer 所属と類群像の零化が別途証明された場合に、
同じ定数を実際の整数環単元と底体の冪に分解する。
元のベクトルとの一致と単元冪商での非自明性を返す。
所属・類群消滅・単数消滅を供給する定理ではなく、一般 `hno` は未完成。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight
open KummerSelmer KummerSelmerExact DkMath.Lib.RepresentationTheory

set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicKummerClassMap : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberField : NumberField (rootField ζ) := rootField_numberField ζ

variable (v : TorsionPreimageQuotient.Quotient p K)
    (P : (letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
      Presentation p (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)))

include hline hcofixed hstable hm hcard hbase

/-- 元の表示のまま単元へ戻る。`hval` と `hzero` は未解決の算術的入力として明示する。
別の類を選んだり、類群が零なら Kummer ベクトルも零と結論したりしない。 -/
theorem residual_kummer_unit_of_classImage_eq_one
    (hval : constantVector
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ P ∈
        valuationSpace (R := NumberField.RingOfIntegers (rootField ζ)) p)
    (hzero : CyclotomicKummerClassMap.classImage
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ P hval = 1) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    letI := extensionAlgebra ψ hζ
    ∃ (u : (NumberField.RingOfIntegers (rootField ζ))ˣ) (c : (rootField ζ)ˣ),
      P.constant = algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ) u * (c : rootField ζ) ^ p ∧
      constantVector ψ hζ P = Additive.ofMul
        ((Units.map (algebraMap (NumberField.RingOfIntegers (rootField ζ)) (rootField ζ)).toMonoidHom u :
          (rootField ζ)ˣ) : KummerClass (rootField ζ) p) ∧
      (u : UnitClass (NumberField.RingOfIntegers (rootField ζ)) p) ≠ 1 :=
  CyclotomicKummerClassMap.unit_of_classImage_eq_one _ hζ P hval hzero

end
end DkMath.FLT.Frey.Source
