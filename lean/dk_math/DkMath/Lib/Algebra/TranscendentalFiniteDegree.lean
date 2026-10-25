/-
Copyright (c) 2021 Anne Baanen, Ashvni Narayanan.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
The exchange-and-tower proof is adapted from Mathlib/NumberTheory/FunctionField.lean,
FunctionField.finiteDimensional_of_adjoin_transcendental.
Modified: take a finite extension of k(x) directly, without choosing a RatFunc algebra;
add the actual two-generator entrance and textbook documentation.
-/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Bivariate
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

#print "file: DkMath.Lib.Algebra.TranscendentalFiniteDegree"

/-!
# NOTE-032-005C₂c₁: 超越元を替えたときの有限拡大

[DkMath.Lib] L=k(x,y)でyがk(x)上整なら、L/k(x)は有限である。
さらにL/k(x)が有限でx,zがk上超越的なら、交換補題からxはk(z)上代数的となる。
k(z,x)の二通りの生成を比較し、L/k(z)の有限性を得る。
これは有限性であり、次数と極位数の総和を同定する定理ではない。
-/
namespace DkMath.Lib.Algebra.TranscendentalFiniteDegree
open IntermediateField
variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- [DkMath.Lib] 同じ二元生成表示とyの整関係から、L/k(x)の有限性を得る。
生成表示を仮定に保持し、任意の大きい周囲の体へ結論を広げない。 -/
theorem finiteDimensional_of_pair (x y : L) (hgen : adjoin k {x, y} = ⊤)
    (hy : IsIntegral k⟮x⟯ y) : FiniteDimensional k⟮x⟯ L := by
  have htop : k⟮x⟯⟮y⟯ = ⊤ := by
    apply restrictScalars_injective k
    rw [restrictScalars_top, adjoin_simple_adjoin_simple, hgen]
  let := adjoin.finiteDimensional hy
  exact LinearEquiv.finiteDimensional
    ((equivOfEq htop).trans IntermediateField.topEquiv).toLinearEquiv

/-- [DkMath.Lib] 一変数関数体の超越元を替えても、同じ全体の体の有限性は保たれる。
標的の次数を計算したとはせず、代数的交換と有限拡大の塔を明示する。 -/
theorem finiteDimensional_of_transcendental (x z : L) (hx : Transcendental k x)
    [FiniteDimensional k⟮x⟯ L] (hz : Transcendental k z) : FiniteDimensional k⟮z⟯ L := by
  have hxalg : IsAlgebraic k⟮z⟯ x :=
    isAlgebraic_adjoin_iff.mpr (.adjoin_singleton hx hz
      (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic z)))
  let Fzx := restrictScalars k k⟮z⟯⟮x⟯
  let Fxz := restrictScalars k k⟮x⟯⟮z⟯
  let : Algebra k⟮z⟯ Fzx := k⟮z⟯⟮x⟯.algebra
  let : Module k⟮z⟯ Fzx := Algebra.toModule
  let : SMul k⟮z⟯ Fzx := Algebra.toSMul
  let : Algebra k⟮x⟯ Fxz := k⟮x⟯⟮z⟯.algebra
  let : Module k⟮x⟯ Fxz := Algebra.toModule
  let : SMul k⟮x⟯ Fxz := Algebra.toSMul
  have : FiniteDimensional k⟮z⟯ Fzx := adjoin.finiteDimensional hxalg.isIntegral
  have : FiniteDimensional Fzx L := by
    unfold Fzx
    rw [adjoin_simple_comm]
    have : IsScalarTower k⟮x⟯ Fxz L := isScalarTower_mid' k⟮x⟯⟮z⟯
    exact FiniteDimensional.right k⟮x⟯ Fxz L
  have : IsScalarTower k⟮z⟯ Fzx L := isScalarTower_mid' k⟮z⟯⟮x⟯
  exact FiniteDimensional.trans k⟮z⟯ Fzx L

end DkMath.Lib.Algebra.TranscendentalFiniteDegree
