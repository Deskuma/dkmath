/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNonresonantInertia
import DkMath.FLT.FreyCyclicTateVector
import DkMath.Lib.Algebra.PrimePowerTateModule
import DkMath.Lib.NumberTheory.EllipticNodalUnipotence
import DkMath.Lib.NumberTheory.CyclotomicFrobeniusAll

#print "file: DkMath.FLT.FreyTateInertiaUnipotent"

/-!
# 同じ Frey 曲線の全 Tate 慣性作用の二次冪零性

節点幾何と滑らかな捩れ固定性から、全有限段を経て同じ全点列へ接続する。
hclass・hbad・Cofixed・基底の存在はこの局所定理の入力ではない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation PrimePowerTateSequence ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- q≠p の悪い住所の同じ有限捩れ作用で、慣性差分は二次冪零。 -/
theorem prime_power_inertia_difference_square_zero (hp5 : 5 ≤ p) (n : ℕ)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    (representation S.rationalCurve (p ^ (n + 1)) τ - 1) ^ 2 = 0 := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨C, ⟨D⟩⟩ := S.exists_geometry_at_bad_address hp5 haddr A hA
  exact EllipticNodalUnipotence.inertia_difference_square_zero S.rationalCurve _ A
    (S.valuationModel A) (S.valuationModel_map A) C D
    (CyclotomicFrobenius.prime_power_valuation_eq_one hq hqp A hA n) τ hτ

/-- 全点列の各成分で上の実際の有限作用を比較する。 -/
theorem tate_inertia_difference_square_zero (hp5 : 5 ≤ p)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    (actionLinear (p := p) S.residualPointActionHom τ - 1) ^ 2 = 0 := by
  apply LinearMap.ext
  intro x
  apply PrimePowerTateSequence.ext
  intro n
  have h := S.prime_power_inertia_difference_square_zero hp5 n hq hqp haddr A hA τ hτ
  have he := congrArg (fun f : Module.End (ZMod (p ^ (n + 1)))
      (Torsion S.rationalCurve (p ^ (n + 1))) => (f ⟨evaluation n x, killed x n⟩).val) h
  exact he

end
end DkMath.FLT.Frey.Source
