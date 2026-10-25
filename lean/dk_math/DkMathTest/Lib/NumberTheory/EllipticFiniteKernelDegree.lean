/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDegree
import DkMathTest.Lib.NumberTheory.EllipticFiniteKernel
import Mathlib.FieldTheory.RatFunc.IntermediateField

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelDegree"

/-!
005C₂c₁の次数と生成の検査。任意の体k上のk(t)の部分体k(tⁿ)を使い、互いに素な次数2,3と
共通因子を持つ次数4,6を検査する。k=ℚにも特殊化できる。同じ部分体二つやfinrank=0の消去の失敗も区別する。
楕円曲線では前回と同じ実曲線・同じHで有限性とモニック関係までを確認する。
-/
namespace EllipticFiniteKernelDegreeTest
open Polynomial IntermediateField
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
noncomputable section

/-- 同じ有理関数体内の、tⁿで生成した実際の部分体。 -/
def powerField (k : Type*) [Field k] (n : ℕ) : IntermediateField k (RatFunc k) :=
  k⟮(RatFunc.X : RatFunc k) ^ n⟯

variable (k : Type*) [Field k]

/-- 有理関数体の分子・分母の次数公式から、[k(t):k(tⁿ)]=nを独立計算する。
n=0では定数体に対する無限拡大のfinrank=0である。 -/
theorem powerField_degree (n : ℕ) : Module.finrank (powerField k n) (RatFunc k) = n := by
  have he : powerField k n = k⟮algebraMap k[X] (RatFunc k) (Polynomial.X ^ n)⟯ := by
    simp only [powerField, map_pow, RatFunc.algebraMap_X]
  rw [he]
  have hd := RatFunc.finrank_eq_max_natDegree
    (algebraMap k[X] (RatFunc k) (Polynomial.X ^ n))
  rw [RatFunc.num_algebraMap, RatFunc.denom_algebraMap, Polynomial.natDegree_X_pow,
    Polynomial.natDegree_one, max_zero] at hd
  exact hd

/-- 超越元の交換を実際のtとtⁿへ適用する。n>0を明示し、定数t⁰を混ぜない。 -/
theorem exchange_finite (n : ℕ) (hn : 0 < n) : FiniteDimensional (powerField k n) (RatFunc k) := by
  have h1 : Module.finrank k⟮(RatFunc.X : RatFunc k)⟯ (RatFunc k) = 1 := by
    have he : powerField k 1 = k⟮(RatFunc.X : RatFunc k)⟯ := by simp [powerField]
    have hd := powerField_degree k 1
    rwa [he] at hd
  have hfd : FiniteDimensional k⟮(RatFunc.X : RatFunc k)⟯ (RatFunc k) :=
    Module.finite_of_finrank_pos (by rw [h1]; decide)
  let := hfd
  exact TranscendentalFiniteDegree.finiteDimensional_of_transcendental
    (RatFunc.X : RatFunc k) ((RatFunc.X : RatFunc k) ^ n)
    RatFunc.transcendental_X (RatFunc.transcendental_X.pow hn)

/-- 次数2と3の二部分体は同じ全体k(t)を生成する。 -/
theorem coprime_two_three : powerField k 2 ⊔ powerField k 3 = ⊤ := by
  apply CoprimeFieldGeneration.sup_eq_of_ambient_degrees
    (powerField k 2) (powerField k 3) ⊤ le_top le_top 2 3 1 (by decide) (by decide)
  · simp
  · simpa using powerField_degree k 2
  · simpa using powerField_degree k 3

/-- 周囲の次数4,6は共通因子2を消すと相対次数2,3となり、同じk(t²)を生成する。
周囲の体の全体まで生成すると過大に結論しない。 -/
theorem common_factor_four_six : powerField k 4 ⊔ powerField k 6 = powerField k 2 := by
  have h4 : powerField k 4 ≤ powerField k 2 := by
    apply adjoin_simple_le_iff.mpr
    have he : ((RatFunc.X : RatFunc k) ^ 2) ^ 2 = (RatFunc.X : RatFunc k) ^ 4 :=
      (pow_mul (RatFunc.X : RatFunc k) 2 2).symm
    exact he ▸ (powerField k 2).pow_mem
      (mem_adjoin_simple_self k ((RatFunc.X : RatFunc k) ^ 2)) 2
  have h6 : powerField k 6 ≤ powerField k 2 := by
    apply adjoin_simple_le_iff.mpr
    have he : ((RatFunc.X : RatFunc k) ^ 2) ^ 3 = (RatFunc.X : RatFunc k) ^ 6 :=
      (pow_mul (RatFunc.X : RatFunc k) 2 3).symm
    exact he ▸ (powerField k 2).pow_mem
      (mem_adjoin_simple_self k ((RatFunc.X : RatFunc k) ^ 2)) 3
  exact CoprimeFieldGeneration.sup_eq_of_ambient_degrees
    (powerField k 4) (powerField k 6) (powerField k 2) h4 h6 2 3 2 (by decide) (by decide)
    (powerField_degree k 2) (by simpa using powerField_degree k 4) (by simpa using powerField_degree k 6)

/-- 同じ次数2の部分体を二つ置いても全体を生成しない。互いに素の条件が必要。 -/
theorem noncoprime_boundary : powerField k 2 ⊔ powerField k 2 ≠ ⊤ := by
  rw [sup_idem]
  intro he
  have hd := powerField_degree k 2
  rw [he] at hd
  norm_num at hd

/-- 共通因子0では次数の消去ができない。k上無限拡大のfinrank=0と、
同じ中間体自身の相対次数1は、仮想的な比2と異なる。 -/
theorem zero_finrank_boundary :
    Module.finrank (powerField k 0) (RatFunc k) = 0 ∧
    Module.finrank (powerField k 0) (RatFunc k) = 2 * 0 ∧
    (powerField k 0).relfinrank (powerField k 0) ≠ 2 := by
  exact ⟨powerField_degree k 0, by simpa using powerField_degree k 0, by simp⟩

open EllipticFiniteKernelTest WeierstrassCurve WeierstrassCurve.Affine
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
local instance : DecidableEq (Points curve) := Classical.decEq _
local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩
local instance : Fintype kernel := Fintype.ofFinset {0, Q} (fun P => by simp [kernel])

/-- 同じ実曲線・同じ二元核の正規化関数の単純部分体に対する次数は有限で正である。 -/
theorem actual_finite_degrees :
    FiniteDimensional (AlgebraicClosure ℚ)⟮veluX curve kernel⟯
        (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField ∧
    FiniteDimensional (AlgebraicClosure ℚ)⟮veluY curve kernel⟯
        (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField ∧
    0 < Module.finrank (AlgebraicClosure ℚ)⟮veluX curve kernel⟯
        (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField ∧
    0 < Module.finrank (AlgebraicClosure ℚ)⟮veluY curve kernel⟯
        (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField :=
  ⟨(finiteDimensional_over_velu curve kernel).1, (finiteDimensional_over_velu curve kernel).2,
    velu_simple_degrees_pos curve kernel⟩

/-- 同じY_Hの正次数モニック関係を、同じX_H上の実際の多項式として得る。
次数2・短いWeierstrass形を仮定しない。 -/
theorem actual_monic_relation :
    ∃ q : ((AlgebraicClosure ℚ)⟮veluX curve kernel⟯)[X],
      q.Monic ∧ 0 < q.natDegree ∧ aeval (veluY curve kernel) q = 0 :=
  exists_velu_monic_relation curve kernel

end
end EllipticFiniteKernelDegreeTest
