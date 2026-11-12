/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
The generic-coordinate quadratic relation is adapted from
DkMath.Lib.NumberTheory.EllipticMultiplicationFunctionDegree, originally from
P2M/Sol/S_WeierstrassCurve_Affine_finrank_fieldRange_mulPull_le.lean,
blob 346a32fb08ba430a7125a16d9c7b96c9608ea417.
Modified: use exchange for arbitrary transcendental functions; keep exact degrees
as explicit inputs in the coprime-generation theorem.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelPoles
import DkMath.Lib.NumberTheory.EllipticFunctionFieldGenerators
import DkMath.Lib.Algebra.TranscendentalFiniteDegree
import DkMath.Lib.Algebra.CoprimeFieldGeneration

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelDegree"

/-!
# NOTE-032-005C₂c₁: 同じ二関数の有限次数と条件付き固定体生成

[DkMath.Lib] 楕円曲線の実際の関数体は一般座標x,yで生成され、yはk(x)上の二次式を満たす。
これと超越元の交換から、構成済みX_H,Y_Hの各々で生成した部分体に対する有限性を供給する。
同じ二関数が生成する中間体、固定体への包含、次数の塔、実際の最小多項式の関係を固定する。

次数が2|H|,3|H|であることを別に供給できれば、互いに素な相対次数から同じ固定体を生成する。
今回その正確な次数は未証明であり、総極位数の式を次数公式と読み替えない。
最小多項式の関係も、標的のWeierstrass方程式・非特異性の証明とは区別する。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation
open DkMath.Lib.Algebra
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelDegree :
    DecidableEq (AlgebraicClosure K) := Classical.decEq _

omit [E.IsElliptic] in
/-- [DkMath.Lib] 同じ一般座標の二次関係と二元生成から、関数体はk(x)上有限となる。
ここでは次数が正確に2とは主張せず、後続の交換に必要な有限性だけを供給する。 -/
theorem finiteDimensional_over_genericX :
    FiniteDimensional (AlgebraicClosure K)⟮genericX E (AlgebraicClosure K)⟯
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField := by
  let F := (E.toAffine⁄(AlgebraicClosure K)).FunctionField
  let x := genericX E (AlgebraicClosure K)
  let y := genericY E (AlgebraicClosure K)
  let M := (AlgebraicClosure K)⟮x⟯
  let A : F := (E⁄F).a₁ * x + (E⁄F).a₃
  let B : F := -(x ^ 3 + (E⁄F).a₂ * x ^ 2 + (E⁄F).a₄ * x + (E⁄F).a₆)
  have hcoef : ∀ c : K, algebraMap K F c ∈ M := fun c => by
    rw [IsScalarTower.algebraMap_apply K (AlgebraicClosure K) F]
    exact IntermediateField.algebraMap_mem M _
  have hx : x ∈ M := mem_adjoin_simple_self _ _
  have hA : A ∈ M := add_mem (mul_mem (hcoef E.a₁) hx) (hcoef E.a₃)
  have hB : B ∈ M := neg_mem (add_mem (add_mem
    (add_mem (pow_mem hx 3) (mul_mem (hcoef E.a₂) (pow_mem hx 2)))
    (mul_mem (hcoef E.a₄) hx)) (hcoef E.a₆))
  have hyq : y ^ 2 + A * y + B = 0 := by
    have h := (equation_iff _ _).mp (generic_equation E (AlgebraicClosure K))
    change y ^ 2 + ((E⁄F).a₁ * x + (E⁄F).a₃) * y -
      (x ^ 3 + (E⁄F).a₂ * x ^ 2 + (E⁄F).a₄ * x + (E⁄F).a₆) = 0
    linear_combination h
  let a : M := ⟨A, hA⟩
  let b : M := ⟨B, hB⟩
  let q : M[X] := X ^ 2 + (C a * X + C b)
  have hlow : (C a * X + C b).degree < 2 := by
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (degree_C_mul_X_le a) (by decide)
    · exact lt_of_le_of_lt degree_C_le (by decide)
  have hq : q.Monic := monic_X_pow_add hlow
  have hqy : aeval y q = 0 := by
    change aeval y (X ^ 2 + (C a * X + C b)) = 0
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    change y ^ 2 + (A * y + B) = 0
    simpa only [add_assoc] using hyq
  have hy : IsIntegral M y := ⟨q, hq, by rwa [← aeval_def]⟩
  exact TranscendentalFiniteDegree.finiteDimensional_of_pair x y
    (functionField_adjoin_X_Y (E.baseChange (AlgebraicClosure K))) hy

/-- [DkMath.Lib] 同じ楕円関数体の任意の超越関数fは、一変数の有限次数の入口となる。
次数の数値や極の重複度からの等式はここに仮定しない。 -/
theorem finiteDimensional_over_transcendental
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
    (hf : Transcendental (AlgebraicClosure K) f) :
    FiniteDimensional (AlgebraicClosure K)⟮f⟯ (E.toAffine⁄(AlgebraicClosure K)).FunctionField := by
  let := finiteDimensional_over_genericX E
  have hx : Transcendental (AlgebraicClosure K) (genericX E (AlgebraicClosure K)) := by
    apply transcendental_of_point_pole E 0
    change 1 < pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point)
      (genericX E (AlgebraicClosure K))
    rw [pointValuation_zero_genericX, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  exact TranscendentalFiniteDegree.finiteDimensional_of_transcendental _ f hx hf

/-- [DkMath.Lib] 同じX_H,Y_Hのそれぞれによる関数体拡大は有限である。
有限性のproviderを追加の仮定にせず、幾何学的な二元生成と超越性から内部供給する。 -/
theorem finiteDimensional_over_velu (H : AddSubgroup (Points E)) [Fintype H] :
    FiniteDimensional (AlgebraicClosure K)⟮veluX E H⟯ (E.toAffine⁄(AlgebraicClosure K)).FunctionField ∧
      FiniteDimensional (AlgebraicClosure K)⟮veluY E H⟯ (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  ⟨finiteDimensional_over_transcendental E _ (veluX_transcendental E H),
    finiteDimensional_over_transcendental E _ (veluY_transcendental E H)⟩

/-- [DkMath.Lib] 同じ構成済み二関数が生成する中間体。商曲線モデルはまだ含めない。 -/
noncomputable def veluCoordinateField (H : AddSubgroup (Points E)) [Fintype H] :
    IntermediateField (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  adjoin (AlgebraicClosure K) {veluX E H, veluY E H}

/-- [DkMath.Lib] 同じ二関数の生成体は同じ核の平行移動固定体に含まれる。 -/
theorem veluCoordinateField_le_fixedField (H : AddSubgroup (Points E)) [Fintype H] :
    veluCoordinateField E H ≤ kernelFixedField E H := by
  rw [veluCoordinateField, adjoin_le_iff]
  intro z hz
  rcases hz with rfl | hz
  · exact (velu_coordinates_mem E H).1
  · rw [Set.mem_singleton_iff] at hz
    exact hz ▸ (velu_coordinates_mem E H).2

/-- [DkMath.Lib] 有限次数は正である。無限拡大のfinrank=0を数値の次数に使わない。 -/
theorem velu_simple_degrees_pos (H : AddSubgroup (Points E)) [Fintype H] :
    0 < Module.finrank (AlgebraicClosure K)⟮veluX E H⟯ (E.toAffine⁄(AlgebraicClosure K)).FunctionField ∧
      0 < Module.finrank (AlgebraicClosure K)⟮veluY E H⟯ (E.toAffine⁄(AlgebraicClosure K)).FunctionField := by
  let := (finiteDimensional_over_velu E H).1
  let := (finiteDimensional_over_velu E H).2
  exact ⟨Module.finrank_pos, Module.finrank_pos⟩

/-- [DkMath.Lib] 同じY_Hはk(X_H)上の実際の正次数モニック多項式を満たす。
次数2やWeierstrass形、基礎体の多項式係数であることはまだ結論しない。 -/
theorem exists_velu_monic_relation (H : AddSubgroup (Points E)) [Fintype H] :
    ∃ q : ((AlgebraicClosure K)⟮veluX E H⟯)[X],
      q.Monic ∧ 0 < q.natDegree ∧ aeval (veluY E H) q = 0 := by
  let := (finiteDimensional_over_velu E H).1
  have hy : IsIntegral (AlgebraicClosure K)⟮veluX E H⟯ (veluY E H) :=
    (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  exact ⟨minpoly _ _, minpoly.monic hy, minpoly.natDegree_pos hy, minpoly.aeval _ _⟩

/-- [DkMath.Lib] 同じ固定体とX_H,Y_Hの単純部分体の次数の塔。
左辺の共通因子は同じHの位数であり、2,3という相対次数は未供給。 -/
theorem velu_degree_towers (H : AddSubgroup (Points E)) [Fintype H] :
    ((AlgebraicClosure K)⟮veluX E H⟯).relfinrank (kernelFixedField E H) * Nat.card H =
      Module.finrank (AlgebraicClosure K)⟮veluX E H⟯ (E.toAffine⁄(AlgebraicClosure K)).FunctionField ∧
    ((AlgebraicClosure K)⟮veluY E H⟯).relfinrank (kernelFixedField E H) * Nat.card H =
      Module.finrank (AlgebraicClosure K)⟮veluY E H⟯ (E.toAffine⁄(AlgebraicClosure K)).FunctionField := by
  have hx := relfinrank_mul_finrank_top
    (adjoin_simple_le_iff.mpr (velu_coordinates_mem E H).1)
  have hy := relfinrank_mul_finrank_top
    (adjoin_simple_le_iff.mpr (velu_coordinates_mem E H).2)
  rw [finrank_kernelFixedField E H] at hx hy
  exact ⟨hx, hy⟩

/-- [DkMath.Lib] 正確な次数2|H|,3|H|を供給できれば、同じ二関数は同じ固定体を生成する。
この二つの次数が今後の未供給の数学であり、極位数の総和で代用していない。 -/
theorem veluCoordinateField_eq_fixedField_of_degrees (H : AddSubgroup (Points E)) [Fintype H]
    (hX : Module.finrank (AlgebraicClosure K)⟮veluX E H⟯
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField = 2 * Nat.card H)
    (hY : Module.finrank (AlgebraicClosure K)⟮veluY E H⟯
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField = 3 * Nat.card H) :
    veluCoordinateField E H = kernelFixedField E H := by
  have he := CoprimeFieldGeneration.sup_eq_of_ambient_degrees
    ((AlgebraicClosure K)⟮veluX E H⟯) ((AlgebraicClosure K)⟮veluY E H⟯) (kernelFixedField E H)
    (adjoin_simple_le_iff.mpr (velu_coordinates_mem E H).1)
    (adjoin_simple_le_iff.mpr (velu_coordinates_mem E H).2)
    2 3 (Nat.card H) (by decide) (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
    (finrank_kernelFixedField E H) hX hY
  simpa only [veluCoordinateField, ← adjoin_union, Set.singleton_union] using he

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
