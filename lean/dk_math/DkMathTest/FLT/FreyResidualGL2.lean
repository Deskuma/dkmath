/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidualGL2
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyResidualGL2"

/-!
# NOTE-017: 実在するE[37]のGL₂と、二次元でも可約な実例

Source 2の曲線の37-torsionを用い、仮想的なSource 37の存在に依存せず行列化を検査する。
基底の0番と1番を交換して共役・行列式・特性多項式・既約性・核の不変性を確かめる。
同じ曲線の2-torsionには有理点(0,0)が生成する安定直線が実在する。
従って二次元性の定理をもって既約性を証明したと解釈してはならない。
-/
namespace FreyResidualGL2Test
open Module
open scoped Matrix
open DkMath.FLT.Frey
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
open FreyResidualRepresentationTest
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic

noncomputable abbrev b37 := torsionBasis sample.rationalCurve 37
noncomputable abbrev swapped37 := b37.reindex (Equiv.swap (0 : Fin 2) 1)

/-- 交換する二つの基底は実際に異なる。単に同じ基底同士を比較するテストではない。 -/
theorem swapped37_ne : swapped37 ≠ b37 := by
  intro h
  have hv := congrArg (fun b : Basis (Fin 2) (ZMod 37) (Torsion sample.rationalCurve 37) => b 0) h
  have hh : b37 1 = b37 0 := by simpa [swapped37, Basis.reindex_apply] using hv
  have := b37.injective hh
  exact (by decide : (1 : Fin 2) ≠ 0) this

/-- 実際の37-torsion点への作用を、同じ基底の列ベクトル作用として読む。 -/
theorem actual37_action (σ : Field.absoluteGaloisGroup ℚ) (P : Torsion sample.rationalCurve 37) :
    (torsionGL2 sample.rationalCurve 37 σ : Matrix (Fin 2) (Fin 2) (ZMod 37)) *ᵥ b37.equivFun P =
      b37.equivFun (representation sample.rationalCurve 37 σ P) :=
  torsionGL2_mulVec sample.rationalCurve 37 σ P

/-- 異なる基底へ変更したGL₂表現は、一般定理どおり共役になる。 -/
theorem actual37_conjugate (σ : Field.absoluteGaloisGroup ℚ) :
    torsionGL2WithBasis sample.rationalCurve 37 swapped37 σ =
      basisChange b37 swapped37 * torsionGL2WithBasis sample.rationalCurve 37 b37 σ *
        (basisChange b37 swapped37)⁻¹ :=
  torsionGL2_basis_change sample.rationalCurve 37 b37 swapped37 σ

/-- 行列式指標全体は、二つの異なる基底で同じである。 -/
theorem actual37_determinant :
    determinantCharacterWithBasis (representation sample.rationalCurve 37) b37 =
      determinantCharacterWithBasis (representation sample.rationalCurve 37) swapped37 :=
  determinantCharacterWithBasis_independent _ _ _

/-- 特性多項式も基底に依存しない。 -/
theorem actual37_charpoly (σ : Field.absoluteGaloisGroup ℚ) :
    (torsionGL2WithBasis sample.rationalCurve 37 b37 σ : Matrix (Fin 2) (Fin 2) (ZMod 37)).charpoly =
      (torsionGL2WithBasis sample.rationalCurve 37 swapped37 σ : Matrix (Fin 2) (Fin 2) (ZMod 37)).charpoly :=
  matrixGroupHom_charpoly_basis_independent _ _ _ _

/-- 座標表現の既約性は基底に依存しない。どちらの既約性もここでは断定しない。 -/
theorem actual37_irreducible_basis :
    DkMath.Lib.RepresentationTheory.IsIrreducible
        (coordinateRepresentation (representation sample.rationalCurve 37) b37) ↔
      DkMath.Lib.RepresentationTheory.IsIrreducible
        (coordinateRepresentation (representation sample.rationalCurve 37) swapped37) :=
  coordinate_isIrreducible_basis_independent _ _ _

/-- 核も二つの基底で変わらない。 -/
theorem actual37_kernel :
    (torsionGL2WithBasis sample.rationalCurve 37 b37).ker =
      (torsionGL2WithBasis sample.rationalCurve 37 swapped37).ker :=
  (matrixGroupHom_ker _ _).trans (matrixGroupHom_ker _ _).symm

/-- 有限正規レベルは、実際の37-torsionのGL₂表現について存在する。 -/
theorem actual37_finite_level :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧ Normal ℚ L ∧
      L.fixingSubgroup ≤ (torsionGL2 sample.rationalCurve 37).ker :=
  torsionGL2_normal_finite_level sample.rationalCurve 37

/-- 任意のSource 37からの判定基準には、次元・位数・既約性の追加仮定がない。 -/
theorem source37_line_criterion (S : Source 37) :
    S.ResidualIsIrreducible ↔ ¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace,
      finrank (ZMod 37) L = 1 ∧ S.IsGaloisStable L :=
  S.residual_isIrreducible_iff_no_stable_line

/-- 実在する2-torsionの有理点が生成する直線はガロア作用で安定である。 -/
theorem actual2_stable_line :
    ∃ L : Submodule (ZMod 2) sample.ResidualSpace,
      finrank (ZMod 2) L = 1 ∧ sample.IsGaloisStable L := by
  refine ⟨Submodule.span (ZMod 2) {twoPoint}, finrank_span_singleton twoPoint_ne_zero, ?_⟩
  intro σ P hP
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hP
  rw [map_smul, twoPoint_fixed]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self twoPoint)

/-- 反例の存在を仮定せず、実在するSource 2の残余表現は二次元かつ可約である。 -/
theorem actual2_rank_two_reducible :
    finrank (ZMod 2) sample.ResidualSpace = 2 ∧ ¬ sample.ResidualIsIrreducible :=
  ⟨sample.residual_finrank_eq_two, fun h =>
    (sample.residual_isIrreducible_iff_no_stable_line.mp h) actual2_stable_line⟩

end FreyResidualGL2Test
