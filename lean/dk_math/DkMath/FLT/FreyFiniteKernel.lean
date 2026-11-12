/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedImage
import DkMath.Lib.NumberTheory.EllipticFiniteKernelGalois

#print "file: DkMath.FLT.FreyFiniteKernel"

/-!
# NOTE-032-005C₂a: 同じFrey核の固定体と正規化有理関数

直線Lを元の実点群へ写した同じH=pointSubgroupから固定体を構成し、拡大次数pを得る。
同じHの正規化座標和を実際の関数体の元として構成する。
Lが安定なら係数ガロア作用で固定され、Cofixed条件は安定性を内部供給する。
商楕円曲線や点写像はまだ構成していないため、005C₁のφを入力から除去したとはしない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticFiniteKernel
open DkMath.Lib.RepresentationTheory
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

/-- 同じ実点群内の直線像の有限性を、既存の正確な位数pから供給する。 -/
theorem finite_residualPointSubgroup (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1) : Finite (pointSubgroup S.rationalCurve p L) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_pointSubgroup S.rationalCurve p L hline]
    exact (Fact.out : p.Prime).ne_zero)

/-- 同じ直線核の平行移動固定体に対する関数体の次数はpである。
商曲線やisogenyの次数をすでに構成したという意味ではない。 -/
theorem residual_kernelFixedField_finrank (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1) :
    Module.finrank (kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve p L))
      (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = p := by
  let := S.finite_residualPointSubgroup L hline
  rw [finrank_kernelFixedField, card_pointSubgroup S.rationalCurve p L hline]

/-- 同じSourceの同じ直線核から正規化x座標和を構成する。列挙の選択は有限性から行う。 -/
noncomputable def residualKernelX (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1) :
    (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField := by
  letI := S.finite_residualPointSubgroup L hline
  letI := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact veluX S.rationalCurve (pointSubgroup S.rationalCurve p L)

/-- 同じ核の正規化y座標和。まだ標的曲線の点という型へは包まない。 -/
noncomputable def residualKernelY (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1) :
    (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField := by
  letI := S.finite_residualPointSubgroup L hline
  letI := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact veluY S.rationalCurve (pointSubgroup S.rationalCurve p L)

/-- 同じ安定核の二つの構成済み関数は、同じ平行移動固定体に入り、係数ガロア作用で固定される。
核の各点が有理であるとは要求しない。 -/
theorem residual_kernel_coordinates_invariant
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    (S.residualKernelX L hline ∈ kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve p L) ∧
      S.residualKernelY L hline ∈ kernelFixedField S.rationalCurve (pointSubgroup S.rationalCurve p L)) ∧
    ∀ σ : Field.absoluteGaloisGroup ℚ,
      EllipticFunctionField.galFunctionFieldEquiv S.rationalCurve σ (S.residualKernelX L hline) =
        S.residualKernelX L hline ∧
      EllipticFunctionField.galFunctionFieldEquiv S.rationalCurve σ (S.residualKernelY L hline) =
        S.residualKernelY L hline := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  refine ⟨velu_coordinates_mem S.rationalCurve (pointSubgroup S.rationalCurve p L), fun σ => ?_⟩
  exact ⟨veluX_galois S.rationalCurve (pointSubgroup S.rationalCurve p L) (pointSubgroup_stable S.rationalCurve p L hstable) σ,
    veluY_galois S.rationalCurve (pointSubgroup S.rationalCurve p L) (pointSubgroup_stable S.rationalCurve p L hstable) σ⟩

/-- Cofixed直線では安定性を内部供給し、同じ二つの有理関数のガロア固定を得る。
曲線方程式や加法性のproviderを仮定に追加しない。 -/
theorem residual_cofixed_kernel_coordinates_galois
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) (σ : Field.absoluteGaloisGroup ℚ) :
    EllipticFunctionField.galFunctionFieldEquiv S.rationalCurve σ (S.residualKernelX L hline) =
        S.residualKernelX L hline ∧
      EllipticFunctionField.galFunctionFieldEquiv S.rationalCurve σ (S.residualKernelY L hline) =
        S.residualKernelY L hline :=
  (S.residual_kernel_coordinates_invariant L hline hcofixed.isStable).2 σ

end DkMath.FLT.Frey.Source
