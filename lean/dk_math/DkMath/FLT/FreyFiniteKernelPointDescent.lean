/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelNonsingular
import DkMath.Lib.NumberTheory.EllipticFiniteKernelPointDescent

#print "file: DkMath.FLT.FreyFiniteKernelPointDescent"

/-!
# 同じ残余核の全点関数をℚ係数標的へ接続する

同じSource、同じ安定直線L、その実点像Hを全て保持する。
標的を選び直さず、Libの既存の係数降下をSourceから参照する。
奇素数では同じ全点関数の零ファイバーとGalois同変性を内部供給できる。
Cofixedなら核外の残余点の像は非零ℚ有理点になる。
加法性未証明のため、その有理点のp捩れ性とhnoの結論はまだ含めない。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ安定直線から既に降下した、同じℚ係数モデル。 -/
noncomputable def residualDescendedKernelModel
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) : WeierstrassCurve ℚ := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact descendedKernelModel S.rationalCurve (pointSubgroup S.rationalCurve p L)
    (pointSubgroup_stable S.rationalCurve p L hstable)

/-- ℚ係数モデルの基底変換は、同じresidualKernelModelである。 -/
theorem residual_descended_kernel_model_map
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    (S.residualDescendedKernelModel L hline hstable).map (algebraMap ℚ (AlgebraicClosure ℚ)) =
      S.residualKernelModel L hline := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact descendedKernelModel_map S.rationalCurve (pointSubgroup S.rationalCurve p L)
    (pointSubgroup_stable S.rationalCurve p L hstable)

/-- 同じℚ係数標的の楕円性。 -/
theorem residual_descended_kernel_model_isElliptic (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    (S.residualDescendedKernelModel L hline hstable).IsElliptic := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  apply descendedKernelModel_isElliptic_of_odd_card S.rationalCurve
    (pointSubgroup S.rationalCurve p L) _ (pointSubgroup_stable S.rationalCurve p L hstable)
  rw [card_pointSubgroup S.rationalCurve p L hline]
  exact (Fact.out : p.Prime).odd_of_ne_two hp2

/-- 同じℚ係数標的の幾何学的実点へ移した、既存の全点関数。 -/
noncomputable def residualDescendedKernelPointMap (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) :
    Points S.rationalCurve → Points (S.residualDescendedKernelModel L hline hstable) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have ho : Odd (Nat.card (pointSubgroup S.rationalCurve p L)) := by
    rw [card_pointSubgroup S.rationalCurve p L hline]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  exact descendedKernelPointMap S.rationalCurve _ ho (pointSubgroup_stable S.rationalCurve p L hstable)

/-- 点の移送を戻すと、構成済みの同じresidualOddKernelPointMapになる。 -/
theorem residual_descended_kernel_pointMap_transport (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) (P : Points S.rationalCurve) :
    pointModelEquiv (S.residual_descended_kernel_model_map L hline hstable)
      (S.residualDescendedKernelPointMap hp2 L hline hstable P) =
        S.residualOddKernelPointMap hp2 L hline P := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact descendedKernelPointMap_transport S.rationalCurve _ _ _ P

/-- 降下後も同じ全点関数の零ファイバーはH。 -/
theorem residual_descended_kernel_pointMap_eq_zero_iff (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L) (P : Points S.rationalCurve) :
    S.residualDescendedKernelPointMap hp2 L hline hstable P = 0 ↔
      P ∈ pointSubgroup S.rationalCurve p L := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact descendedKernelPointMap_eq_zero_iff S.rationalCurve _ _ _ P

/-- 同じ全点関数の実際のGalois同変性。加法性のproviderは要求しない。 -/
theorem residual_descended_kernel_pointMap_equivariant (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hstable : IsStable S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) (P : Points S.rationalCurve) :
    S.residualDescendedKernelPointMap hp2 L hline hstable (pointAction S.rationalCurve σ P) =
      pointAction (S.residualDescendedKernelModel L hline hstable) σ
        (S.residualDescendedKernelPointMap hp2 L hline hstable P) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact descendedKernelPointMap_equivariant S.rationalCurve _ _ _ σ P

/-- Cofixedなら同じ全点関数の像をℚ有理点として構成できる。
零判定も同じLで行う。p倍で消えるという主張を付け加えない。 -/
theorem exists_rational_residual_kernel_image (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hL : IsCofixedOn S.residualRepresentation L) (P : S.ResidualSpace) :
    ∃ R : (S.residualDescendedKernelModel L hline hL.isStable).toAffine.Point,
      baseChangePoint _ R = S.residualDescendedKernelPointMap hp2 L hline hL.isStable P.val ∧
      (R = 0 ↔ P ∈ L) := by
  let := S.finite_residualPointSubgroup L hline
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  exact exists_rational_image_of_cofixed S.rationalCurve p L _ hL P

/-- 同じCofixed直線があれば、その外の残余点から非零ℚ有理像が実際に得られる。
幾何学的次元2から核外点を内部供給する。これは有理捩れ点の存在とは区別する。 -/
theorem exists_nonzero_rational_residual_kernel_image (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ (P : S.ResidualSpace)
      (R : (S.residualDescendedKernelModel L hline hL.isStable).toAffine.Point),
      P ∉ L ∧ R ≠ 0 ∧
        baseChangePoint _ R = S.residualDescendedKernelPointMap hp2 L hline hL.isStable P.val := by
  have ht := ((proper_nonzero_iff_finrank_one (finrank_torsion_prime S.rationalCurve p) L).mpr hline).2
  obtain ⟨P, _, hP⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr ht)
  obtain ⟨R, he, hz⟩ := S.exists_rational_residual_kernel_image hp2 L hline hL P
  exact ⟨P, R, hP, fun h => hP (hz.mp h), he⟩

end DkMath.FLT.Frey.Source
