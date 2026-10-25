/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedCyclotomic
import DkMath.Lib.NumberTheory.EllipticCofixedImage

#print "file: DkMath.FLT.FreyCofixedImage"

/-!
# NOTE-032-005C₁: 同じFrey核候補の像から、標的の有理捩れへ

同じSourceの残余直線Lを核とする実点準同型φが入力されたとき、
同じφ(E[p])は位数pとなる。大域Cofixed性とガロア同変性を入力すれば、
標的E'に実際の非零ℚ有理p捩れ点が得られる。

標的E'、写像φ、核の一致、同変性は未構成の入力であり、商曲線やisogenyの存在を
供給したとはしない。元のSourceの有理捩れ排除を別曲線E'へ流用しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 同じSourceの残余直線を正確に核とする実点写像のp捩れ像は位数pである。 -/
theorem card_residual_pointMap_image (E' : WeierstrassCurve ℚ)
    (φ : Points S.rationalCurve →+ Points E')
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hker : φ.ker = pointSubgroup S.rationalCurve p L) :
    Nat.card (LinearMap.range (torsionPointMap S.rationalCurve E' p φ)) = p := by
  have := S.rationalCurve_isElliptic
  exact card_torsionPointMap_range S.rationalCurve E' p φ L hline hker

/-- 同じCofixed核の同変実点写像から、標的上の非零ℚ有理p捩れ点を得る。
元P∉Lと同じφ(P)への等式を保持する。写像の存在や幾何学的性質は結論に含めない。 -/
theorem exists_rational_torsion_of_cofixed_residual_pointMap (E' : WeierstrassCurve ℚ)
    (φ : Points S.rationalCurve →+ Points E')
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hker : φ.ker = pointSubgroup S.rationalCurve p L)
    (hφ : ∀ σ P, φ (pointAction S.rationalCurve σ P) = pointAction E' σ (φ P))
    (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ (P : S.ResidualSpace) (Q : E'.toAffine.Point),
      P ∉ L ∧ p • Q = 0 ∧ Q ≠ 0 ∧ baseChangePoint E' Q = φ P.val := by
  have := S.rationalCurve_isElliptic
  exact exists_rational_torsion_of_cofixed_pointMap S.rationalCurve E' p φ L hline hker hφ hL

end DkMath.FLT.Frey.Source
