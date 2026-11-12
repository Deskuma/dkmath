/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreySplitDyadic
import DkMath.FLT.FreyGeometricWeilPairing
import DkMath.Lib.NumberTheory.EllipticCofixedCyclotomic

#print "file: DkMath.FLT.FreyCofixedCyclotomic"

/-!
# NOTE-032-005B: 同じFrey SourceのCofixed直線上の円分作用

一般核の「商が恒等なら直線上の作用は行列式倍」を、同じ実際のE[p]へ適用する。
同じ曲線の構成済みWeil対による円分行列式の同定を使い、
ρ(σ)P=χₚ(σ)Pを実際の点群の倍点としても公開する。
適合基底での行列は[χₚ,*;0,1]となる。右上成分を消去したとはしない。

005Aの候補L=E₀[p]と組み合わせ、Cofixed直線を仮定した同じ零成分上にも公式を運ぶ。
直線の存在・不存在、一般hno、商楕円曲線・isogeny・有理捩れの構成は本章の結論ではない。
特に、商の固定性から元の曲線の直線の各点が有理になるとは主張しない。
-/
namespace DkMath.FLT.Frey.Source
open Module DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicRootModule ValuationInertia
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 同じ残余表現のCofixed直線上の作用は、同じ作用素の行列式倍となる。 -/
theorem residual_cofixed_line_apply_eq_det_smul
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) {P : S.ResidualSpace} (hP : P ∈ L) :
    S.residualRepresentation σ P = LinearMap.det (S.residualRepresentation σ) • P := by
  have := S.rationalCurve_isElliptic
  exact CofixedDeterminant.apply_eq_det_smul_of_cofixed S.residualRepresentation L hline hcofixed σ hP

/-- 同じCofixed直線上の作用は円分スカラー倍。Weil対providerや合同条件は不要。
素数性と直線の次元・Cofixed性は明示したままである。 -/
theorem residual_cofixed_line_apply_eq_cyclotomic_smul
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) {P : S.ResidualSpace} (hP : P ∈ L) :
    S.residualRepresentation σ P = (cyclotomicCharacter p σ : ZMod p) • P := by
  have := S.rationalCurve_isElliptic
  exact cofixed_torsion_apply_eq_cyclotomic_smul S.rationalCurve p L hline hcofixed σ hP

/-- 同じ点を曲線の点群へ戻した倍点公式。円分指標の自然数代表を使う。 -/
theorem residual_cofixed_line_pointAction_eq_cyclotomic_nsmul
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) {P : S.ResidualSpace} (hP : P ∈ L) :
    pointAction S.rationalCurve σ P.val = (cyclotomicCharacter p σ : ZMod p).val • P.val := by
  have := S.rationalCurve_isElliptic
  exact cofixed_pointAction_eq_cyclotomic_nsmul S.rationalCurve p L hline hcofixed σ hP

/-- 同じ実点群内の位数pの核候補pointSubgroupにも円分倍点公式を供給する。
既存の巡回性・ガロア安定性と併用できる。商曲線の存在は未供給。 -/
theorem residual_cofixed_pointSubgroup_action_eq_cyclotomic_nsmul
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) {Q : Points S.rationalCurve}
    (hQ : Q ∈ pointSubgroup S.rationalCurve p L) :
    pointAction S.rationalCurve σ Q = (cyclotomicCharacter p σ : ZMod p).val • Q := by
  have := S.rationalCurve_isElliptic
  exact cofixed_pointSubgroup_action_eq_cyclotomic_nsmul S.rationalCurve p L hline hcofixed σ hQ

/-- Cofixed直線に適合する基底では、実際の行列が[χₚ,*;0,1]になる。
同じ行列の右上成分を保持し、分裂・対角化を仮定しない。 -/
theorem residual_cofixed_basis_matrix (b : Basis (Fin 2) (ZMod p) S.ResidualSpace)
    (hcofixed : IsCofixedOn S.residualRepresentation
      (Submodule.span (ZMod p) ({b 0} : Set S.ResidualSpace)))
    (σ : Field.absoluteGaloisGroup ℚ) :
    (S.residualGL2WithBasis b σ : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      !![(cyclotomicCharacter p σ : ZMod p),
        (S.residualGL2WithBasis b σ : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1; 0, 1] := by
  have hd := congrArg (fun χ : Field.absoluteGaloisGroup ℚ →* (ZMod p)ˣ => (χ σ : ZMod p))
    S.residual_determinant_eq_cyclotomic
  rw [S.residualDeterminantCharacter_val] at hd
  simpa only [residualGL2WithBasis, hd] using
    CofixedDeterminant.basis_line_matrix S.residualRepresentation b hcofixed σ

/-- 大域Cofixed直線が存在するという仮定の下で、同じE₀[p]上の作用も円分倍となる。
005AのL=E₀[p]を使用する。局所Cofixed性だけからこの大域公式を得たとはしない。 -/
theorem residualZeroComponent_apply_eq_cyclotomic_smul_of_cofixed_line (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) {P : S.ResidualSpace} (hP : P ∈ S.residualZeroComponent A) :
    S.residualRepresentation σ P = (cyclotomicCharacter p σ : ZMod p) • P := by
  have heq := S.residual_cofixed_line_eq_zeroComponent_at_two hp5 A hA L hline hcofixed
  exact S.residual_cofixed_line_apply_eq_cyclotomic_smul L hline hcofixed σ (heq.symm ▸ hP)

end DkMath.FLT.Frey.Source
