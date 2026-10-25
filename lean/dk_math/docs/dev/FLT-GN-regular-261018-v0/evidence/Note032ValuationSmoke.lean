import DkMath.FLT.FreyFiniteKernelValuation

#print "file: Note032ValuationSmoke"

/-! 同じSource37の全点関数・同じ引き戻し・同じ軌道積の局所比較。 -/
namespace Note032ValuationSmoke
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open scoped BigOperators
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance (S : Source 37) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- Source37の全点で、同じ関数体引き戻しは正規化付値を保存する。 -/
theorem source37_allpoint (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (P : Points S.rationalCurve)
    (g : (S.residualKernelModel L hline).toAffine.FunctionField) :
    pointValuation S.rationalCurve P (S.residualKernelModelPull L hline g) =
      S.residualKernelTargetValuation (by decide) L hline
        (S.residualOddKernelPointMap (by decide) L hline P) g :=
  S.residual_kernel_model_pull_valuation_all (by decide) L hline P g

/-- 源のOでの比較は、同じ標的のOでの比較になる。 -/
theorem source37_infinity (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1)
    (g : (S.residualKernelModel L hline).toAffine.FunctionField) :
    pointValuation S.rationalCurve 0 (S.residualKernelModelPull L hline g) =
      S.residualKernelTargetValuation (by decide) L hline 0 g := by
  have hz : S.residualOddKernelPointMap (by decide) L hline 0 = 0 :=
    (S.residual_odd_kernel_pointMap_eq_zero_iff (by decide) L hline 0).mpr
      (pointSubgroup S.rationalCurve 37 L).zero_mem
  have h := source37_allpoint S L hline 0 g
  rw [hz] at h
  exact h

/-- Source37の軌道積位数公式。源の核上の点も含み、局所倍率のproviderは不要。 -/
theorem source37_norm (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (P : Points S.rationalCurve)
    (f : (S.rationalCurve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField) (hf : f ≠ 0) :
    -log (S.residualKernelTargetValuation (by decide) L hline
      (S.residualOddKernelPointMap (by decide) L hline P) (S.residualKernelModelNorm L hline f)) =
      (let _ := S.finite_residualPointSubgroup L hline
       let _ := Fintype.ofFinite (pointSubgroup S.rationalCurve 37 L)
       ∑ Q : pointSubgroup S.rationalCurve 37 L, pointOrder S.rationalCurve (P + Q.val) f hf) :=
  S.residual_kernel_model_norm_order_all (by decide) L hline P f hf

end Note032ValuationSmoke
