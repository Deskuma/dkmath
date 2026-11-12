import DkMath.FLT.FreyFiniteKernelGlobal

#print "file: Note032GlobalFibersSmoke"

/-! 同じSource37と同じ残余直線に、全ファイバー・全射性・主因子保存を接続する。 -/
namespace Note032GlobalFibersSmoke
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticTorsionRepresentation
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance (S : Source 37) : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じSource37の全点関数は、同じ標的の全点へ全射。 -/
theorem source37_surjective (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) :
    Function.Surjective (S.residualOddKernelPointMap (by decide) L hline) :=
  S.residual_odd_kernel_pointMap_surjective (by decide) L hline

/-- 同じSource37の全てのファイバーは、同じH剰余類である。 -/
theorem source37_fiber_relation (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (P R : Points S.rationalCurve) :
    S.residualOddKernelPointMap (by decide) L hline P =
      S.residualOddKernelPointMap (by decide) L hline R ↔ R - P ∈ pointSubgroup S.rationalCurve 37 L :=
  S.residual_odd_kernel_pointMap_eq_iff_sub_mem (by decide) L hline P R

/-- 零点以外も含めて、同じ標的の各点のファイバーの位数は37。 -/
theorem source37_fiber_card (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (T : (S.residualKernelModel L hline).toAffine.Point) :
    Nat.card {P : Points S.rationalCurve // S.residualOddKernelPointMap (by decide) L hline P = T} = 37 :=
  S.card_residual_odd_kernel_fiber (by decide) L hline T

/-- 同じSource37の主因子は、同じ標的の主因子へ輸送される。 -/
theorem source37_principal_transport (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hline : Module.finrank (ZMod 37) L = 1) (D : Points S.rationalCurve →₀ ℤ)
    (hD : ValuationDivisor.IsPrincipal (pointValuation S.rationalCurve) D) :
    ValuationDivisor.IsPrincipal (S.residualKernelTargetValuation (by decide) L hline)
      (S.residualKernelDivisorPush (by decide) L hline D) :=
  S.residual_kernel_divisor_push_isPrincipal (by decide) L hline D hD

end Note032GlobalFibersSmoke
