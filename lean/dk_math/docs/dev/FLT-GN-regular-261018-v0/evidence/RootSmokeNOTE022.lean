import DkMath

#print "file: RootSmokeNOTE022"

/-! NOTE-022: ルートから、実際のファイバー総和・主性・非零生成元・商へ到達する。 -/
#check DkMath.Lib.Algebra.FiniteTorsionSum.sum_kernel_eq_zero
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiber_finite
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.sum_fiber
#check DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal.isPrincipal_prod_XYIdeal_zpow_iff
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberIdeal_isPrincipal_iff
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.sum_fiber
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.fiberIdeal_isPrincipal_iff
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilFunction_ne_zero

open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

example {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) (T : Points E) :
    (fiberIdeal E n hn T).IsPrincipal ↔ n • T = 0 := fiberIdeal_isPrincipal_iff E n hn T

example {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) :
    ∃ f : (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing,
      f ≠ 0 ∧ Ideal.span {f} = fiberIdeal E n hn T :=
  ⟨weilNumerator E n hn T hT, weilNumerator_ne_zero E n hn T hT, span_weilNumerator E n hn T hT⟩

example (S : DkMath.FLT.Frey.Source 2) :
    (fiberSet S.rationalCurve 37 0).ncard = 1369 := S.curve_fiber_card 37 (by decide) 0

example (S : DkMath.FLT.Frey.Source 2) :
    S.curve_weilFunction 1 (by decide) 0 (smul_zero _) ≠ 0 :=
  S.curve_weilFunction_ne_zero 1 (by decide) 0 (smul_zero _)
