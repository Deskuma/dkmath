import DkMath

#print "file: RootSmokeNOTE023"

/-! NOTE-023: ルートから同じ座標環・場所・分子・商の有限点付値へ到達する。 -/
#check DkMath.Lib.NumberTheory.EllipticPointIdealValuation.intValuation_of_span_eq_prod
#check DkMath.Lib.NumberTheory.EllipticPointIdealValuation.intValuation_generator_independent
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointValuation
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointOrder_div
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_weilNumerator
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.order_weilFunction

open WeierstrassCurve WeierstrassCurve.Affine WithZero
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

open Classical in
example {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) (P : Points E) (hP : P ≠ 0) :
    finitePointOrder E P hP (weilFunction E n hn T hT) (weilFunction_ne_zero E n hn T hT) =
      (if n • P = T then 1 else 0) - (if n • P = 0 then 1 else 0) :=
  order_weilFunction E n hn T hT P hP

open Classical in
example (S : DkMath.FLT.Frey.Source 2) (T : Points S.rationalCurve) (hT : 2 • T = 0)
    (P : Points S.rationalCurve) (hP : P ≠ 0) :
    letI := S.rationalCurve_isElliptic
    finitePointOrder S.rationalCurve P hP (S.curve_weilFunction 2 (by decide) T hT)
      (S.curve_weilFunction_ne_zero 2 (by decide) T hT) =
      (if 2 • P = T then 1 else 0) - (if 2 • P = 0 then 1 else 0) :=
  S.curve_weilFunction_order 2 (by decide) T hT P hP
