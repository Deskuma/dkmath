import DkMath

#print "file: RootSmokeNOTE024"

/-! NOTE-024: ルートから次数・無限遠点・全点付値輸送へ到達する。 -/
#check DkMath.Lib.NumberTheory.EllipticPointIdealNorm.natDegree_norm_of_span_eq_prod
#check DkMath.Lib.NumberTheory.EllipticInfinityValuation.valuationInfty
#check DkMath.Lib.NumberTheory.EllipticFunctionField.valuation_placeOf_neg_transEquiv
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointValuation_transEquiv
#check DkMath.FLT.Frey.Source.curve_weilFunction_pointOrder_transEquiv
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.normDegree_weilNumerator
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_transEquiv_weilFunction_of_torsion

open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.NumberTheory.EllipticFunctionField

open Classical in
example {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) (T : Points E) (hT : n • T = 0) (P S : Points E) :
    pointOrder E P (transEquiv E (AlgebraicClosure K) S (weilFunction E n hn T hT))
      ((transEquiv E (AlgebraicClosure K) S).toRingEquiv.map_ne_zero_iff.mpr
        (weilFunction_ne_zero E n hn T hT)) =
      (if n • (P + S) = T then 1 else 0) - (if n • (P + S) = 0 then 1 else 0) :=
  pointOrder_transEquiv_weilFunction E n hn T hT P S
