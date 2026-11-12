import DkMath

#print "file: RootSmokeNOTE021"

/-! NOTE-021: ルートimportから実際の座標環・一般点・平行移動・有限場所へ到達する。 -/
#check DkMath.Lib.NumberTheory.EllipticCoordinateRing.isDedekindDomain
#check DkMath.Lib.NumberTheory.EllipticFunctionField.genericPoint
#check DkMath.Lib.NumberTheory.EllipticFunctionField.pointHom_injective_of_ne_baseChange
#check DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv
#check DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv_injective
#check DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_surjective
#check DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_injective
#print axioms DkMath.Lib.NumberTheory.EllipticCoordinateRing.isDedekindDomain
#print axioms DkMath.Lib.NumberTheory.EllipticFunctionField.transEquiv
#print axioms DkMath.Lib.NumberTheory.EllipticFunctionField.placeOf_surjective

open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory
open EllipticFunctionField

example {K : Type*} [Field K] [IsAlgClosed K] (E : WeierstrassCurve K) [E.IsElliptic] :
    IsDedekindDomain E.toAffine.CoordinateRing := EllipticCoordinateRing.isDedekindDomain

example {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsElliptic] (P Q : (E⁄K).Point) :
    transEquiv E K (P + Q) = (transEquiv E K Q).trans (transEquiv E K P) :=
  transEquiv_add E K P Q

example (S : DkMath.FLT.Frey.Source 37) :
    IsDedekindDomain (S.rationalCurve⁄(AlgebraicClosure ℚ)).CoordinateRing :=
  S.geometricCoordinateRing_isDedekindDomain

example (S : DkMath.FLT.Frey.Source 2) : Function.Injective S.functionFieldTranslation :=
  S.functionFieldTranslation_injective
