import DkMath

#print "file: RootSmokeNOTE025"

/-! NOTE-025: ルートから定数復元・同じ関数の固有方程式・μₙ指標へ到達する。 -/
#check DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants.existsUnique_unit_of_valuation_eq_one
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_scalar_of_pointOrder_eq
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_spec
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_rescaled_numerators
#check DkMath.FLT.Frey.Source.curve_weilTranslationCharacter
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_weilTranslationUnit
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationCharacter

open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

noncomputable example {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) (T : Torsion E n) :
    AddChar (Torsion E n) (rootsOfUnity n (AlgebraicClosure K)) :=
  weilTranslationCharacter E n hn T

example {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) (T S : Torsion E n) : weilTranslationUnit E n hn T S ^ n = 1 :=
  weilTranslationUnit_pow E n hn T S
