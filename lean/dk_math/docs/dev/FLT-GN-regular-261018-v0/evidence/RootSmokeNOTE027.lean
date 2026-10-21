import DkMath

#print "file: RootSmokeNOTE027"

/-! NOTE-027: ルートから半線形作用・付値輸送・同じ双指標の同変性へ到達する。 -/
#check DkMath.Lib.NumberTheory.EllipticFunctionField.galFunctionFieldEquiv
#check DkMath.Lib.NumberTheory.EllipticFunctionField.gal_transEquiv
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finitePointValuation_galois
#check DkMath.FLT.Frey.Source.curve_weilAlternatingBicharacter_residual
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.existsUnique_scalar_galois_weilFunction
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_galois

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

example {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) (σ : Field.absoluteGaloisGroup K) (S T : Torsion E n) :
    weilAlternatingBicharacter E n hn (representation E n σ S) (representation E n σ T) =
      galoisRootMap n σ (weilAlternatingBicharacter E n hn S T) :=
  weilAlternatingBicharacter_representation E n hn σ S T
