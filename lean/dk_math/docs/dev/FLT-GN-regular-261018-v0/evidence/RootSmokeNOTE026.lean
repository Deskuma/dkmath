import DkMath

#print "file: RootSmokeNOTE026"

/-! NOTE-026: ルートから同じ関数の右加法性・軌道積・交代的双指標へ到達する。 -/
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add_right
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.pointOrder_weilTranslateOrbitProduct
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.transEquiv_weilFunction_self
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_swap
#check DkMath.FLT.Frey.Source.curve_weilAlternatingBicharacter
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_add_right
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilTranslationUnit_self

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

noncomputable example {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) :
    AddChar (Torsion E n) (AddChar (Torsion E n) (rootsOfUnity n (AlgebraicClosure K))) :=
  weilAlternatingBicharacter E n hn

example {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) (T : Torsion E n) : weilAlternatingBicharacter E n hn T T = 1 :=
  weilAlternatingBicharacter_self E n hn T
