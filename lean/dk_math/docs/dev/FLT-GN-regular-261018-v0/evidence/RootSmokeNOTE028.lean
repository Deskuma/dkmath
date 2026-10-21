import DkMath

#print "file: RootSmokeNOTE028"

/-! NOTE-028: ルートからA・B・Cと対データ入力なしの円分行列式へ到達する。 -/
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finiteDimensional_finrank_multiplicationPull
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationRange_eq_torsionFixedField
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.valuation_multiplicationPull_le
#check DkMath.FLT.Frey.Source.residual_geometricWeilPairingData
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.finiteDimensional_finrank_multiplicationPull
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.multiplicationRange_eq_torsionFixedField
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.weilAlternatingBicharacter_nondegenerate_right
#print axioms DkMath.FLT.Frey.Source.residual_determinant_eq_cyclotomic

open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicRootModule

example {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : n ≠ 0) (T : Torsion E n)
    (hT : ∀ S, weilAlternatingBicharacter E n hn S T = 1) : T = 0 :=
  weilAlternatingBicharacter_nondegenerate_right E n hn T hT

example (S : DkMath.FLT.Frey.Source 37) :
    letI : Fact (Nat.Prime 37) := ⟨by decide⟩
    S.residualDeterminantCharacter = cyclotomicCharacter 37 := by
  let : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact S.residual_determinant_eq_cyclotomic
