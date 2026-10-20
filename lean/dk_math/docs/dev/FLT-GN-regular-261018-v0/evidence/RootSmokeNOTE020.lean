import DkMath

#print "file: RootSmokeNOTE020"

/-! NOTE-020: 同じ実際の素数冪ねじれ点の自由性と、加法群の非分裂性をルートから確認する。 -/
#check DkMath.Lib.Algebra.TorsionPowerLifting.lifted_pair_generates
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerEquiv
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerBasis
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePower_finrank
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerTransition_equivariant
#check DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.prime_square_no_additive_section
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.primePowerEquiv
#print axioms DkMath.Lib.NumberTheory.EllipticTorsionRepresentation.prime_square_not_product

open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example (E : WeierstrassCurve ℚ) [E.IsElliptic] (k : ℕ) :
    Nonempty (Torsion E (37 ^ k) ≃ₗ[ZMod (37 ^ k)] (Fin 2 → ZMod (37 ^ k))) :=
  ⟨primePowerEquiv E 37 k⟩

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Module.finrank (ZMod (37 ^ 3)) (Torsion E (37 ^ 3)) = 2 := primePower_finrank E 37 2

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ Nonempty (Torsion E (37 * 37) ≃+ (Torsion E 37 × Torsion E 37)) := prime_square_not_product E 37

example (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ s : Torsion E 37 →+ Torsion E (37 * 37), Function.RightInverse s (torsionMultiply E 37 37) :=
  prime_square_no_additive_section E 37

example (S : DkMath.FLT.Frey.Source 2) :
    Module.Free (ZMod (37 ^ 2)) (Torsion S.rationalCurve (37 ^ 2)) := S.curve_primePower_free 37 2
