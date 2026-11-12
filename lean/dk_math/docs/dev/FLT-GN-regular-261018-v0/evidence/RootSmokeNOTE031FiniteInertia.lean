import DkMath

#print "file: RootSmokeNOTE031FiniteInertia"

/-! NOTE-031-001A: 通常入口から有限ガロア段階の算術と同じ側の輸送へ到達する。 -/
#check DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.fixedField_unramifiedAt_int_of_inertia_le
#check DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.fixedField_finrank_eq_one_of_inertia_le
#check DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.subgroup_eq_top_of_inertia_le
#check DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.iSup_inertia_eq_top
#check DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.isFixedOn_of_inertia
#check DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.isCofixedOn_of_inertia
#check DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.fixed_or_cofixed_of_inertia_common_side

#print axioms DkMath.Lib.NumberTheory.NumberFieldInertiaGeneration.iSup_inertia_eq_top
#print axioms DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.isCofixedOn_of_inertia

open scoped NumberField
open DkMath.Lib.RepresentationTheory LocalFixedCofixed

example {K R V : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    [CommRing R] [AddCommGroup V] [Module R V]
    (ρ : Representation R (K ≃ₐ[ℚ] K) V) (N : Submodule R V)
    (hlocal : ∀ P : Ideal (𝓞 K), P.IsMaximal → CofixedOn ρ N (P.inertia (K ≃ₐ[ℚ] K))) :
    IsCofixedOn ρ N :=
  DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation.isCofixedOn_of_inertia ρ N hlocal
