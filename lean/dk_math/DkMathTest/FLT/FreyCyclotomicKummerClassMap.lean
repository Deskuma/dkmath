/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerClassMap

namespace DkMathTest.FLT.FreyCyclotomicKummerClassMap

open DkMath.Lib.NumberTheory CyclotomicKummerWeight KummerSelmerClassMap KummerSelmerExact
open DkMath.Lib.Algebra IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section

private theorem sign_class_ne_one : ((-1 : ℤˣ) : UnitClass ℤ 2) ≠ 1 := by
  intro h
  obtain ⟨u, hu⟩ := (QuotientGroup.eq_one_iff (-1 : ℤˣ)).mp h
  change u ^ 2 = -1 at hu
  have hz := congrArg (fun a : ℤˣ => (a : ℤ)) hu
  change (u : ℤ) ^ 2 = -1 at hz
  nlinarith [sq_nonneg (u : ℤ)]

private def signSelmer : Selmer ℤ ℚ 2 :=
  IsDedekindDomain.selmerGroup.fromUnit (K := ℚ) (n := 2) (-1 : ℤˣ)

private theorem sign_selmer_ne_one : signSelmer ≠ 1 := by
  intro h
  apply sign_class_ne_one
  apply unitInclusion_injective (R := ℤ) (F := ℚ) 2 (by decide)
  rw [unitInclusion_mk, map_one]
  exact h

-- A zero class-group image does NOT imply a zero Selmer class: the actual unit -1 survives.
example : signSelmer ≠ 1 ∧ toClassTorsion 2 (by decide) signSelmer = 1 := by
  refine ⟨sign_selmer_ne_one, Subtype.ext ?_⟩
  exact (toClassGroup_eq_one_iff_unit 2 (by decide) signSelmer).mpr ⟨-1, rfl⟩

-- The same nontrivial sign class can be represented by -4, and returns an actual unit-times-square.
example : ∃ (u : ℤˣ) (d : ℚˣ), (-4 : ℚ) = algebraMap ℤ ℚ u * (d : ℚ) ^ 2 := by
  let c : ℚˣ := Units.mk0 2 (by decide)
  let y : ℚˣ := Units.map (algebraMap ℤ ℚ).toMonoidHom (-1 : ℤˣ)
  let x : ℚˣ := c ^ 2 * y
  have hx : (x : KummerClass ℚ 2) = signSelmer.val := by
    change ((c ^ 2 * y : ℚˣ) : KummerClass ℚ 2) = (y : KummerClass ℚ 2)
    have hcq : ((c ^ 2 : ℚˣ) : KummerClass ℚ 2) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨c, rfl⟩
    rw [QuotientGroup.mk_mul, hcq, one_mul]
  have hz : toClassGroup 2 (by decide) signSelmer = 1 :=
    (toClassGroup_eq_one_iff_unit 2 (by decide) signSelmer).mpr ⟨-1, rfl⟩
  obtain ⟨u, d, he⟩ := unit_decomposition 2 (by decide) signSelmer hz x hx
  have hval : (x : ℚ) = -4 := by norm_num [x, c, y]
  refine ⟨u, d, ?_⟩
  have hh := congrArg Units.val he
  change (x : ℚ) = algebraMap ℤ ℚ u * (d : ℚ) ^ 2 at hh
  exact hval.symm.trans hh

-- At exponent 1 the whole Selmer group is trivial, as the positive-exponent API permits.
example (z : Selmer ℤ ℚ 1) : z = 1 := by
  apply Subtype.ext
  obtain ⟨x, he⟩ := QuotientGroup.mk'_surjective (powerSubgroup ℚˣ 1) z.val
  change (x : KummerClass ℚ 1) = z.val at he
  rw [← he]
  exact (QuotientGroup.eq_one_iff x).mpr ⟨x, pow_one x⟩

private def twoPlace : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(2 : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by decide : (2 : ℤ) ≠ 0)).mpr
    (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 2))
  ne_bot := by simp only [ne_eq, Ideal.span_singleton_eq_bot]; decide

-- At exponent 0 distinct nonzero ideals have the same power; the positivity guard is essential.
example : ∃ I J : (FractionalIdeal ℤ⁰ ℚ)ˣ, I ≠ J ∧ I ^ 0 = J ^ 0 := by
  let c : ℚˣ := Units.mk0 2 (by decide)
  let I := toPrincipalIdeal ℤ ℚ c
  refine ⟨I, 1, ?_, by rw [pow_zero, pow_zero]⟩
  intro h
  have hc : (I : FractionalIdeal ℤ⁰ ℚ) = (twoPlace.asIdeal : FractionalIdeal ℤ⁰ ℚ) := by
    rw [coe_toPrincipalIdeal]
    exact (FractionalIdeal.coeIdeal_span_singleton (2 : ℤ)).symm
  have hh := congrArg (fun J : (FractionalIdeal ℤ⁰ ℚ)ˣ => FractionalIdeal.count ℚ twoPlace J.val) h
  change FractionalIdeal.count ℚ twoPlace (I : FractionalIdeal ℤ⁰ ℚ) =
    FractionalIdeal.count ℚ twoPlace 1 at hh
  rw [hc, FractionalIdeal.count_self, FractionalIdeal.count_one] at hh
  exact (by decide : (1 : ℤ) ≠ 0) hh

#print axioms KummerSelmerClassMap.rootIdeal_pow
#print axioms KummerSelmerClassMap.idealUnits_pow_injective
#print axioms KummerSelmerClassMap.rootIdeal_change_representative
#print axioms KummerSelmerClassMap.rootClass_independent
#print axioms KummerSelmerClassMap.rootIdeal_mul
#print axioms KummerSelmerClassMap.toClassGroup
#print axioms KummerSelmerClassMap.toClassGroup_pow
#print axioms KummerSelmerClassMap.toClassTorsionLinear
#print axioms KummerSelmerExact.principal_of_class_eq_one
#print axioms KummerSelmerExact.toClassGroup_eq_one_iff_unit
#print axioms KummerSelmerExact.unit_decomposition
#print axioms KummerSelmerExact.unitInclusion_injective
#print axioms KummerSelmerExact.kernel_eq_unit_range
#print axioms KummerSelmerExact.toClassTorsion_surjective
#print axioms KummerSelmerExact.short_exact
#print axioms CyclotomicKummerClassMap.classImage_via_root
#print axioms CyclotomicKummerClassMap.rescale_classImage
#print axioms CyclotomicKummerClassMap.unit_of_classImage_eq_one
#print axioms DkMath.FLT.Frey.Source.residual_kummer_unit_of_classImage_eq_one

end
end DkMathTest.FLT.FreyCyclotomicKummerClassMap
