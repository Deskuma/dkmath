/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixDomain
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicSevenPID

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixPID"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

open Polynomial
open scoped NumberField

namespace SevenCyclotomicDegreeSixInt

/-- The displayed inverse root is the sixth power of the oriented primitive
seventh root. -/
theorem zetaInv_eq_pow_six :
    zetaInv = zeta ^ 6 := by
  have hzeta0 : zeta ≠ 0 := by
    intro hzeta
    have h := zeta_pow_seven
    rw [hzeta] at h
    norm_num at h
  apply mul_left_cancel₀ hzeta0
  rw [zeta_mul_zetaInv, mul_comm, ← pow_succ, zeta_pow_seven]

/-- Every real-cubic coordinate is an integral polynomial of degree at most
two in `alpha`. -/
private theorem real_coordinate_decomposition
    (x : SevenRealCubicInt) :
    x =
      (x.fst : SevenRealCubicInt) +
        (x.snd : SevenRealCubicInt) * SevenRealCubicInt.alpha +
        (x.thd : SevenRealCubicInt) * SevenRealCubicInt.alpha ^ 2 := by
  ext <;> simp [pow_two]

/-- Every element of the explicit quadratic carrier is its real coordinate
plus its imaginary coordinate times `zeta`. -/
theorem quadratic_coordinate_decomposition
    (x : Ring) :
    x = ofReal x.re + ofReal x.im * zeta := by
  ext <;> simp [ofReal, zeta, QuadraticAlgebra.algebraMap_eq]

/-- The concrete degree-six carrier is generated as a `ℤ`-algebra by its
oriented primitive seventh root `zeta`.

This is a statement about the explicit coordinate carrier. It does not identify
that carrier with a ring of integers. -/
theorem adjoin_zeta_eq_top :
    Algebra.adjoin ℤ ({zeta} : Set Ring) = ⊤ := by
  apply top_unique
  intro x hx
  let A : Subalgebra ℤ Ring :=
    Algebra.adjoin ℤ ({zeta} : Set Ring)
  have hzeta : zeta ∈ A :=
    Algebra.subset_adjoin (Set.mem_singleton zeta)
  have hzetaInv : zetaInv ∈ A := by
    rw [zetaInv_eq_pow_six]
    exact A.pow_mem hzeta 6
  have halpha : ofReal SevenRealCubicInt.alpha ∈ A := by
    rw [ofReal_alpha]
    exact A.add_mem (A.add_mem A.one_mem hzeta) hzetaInv
  have hofReal : ∀ y : SevenRealCubicInt, ofReal y ∈ A := by
    intro y
    rw [real_coordinate_decomposition y, map_add, map_add, map_mul,
      map_mul, map_pow]
    exact A.add_mem
      (A.add_mem
        (A.intCast_mem y.fst)
        (A.mul_mem (A.intCast_mem y.snd) halpha))
      (A.mul_mem (A.intCast_mem y.thd) (A.pow_mem halpha 2))
  rw [quadratic_coordinate_decomposition x]
  exact A.add_mem (hofReal x.re) (A.mul_mem (hofReal x.im) hzeta)

private abbrev AbstractField : Type :=
  CyclotomicField 7 ℚ

private instance abstractFieldIsCyclotomic :
    IsCyclotomicExtension {7} ℚ AbstractField :=
  CyclotomicField.isCyclotomicExtension 7 ℚ

private def abstractZeta : AbstractField :=
  IsCyclotomicExtension.zeta 7 ℚ AbstractField

private theorem abstractZeta_isPrimitiveRoot :
    IsPrimitiveRoot abstractZeta 7 :=
  IsCyclotomicExtension.zeta_spec 7 ℚ AbstractField

private def abstractIntegralPowerBasis :
    PowerBasis ℤ (𝓞 AbstractField) :=
  abstractZeta_isPrimitiveRoot.integralPowerBasis

private theorem abstractIntegralPowerBasis_minpoly :
    minpoly ℤ abstractIntegralPowerBasis.gen =
      cyclotomic 7 ℤ := by
  rw [abstractIntegralPowerBasis,
    IsPrimitiveRoot.integralPowerBasis_gen,
    ← NumberField.RingOfIntegers.minpoly_coe]
  change minpoly ℤ abstractZeta = cyclotomic 7 ℤ
  exact
    (cyclotomic_eq_minpoly
      abstractZeta_isPrimitiveRoot (by norm_num)).symm

private theorem zeta_aeval_abstractIntegralPowerBasis_minpoly :
    aeval zeta (minpoly ℤ abstractIntegralPowerBasis.gen) = 0 := by
  simpa [abstractIntegralPowerBasis_minpoly, aeval_def,
    eval₂_eq_eval_map, IsRoot.def] using
      zeta_isPrimitiveRoot.isRoot_cyclotomic (by norm_num)

/-- The power-basis map associated to Mathlib's chosen primitive root in the
abstract seventh cyclotomic field, sending that root to the concrete `zeta`. -/
def ringOfIntegersToRing :
    (𝓞 (CyclotomicField 7 ℚ)) →ₐ[ℤ] Ring :=
  abstractIntegralPowerBasis.lift
    zeta zeta_aeval_abstractIntegralPowerBasis_minpoly

/-- The power-basis map from the abstract seventh cyclotomic ring of integers
onto the explicit degree-six carrier is surjective.

Surjectivity, rather than a full ring-of-integers equivalence, is exactly what
is needed to transport principality. -/
theorem ringOfIntegersToRing_surjective :
    Function.Surjective ringOfIntegersToRing := by
  intro x
  have hx : x ∈ Algebra.adjoin ℤ ({zeta} : Set Ring) := by
    rw [adjoin_zeta_eq_top]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨f, rfl⟩ := hx
  refine ⟨aeval abstractIntegralPowerBasis.gen f, ?_⟩
  exact abstractIntegralPowerBasis.lift_aeval zeta
    zeta_aeval_abstractIntegralPowerBasis_minpoly f

/-- The explicit degree-six cyclotomic carrier is a principal ideal ring.

The proof transports the abstract cyclotomic-seven PID theorem along the
surjective power-basis map above. It does not assert that this map is injective
or that the concrete carrier is definitionally the full ring of integers. -/
noncomputable instance ringIsPrincipalIdealRing :
    IsPrincipalIdealRing Ring := by
  letI : IsPrincipalIdealRing (𝓞 AbstractField) :=
    CyclotomicSeven.ringOfIntegers_isPrincipalIdealRing AbstractField
  exact
    IsPrincipalIdealRing.of_surjective
      ringOfIntegersToRing.toRingHom
      ringOfIntegersToRing_surjective

/-- Concrete element extraction from a principal ideal seventh-power identity.

The residual unit is retained explicitly; this theorem makes no claim that an
arbitrary unit of the degree-six carrier is itself a seventh power. -/
theorem unitMulPowOfSpanEqPow
    {I : Ideal Ring} {a : Ring} {n : ℕ}
    (h : Ideal.span {a} = I ^ n) :
    ∃ u : Ring, IsUnit u ∧
      a = u * Submodule.IsPrincipal.generator I ^ n := by
  rw [← Ideal.span_singleton_generator I,
    Ideal.span_singleton_pow] at h
  have hassociated :
      Associated a (Submodule.IsPrincipal.generator I ^ n) :=
    (Ideal.span_singleton_eq_span_singleton).mp h
  rcases hassociated with ⟨u, hu⟩
  refine ⟨↑(u⁻¹), (u⁻¹).isUnit, ?_⟩
  calc
    a = a * ↑u * ↑(u⁻¹) := by simp [mul_assoc]
    _ = Submodule.IsPrincipal.generator I ^ n * ↑(u⁻¹) := by
      rw [hu]
    _ = ↑(u⁻¹) * Submodule.IsPrincipal.generator I ^ n := by
      rw [mul_comm]

#synth IsDomain Ring
#synth IsPrincipalIdealRing Ring

#print axioms zetaInv_eq_pow_six
#print axioms adjoin_zeta_eq_top
#print axioms ringOfIntegersToRing_surjective
#print axioms ringIsPrincipalIdealRing
#print axioms unitMulPowOfSpanEqPow

end SevenCyclotomicDegreeSixInt

end

end DkMath.FLT.Seven
