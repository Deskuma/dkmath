import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareGaloisSupport
import DkMath.FLT.Seven.SevenRealCubicAxisDrop
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Localization.FractionRing

open scoped NumberField
open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt
open Polynomial

#check IsLocalization.ringEquivOfRingEquiv
#check IsLocalization.ringEquivOfRingEquiv_eq
#check IsFractionRing.injective
#check IsGalois.of_separable_splitting_field
#check Normal.of_isSplittingField
#check Polynomial.dvd_iff_isRoot
#check Polynomial.Splits.of_dvd
#check Polynomial.Splits.X_sub_C
#check Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
#check Ideal.ramificationIdxIn_ne_zero
#check Ideal.inertiaDegIn_ne_zero
#check IsGalois.card_aut_eq_finrank
#check IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
#check IsFractionRing.ringHom_ext
#check IsFractionRing.div_surjective
#check AdjoinRoot.eval₂_root
#check AdjoinRoot.isRoot_root
#check Polynomial.IsRoot.def
#check PowerBasis.adjoin_gen_eq_top
#check Algebra.adjoin_le
#check Algebra.adjoin_le_iff

namespace DkMath.FLT.Seven

noncomputable section

abbrev O := 𝓞 SevenRealCubic.Field

noncomputable def scratchFieldRotateRingEquiv :
    SevenRealCubic.Field ≃+* SevenRealCubic.Field :=
  IsFractionRing.ringEquivOfRingEquiv
    SevenRealCubic.ringOfIntegersRotateEquiv

noncomputable def scratchFieldRotateEquiv :
    SevenRealCubic.Field ≃ₐ[ℚ] SevenRealCubic.Field :=
  { scratchFieldRotateRingEquiv with
    commutes' := by
      intro q
      simp [map_ratCast scratchFieldRotateRingEquiv q] }

namespace scratch

abbrev theta0 : SevenRealCubic.Field := SevenRealCubic.powerBasis.gen

theorem theta0_root :
    (SevenRealCubic.polynomialQ.map (algebraMap ℚ SevenRealCubic.Field)).IsRoot
      theta0 := by
  change (Polynomial.map (AdjoinRoot.of SevenRealCubic.polynomialQ)
    SevenRealCubic.polynomialQ).IsRoot
      (AdjoinRoot.root SevenRealCubic.polynomialQ)
  exact AdjoinRoot.isRoot_root SevenRealCubic.polynomialQ

theorem map_root (e : SevenRealCubic.Field ≃ₐ[ℚ] SevenRealCubic.Field)
    {x : SevenRealCubic.Field}
    (hx : (SevenRealCubic.polynomialQ.map
      (algebraMap ℚ SevenRealCubic.Field)).IsRoot x) :
    (SevenRealCubic.polynomialQ.map
      (algebraMap ℚ SevenRealCubic.Field)).IsRoot (e x) := by
  rw [Polynomial.IsRoot.def] at hx ⊢
  have hm := Polynomial.IsRoot.map (f := e.toRingEquiv.toRingHom) hx
  rw [Polynomial.IsRoot.def] at hm
  rw [← Polynomial.eval₂_eq_eval_map] at hm ⊢
  rw [Polynomial.eval₂_map] at hm
  have he : e.toRingEquiv.toRingHom.comp (algebraMap ℚ
      SevenRealCubic.Field) = algebraMap ℚ SevenRealCubic.Field := by
    ext q
    exact e.commutes q
  rw [he] at hm
  exact hm

theorem theta0_root_aeval :
    (Polynomial.aeval theta0 SevenRealCubic.polynomialQ) = 0 := by
  rw [Polynomial.aeval_def]
  change Polynomial.eval₂ (AdjoinRoot.of SevenRealCubic.polynomialQ)
    (AdjoinRoot.root SevenRealCubic.polynomialQ) SevenRealCubic.polynomialQ = 0
  exact AdjoinRoot.eval₂_root SevenRealCubic.polynomialQ

theorem theta0_mem_rootSet :
    theta0 ∈ SevenRealCubic.polynomialQ.rootSet SevenRealCubic.Field := by
  rw [Polynomial.mem_rootSet]
  exact ⟨SevenRealCubic.polynomialQ_ne_zero, theta0_root_aeval⟩

theorem adjoin_theta0_rootSet_le :
    Algebra.adjoin ℚ ({theta0} : Set SevenRealCubic.Field) ≤
      Algebra.adjoin ℚ (SevenRealCubic.polynomialQ.rootSet SevenRealCubic.Field) := by
  apply Algebra.adjoin_le
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact Algebra.subset_adjoin theta0_mem_rootSet

theorem algEquiv_eq_refl_of_gen_fix
    (e : SevenRealCubic.Field ≃ₐ[ℚ] SevenRealCubic.Field)
    (hfix : e theta0 = theta0) :
    e = (AlgEquiv.refl : SevenRealCubic.Field ≃ₐ[ℚ] SevenRealCubic.Field) := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨p, rfl⟩ := SevenRealCubic.powerBasis.exists_eq_aeval' x
  have he : (algebraMap ℚ SevenRealCubic.Field).comp (RingHom.id ℚ) =
      e.toRingHom.comp (algebraMap ℚ SevenRealCubic.Field) := by
    ext q
    exact (e.commutes q).symm
  have hm := Polynomial.map_aeval_eq_aeval_map
    (R := ℚ) (φ := RingHom.id ℚ) (ψ := e.toRingHom) he p theta0
  simp only [Polynomial.map_id] at hm
  have hfix' : e.toRingEquiv.toRingHom theta0 = theta0 := hfix
  rw [hfix'] at hm
  simpa using hm

abbrev theta1 : SevenRealCubic.Field := scratchFieldRotateEquiv theta0

abbrev theta2 : SevenRealCubic.Field := scratchFieldRotateEquiv theta1

theorem theta1_root :
    (SevenRealCubic.polynomialQ.map (algebraMap ℚ SevenRealCubic.Field)).IsRoot
      theta1 :=
  map_root scratchFieldRotateEquiv theta0_root

theorem theta1_ne_theta0 : theta1 ≠ theta0 := by
  intro h
  apply SevenRealCubic.fieldRotateEquiv_ne_one
  exact algEquiv_eq_refl_of_gen_fix scratchFieldRotateEquiv h

theorem polynomialQ_map_splits :
    (SevenRealCubic.polynomialQ.map
      (algebraMap ℚ SevenRealCubic.Field)).Splits := by
  let p0 := SevenRealCubic.polynomialQ.map
    (algebraMap ℚ SevenRealCubic.Field)
  let l0 : SevenRealCubic.Field[X] := Polynomial.X - Polynomial.C theta0
  let l1 : SevenRealCubic.Field[X] := Polynomial.X - Polynomial.C theta1
  have hp0 : p0.IsRoot theta0 := by
    simpa [p0] using theta0_root
  have hdiv0 : l0 ∣ p0 := by
    exact (Polynomial.dvd_iff_isRoot).mpr hp0
  obtain ⟨q1, hq1⟩ := hdiv0
  have hq1root : q1.IsRoot theta1 := by
    have hprod : p0.eval theta1 = 0 := by
      simpa [p0] using theta1_root
    rw [hq1, eval_mul] at hprod
    have hl0 : l0.eval theta1 ≠ 0 := by
      simpa [l0, sub_eq_zero] using theta1_ne_theta0
    exact (mul_eq_zero.mp hprod).resolve_left hl0
  have hq1monic : q1.Monic := by
    apply Monic.of_mul_monic_left
      (monic_X_sub_C theta0)
    rw [← hq1]
    exact (SevenRealCubic.polynomialQ_monic.map _)
  have hq1deg : q1.natDegree = 2 := by
    have hdeg : p0.natDegree = 3 := by
      dsimp [p0]
      rw [Polynomial.natDegree_map]
      rw [SevenRealCubic.polynomialQ,
        Polynomial.natDegree_map_eq_of_injective
          (algebraMap ℤ ℚ).injective_int]
      exact SevenRealCubicInt.eisensteinPolynomial_natDegree
    rw [hq1, natDegree_mul (monic_X_sub_C theta0).ne_zero hq1monic.ne_zero,
      natDegree_X_sub_C] at hdeg
    omega
  have hq1split : q1.Splits :=
    Polynomial.Splits.of_natDegree_eq_two hq1deg
      (Polynomial.IsRoot.def.mp hq1root)
  change p0.Splits
  rw [hq1]
  exact (Polynomial.Splits.X_sub_C theta0).mul hq1split

end scratch

end
end DkMath.FLT.Seven
