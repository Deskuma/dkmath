import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCanonicalCommonFactor
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareIdealSupport
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareTwistObstruction
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactor

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt
open scoped NumberField Pointwise

namespace DkMath.FLT.Seven.SevenRealCubic

noncomputable section

#check Ideal.absNorm_span_singleton
#check Ideal.absNorm_dvd_absNorm_of_le
#check Ideal.absNorm_eq_one_iff
#check Ideal.isCoprime_span_singleton_iff
#check IsCoprime.dvd_of_dvd_mul_right
#check IsCoprime.dvd_of_dvd_mul_left
#check Nat.Coprime.eq_one_of_dvd
#check Ideal.exists_le_maximal
#check Ideal.IsMaximal.ne_top
#check Ideal.absNorm_eq_zero_iff
#check Ideal.isMaximal_iff_isPrime
#check Ideal.isCoprime_iff_sup_eq
#check IsCoprime
#check IsCoprime.sup_eq
#check Ideal.span_singleton_eq_span_singleton
#check Associated
#check RingEquiv.toMonoidHom
#check Units.map
#check Ideal.span_singleton_mul_span_singleton
#check directOrbitSquareRefinement_absNorm_span_model
#check directOrbitSquareRefinement_principal_ideal_scalar_split
#check directOrbit_squareTwist_twisted_eq
#check directOrbit_norm_coprime_ideal_coprime
#check directOrbitTrivialCommonFactor_scalarIdealU
#check directOrbitTrivialCommonFactor_scalarIdealV
#check directOrbitTrivialCommonFactor_scalarIdealU_absNorm
#check directOrbitTrivialCommonFactor_scalarIdealV_absNorm
#check directOrbitTrivialCommonFactor_gapIdeal_absNorm_of_c_eq_one
#check directOrbitTrivialCommonFactor_quotientIdeal_absNorm_of_c_eq_one
#check directOrbitTrivialCommonFactor_cross_coprime
#check directOrbitTrivialCommonFactor_ideal_product_of_c_eq_one
#check directOrbitTrivialCommonFactor_ideal_eq_scalar_of_c_eq_one
#check directOrbitTrivialCommonFactor_gap_scalar_unit_of_c_eq_one
#check directOrbitTrivialCommonFactor_quotient_scalar_unit_of_c_eq_one
#check directOrbitTrivialCommonFactor_gap_rotate_scalar_unit
#check directOrbitTrivialCommonFactor_gap_twice_rotate_scalar_unit
#check directOrbitTrivialCommonFactor_unit_twisted_eq
#check thetaResidue_rotateEquiv
#check thetaConstModSeven
#check thetaLinearModSeven
#check thetaSquareModSeven

theorem r39_norm_coprime_ideal_coprime
    {S : Type} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S] [Infinite S]
    {I J : Ideal S}
    (hcop : Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm J))
    (_hI : I ≠ ⊥) (_hJ : J ≠ ⊥) :
    IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (I ⊔ J) htop
  have hMI : I ≤ M := le_sup_left.trans hle
  have hMJ : J ≤ M := le_sup_right.trans hle
  have hnormMI : Ideal.absNorm M ∣ Ideal.absNorm I :=
    Ideal.absNorm_dvd_absNorm_of_le hMI
  have hnormMJ : Ideal.absNorm M ∣ Ideal.absNorm J :=
    Ideal.absNorm_dvd_absNorm_of_le hMJ
  have hnormM_one : Ideal.absNorm M = 1 := by
    apply Nat.dvd_one.mp
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hnormMI hnormMJ
  exact hM.ne_top (Ideal.absNorm_eq_one_iff.mp hnormM_one)

theorem r39_theta_coordinates_cancel
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    thetaResidue
          ((directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt) *
            ((eta : SevenRealCubicInt) ^ 7) ^ 2) +
        thetaResidue
          ((directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt) *
            ((directOrbitRotateUnit eta : SevenRealCubicInt) ^ 7) ^ 2) +
        thetaResidue
          ((directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt) *
            ((directOrbitRotateUnit (directOrbitRotateUnit eta) :
              SevenRealCubicInt) ^ 7) ^ 2) = 0 ∧
      thetaLinearModSeven
          ((directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt) *
            ((eta : SevenRealCubicInt) ^ 7) ^ 2) +
        thetaLinearModSeven
          ((directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt) *
            ((directOrbitRotateUnit eta : SevenRealCubicInt) ^ 7) ^ 2) +
        thetaLinearModSeven
          ((directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt) *
            ((directOrbitRotateUnit (directOrbitRotateUnit eta) :
              SevenRealCubicInt) ^ 7) ^ 2) = 0 ∧
      thetaSquareModSeven
          ((directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt) *
            ((eta : SevenRealCubicInt) ^ 7) ^ 2) +
        thetaSquareModSeven
          ((directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt) *
            ((directOrbitRotateUnit eta : SevenRealCubicInt) ^ 7) ^ 2) +
        thetaSquareModSeven
          ((directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt) *
            ((directOrbitRotateUnit (directOrbitRotateUnit eta) :
              SevenRealCubicInt) ^ 7) ^ 2) = 0 := by
  have hunit := directOrbitTrivialCommonFactor_unit_twisted_eq h hc eta heta
  have hlinear_add (a b : SevenRealCubicInt) :
      thetaLinearModSeven (a + b) =
        thetaLinearModSeven a + thetaLinearModSeven b := by
    rcases a with ⟨a₀, a₁, a₂⟩
    rcases b with ⟨b₀, b₁, b₂⟩
    simp [thetaLinearModSeven]
    ring
  have hsquare_add (a b : SevenRealCubicInt) :
      thetaSquareModSeven (a + b) =
        thetaSquareModSeven a + thetaSquareModSeven b := by
    rcases a with ⟨a₀, a₁, a₂⟩
    rcases b with ⟨b₀, b₁, b₂⟩
    simp [thetaSquareModSeven]
  constructor
  · simpa only [map_add, map_zero] using congrArg thetaResidue hunit
  constructor
  · have hlinear := congrArg thetaLinearModSeven hunit
    rw [hlinear_add, hlinear_add] at hlinear
    simpa [thetaLinearModSeven] using hlinear
  · have hsquare := congrArg thetaSquareModSeven hunit
    rw [hsquare_add, hsquare_add] at hsquare
    simpa [thetaSquareModSeven] using hsquare

#print axioms r39_theta_coordinates_cancel

end
end DkMath.FLT.Seven.SevenRealCubic
