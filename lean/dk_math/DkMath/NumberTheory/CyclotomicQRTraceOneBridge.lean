/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRGaussNormalization
import DkMath.NumberTheory.TraceOneDiscriminantAxis
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.CyclotomicQRTraceOneBridge"

namespace DkMath.NumberTheory.CyclotomicQRTraceOneBridge

open scoped BigOperators

open DkMath.CosmicFormula
open DkMath.NumberTheory.CyclotomicQRProduct
open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.CyclotomicQRGaussNormalization
open DkMath.NumberTheory.CyclotomicQRIntegralDescent
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

/-! ## The integral homogeneous shell -/

/-- The integral homogeneous degree-`p` prime cyclotomic shell. -/
def primeCyclotomicShellPoly (p : ℕ) : MvPolynomial (Fin 2) ℤ :=
  ∑ k ∈ Finset.range p,
    MvPolynomial.X 0 ^ k * MvPolynomial.X 1 ^ (p - 1 - k)

theorem eval_primeCyclotomicShellPoly
    (p : ℕ) (z y : ℤ) :
    MvPolynomial.eval ![z, y] (primeCyclotomicShellPoly p) =
      GTailCyclotomicShell p (z - y) y := by
  simp [primeCyclotomicShellPoly, GTailCyclotomicShell, sub_add_cancel]

theorem map_primeCyclotomicShellPoly_eq_qr_mul_qnr
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    MvPolynomial.map (algebraMap ℤ L) (primeCyclotomicShellPoly p) =
      qrFactorPoly (p := p) ζ * qnrFactorPoly (p := p) ζ := by
  classical
  have hinj := rootPowerMap_injective_on_nonzero ζ hζ
  calc
    MvPolynomial.map (algebraMap ℤ L) (primeCyclotomicShellPoly p) =
        ∑ k ∈ Finset.range p,
          MvPolynomial.X 0 ^ k * MvPolynomial.X 1 ^ (p - 1 - k) := by
      simp [primeCyclotomicShellPoly]
    _ = ∏ μ ∈ primitiveRoots p L,
        (MvPolynomial.X 0 - MvPolynomial.C μ * MvPolynomial.X 1) :=
      (primitiveRoots_product_poly_eq_shell ζ hζ).symm
    _ = (nonzeroResidues p).prod
        (fun a => rootFactorPoly ζ a) := by
      rw [← rootPowerSet_eq_primitiveRoots ζ hζ]
      change ((nonzeroResidues p).image (fun a : ZMod p => ζ ^ a.val)).prod
          (fun μ => MvPolynomial.X (0 : Fin 2) -
            MvPolynomial.C μ * MvPolynomial.X (1 : Fin 2)) =
        (nonzeroResidues p).prod (fun a => rootFactorPoly ζ a)
      rw [Finset.prod_image hinj]
      rfl
    _ = qrFactorPoly (p := p) ζ * qnrFactorPoly (p := p) ζ := by
      rw [← qr_product_mul_qnr_product p (fun a => rootFactorPoly ζ a)]
      rfl

private theorem algebraMap_int_injective
    {L : Type*} [Field L] [Algebra ℚ L] :
    Function.Injective (algebraMap ℤ L) := by
  intro a b hab
  apply (Int.cast_injective : Function.Injective (algebraMap ℤ ℚ))
  apply (FaithfulSMul.algebraMap_injective ℚ L)
  change algebraMap ℚ L (algebraMap ℤ ℚ a) =
    algebraMap ℚ L (algebraMap ℤ ℚ b)
  rw [← IsScalarTower.algebraMap_apply ℤ ℚ L a,
    ← IsScalarTower.algebraMap_apply ℤ ℚ L b]
  exact hab

/-! ## The integral Gauss-form packet -/

theorem exists_integral_gauss_form
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2) (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ RZ SZ : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (algebraMap ℤ L) RZ = Rpoly (p := p) ζ ∧
      MvPolynomial.C 4 * primeCyclotomicShellPoly p =
        RZ ^ 2 - MvPolynomial.C (signedPrimeDiscriminant p) * SZ ^ 2 ∧
      MvPolynomial.C (quadraticGauss ζ hζ) *
          MvPolynomial.map (algebraMap ℤ L) SZ = Dpoly (p := p) ζ := by
  obtain ⟨RZ, hRZ⟩ := exists_Rpoly_over_int ζ hζ
  obtain ⟨SZ, hSZ⟩ := exists_Dpoly_over_gauss_int hp2 ζ hζ
  have hDsq :
      MvPolynomial.C (algebraMap ℤ L (signedPrimeDiscriminant p)) *
          (MvPolynomial.map (algebraMap ℤ L) SZ) ^ 2 =
        Dpoly (p := p) ζ ^ 2 := by
    calc
      MvPolynomial.C (algebraMap ℤ L (signedPrimeDiscriminant p)) *
          (MvPolynomial.map (algebraMap ℤ L) SZ) ^ 2 =
          MvPolynomial.C (quadraticGauss ζ hζ ^ 2) *
            (MvPolynomial.map (algebraMap ℤ L) SZ) ^ 2 := by
        rw [quadraticGauss_sq hp2 ζ hζ]
      _ = (MvPolynomial.C (quadraticGauss ζ hζ) *
          MvPolynomial.map (algebraMap ℤ L) SZ) ^ 2 := by
        simp only [mul_pow, MvPolynomial.C_pow]
      _ = Dpoly (p := p) ζ ^ 2 := by rw [hSZ]
  have hmapped :
      MvPolynomial.map (algebraMap ℤ L)
          (MvPolynomial.C 4 * primeCyclotomicShellPoly p) =
        MvPolynomial.map (algebraMap ℤ L)
          (RZ ^ 2 - MvPolynomial.C (signedPrimeDiscriminant p) * SZ ^ 2) := by
    calc
      MvPolynomial.map (algebraMap ℤ L)
          (MvPolynomial.C 4 * primeCyclotomicShellPoly p) =
          MvPolynomial.C 4 *
            (qrFactorPoly (p := p) ζ * qnrFactorPoly (p := p) ζ) := by
        rw [map_mul, MvPolynomial.map_C]
        rw [map_primeCyclotomicShellPoly_eq_qr_mul_qnr ζ hζ]
        norm_num
      _ = Rpoly (p := p) ζ ^ 2 - Dpoly (p := p) ζ ^ 2 := by
        rw [Rpoly, Dpoly]
        have hC4 : MvPolynomial.C (4 : L) =
            (4 : MvPolynomial (Fin 2) L) :=
          MvPolynomial.C_eq_coe_nat 4
        rw [hC4]
        ring
      _ = MvPolynomial.map (algebraMap ℤ L)
          (RZ ^ 2 - MvPolynomial.C (signedPrimeDiscriminant p) * SZ ^ 2) := by
        rw [map_sub, map_pow, map_mul, MvPolynomial.map_C]
        rw [hRZ, map_pow, hDsq]
  refine ⟨RZ, SZ, hRZ, ?_, hSZ⟩
  apply MvPolynomial.map_injective (algebraMap ℤ L)
    (algebraMap_int_injective (L := L))
  exact hmapped

/-! ## Characteristic-two parity -/

private theorem signedPrimeDiscriminant_mod_two
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (signedPrimeDiscriminant p : ZMod 2) = 1 := by
  change (signedPrimeDiscriminant p : ZMod 2) = ((1 : ℤ) : ZMod 2)
  apply (ZMod.intCast_eq_intCast_iff _ _ 2).2
  rw [Int.modEq_iff_dvd]
  have hmod := signedPrimeDiscriminant_mod_four hp hp2
  have hdecomp := Int.mul_ediv_add_emod (signedPrimeDiscriminant p - 1) 4
  refine ⟨-2 * ((signedPrimeDiscriminant p - 1) / 4), ?_⟩
  omega

private theorem add_self_eq_zero_modTwo
    (T : MvPolynomial (Fin 2) (ZMod 2)) : T + T = 0 := by
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_zero]
  have htwo : (2 : ZMod 2) = 0 := by
    change ((2 : ℤ) : ZMod 2) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  calc
    MvPolynomial.coeff d T + MvPolynomial.coeff d T =
        (2 : ZMod 2) * MvPolynomial.coeff d T := by ring
    _ = 0 := by rw [htwo, zero_mul]

theorem map_modTwo_eq_of_integral_gauss_form
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (RZ SZ : MvPolynomial (Fin 2) ℤ)
    (hform : MvPolynomial.C 4 * primeCyclotomicShellPoly p =
      RZ ^ 2 - MvPolynomial.C (signedPrimeDiscriminant p) * SZ ^ 2) :
    MvPolynomial.map (Int.castRingHom (ZMod 2)) RZ =
      MvPolynomial.map (Int.castRingHom (ZMod 2)) SZ := by
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  let R₂ := MvPolynomial.map φ RZ
  let S₂ := MvPolynomial.map φ SZ
  have hmap := congrArg (MvPolynomial.map φ) hform
  have hD : (signedPrimeDiscriminant p : ZMod 2) = 1 :=
    signedPrimeDiscriminant_mod_two (Fact.out : p.Prime) hp2
  have hsquares : R₂ ^ 2 = S₂ ^ 2 := by
    have hmap' := hmap
    simp only [map_sub, map_pow, map_mul, MvPolynomial.map_C] at hmap'
    have hD' : φ (signedPrimeDiscriminant p) = 1 := by
      simpa [φ] using hD
    have hzero : φ 4 = 0 := by
      change ((4 : ℤ) : ZMod 2) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      norm_num
    rw [hD', hzero] at hmap'
    have hzero' : (0 : MvPolynomial (Fin 2) (ZMod 2)) =
        R₂ ^ 2 - S₂ ^ 2 := by
      simpa [R₂, S₂] using hmap'
    exact sub_eq_zero.mp hzero'.symm
  have hsum_sq : (R₂ + S₂) ^ 2 = 0 := by
    calc
      (R₂ + S₂) ^ 2 = R₂ ^ 2 + S₂ ^ 2 := by
        calc
          (R₂ + S₂) ^ 2 = R₂ ^ 2 + (R₂ * S₂ + R₂ * S₂) + S₂ ^ 2 := by ring
          _ = R₂ ^ 2 + S₂ ^ 2 := by
            have hcross := add_self_eq_zero_modTwo (R₂ * S₂)
            rw [hcross, add_zero]
      _ = 0 := by
        rw [hsquares]
        have hself := add_self_eq_zero_modTwo (S₂ ^ 2)
        exact hself
  have hsum : R₂ + S₂ = 0 := eq_zero_of_pow_eq_zero hsum_sq
  have hneg : -S₂ = S₂ := by
    apply MvPolynomial.ext
    intro d
    simp only [MvPolynomial.coeff_neg]
    exact ZMod.neg_eq_self_mod_two _
  have hRS : R₂ = S₂ := by
    calc
      R₂ = R₂ + 0 := by simp
      _ = R₂ + (S₂ + S₂) := by
        have hself := add_self_eq_zero_modTwo S₂
        rw [hself, add_zero]
      _ = (R₂ + S₂) + S₂ := by ring
      _ = S₂ := by rw [hsum, zero_add]
  simpa [R₂, S₂] using hRS

/-! ## Division-free half-coordinate extraction -/

private def halfOf (c : ℤ) : ℤ :=
  if h : (2 : ℤ) ∣ c then Classical.choose h else 0

private theorem halfOf_spec {c : ℤ} (hc : (2 : ℤ) ∣ c) :
    c = 2 * halfOf c := by
  unfold halfOf
  split
  · rename_i h
    exact Classical.choose_spec h
  · contradiction

private theorem halfOf_zero : halfOf 0 = 0 := by
  simp [halfOf]

theorem exists_half_difference
    (RZ SZ : MvPolynomial (Fin 2) ℤ)
    (hmod2 : MvPolynomial.map (Int.castRingHom (ZMod 2)) RZ =
      MvPolynomial.map (Int.castRingHom (ZMod 2)) SZ) :
    ∃ AZ : MvPolynomial (Fin 2) ℤ,
      RZ = MvPolynomial.C 2 * AZ + SZ := by
  classical
  have hdiv (d : Fin 2 →₀ ℕ) :
      (2 : ℤ) ∣ MvPolynomial.coeff d RZ - MvPolynomial.coeff d SZ := by
    have hd := congrArg (MvPolynomial.coeff d) hmod2
    have hz :
        ((MvPolynomial.coeff d RZ - MvPolynomial.coeff d SZ : ℤ) : ZMod 2) = 0 := by
      have hd' :
          ((MvPolynomial.coeff d RZ : ℤ) : ZMod 2) =
            ((MvPolynomial.coeff d SZ : ℤ) : ZMod 2) := by
        simpa [MvPolynomial.coeff_map] using hd
      change (Int.castRingHom (ZMod 2))
        (MvPolynomial.coeff d RZ - MvPolynomial.coeff d SZ) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hd'
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  let AZ : MvPolynomial (Fin 2) ℤ :=
    .ofCoeff <| Finsupp.mapRange halfOf halfOf_zero <|
      AddMonoidAlgebra.coeff (RZ - SZ)
  have hcoeff_AZ (d : Fin 2 →₀ ℕ) :
      MvPolynomial.coeff d AZ =
        halfOf (MvPolynomial.coeff d (RZ - SZ)) := by
    change (Finsupp.mapRange halfOf halfOf_zero
      (AddMonoidAlgebra.coeff (RZ - SZ))) d = _
    rfl
  have hcoeff_diff (d : Fin 2 →₀ ℕ) :
      MvPolynomial.coeff d (RZ - SZ) =
        MvPolynomial.coeff d RZ - MvPolynomial.coeff d SZ := by
    simp
  have hhalf (d : Fin 2 →₀ ℕ) :
      MvPolynomial.coeff d RZ - MvPolynomial.coeff d SZ =
        2 * MvPolynomial.coeff d AZ := by
    rw [hcoeff_AZ, hcoeff_diff]
    exact halfOf_spec (hdiv d)
  refine ⟨AZ, ?_⟩
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul]
  linear_combination hhalf d

/-! ## The arbitrary-prime TraceOne bridge -/

/-- The complete provenance packet for the arbitrary-prime TraceOne
coordinates.

The older existential API below intentionally exposes only the two integer
coordinate polynomials and their norm identity.  This packet keeps the
integral Gauss-form witnesses and the characteristic-two half extraction
which produced those coordinates, so later cyclotomic arguments can inspect
the construction rather than receiving an opaque norm endpoint. -/
structure PrimeTraceOneCoordinatePacket
    (L : Type*) [Field L] [Algebra ℚ L]
    (p : ℕ) [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) where
  RZ : MvPolynomial (Fin 2) ℤ
  SZ : MvPolynomial (Fin 2) ℤ
  AZ : MvPolynomial (Fin 2) ℤ
  map_RZ :
    MvPolynomial.map (algebraMap ℤ L) RZ = Rpoly (p := p) ζ
  gauss_form :
    MvPolynomial.C 4 * primeCyclotomicShellPoly p =
      RZ ^ 2 - MvPolynomial.C (signedPrimeDiscriminant p) * SZ ^ 2
  gauss_difference :
    MvPolynomial.C (quadraticGauss ζ hζ) *
        MvPolynomial.map (algebraMap ℤ L) SZ = Dpoly (p := p) ζ
  half_relation :
    RZ = MvPolynomial.C 2 * AZ + SZ
  norm_eq :
    ∀ z y : ℤ,
      norm
          (⟨MvPolynomial.eval ![z, y] AZ,
             MvPolynomial.eval ![z, y] SZ⟩ :
            TraceOneInt (signedPrimeParameter p)) =
        GTailCyclotomicShell p (z - y) y

/-- Evaluate the retained arbitrary-prime TraceOne coordinates. -/
def PrimeTraceOneCoordinatePacket.coord
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    TraceOneInt (signedPrimeParameter p) :=
  ⟨MvPolynomial.eval ![z, y] P.AZ,
    MvPolynomial.eval ![z, y] P.SZ⟩

theorem PrimeTraceOneCoordinatePacket.coord_norm_eq
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) (z y : ℤ) :
    norm (P.coord z y) = GTailCyclotomicShell p (z - y) y :=
  P.norm_eq z y

/-- The QR/QNR/Gauss construction supplies a complete provenance packet. -/
theorem exists_prime_traceOne_coordinate_packet
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2) (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    Nonempty (PrimeTraceOneCoordinatePacket L p ζ hζ) := by
  obtain ⟨RZ, SZ, hRZ, hform, hSZ⟩ :=
    exists_integral_gauss_form hp2 ζ hζ
  obtain ⟨AZ, hAZ⟩ := exists_half_difference RZ SZ
    (map_modTwo_eq_of_integral_gauss_form hp2 RZ SZ hform)
  refine ⟨{
    RZ := RZ
    SZ := SZ
    AZ := AZ
    map_RZ := hRZ
    gauss_form := hform
    gauss_difference := hSZ
    half_relation := hAZ
    norm_eq := ?_ }⟩
  intro z y
  let A : ℤ := MvPolynomial.eval ![z, y] AZ
  let S : ℤ := MvPolynomial.eval ![z, y] SZ
  let R : ℤ := MvPolynomial.eval ![z, y] RZ
  have hR : R = 2 * A + S := by
    simpa [R, A, S] using congrArg (MvPolynomial.eval ![z, y]) hAZ
  have hform_eval := congrArg (MvPolynomial.eval ![z, y]) hform
  have hform_int :
      4 * GTailCyclotomicShell p (z - y) y =
        R ^ 2 - signedPrimeDiscriminant p * S ^ 2 := by
    simpa [R, S, eval_primeCyclotomicShellPoly,
      GTailCyclotomicShell, sub_add_cancel] using hform_eval
  apply norm_eq_of_gauss_coordinates hR
  simpa [discr_signedPrimeParameter (Fact.out : p.Prime) hp2] using hform_int

theorem exists_prime_traceOne_coordinates
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2) (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ AZ SZ : MvPolynomial (Fin 2) ℤ,
      ∀ z y : ℤ,
        norm
          (⟨MvPolynomial.eval ![z, y] AZ,
             MvPolynomial.eval ![z, y] SZ⟩ :
            TraceOneInt (signedPrimeParameter p)) =
          GTailCyclotomicShell p (z - y) y := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet hp2 ζ hζ
  exact ⟨P.AZ, P.SZ, P.norm_eq⟩

end

end DkMath.NumberTheory.CyclotomicQRTraceOneBridge
