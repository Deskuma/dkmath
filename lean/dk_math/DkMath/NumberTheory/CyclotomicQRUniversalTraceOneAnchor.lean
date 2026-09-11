/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRTraceOneBridge
import DkMath.NumberTheory.CyclotomicQRUniversalTransport

#print "file: DkMath.NumberTheory.CyclotomicQRUniversalTraceOneAnchor"

namespace DkMath.NumberTheory.CyclotomicQRUniversalTraceOneAnchor

open DkMath.NumberTheory.CyclotomicQRProduct
open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.CyclotomicQRUniversalTransport

noncomputable section

/-! ## Anchoring the Phase-22 `RZ` witness -/

/-- The Phase-22 integral `RZ` witness becomes the universal QR/QNR sum after
embedding its integer coefficients into the universal cyclotomic carrier. -/
theorem phase22_RZ_anchor_eq_universal
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ) :
    MvPolynomial.map
        (AdjoinRoot.of (Polynomial.cyclotomic p ℤ)) P.RZ =
      universalRpoly p := by
  apply MvPolynomial.map_injective (charZeroAnchorMap ζ hζ)
    (charZeroAnchorMap_injective hζ)
  have hcomp :
      (charZeroAnchorMap ζ hζ).comp
          (AdjoinRoot.of (Polynomial.cyclotomic p ℤ)) =
        algebraMap ℤ L := by
    ext z
    simp [charZeroAnchorMap, specializePrimitiveRoot, specializeRoot]
  calc
    MvPolynomial.map (charZeroAnchorMap ζ hζ)
        (MvPolynomial.map
          (AdjoinRoot.of (Polynomial.cyclotomic p ℤ)) P.RZ) =
        MvPolynomial.map
          ((charZeroAnchorMap ζ hζ).comp
            (AdjoinRoot.of (Polynomial.cyclotomic p ℤ))) P.RZ := by
      rw [MvPolynomial.map_map]
    _ = MvPolynomial.map (algebraMap ℤ L) P.RZ := by rw [hcomp]
    _ = Rpoly (p := p) ζ := P.map_RZ
    _ = MvPolynomial.map (charZeroAnchorMap ζ hζ) (universalRpoly p) := by
      symm
      exact map_universalRpoly (charZeroAnchorMap ζ hζ) ζ
        (charZeroAnchorMap_zeta hζ)

/-- The anchored Phase-22 `RZ` identity specializes to every primitive root
in characteristic `q` away from the exponent prime. -/
theorem packet_RZ_map_eq_Rpoly_of_primitive_root
    {L K : Type*} [Field L] [Algebra ℚ L]
    [Field K] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [IsCyclotomicExtension {p} ℚ L] [CharP K q]
    (hpq : q ≠ p) {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (ξ : K) (hξ : IsPrimitiveRoot ξ p) :
    MvPolynomial.map (Int.castRingHom K) P.RZ =
      Rpoly (p := p) ξ := by
  have hcomp :
      (positiveCharSpecializeRoot hpq ξ hξ).comp
          (AdjoinRoot.of (Polynomial.cyclotomic p ℤ)) =
        Int.castRingHom K := by
    ext z
    simp [positiveCharSpecializeRoot, specializePrimitiveRoot,
      specializeRoot]
  have hanchored := congrArg
    (MvPolynomial.map (positiveCharSpecializeRoot hpq ξ hξ))
    (phase22_RZ_anchor_eq_universal P)
  calc
    MvPolynomial.map (Int.castRingHom K) P.RZ =
        MvPolynomial.map (positiveCharSpecializeRoot hpq ξ hξ)
          (MvPolynomial.map
            (AdjoinRoot.of (Polynomial.cyclotomic p ℤ)) P.RZ) := by
      rw [MvPolynomial.map_map, hcomp]
    _ = MvPolynomial.map (positiveCharSpecializeRoot hpq ξ hξ)
        (universalRpoly p) := hanchored
    _ = Rpoly (p := p) ξ :=
      map_universalRpoly_positiveChar hpq ξ hξ

end

end DkMath.NumberTheory.CyclotomicQRUniversalTraceOneAnchor
