/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicRamifiedPrime
import DkMath.FLT.Seven.SevenRamifiedFusionDirectChartObstruction
import DkMath.FLT.Seven.SevenRamifiedFusionElementLevelOrientedPower
import DkMath.FLT.Seven.SevenRamifiedFusionGlobalOrientedPrimeFactorization

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicAdditiveChartBoundary"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

open scoped QuadraticAlgebra

namespace SevenCyclotomicDegreeSixInt

open SevenRealCubicInt

/-- The degree-six integral norm on the explicit cyclotomic carrier:
first take the quadratic norm to the real cubic order, then its integral
cubic norm. -/
def cyclotomicNormHom : Ring →* ℤ where
  toFun x := SevenRealCubicInt.norm (QuadraticAlgebra.norm x)
  map_one' := by
    norm_num [SevenRealCubicInt.norm, QuadraticAlgebra.norm]
  map_mul' x y := by
    rw [QuadraticAlgebra.norm.map_mul,
      SevenRealCubicInt.norm_mul]

@[simp] theorem cyclotomicNormHom_apply (x : Ring) :
    cyclotomicNormHom x =
      SevenRealCubicInt.norm (QuadraticAlgebra.norm x) :=
  rfl

@[simp] theorem cyclotomicNormHom_zero :
    cyclotomicNormHom (0 : Ring) = 0 := by
  norm_num [cyclotomicNormHom, SevenRealCubicInt.norm,
    QuadraticAlgebra.norm]

/-- The relative quadratic norm of `1 - zeta` is the negative real
Eisenstein axis. -/
theorem quadraticNorm_ramifiedUniformizer :
    QuadraticAlgebra.norm ramifiedUniformizer =
      -eisensteinAxis := by
  rw [QuadraticAlgebra.norm_def]
  ext <;>
    norm_num [ramifiedUniformizer, zeta, eisensteinAxis,
      alpha, SevenRealCubicInt.mul]

/-- The integral norm of the selected prime element above seven is exactly
seven. -/
theorem cyclotomicNormHom_ramifiedUniformizer :
    cyclotomicNormHom ramifiedUniformizer = 7 := by
  rw [cyclotomicNormHom_apply,
    quadraticNorm_ramifiedUniformizer]
  norm_num [SevenRealCubicInt.norm, eisensteinAxis]

/-- The integral norm is invariant under quadratic conjugation. -/
@[simp] theorem cyclotomicNormHom_star (x : Ring) :
    cyclotomicNormHom (star x) =
      cyclotomicNormHom x := by
  rw [cyclotomicNormHom_apply, cyclotomicNormHom_apply,
    QuadraticAlgebra.norm_star]

/-- The relative quadratic norm commutes with the order-three Galois
rotation. -/
theorem quadraticNorm_rotateEquiv (x : Ring) :
    QuadraticAlgebra.norm
        (SevenCyclotomicDegreeSixInt.rotateEquiv x) =
      SevenRealCubicInt.rotateEquiv
        (QuadraticAlgebra.norm x) := by
  rcases x with ⟨r, i⟩
  have hrotate :
      SevenCyclotomicDegreeSixInt.rotateEquiv
          (⟨r, i⟩ : Ring) =
        ⟨SevenRealCubicInt.rotateEquiv r -
            SevenRealCubicInt.rotateEquiv i,
          (SevenRealCubicInt.alpha - 1) *
            SevenRealCubicInt.rotateEquiv i⟩ :=
    rfl
  rw [hrotate, QuadraticAlgebra.norm_def,
    QuadraticAlgebra.norm_def]
  simp only [map_add, map_sub, map_mul, map_one,
    map_neg]
  rw [SevenRealCubicInt.rotateEquiv_alpha]
  ring

/-- The integral norm is invariant under the order-three Galois rotation. -/
@[simp] theorem cyclotomicNormHom_rotateEquiv (x : Ring) :
    cyclotomicNormHom
        (SevenCyclotomicDegreeSixInt.rotateEquiv x) =
      cyclotomicNormHom x := by
  rw [cyclotomicNormHom_apply, cyclotomicNormHom_apply,
    quadraticNorm_rotateEquiv,
    SevenRealCubicInt.norm_rotateEquiv]

/-- A unit in the degree-six carrier has integral norm `1` or `-1`.
This does not say that the unit is a seventh power. -/
theorem cyclotomicNormHom_eq_one_or_neg_one_of_isUnit
    {u : Ring} (hu : IsUnit u) :
    cyclotomicNormHom u = 1 ∨
      cyclotomicNormHom u = -1 :=
  Int.isUnit_iff.mp (hu.map cyclotomicNormHom)

/-- Product of the three quadratic-conjugate pairs in all six Galois
phases. -/
def sixPhaseProduct (x : Ring) : Ring :=
  (x * star x) *
    (SevenCyclotomicDegreeSixInt.rotateEquiv x *
      star (SevenCyclotomicDegreeSixInt.rotateEquiv x)) *
    (SevenCyclotomicDegreeSixInt.rotateEquiv
          (SevenCyclotomicDegreeSixInt.rotateEquiv x) *
      star
        (SevenCyclotomicDegreeSixInt.rotateEquiv
          (SevenCyclotomicDegreeSixInt.rotateEquiv x)))

/-- Multiplying all six Galois phases loses the oriented coordinates and
retains exactly the embedded integral norm. -/
theorem sixPhaseProduct_eq_ofReal_cyclotomicNorm
    (x : Ring) :
    sixPhaseProduct x =
      ofReal
        (cyclotomicNormHom x : SevenRealCubicInt) := by
  rw [sixPhaseProduct,
    ← QuadraticAlgebra.algebraMap_norm_eq_mul_star x,
    ← QuadraticAlgebra.algebraMap_norm_eq_mul_star
      (SevenCyclotomicDegreeSixInt.rotateEquiv x),
    ← QuadraticAlgebra.algebraMap_norm_eq_mul_star
      (SevenCyclotomicDegreeSixInt.rotateEquiv
        (SevenCyclotomicDegreeSixInt.rotateEquiv x))]
  rw [quadraticNorm_rotateEquiv,
    quadraticNorm_rotateEquiv,
    quadraticNorm_rotateEquiv]
  rw [← map_mul, ← map_mul,
    SevenRealCubicInt.mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm]
  rfl

/-- The zeroth integral coordinate is not multiplicative.  Thus the
rank-six additive coordinates cannot be applied componentwise to an
element-level seventh-power equation as if they were ring homomorphisms. -/
theorem zerothCoordinate_not_multiplicative :
    coordinates (zeta * zeta) 0 ≠
      coordinates zeta 0 * coordinates zeta 0 := by
  norm_num [coordinates, zeta]

/-- There is no unital ring homomorphism from the concrete cyclotomic
carrier to the integers.

Indeed, the image of the seventh root unit would be `1`, while total
ramification would then send the nonzero integer seven to zero.  This rules
out a naive multiplicative projection from a carrier power equation to
integer seventh powers; it does not rule out a genuinely new additive
reconstruction argument. -/
theorem no_ringHom_to_int :
    ¬ Nonempty (Ring →+* ℤ) := by
  rintro ⟨f⟩
  have hzetaUnit : IsUnit (f zeta) :=
    (show IsUnit zeta from ⟨zetaUnit, rfl⟩).map f
  have hzetaPow : f zeta ^ 7 = 1 := by
    rw [← map_pow, zeta_pow_seven, map_one]
  have hzeta : f zeta = 1 := by
    rcases Int.isUnit_iff.mp hzetaUnit with h | h
    · exact h
    · rw [h] at hzetaPow
      norm_num at hzetaPow
  have hseven :=
    congrArg f
      ofReal_seven_eq_uniformizer_pow_six_mul_unit
  simp only [map_mul, map_pow] at hseven
  have hleft :
      f (ofReal (7 : SevenRealCubicInt)) = 7 := by
    change f (7 : Ring) = 7
    exact map_intCast f 7
  have huniformizer :
      f ramifiedUniformizer = 0 := by
    rw [ramifiedUniformizer, map_sub, map_one, hzeta,
      sub_self]
  rw [hleft, huniformizer] at hseven
  norm_num at hseven

end SevenCyclotomicDegreeSixInt

namespace RamifiedSignedRootDepthPacket

open SevenRealCubicInt SevenCyclotomicDegreeSixInt

/-- The relative quadratic norm of `R - zeta L` is the zeroth real-pair
carrier. -/
theorem quadraticNorm_cyclotomicDegreeSixCarrier
    (p : RamifiedSignedRootDepthPacket) :
    QuadraticAlgebra.norm
        p.cyclotomicDegreeSixCarrier =
      p.realPairCarrier 0 := by
  simp [QuadraticAlgebra.norm_def,
    cyclotomicDegreeSixCarrier, ofReal, zeta,
    QuadraticAlgebra.algebraMap_eq, realPairCarrier,
    cyclicAlpha]
  ring

/-- The integral norm of the oriented carrier is the signed seventh
quotient, hence exactly `7 * quotientRoot`. -/
theorem cyclotomicNorm_cyclotomicDegreeSixCarrier
    (p : RamifiedSignedRootDepthPacket) :
    cyclotomicNormHom
        p.cyclotomicDegreeSixCarrier =
      7 * p.quotientRoot := by
  rw [cyclotomicNormHom_apply,
    p.quadraticNorm_cyclotomicDegreeSixCarrier,
    p.norm_realPairCarrier_zero,
    p.signedQuotient_eq]

/-- The product over all six phases of `R - zeta L` is exactly the
embedded signed seventh quotient. -/
theorem sixPhaseProduct_cyclotomicDegreeSixCarrier
    (p : RamifiedSignedRootDepthPacket) :
    sixPhaseProduct p.cyclotomicDegreeSixCarrier =
      ofReal
        ((7 * p.quotientRoot : ℤ) :
          SevenRealCubicInt) := by
  rw [sixPhaseProduct_eq_ofReal_cyclotomicNorm,
    p.cyclotomicNorm_cyclotomicDegreeSixCarrier]

/-- In the canonical integral basis, the oriented carrier has precisely
the two visible signed endpoint coordinates `[R,0,0,-L,0,0]`. -/
theorem cyclotomicDegreeSixCarrier_coordinates
    (p : RamifiedSignedRootDepthPacket) :
    coordinates p.cyclotomicDegreeSixCarrier 0 =
        p.signedRightRoot ∧
      coordinates p.cyclotomicDegreeSixCarrier 1 = 0 ∧
      coordinates p.cyclotomicDegreeSixCarrier 2 = 0 ∧
      coordinates p.cyclotomicDegreeSixCarrier 3 =
        -p.signedLeftRoot ∧
      coordinates p.cyclotomicDegreeSixCarrier 4 = 0 ∧
      coordinates p.cyclotomicDegreeSixCarrier 5 = 0 := by
  simp [coordinates, cyclotomicDegreeSixCarrier,
    ofReal, zeta, QuadraticAlgebra.algebraMap_eq]

/-- Any proposed element-level factorization of the oriented carrier must
land in the same two-coordinate slice; four integral coordinates of its
right-hand side must vanish. -/
theorem elementEquation_coordinate_packet
    (p : RamifiedSignedRootDepthPacket)
    {rhs : SevenCyclotomicDegreeSixInt.Ring}
    (h : p.cyclotomicDegreeSixCarrier = rhs) :
    coordinates rhs 0 = p.signedRightRoot ∧
      coordinates rhs 1 = 0 ∧
      coordinates rhs 2 = 0 ∧
      coordinates rhs 3 = -p.signedLeftRoot ∧
      coordinates rhs 4 = 0 ∧
      coordinates rhs 5 = 0 := by
  rw [← h]
  exact p.cyclotomicDegreeSixCarrier_coordinates

/-- Taking all six Galois phases of an abstract element equation yields
only this multiplicative integral norm identity. -/
theorem elementEquation_norm
    (p : RamifiedSignedRootDepthPacket)
    {u load root : SevenCyclotomicDegreeSixInt.Ring}
    (h :
      p.cyclotomicDegreeSixCarrier =
        u * load * root ^ 7) :
    7 * p.quotientRoot =
      cyclotomicNormHom u *
        cyclotomicNormHom load *
        cyclotomicNormHom root ^ 7 := by
  have hn := congrArg cyclotomicNormHom h
  simpa only [p.cyclotomicNorm_cyclotomicDegreeSixCarrier,
    map_mul, map_pow] using hn

/-- If the forced ramified uniformizer is displayed separately, its norm
seven cancels and the remaining equation is the quotient-root
load-times-seventh-power identity. -/
theorem ramifiedElementEquation_norm
    (p : RamifiedSignedRootDepthPacket)
    {u load root : SevenCyclotomicDegreeSixInt.Ring}
    (h :
      p.cyclotomicDegreeSixCarrier =
        u * ramifiedUniformizer * load * root ^ 7) :
    p.quotientRoot =
      cyclotomicNormHom u *
        cyclotomicNormHom load *
        cyclotomicNormHom root ^ 7 := by
  have hn := congrArg cyclotomicNormHom h
  simp only [p.cyclotomicNorm_cyclotomicDegreeSixCarrier,
    map_mul, map_pow,
    cyclotomicNormHom_ramifiedUniformizer] at hn
  apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
  calc
    7 * p.quotientRoot =
        cyclotomicNormHom u * 7 *
          cyclotomicNormHom load *
          cyclotomicNormHom root ^ 7 := hn
    _ = 7 *
        (cyclotomicNormHom u *
          cyclotomicNormHom load *
          cyclotomicNormHom root ^ 7) := by ring

/-- Exact boundary for the corrected U1.4 equation in which the ramified
factor and its associated unit remain absorbed in `load`.

The equation gives the sparse coordinate packet and one multiplicative norm
identity.  It still cannot reuse the visible endpoints as an additive Fermat
chart. -/
theorem loadedElementEquation_boundary
    (p : RamifiedSignedRootDepthPacket)
    {load root : SevenCyclotomicDegreeSixInt.Ring}
    (h :
      p.cyclotomicDegreeSixCarrier =
        load * root ^ 7) :
    (coordinates (load * root ^ 7) 0 =
        p.signedRightRoot ∧
      coordinates (load * root ^ 7) 1 = 0 ∧
      coordinates (load * root ^ 7) 2 = 0 ∧
      coordinates (load * root ^ 7) 3 =
        -p.signedLeftRoot ∧
      coordinates (load * root ^ 7) 4 = 0 ∧
      coordinates (load * root ^ 7) 5 = 0) ∧
      7 * p.quotientRoot =
        cyclotomicNormHom load *
          cyclotomicNormHom root ^ 7 ∧
      ¬ ∃ c : ℤ,
        SignedFermatSevenChart
          p.signedRightRoot (-p.signedLeftRoot) c := by
  have hnorm :
      7 * p.quotientRoot =
        cyclotomicNormHom load *
          cyclotomicNormHom root ^ 7 := by
    have h' :
        p.cyclotomicDegreeSixCarrier =
          (1 : SevenCyclotomicDegreeSixInt.Ring) *
            load * root ^ 7 := by
      simpa only [one_mul] using h
    simpa only [map_one, one_mul] using
      p.elementEquation_norm h'
  exact ⟨p.elementEquation_coordinate_packet h,
    hnorm, p.no_direct_signedFermatSevenChart⟩

/-- Exact additive-chart boundary of a ramified element equation.

The equation supplies the six coordinate conditions and the multiplicative
norm identity, but the same visible signed endpoints cannot form a Fermat
chart: their seventh-power difference has exact seven-adic depth five.
Therefore a later chart must provide genuinely new integer coordinates and
an independent additive compatibility theorem. -/
theorem ramifiedElementEquation_boundary
    (p : RamifiedSignedRootDepthPacket)
    {u load root : SevenCyclotomicDegreeSixInt.Ring}
    (h :
      p.cyclotomicDegreeSixCarrier =
        u * ramifiedUniformizer * load * root ^ 7) :
    (coordinates
          (u * ramifiedUniformizer * load * root ^ 7) 0 =
        p.signedRightRoot ∧
      coordinates
          (u * ramifiedUniformizer * load * root ^ 7) 1 = 0 ∧
      coordinates
          (u * ramifiedUniformizer * load * root ^ 7) 2 = 0 ∧
      coordinates
          (u * ramifiedUniformizer * load * root ^ 7) 3 =
        -p.signedLeftRoot ∧
      coordinates
          (u * ramifiedUniformizer * load * root ^ 7) 4 = 0 ∧
      coordinates
          (u * ramifiedUniformizer * load * root ^ 7) 5 = 0) ∧
      p.quotientRoot =
        cyclotomicNormHom u *
          cyclotomicNormHom load *
          cyclotomicNormHom root ^ 7 ∧
      ¬ ∃ c : ℤ,
        SignedFermatSevenChart
          p.signedRightRoot (-p.signedLeftRoot) c := by
  exact ⟨p.elementEquation_coordinate_packet h,
    p.ramifiedElementEquation_norm h,
    p.no_direct_signedFermatSevenChart⟩

end RamifiedSignedRootDepthPacket

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

open SevenCyclotomicDegreeSixInt

/-- U1.5 audit of the actual U1.4 choice-based element equation.

It records exactly what coefficient comparison and all-six-phase norm
multiplication recover.  The result contains no new additive seventh-power
identity: the direct visible-endpoint chart is formally excluded. -/
theorem orientedElementLevelPower_additiveBoundary
    (p : RamifiedSignedRootRoutingPacket) :
    (coordinates
          (orientedLoadElement p *
            orientedResidualRoot p ^ 7) 0 =
        p.signedDepth.signedRightRoot ∧
      coordinates
          (orientedLoadElement p *
            orientedResidualRoot p ^ 7) 1 = 0 ∧
      coordinates
          (orientedLoadElement p *
            orientedResidualRoot p ^ 7) 2 = 0 ∧
      coordinates
          (orientedLoadElement p *
            orientedResidualRoot p ^ 7) 3 =
        -p.signedDepth.signedLeftRoot ∧
      coordinates
          (orientedLoadElement p *
            orientedResidualRoot p ^ 7) 4 = 0 ∧
      coordinates
          (orientedLoadElement p *
            orientedResidualRoot p ^ 7) 5 = 0) ∧
      7 * p.signedDepth.quotientRoot =
        cyclotomicNormHom (orientedLoadElement p) *
          cyclotomicNormHom (orientedResidualRoot p) ^ 7 ∧
      ¬ ∃ c : ℤ,
        SignedFermatSevenChart
          p.signedDepth.signedRightRoot
          (-p.signedDepth.signedLeftRoot) c :=
  p.signedDepth.loadedElementEquation_boundary
    (cyclotomicDegreeSixCarrier_eq_load_mul_residualRoot_pow p)

/-- The chosen oriented residual generator is nonzero. -/
theorem orientedResidualRoot_ne_zero
    (p : RamifiedSignedRootRoutingPacket) :
    orientedResidualRoot p ≠ 0 := by
  intro hzero
  have hcarrier :
      p.signedDepth.cyclotomicDegreeSixCarrier = 0 := by
    calc
      p.signedDepth.cyclotomicDegreeSixCarrier =
          orientedLoadElement p *
            orientedResidualRoot p ^ 7 :=
        cyclotomicDegreeSixCarrier_eq_load_mul_residualRoot_pow p
      _ = 0 := by rw [hzero]; norm_num
  have hnorm :=
    p.signedDepth.cyclotomicNorm_cyclotomicDegreeSixCarrier
  rw [hcarrier, cyclotomicNormHom_zero] at hnorm
  have hquotient : p.signedDepth.quotientRoot = 0 := by
    omega
  apply p.signedDepth.quotientRoot_not_seven_dvd
  rw [hquotient]
  exact dvd_zero 7

/-- Multiplication by the primitive seventh root genuinely changes the
nonzero residual generator. -/
theorem zeta_mul_orientedResidualRoot_ne
    (p : RamifiedSignedRootRoutingPacket) :
    zeta * orientedResidualRoot p ≠
      orientedResidualRoot p := by
  intro heq
  have hproduct :
      (zeta - 1) * orientedResidualRoot p = 0 := by
    calc
      (zeta - 1) * orientedResidualRoot p =
          zeta * orientedResidualRoot p -
            orientedResidualRoot p := by ring
      _ = 0 := sub_eq_zero.mpr heq
  rcases mul_eq_zero.mp hproduct with hzeta | hroot
  · exact zeta_ne_one (sub_eq_zero.mp hzeta)
  · exact orientedResidualRoot_ne_zero p hroot

/-- Nevertheless the primitive-root translate generates exactly the same
residual ideal. -/
theorem span_zeta_mul_orientedResidualRoot
    (p : RamifiedSignedRootRoutingPacket) :
    Ideal.span {zeta * orientedResidualRoot p} =
      Ideal.span {orientedResidualRoot p} :=
  Ideal.span_singleton_mul_left_unit
    (show IsUnit zeta from ⟨zetaUnit, rfl⟩)
    (orientedResidualRoot p)

/-- The primitive-root translate also has exactly the same seventh power,
so it satisfies the identical U1.4 carrier equation with the load element
unchanged. -/
theorem cyclotomicDegreeSixCarrier_eq_load_mul_zetaResidualRoot_pow
    (p : RamifiedSignedRootRoutingPacket) :
    p.signedDepth.cyclotomicDegreeSixCarrier =
      orientedLoadElement p *
        (zeta * orientedResidualRoot p) ^ 7 := by
  rw [mul_pow, zeta_pow_seven, one_mul]
  exact cyclotomicDegreeSixCarrier_eq_load_mul_residualRoot_pow p

/-- The two equally valid residual generators have different complete
integer-coordinate vectors. -/
theorem coordinates_zeta_mul_orientedResidualRoot_ne
    (p : RamifiedSignedRootRoutingPacket) :
    coordinates (zeta * orientedResidualRoot p) ≠
      coordinates (orientedResidualRoot p) := by
  intro hcoordinates
  exact zeta_mul_orientedResidualRoot_ne p
    (coordinates.injective hcoordinates)

/-- Exact `mu_7` gauge boundary of U1.4.

The ideal, seventh power, load element, and carrier equation do not select a
unique residual integer-coordinate vector.  Any U1.5 chart extractor must
either be invariant under this gauge or prove an additional phase
normalization. -/
theorem orientedResidualRoot_muSevenGaugeBoundary
    (p : RamifiedSignedRootRoutingPacket) :
    Ideal.span {zeta * orientedResidualRoot p} =
        globalOrientedResidualIdeal (p := p) ∧
      p.signedDepth.cyclotomicDegreeSixCarrier =
        orientedLoadElement p *
          (zeta * orientedResidualRoot p) ^ 7 ∧
      coordinates (zeta * orientedResidualRoot p) ≠
        coordinates (orientedResidualRoot p) := by
  exact
    ⟨(span_zeta_mul_orientedResidualRoot p).trans
        (span_orientedResidualRoot p),
      cyclotomicDegreeSixCarrier_eq_load_mul_zetaResidualRoot_pow p,
      coordinates_zeta_mul_orientedResidualRoot_ne p⟩

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

#print axioms
  SevenCyclotomicDegreeSixInt.sixPhaseProduct_eq_ofReal_cyclotomicNorm
#print axioms
  SevenCyclotomicDegreeSixInt.no_ringHom_to_int
#print axioms
  RamifiedSignedRootDepthPacket.cyclotomicNorm_cyclotomicDegreeSixCarrier
#print axioms
  RamifiedSignedRootDepthPacket.ramifiedElementEquation_boundary
#print axioms
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.orientedElementLevelPower_additiveBoundary
#print axioms
  RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.orientedResidualRoot_muSevenGaugeBoundary

end

end DkMath.FLT.Seven
