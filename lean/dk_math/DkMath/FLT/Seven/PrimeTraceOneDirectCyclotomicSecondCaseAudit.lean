/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedProvenance
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicConjugatePrimePair

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicSecondCaseAudit"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

open SevenRealCubicInt
open SevenCyclotomicDegreeSixInt

/-- The direct degree-six linear factor attached to the *same* ramified
summit carried by a primitive counterexample provenance.  This is an adapter
for the classical second-case factor `L - zeta R`; it does not construct a
second summit or use the old signed-root routing packet. -/
def directLinearFactor
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    SevenCyclotomicDegreeSixInt.Ring :=
  ofReal (r.summit.endpointLeft : SevenRealCubicInt) -
    zeta * ofReal (r.summit.endpointRight : SevenRealCubicInt)

/-- The real-cubic element obtained by multiplying the direct factor by its
quadratic conjugate. -/
def directRelativeNorm
    (left right : ℤ) : SevenRealCubicInt :=
  (left : SevenRealCubicInt) ^ 2 -
      (alpha - 1) * (left : SevenRealCubicInt) *
        (right : SevenRealCubicInt) +
      (right : SevenRealCubicInt) ^ 2

/-- The full degree-six norm in this explicit carrier: relative quadratic
norm followed by the determinant norm of the real cubic order. -/
def directCyclotomicNorm (left right : ℤ) : ℤ :=
  norm (directRelativeNorm left right)

/-- A packet retaining the source and the original ramified summit while
recording the direct cyclotomic factor. -/
structure PrimitiveCounterexampleDirectCyclotomicSecondCasePacket
    {x y z : ℕ} (source : CounterexamplePack x y z)
    (r : PrimitiveCounterexampleRamifiedProvenance source) where
  linearFactor : SevenCyclotomicDegreeSixInt.Ring
  linearFactor_eq :
    linearFactor = directLinearFactor r

namespace PrimitiveCounterexampleDirectCyclotomicSecondCasePacket

def ofProvenance
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    PrimitiveCounterexampleDirectCyclotomicSecondCasePacket source r :=
  ⟨directLinearFactor r, rfl⟩

@[simp] theorem ofProvenance_linearFactor
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    (ofProvenance r).linearFactor = directLinearFactor r :=
  rfl

end PrimitiveCounterexampleDirectCyclotomicSecondCasePacket

/-- The relative norm of the direct factor is the displayed real-cubic
element. -/
theorem directLinearFactor_mul_star
    (left right : ℤ) :
    (ofReal (left : SevenRealCubicInt) -
        zeta * ofReal (right : SevenRealCubicInt)) *
      star (ofReal (left : SevenRealCubicInt) -
        zeta * ofReal (right : SevenRealCubicInt)) =
      ofReal (directRelativeNorm left right) := by
  simp only [star_sub, star_mul, star_ofReal, star_zeta]
  rw [mul_comm zeta (ofReal (right : SevenRealCubicInt))]
  change
    (ofReal (left : SevenRealCubicInt) -
        ofReal (right : SevenRealCubicInt) * zeta) *
      (ofReal (left : SevenRealCubicInt) -
        ofReal (right : SevenRealCubicInt) * zetaInv) =
      ofReal ((left : SevenRealCubicInt) ^ 2 -
        (alpha - 1) * (left : SevenRealCubicInt) *
          (right : SevenRealCubicInt) +
        (right : SevenRealCubicInt) ^ 2)
  ring_nf
  simp only [mul_assoc, zeta_mul_zetaInv]
  simp only [map_add, map_mul, map_pow, map_intCast, map_neg]
  have hsum :
      (left : SevenCyclotomicDegreeSixInt.Ring) *
          (right : SevenCyclotomicDegreeSixInt.Ring) * zeta +
        (left : SevenCyclotomicDegreeSixInt.Ring) *
          (right : SevenCyclotomicDegreeSixInt.Ring) * zetaInv =
      (left : SevenCyclotomicDegreeSixInt.Ring) *
          (right : SevenCyclotomicDegreeSixInt.Ring) *
    (ofReal alpha - 1) := by
    rw [← mul_add, zeta_add_zetaInv]
    rw [map_sub, map_one]
  linear_combination -hsum

/-- The explicit degree-six norm agrees with the classical homogeneous
seventh cyclotomic kernel. -/
theorem directCyclotomicNorm_eq_cyclotomicSeven
    (left right : ℤ) :
    directCyclotomicNorm left right = cyclotomicSeven left right := by
  simp [directCyclotomicNorm, directRelativeNorm, SevenRealCubicInt.norm,
    SevenRealCubicInt.alpha, cyclotomicSeven]
  ring

/-- The direct factor satisfies the integer product identity without any
division: the endpoint gap times its full norm is the difference of seventh
powers. -/
theorem directLinearFactor_norm_product_identity
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    (r.summit.endpointLeft - r.summit.endpointRight) *
        directCyclotomicNorm r.summit.endpointLeft
          r.summit.endpointRight =
      r.summit.endpointLeft ^ 7 - r.summit.endpointRight ^ 7 := by
  rw [directCyclotomicNorm_eq_cyclotomicSeven]
  exact (seventh_pow_sub_pow_eq_sub_mul_cyclotomicSeven
    r.summit.endpointLeft r.summit.endpointRight).symm

/-- The same product identity specializes to the distinguished seventh
power stored by the ramified summit. -/
theorem directLinearFactor_norm_product_eq_distinguished_pow
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    (r.summit.endpointLeft - r.summit.endpointRight) *
        directCyclotomicNorm r.summit.endpointLeft
          r.summit.endpointRight =
      r.summit.distinguished ^ 7 := by
  rw [directLinearFactor_norm_product_identity]
  exact r.summit.fermat_eq

/-- The direct full norm is exactly the ramified residual seventh power. -/
theorem directCyclotomicNorm_eq_seven_mul_residual_pow
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directCyclotomicNorm r.summit.endpointLeft
        r.summit.endpointRight =
      7 * (r.summit.residualRoot : ℤ) ^ 7 := by
  rw [directCyclotomicNorm_eq_cyclotomicSeven]
  exact r.summit.residual_eq

end
end DkMath.FLT.Seven
