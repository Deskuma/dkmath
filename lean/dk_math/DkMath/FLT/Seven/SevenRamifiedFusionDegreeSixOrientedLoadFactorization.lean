/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicConjugatePrimePair
import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadGlobalFactorization

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionDegreeSixOrientedLoadFactorization"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace RamifiedFusionRow2LoadFamily

open SevenCyclotomicDegreeSixInt

variable (family : RamifiedFusionRow2LoadFamily)
  (p : RamifiedSignedRootRoutingPacket)

namespace PrimeSupport

variable {family : RamifiedFusionRow2LoadFamily}
  {p : RamifiedSignedRootRoutingPacket}

/-- Canonical degree-six orientation above one member of the existing
real-cubic prime support. -/
def cyclotomicAddress
    (s : PrimeSupport family p) :
    p.CyclotomicLinearPrimeAddress s.1 :=
  p.cyclotomicLinearPrimeAddress s.address.muSevenAddress

/-- Exact oriented prime power over one supported rational prime. -/
def orientedKernelPower
    (s : PrimeSupport family p) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  s.cyclotomicAddress.evalKernel ^
    padicValNat s.1 (family.cell p)

/-- Exact conjugate prime power over the same supported rational prime. -/
def conjugateKernelPower
    (s : PrimeSupport family p) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  s.cyclotomicAddress.conjugateEvalKernel ^
    padicValNat s.1 (family.cell p)

/-- The complete conjugate pair over one real-cubic prime power. -/
def orientedPairPower
    (s : PrimeSupport family p) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  s.orientedKernelPower * s.conjugateKernelPower

/-- Extending one exact real-cubic kernel power gives exactly the product of
the two oriented/conjugate degree-six prime powers. -/
theorem map_kernelPower_eq_orientedPairPower
    (s : PrimeSupport family p) :
    Ideal.map ofReal s.kernelPower =
      s.orientedPairPower := by
  rw [kernelPower, Ideal.map_pow]
  have hfibre :=
    s.cyclotomicAddress.realPrimeFiberIdeal_eq_conjugateProduct
  change
    Ideal.map ofReal s.address.evalKernel =
      s.cyclotomicAddress.evalKernel *
        s.cyclotomicAddress.conjugateEvalKernel at hfibre
  rw [hfibre, mul_pow]
  rfl

/-- Conjugate prime-power pairs belonging to different rational primes remain
comaximal after extension to the degree-six carrier. -/
theorem orientedPairPowers_pairwise_isCoprime :
    Pairwise
      (fun s t : PrimeSupport family p =>
        IsCoprime s.orientedPairPower
          t.orientedPairPower) := by
  intro s t hst
  have h :=
    (kernelPowers_pairwise_isCoprime hst).map
      (Ideal.mapHom ofReal)
  change
    IsCoprime
      (Ideal.map ofReal s.kernelPower)
      (Ideal.map ofReal t.kernelPower) at h
  rw [s.map_kernelPower_eq_orientedPairPower,
    t.map_kernelPower_eq_orientedPairPower] at h
  exact h

end PrimeSupport

/-- Finite product of all exact oriented/conjugate prime-power pairs
supporting the selected load. -/
def globalDegreeSixOrientedFactorIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : PrimeSupport family p, s.orientedPairPower

/-- Mapping the existing real-cubic global factor ideal to the degree-six
carrier produces exactly the finite oriented/conjugate product. -/
theorem map_globalLoadFactorIdeal_eq_orientedFactorIdeal :
    Ideal.map ofReal (globalLoadFactorIdeal family p) =
      globalDegreeSixOrientedFactorIdeal family p := by
  rw [globalLoadFactorIdeal, globalDegreeSixOrientedFactorIdeal]
  change
    (Ideal.mapHom ofReal)
        (∏ s : PrimeSupport family p, s.kernelPower) =
      ∏ s : PrimeSupport family p, s.orientedPairPower
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro s hs
  exact PrimeSupport.map_kernelPower_eq_orientedPairPower s

/-- The finite oriented/conjugate product is the extension of the selected
principal real-cubic load ideal. -/
theorem globalDegreeSixOrientedFactorIdeal_eq_map_span_load :
    globalDegreeSixOrientedFactorIdeal family p =
      Ideal.map ofReal
        (Ideal.span {family.load p 0}) := by
  rw [← map_globalLoadFactorIdeal_eq_orientedFactorIdeal,
    globalLoadFactorIdeal_eq_span_load]

/-- Principal-ideal form of the global oriented launchpad. -/
theorem globalDegreeSixOrientedFactorIdeal_eq_span_ofReal_load :
    globalDegreeSixOrientedFactorIdeal family p =
      Ideal.span {ofReal (family.load p 0)} := by
  rw [globalDegreeSixOrientedFactorIdeal_eq_map_span_load,
    Ideal.map_span]
  congr
  ext x
  simp

/-- Compact NORMAL/N2 launch packet.  It retains the old finite support and
ordinary `padicValNat` exponents while exposing the canonical oriented and
conjugate degree-six prime powers, their local fibre equality, cross-prime
comaximality, and the exact mapped principal-load factorization. -/
structure DegreeSixOrientedLoadFactorizationPacket where
  localFibrePower :
    ∀ s : PrimeSupport family p,
      Ideal.map ofReal s.kernelPower =
        s.orientedPairPower
  pairwiseCoprime :
    Pairwise
      (fun s t : PrimeSupport family p =>
        IsCoprime s.orientedPairPower
          t.orientedPairPower)
  mappedFactorization :
    Ideal.map ofReal (globalLoadFactorIdeal family p) =
      globalDegreeSixOrientedFactorIdeal family p
  principalFactorization :
    globalDegreeSixOrientedFactorIdeal family p =
      Ideal.span {ofReal (family.load p 0)}

/-- The canonical global oriented launch packet is inhabited for either
row-two load family. -/
def degreeSixOrientedLoadFactorizationPacket :
    DegreeSixOrientedLoadFactorizationPacket family p where
  localFibrePower :=
    fun s => PrimeSupport.map_kernelPower_eq_orientedPairPower s
  pairwiseCoprime :=
    PrimeSupport.orientedPairPowers_pairwise_isCoprime
  mappedFactorization :=
    map_globalLoadFactorIdeal_eq_orientedFactorIdeal family p
  principalFactorization :=
    globalDegreeSixOrientedFactorIdeal_eq_span_ofReal_load family p

end RamifiedFusionRow2LoadFamily

#print axioms
  RamifiedFusionRow2LoadFamily.PrimeSupport.map_kernelPower_eq_orientedPairPower
#print axioms
  RamifiedFusionRow2LoadFamily.PrimeSupport.orientedPairPowers_pairwise_isCoprime
#print axioms
  RamifiedFusionRow2LoadFamily.globalDegreeSixOrientedFactorIdeal_eq_span_ofReal_load
#print axioms
  RamifiedFusionRow2LoadFamily.degreeSixOrientedLoadFactorizationPacket

end

end DkMath.FLT.Seven
