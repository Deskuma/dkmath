/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionDegreeSixOrientedLoadFactorization

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionGlobalOrientedPrimeFactorization"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false
open scoped QuadraticAlgebra

namespace SevenCyclotomicDegreeSixInt

open SevenRealCubicInt

/-- The order-three lift of the real-cubic rotation to the explicit
degree-six carrier.  In the basis `1,zeta`, it sends

`x + zeta*y` to `rotate(x) + zeta^2*rotate(y)`.

This is a ring homomorphism, rather than an algebra homomorphism over the
real cubic order, because it acts nontrivially on that order. -/
def rotateHom : Ring →+* Ring where
  toFun x :=
    ⟨rotateEquiv x.re - rotateEquiv x.im,
      (alpha - 1) * rotateEquiv x.im⟩
  map_zero' := by
    apply QuadraticAlgebra.ext <;> simp
  map_one' := by
    apply QuadraticAlgebra.ext <;> simp
  map_add' x y := by
    apply QuadraticAlgebra.ext <;> simp <;> ring
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, map_add, map_mul,
        map_neg, map_sub, map_one]
      rw [rotateEquiv_alpha]
      ring
    · simp only [QuadraticAlgebra.im_mul, map_add,
        map_mul, map_sub, map_one]
      rw [rotateEquiv_alpha]
      ring

@[simp] theorem rotateHom_ofReal
    (x : SevenRealCubicInt) :
    rotateHom (ofReal x) = ofReal (rotateEquiv x) := by
  apply QuadraticAlgebra.ext <;>
    simp [rotateHom, ofReal,
      QuadraticAlgebra.algebraMap_eq]

@[simp] theorem rotateHom_zeta :
    rotateHom zeta = zeta ^ 2 := by
  apply QuadraticAlgebra.ext <;>
    simp [rotateHom, zeta, pow_two]

/-- The explicit degree-six rotation has order three. -/
theorem rotateHom_three (x : Ring) :
    rotateHom (rotateHom (rotateHom x)) = x := by
  rw [show x = ofReal x.re + zeta * ofReal x.im by
    apply QuadraticAlgebra.ext <;>
      simp [ofReal, zeta,
        QuadraticAlgebra.algebraMap_eq]]
  simp only [map_add, map_mul, rotateHom_ofReal,
    rotateHom_zeta, map_pow, rotateEquiv_three]
  rw [← pow_mul, ← pow_mul]
  have hzetaEight : zeta ^ (2 * (2 * 2)) = zeta := by
    norm_num
    rw [show (8 : ℕ) = 7 + 1 by norm_num,
      pow_add, zeta_pow_seven, one_mul, pow_one]
  rw [hzetaEight]

/-- The canonical order-three degree-six ring automorphism. -/
def rotateEquiv : Ring ≃+* Ring where
  __ := rotateHom
  invFun x := rotateHom (rotateHom x)
  left_inv := rotateHom_three
  right_inv x := rotateHom_three x

@[simp] theorem rotateEquiv_ofReal
    (x : SevenRealCubicInt) :
    rotateEquiv (ofReal x) =
      ofReal (SevenRealCubicInt.rotateEquiv x) :=
  rotateHom_ofReal x

@[simp] theorem rotateEquiv_zeta :
    rotateEquiv zeta = zeta ^ 2 :=
  rotateHom_zeta

/-- Applying the lifted rotation three times is the identity. -/
theorem rotateEquiv_three (x : Ring) :
    rotateEquiv (rotateEquiv (rotateEquiv x)) = x :=
  rotateHom_three x

/-- The inverse rotation restricts to the inverse real-cubic rotation. -/
@[simp] theorem rotateEquiv_symm_ofReal
    (x : SevenRealCubicInt) :
    rotateEquiv.symm (ofReal x) =
      ofReal (SevenRealCubicInt.rotateEquiv.symm x) := by
  apply rotateEquiv.injective
  simp only [RingEquiv.apply_symm_apply, rotateEquiv_ofReal,
    RingEquiv.apply_symm_apply]

/-- Real-cubic rotation and quadratic conjugation commute, as required for
the abelian six-prime indexing. -/
theorem rotateEquiv_star (x : Ring) :
    rotateEquiv (star x) = star (rotateEquiv x) := by
  change
    (⟨SevenRealCubicInt.rotateEquiv (star x).re -
          SevenRealCubicInt.rotateEquiv (star x).im,
        (alpha - 1) *
          SevenRealCubicInt.rotateEquiv (star x).im⟩ : Ring) =
      star
        (⟨SevenRealCubicInt.rotateEquiv x.re -
            SevenRealCubicInt.rotateEquiv x.im,
          (alpha - 1) *
            SevenRealCubicInt.rotateEquiv x.im⟩ : Ring)
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, map_add, map_mul,
      map_neg, map_sub, map_one]
    rw [SevenRealCubicInt.rotateEquiv_alpha]
    ring
  · simp only [QuadraticAlgebra.im_star, map_neg]
    ring

end SevenCyclotomicDegreeSixInt

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress

open SevenRealCubicInt

variable {p : RamifiedSignedRootRoutingPacket} {q : ℕ}

/-- The real-cubic rotation transports the zeroth addressed kernel to the
first transported kernel. -/
theorem map_rotate_galoisKernel_zero_eq_one
    (a : p.QuotientPrimeGCDLoadAddress q) :
    Ideal.map rotateEquiv.toRingHom (a.galoisKernel 0) =
      a.galoisKernel 1 := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective
    rotateEquiv.toRingHom rotateEquiv.surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change a.galoisEval 1 (rotateEquiv x) = 0
    rw [a.galoisEval_one_rotate]
    exact hx
  · intro hy
    refine ⟨rotateEquiv.symm y, ?_, ?_⟩
    · change a.galoisEval 0 (rotateEquiv.symm y) = 0
      rw [← a.galoisEval_one_rotate]
      change a.galoisEval 1 y = 0 at hy
      simpa only [RingEquiv.apply_symm_apply] using hy
    · exact RingEquiv.apply_symm_apply rotateEquiv y

/-- The second real-cubic rotation transports kernel one to kernel two. -/
theorem map_rotate_galoisKernel_one_eq_two
    (a : p.QuotientPrimeGCDLoadAddress q) :
    Ideal.map rotateEquiv.toRingHom (a.galoisKernel 1) =
      a.galoisKernel 2 := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective
    rotateEquiv.toRingHom rotateEquiv.surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change a.galoisEval 2 (rotateEquiv x) = 0
    rw [a.galoisEval_two_rotate]
    exact hx
  · intro hy
    refine ⟨rotateEquiv.symm y, ?_, ?_⟩
    · change a.galoisEval 1 (rotateEquiv.symm y) = 0
      rw [← a.galoisEval_two_rotate]
      change a.galoisEval 2 y = 0 at hy
      simpa only [RingEquiv.apply_symm_apply] using hy
    · exact RingEquiv.apply_symm_apply rotateEquiv y

/-- The third real-cubic rotation closes the three-kernel cycle. -/
theorem map_rotate_galoisKernel_two_eq_zero
    (a : p.QuotientPrimeGCDLoadAddress q) :
    Ideal.map rotateEquiv.toRingHom (a.galoisKernel 2) =
      a.galoisKernel 0 := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective
    rotateEquiv.toRingHom rotateEquiv.surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change a.galoisEval 0 (rotateEquiv x) = 0
    rw [a.galoisEval_zero_rotate]
    exact hx
  · intro hy
    refine ⟨rotateEquiv.symm y, ?_, ?_⟩
    · change a.galoisEval 2 (rotateEquiv.symm y) = 0
      rw [← a.galoisEval_zero_rotate]
      change a.galoisEval 0 y = 0 at hy
      simpa only [RingEquiv.apply_symm_apply] using hy
    · exact RingEquiv.apply_symm_apply rotateEquiv y

end RamifiedSignedRootRoutingPacket.QuotientPrimeGCDLoadAddress

namespace RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress

open SevenCyclotomicDegreeSixInt

variable {p : RamifiedSignedRootRoutingPacket} {q : ℕ}

/-- The three degree-six evaluations above the three real-cubic Galois
addresses.  They are transported from the canonical phase-zero evaluation
by the explicit order-three lift. -/
def cyclicEval
    (a : CyclotomicLinearPrimeAddress p q) (i : Fin 3) :
    SevenCyclotomicDegreeSixInt.Ring →+* ZMod q :=
  if i = 0 then
    a.eval
  else if i = 1 then
    a.eval.comp SevenCyclotomicDegreeSixInt.rotateEquiv.symm.toRingHom
  else
    a.eval.comp SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom

/-- The oriented degree-one prime at one real Galois phase. -/
def cyclicKernel
    (a : CyclotomicLinearPrimeAddress p q) (i : Fin 3) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  RingHom.ker (a.cyclicEval i)

/-- Quadratic-conjugate evaluation at one real Galois phase. -/
def cyclicConjugateEval
    (a : CyclotomicLinearPrimeAddress p q) (i : Fin 3) :
    SevenCyclotomicDegreeSixInt.Ring →+* ZMod q :=
  (a.cyclicEval i).comp
    (starRingEnd SevenCyclotomicDegreeSixInt.Ring)

/-- The inverse-root prime at one real Galois phase. -/
def cyclicConjugateKernel
    (a : CyclotomicLinearPrimeAddress p q) (i : Fin 3) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  RingHom.ker (a.cyclicConjugateEval i)

@[simp] theorem cyclicEval_zero
    (a : CyclotomicLinearPrimeAddress p q) :
    a.cyclicEval 0 = a.eval := by
  simp [cyclicEval]

@[simp] theorem cyclicEval_one
    (a : CyclotomicLinearPrimeAddress p q) :
    a.cyclicEval 1 =
      a.eval.comp
        SevenCyclotomicDegreeSixInt.rotateEquiv.symm.toRingHom := by
  simp [cyclicEval]

@[simp] theorem cyclicEval_two
    (a : CyclotomicLinearPrimeAddress p q) :
    a.cyclicEval 2 =
      a.eval.comp
        SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom := by
  simp [cyclicEval]

@[simp] theorem cyclicKernel_zero
    (a : CyclotomicLinearPrimeAddress p q) :
    a.cyclicKernel 0 = a.evalKernel := by
  simp [cyclicKernel, evalKernel]

@[simp] theorem cyclicConjugateEval_zero
    (a : CyclotomicLinearPrimeAddress p q) :
    a.cyclicConjugateEval 0 = a.conjugateEval := by
  simp [cyclicConjugateEval, conjugateEval]

@[simp] theorem cyclicConjugateKernel_zero
    (a : CyclotomicLinearPrimeAddress p q) :
    a.cyclicConjugateKernel 0 = a.conjugateEvalKernel := by
  simp [cyclicConjugateKernel, conjugateEvalKernel]

/-- The first transported evaluation reverses the first degree-six
rotation. -/
theorem cyclicEval_one_rotate
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    a.cyclicEval 1 (SevenCyclotomicDegreeSixInt.rotateEquiv x) =
      a.cyclicEval 0 x := by
  change
    a.eval
        (SevenCyclotomicDegreeSixInt.rotateEquiv.symm
          (SevenCyclotomicDegreeSixInt.rotateEquiv x)) =
      a.eval x
  rw [RingEquiv.symm_apply_apply]

/-- The second transported evaluation reverses the second degree-six
rotation. -/
theorem cyclicEval_two_rotate
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    a.cyclicEval 2 (SevenCyclotomicDegreeSixInt.rotateEquiv x) =
      a.cyclicEval 1 x := by
  change
    a.eval
        (SevenCyclotomicDegreeSixInt.rotateEquiv
          (SevenCyclotomicDegreeSixInt.rotateEquiv x)) =
      a.eval
        (SevenCyclotomicDegreeSixInt.rotateEquiv.symm x)
  congr 1

/-- The third transported evaluation closes the degree-six cycle. -/
theorem cyclicEval_zero_rotate
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    a.cyclicEval 0 (SevenCyclotomicDegreeSixInt.rotateEquiv x) =
      a.cyclicEval 2 x := by
  rfl

/-- The conjugate evaluations obey the same first rotation step. -/
theorem cyclicConjugateEval_one_rotate
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    a.cyclicConjugateEval 1
        (SevenCyclotomicDegreeSixInt.rotateEquiv x) =
      a.cyclicConjugateEval 0 x := by
  change
    a.cyclicEval 1
        (star (SevenCyclotomicDegreeSixInt.rotateEquiv x)) =
      a.cyclicEval 0 (star x)
  rw [← SevenCyclotomicDegreeSixInt.rotateEquiv_star]
  exact a.cyclicEval_one_rotate (star x)

/-- The conjugate evaluations obey the second rotation step. -/
theorem cyclicConjugateEval_two_rotate
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    a.cyclicConjugateEval 2
        (SevenCyclotomicDegreeSixInt.rotateEquiv x) =
      a.cyclicConjugateEval 1 x := by
  change
    a.cyclicEval 2
        (star (SevenCyclotomicDegreeSixInt.rotateEquiv x)) =
      a.cyclicEval 1 (star x)
  rw [← SevenCyclotomicDegreeSixInt.rotateEquiv_star]
  exact a.cyclicEval_two_rotate (star x)

/-- The conjugate evaluation cycle also closes after the third step. -/
theorem cyclicConjugateEval_zero_rotate
    (a : CyclotomicLinearPrimeAddress p q)
    (x : SevenCyclotomicDegreeSixInt.Ring) :
    a.cyclicConjugateEval 0
        (SevenCyclotomicDegreeSixInt.rotateEquiv x) =
      a.cyclicConjugateEval 2 x := by
  change
    a.cyclicEval 0
        (star (SevenCyclotomicDegreeSixInt.rotateEquiv x)) =
      a.cyclicEval 2 (star x)
  rw [← SevenCyclotomicDegreeSixInt.rotateEquiv_star]
  exact a.cyclicEval_zero_rotate (star x)

private theorem map_rotate_kernel_step
    (f g :
      SevenCyclotomicDegreeSixInt.Ring →+* ZMod q)
    (h :
      ∀ x, g (SevenCyclotomicDegreeSixInt.rotateEquiv x) = f x) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (RingHom.ker f) =
      RingHom.ker g := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective
    SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
    SevenCyclotomicDegreeSixInt.rotateEquiv.surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change g (SevenCyclotomicDegreeSixInt.rotateEquiv x) = 0
    rw [h]
    exact hx
  · intro hy
    refine
      ⟨SevenCyclotomicDegreeSixInt.rotateEquiv.symm y,
        ?_, RingEquiv.apply_symm_apply _ y⟩
    change
      f (SevenCyclotomicDegreeSixInt.rotateEquiv.symm y) = 0
    rw [← h]
    change g y = 0 at hy
    simpa only [RingEquiv.apply_symm_apply] using hy

/-- Rotation sends the phase-zero oriented prime to phase one. -/
theorem map_rotate_cyclicKernel_zero_eq_one
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (a.cyclicKernel 0) =
      a.cyclicKernel 1 := by
  exact map_rotate_kernel_step
    (a.cyclicEval 0) (a.cyclicEval 1)
    a.cyclicEval_one_rotate

/-- Rotation sends the phase-one oriented prime to phase two. -/
theorem map_rotate_cyclicKernel_one_eq_two
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (a.cyclicKernel 1) =
      a.cyclicKernel 2 := by
  exact map_rotate_kernel_step
    (a.cyclicEval 1) (a.cyclicEval 2)
    a.cyclicEval_two_rotate

/-- Rotation closes the oriented prime cycle. -/
theorem map_rotate_cyclicKernel_two_eq_zero
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (a.cyclicKernel 2) =
      a.cyclicKernel 0 := by
  exact map_rotate_kernel_step
    (a.cyclicEval 2) (a.cyclicEval 0)
    a.cyclicEval_zero_rotate

/-- Rotation sends the phase-zero conjugate prime to phase one. -/
theorem map_rotate_cyclicConjugateKernel_zero_eq_one
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (a.cyclicConjugateKernel 0) =
      a.cyclicConjugateKernel 1 := by
  exact map_rotate_kernel_step
    (a.cyclicConjugateEval 0)
    (a.cyclicConjugateEval 1)
    a.cyclicConjugateEval_one_rotate

/-- Rotation sends the phase-one conjugate prime to phase two. -/
theorem map_rotate_cyclicConjugateKernel_one_eq_two
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (a.cyclicConjugateKernel 1) =
      a.cyclicConjugateKernel 2 := by
  exact map_rotate_kernel_step
    (a.cyclicConjugateEval 1)
    (a.cyclicConjugateEval 2)
    a.cyclicConjugateEval_two_rotate

/-- Rotation closes the conjugate prime cycle. -/
theorem map_rotate_cyclicConjugateKernel_two_eq_zero
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (a.cyclicConjugateKernel 2) =
      a.cyclicConjugateKernel 0 := by
  exact map_rotate_kernel_step
    (a.cyclicConjugateEval 2)
    (a.cyclicConjugateEval 0)
    a.cyclicConjugateEval_zero_rotate

private theorem starRingEnd_surjective :
    Function.Surjective
      (starRingEnd SevenCyclotomicDegreeSixInt.Ring) := by
  intro x
  exact ⟨star x, star_star x⟩

/-- Quadratic conjugation transports the oriented degree-one prime to its
conjugate prime. -/
theorem map_star_evalKernel_eq_conjugateEvalKernel
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        a.evalKernel =
      a.conjugateEvalKernel := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective _
    starRingEnd_surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change a.eval (star (star x)) = 0
    change a.eval x = 0 at hx
    simpa only [star_star] using hx
  · intro hy
    refine ⟨star y, ?_, ?_⟩
    · exact hy
    · exact star_star y

/-- Applying quadratic conjugation again returns the original oriented
prime. -/
theorem map_star_conjugateEvalKernel_eq_evalKernel
    (a : CyclotomicLinearPrimeAddress p q) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        a.conjugateEvalKernel =
      a.evalKernel := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective _
    starRingEnd_surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change a.eval (star x) = 0
    change a.eval (star x) = 0 at hx
    exact hx
  · intro hy
    refine ⟨star y, ?_, ?_⟩
    · change a.eval (star (star y)) = 0
      change a.eval y = 0 at hy
      simpa only [star_star] using hy
    · exact star_star y

/-- Quadratic conjugation exchanges the two primes at every real Galois
phase. -/
theorem map_star_cyclicKernel_eq_cyclicConjugateKernel
    (a : CyclotomicLinearPrimeAddress p q) (i : Fin 3) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (a.cyclicKernel i) =
      a.cyclicConjugateKernel i := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective _
    starRingEnd_surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change a.cyclicEval i (star (star x)) = 0
    change a.cyclicEval i x = 0 at hx
    simpa only [star_star] using hx
  · intro hy
    refine ⟨star y, ?_, star_star y⟩
    exact hy

/-- Conjugating a second time recovers the oriented prime at every real
Galois phase. -/
theorem map_star_cyclicConjugateKernel_eq_cyclicKernel
    (a : CyclotomicLinearPrimeAddress p q) (i : Fin 3) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (a.cyclicConjugateKernel i) =
      a.cyclicKernel i := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective _
    starRingEnd_surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change a.cyclicEval i (star x) = 0
    exact hx
  · intro hy
    refine ⟨star y, ?_, star_star y⟩
    change a.cyclicEval i (star (star y)) = 0
    change a.cyclicEval i y = 0 at hy
    simpa only [star_star] using hy

end RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress

namespace RamifiedFusionRow2LoadFamily

open SevenCyclotomicDegreeSixInt

variable (family : RamifiedFusionRow2LoadFamily)
  (p : RamifiedSignedRootRoutingPacket)

/-- The lifted order-three rotation commutes with extension from the
real-cubic order.  This is the ideal-theoretic square used to transport the
phase-zero fibre equality around the three Galois phases. -/
theorem map_rotate_map_ofReal
    (I : Ideal SevenRealCubicInt) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (Ideal.map ofReal I) =
      Ideal.map ofReal
        (Ideal.map SevenRealCubicInt.rotateEquiv.toRingHom I) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro x
  exact SevenCyclotomicDegreeSixInt.rotateEquiv_ofReal x

namespace PrimeSupport

variable {family : RamifiedFusionRow2LoadFamily}
  {p : RamifiedSignedRootRoutingPacket}

/-- The transported degree-six evaluation restricts to the already existing
real-cubic Galois evaluation at the same phase. -/
theorem cyclicEval_ofReal
    (s : PrimeSupport family p) (i : Fin 3)
    (x : SevenRealCubicInt) :
    s.cyclotomicAddress.cyclicEval i (ofReal x) =
      s.address.galoisEval i x := by
  fin_cases i
  · change
      s.cyclotomicAddress.eval (ofReal x) =
        s.address.evalAlphaRoot x
    rw [RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.eval,
      localEval_ofReal]
    rfl
  · change
      s.cyclotomicAddress.eval
          (SevenCyclotomicDegreeSixInt.rotateEquiv.symm
            (ofReal x)) =
        s.address.evalAlphaRoot
          (SevenRealCubicInt.rotateEquiv.symm x)
    rw [SevenCyclotomicDegreeSixInt.rotateEquiv_symm_ofReal,
      RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.eval,
      localEval_ofReal]
    rfl
  · change
      s.cyclotomicAddress.eval
          (SevenCyclotomicDegreeSixInt.rotateEquiv
            (ofReal x)) =
        s.address.evalAlphaRoot
          (SevenRealCubicInt.rotateEquiv x)
    rw [SevenCyclotomicDegreeSixInt.rotateEquiv_ofReal,
      RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.eval,
      localEval_ofReal]
    rfl

/-- Every oriented degree-six prime contracts to the matching one of the
three real-cubic Galois kernels. -/
theorem cyclicKernel_comap_ofReal
    (s : PrimeSupport family p) (i : Fin 3) :
    Ideal.comap ofReal
        (s.cyclotomicAddress.cyclicKernel i) =
      s.address.galoisKernel i := by
  ext x
  change
    s.cyclotomicAddress.cyclicEval i (ofReal x) = 0 ↔
      s.address.galoisEval i x = 0
  rw [s.cyclicEval_ofReal]

/-- The conjugate degree-six prime has the same matching real-cubic
contraction. -/
theorem cyclicConjugateKernel_comap_ofReal
    (s : PrimeSupport family p) (i : Fin 3) :
    Ideal.comap ofReal
        (s.cyclotomicAddress.cyclicConjugateKernel i) =
      s.address.galoisKernel i := by
  ext x
  change
    s.cyclotomicAddress.cyclicEval i (star (ofReal x)) = 0 ↔
      s.address.galoisEval i x = 0
  rw [SevenCyclotomicDegreeSixInt.star_ofReal,
    s.cyclicEval_ofReal]

/-- The N1 exact conjugate-prime fibre at the canonical Galois phase. -/
theorem map_galoisKernel_zero_eq_cyclicPrimePair
    (s : PrimeSupport family p) :
    Ideal.map ofReal (s.address.galoisKernel 0) =
      s.cyclotomicAddress.cyclicKernel 0 *
        s.cyclotomicAddress.cyclicConjugateKernel 0 := by
  change Ideal.map ofReal
      (RingHom.ker s.address.evalAlphaRoot) = _
  exact s.cyclotomicAddress.realPrimeFiberIdeal_eq_conjugateProduct

/-- Rotation transports the exact fibre equality to phase one. -/
theorem map_galoisKernel_one_eq_cyclicPrimePair
    (s : PrimeSupport family p) :
    Ideal.map ofReal (s.address.galoisKernel 1) =
      s.cyclotomicAddress.cyclicKernel 1 *
        s.cyclotomicAddress.cyclicConjugateKernel 1 := by
  have h := congrArg
    (Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom)
    s.map_galoisKernel_zero_eq_cyclicPrimePair
  rw [map_rotate_map_ofReal,
    s.address.map_rotate_galoisKernel_zero_eq_one,
    Ideal.map_mul,
    s.cyclotomicAddress.map_rotate_cyclicKernel_zero_eq_one,
    s.cyclotomicAddress.map_rotate_cyclicConjugateKernel_zero_eq_one] at h
  exact h

/-- A second rotation transports the exact fibre equality to phase two. -/
theorem map_galoisKernel_two_eq_cyclicPrimePair
    (s : PrimeSupport family p) :
    Ideal.map ofReal (s.address.galoisKernel 2) =
      s.cyclotomicAddress.cyclicKernel 2 *
        s.cyclotomicAddress.cyclicConjugateKernel 2 := by
  have h := congrArg
    (Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom)
    s.map_galoisKernel_one_eq_cyclicPrimePair
  rw [map_rotate_map_ofReal,
    s.address.map_rotate_galoisKernel_one_eq_two,
    Ideal.map_mul,
    s.cyclotomicAddress.map_rotate_cyclicKernel_one_eq_two,
    s.cyclotomicAddress.map_rotate_cyclicConjugateKernel_one_eq_two] at h
  exact h

/-- Exact splitting of every transported real-cubic prime into its oriented
and inverse-root degree-six fibres. -/
theorem map_galoisKernel_eq_cyclicPrimePair
    (s : PrimeSupport family p) (i : Fin 3) :
    Ideal.map ofReal (s.address.galoisKernel i) =
      s.cyclotomicAddress.cyclicKernel i *
        s.cyclotomicAddress.cyclicConjugateKernel i := by
  fin_cases i
  · exact s.map_galoisKernel_zero_eq_cyclicPrimePair
  · exact s.map_galoisKernel_one_eq_cyclicPrimePair
  · exact s.map_galoisKernel_two_eq_cyclicPrimePair

/-- Oriented prime power at one real Galois phase. -/
def cyclicKernelPower
    (s : PrimeSupport family p) (i : Fin 3) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  s.cyclotomicAddress.cyclicKernel i ^
    padicValNat s.1 (family.cell p)

/-- Conjugate prime power at one real Galois phase. -/
def cyclicConjugateKernelPower
    (s : PrimeSupport family p) (i : Fin 3) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  s.cyclotomicAddress.cyclicConjugateKernel i ^
    padicValNat s.1 (family.cell p)

/-- Complete conjugate pair power at one real Galois phase. -/
def cyclicPairPower
    (s : PrimeSupport family p) (i : Fin 3) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  s.cyclicKernelPower i * s.cyclicConjugateKernelPower i

/-- Extension of an exact real-cubic Galois-kernel power is the complete
oriented/conjugate pair power at the same phase. -/
theorem map_galoisKernelPower_eq_cyclicPairPower
    (s : PrimeSupport family p) (i : Fin 3) :
    Ideal.map ofReal
        ((s.address.galoisKernel i) ^
          padicValNat s.1 (family.cell p)) =
      s.cyclicPairPower i := by
  rw [Ideal.map_pow, s.map_galoisKernel_eq_cyclicPrimePair,
    mul_pow]
  rfl

/-- Quadratic conjugation exchanges the two prime powers at every phase. -/
theorem map_star_cyclicKernelPower_eq_cyclicConjugateKernelPower
    (s : PrimeSupport family p) (i : Fin 3) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (s.cyclicKernelPower i) =
      s.cyclicConjugateKernelPower i := by
  rw [cyclicKernelPower, cyclicConjugateKernelPower,
    Ideal.map_pow,
    s.cyclotomicAddress.map_star_cyclicKernel_eq_cyclicConjugateKernel]

/-- The reverse quadratic-conjugation exchange at every phase. -/
theorem map_star_cyclicConjugateKernelPower_eq_cyclicKernelPower
    (s : PrimeSupport family p) (i : Fin 3) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (s.cyclicConjugateKernelPower i) =
      s.cyclicKernelPower i := by
  rw [cyclicKernelPower, cyclicConjugateKernelPower,
    Ideal.map_pow,
    s.cyclotomicAddress.map_star_cyclicConjugateKernel_eq_cyclicKernel]

/-- Each complete phase-indexed fibre power is fixed by quadratic
conjugation. -/
theorem map_star_cyclicPairPower
    (s : PrimeSupport family p) (i : Fin 3) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (s.cyclicPairPower i) =
      s.cyclicPairPower i := by
  rw [cyclicPairPower, Ideal.map_mul,
    s.map_star_cyclicKernelPower_eq_cyclicConjugateKernelPower,
    s.map_star_cyclicConjugateKernelPower_eq_cyclicKernelPower,
    mul_comm]

/-- Rotation transports the phase-zero complete prime power to phase one. -/
theorem map_rotate_cyclicPairPower_zero_eq_one
    (s : PrimeSupport family p) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (s.cyclicPairPower 0) =
      s.cyclicPairPower 1 := by
  rw [cyclicPairPower, cyclicKernelPower,
    cyclicConjugateKernelPower, Ideal.map_mul,
    Ideal.map_pow, Ideal.map_pow,
    s.cyclotomicAddress.map_rotate_cyclicKernel_zero_eq_one,
    s.cyclotomicAddress.map_rotate_cyclicConjugateKernel_zero_eq_one]
  rfl

/-- Rotation transports the phase-one complete prime power to phase two. -/
theorem map_rotate_cyclicPairPower_one_eq_two
    (s : PrimeSupport family p) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (s.cyclicPairPower 1) =
      s.cyclicPairPower 2 := by
  rw [cyclicPairPower, cyclicKernelPower,
    cyclicConjugateKernelPower, Ideal.map_mul,
    Ideal.map_pow, Ideal.map_pow,
    s.cyclotomicAddress.map_rotate_cyclicKernel_one_eq_two,
    s.cyclotomicAddress.map_rotate_cyclicConjugateKernel_one_eq_two]
  rfl

/-- The third rotation closes the complete prime-power cycle. -/
theorem map_rotate_cyclicPairPower_two_eq_zero
    (s : PrimeSupport family p) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (s.cyclicPairPower 2) =
      s.cyclicPairPower 0 := by
  rw [cyclicPairPower, cyclicKernelPower,
    cyclicConjugateKernelPower, Ideal.map_mul,
    Ideal.map_pow, Ideal.map_pow,
    s.cyclotomicAddress.map_rotate_cyclicKernel_two_eq_zero,
    s.cyclotomicAddress.map_rotate_cyclicConjugateKernel_two_eq_zero]
  rfl

/-- Quadratic conjugation exchanges the two exact powers above one supported
real prime. -/
theorem map_star_orientedKernelPower_eq_conjugateKernelPower
    (s : PrimeSupport family p) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        s.orientedKernelPower =
      s.conjugateKernelPower := by
  rw [orientedKernelPower, conjugateKernelPower,
    Ideal.map_pow,
    s.cyclotomicAddress.map_star_evalKernel_eq_conjugateEvalKernel]

/-- The reverse exchange of the conjugate exact prime power. -/
theorem map_star_conjugateKernelPower_eq_orientedKernelPower
    (s : PrimeSupport family p) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        s.conjugateKernelPower =
      s.orientedKernelPower := by
  rw [orientedKernelPower, conjugateKernelPower,
    Ideal.map_pow,
    s.cyclotomicAddress.map_star_conjugateEvalKernel_eq_evalKernel]

/-- Each local conjugate pair power is invariant under quadratic
conjugation. -/
theorem map_star_orientedPairPower
    (s : PrimeSupport family p) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        s.orientedPairPower =
      s.orientedPairPower := by
  rw [orientedPairPower, Ideal.map_mul,
    s.map_star_orientedKernelPower_eq_conjugateKernelPower,
    s.map_star_conjugateKernelPower_eq_orientedKernelPower,
    mul_comm]

end PrimeSupport

/-- Finite product of all exact conjugate-pair powers at one real Galois
phase.  The support and every `padicValNat` exponent are inherited unchanged
from N2. -/
def globalCyclicOrientedFactorIdeal
    (i : Fin 3) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : PrimeSupport family p, s.cyclicPairPower i

/-- The canonical phase of the cyclic product is the N2 launchpad product. -/
theorem globalCyclicOrientedFactorIdeal_zero :
    globalCyclicOrientedFactorIdeal family p 0 =
      globalDegreeSixOrientedFactorIdeal family p := by
  rw [globalCyclicOrientedFactorIdeal,
    globalDegreeSixOrientedFactorIdeal]
  apply Finset.prod_congr rfl
  intro s hs
  simp [PrimeSupport.cyclicPairPower,
    PrimeSupport.cyclicKernelPower,
    PrimeSupport.cyclicConjugateKernelPower,
    PrimeSupport.orientedPairPower,
    PrimeSupport.orientedKernelPower,
    PrimeSupport.conjugateKernelPower]

/-- The lifted rotation transports the full phase-zero product to phase one. -/
theorem map_rotate_globalCyclicOrientedFactorIdeal_zero_eq_one :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (globalCyclicOrientedFactorIdeal family p 0) =
      globalCyclicOrientedFactorIdeal family p 1 := by
  rw [globalCyclicOrientedFactorIdeal,
    globalCyclicOrientedFactorIdeal]
  change
    (Ideal.mapHom SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom)
        (∏ s : PrimeSupport family p, s.cyclicPairPower 0) =
      ∏ s : PrimeSupport family p, s.cyclicPairPower 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro s hs
  exact s.map_rotate_cyclicPairPower_zero_eq_one

/-- The lifted rotation transports the full phase-one product to phase two. -/
theorem map_rotate_globalCyclicOrientedFactorIdeal_one_eq_two :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (globalCyclicOrientedFactorIdeal family p 1) =
      globalCyclicOrientedFactorIdeal family p 2 := by
  rw [globalCyclicOrientedFactorIdeal,
    globalCyclicOrientedFactorIdeal]
  change
    (Ideal.mapHom SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom)
        (∏ s : PrimeSupport family p, s.cyclicPairPower 1) =
      ∏ s : PrimeSupport family p, s.cyclicPairPower 2
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro s hs
  exact s.map_rotate_cyclicPairPower_one_eq_two

/-- The third lifted rotation closes the full three-product orbit. -/
theorem map_rotate_globalCyclicOrientedFactorIdeal_two_eq_zero :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (globalCyclicOrientedFactorIdeal family p 2) =
      globalCyclicOrientedFactorIdeal family p 0 := by
  rw [globalCyclicOrientedFactorIdeal,
    globalCyclicOrientedFactorIdeal]
  change
    (Ideal.mapHom SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom)
        (∏ s : PrimeSupport family p, s.cyclicPairPower 2) =
      ∏ s : PrimeSupport family p, s.cyclicPairPower 0
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro s hs
  exact s.map_rotate_cyclicPairPower_two_eq_zero

/-- Mapping the principal ideal generated by a real-cubic element commutes
with the lifted rotation. -/
theorem map_rotate_span_ofReal
    (x : SevenRealCubicInt) :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (Ideal.span {ofReal x}) =
      Ideal.span {ofReal (SevenRealCubicInt.rotateEquiv x)} := by
  rw [Ideal.map_span]
  congr
  ext y
  simp

/-- Phase-one exact finite factorization of the mapped real load. -/
theorem globalCyclicOrientedFactorIdeal_one_eq_span_ofReal_load :
    globalCyclicOrientedFactorIdeal family p 1 =
      Ideal.span {ofReal (family.load p 1)} := by
  have h := congrArg
    (Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom)
    (globalDegreeSixOrientedFactorIdeal_eq_span_ofReal_load family p)
  rw [← globalCyclicOrientedFactorIdeal_zero,
    map_rotate_globalCyclicOrientedFactorIdeal_zero_eq_one,
    map_rotate_span_ofReal] at h
  refine h.trans ?_
  have ha :=
    (family.rotate_load_zero_associated_one p).map ofReal
  apply le_antisymm
  · exact Ideal.span_singleton_le_span_singleton.mpr ha.symm.dvd
  · exact Ideal.span_singleton_le_span_singleton.mpr ha.dvd

/-- Phase-two exact finite factorization of the mapped real load. -/
theorem globalCyclicOrientedFactorIdeal_two_eq_span_ofReal_load :
    globalCyclicOrientedFactorIdeal family p 2 =
      Ideal.span {ofReal (family.load p 2)} := by
  have h := congrArg
    (Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom)
    (globalCyclicOrientedFactorIdeal_one_eq_span_ofReal_load family p)
  rw [map_rotate_globalCyclicOrientedFactorIdeal_one_eq_two,
    map_rotate_span_ofReal] at h
  refine h.trans ?_
  have ha :=
    (family.rotate_load_one_associated_two p).map ofReal
  apply le_antisymm
  · exact Ideal.span_singleton_le_span_singleton.mpr ha.symm.dvd
  · exact Ideal.span_singleton_le_span_singleton.mpr ha.dvd

/-- Exact finite factorization of every mapped real load into its phase-indexed
oriented and conjugate prime powers. -/
theorem globalCyclicOrientedFactorIdeal_eq_span_ofReal_load
    (i : Fin 3) :
    globalCyclicOrientedFactorIdeal family p i =
      Ideal.span {ofReal (family.load p i)} := by
  fin_cases i
  · change globalCyclicOrientedFactorIdeal family p 0 =
      Ideal.span {ofReal (family.load p 0)}
    rw [globalCyclicOrientedFactorIdeal_zero]
    exact
      globalDegreeSixOrientedFactorIdeal_eq_span_ofReal_load
        family p
  · change globalCyclicOrientedFactorIdeal family p 1 =
      Ideal.span {ofReal (family.load p 1)}
    exact
      globalCyclicOrientedFactorIdeal_one_eq_span_ofReal_load
        family p
  · change globalCyclicOrientedFactorIdeal family p 2 =
      Ideal.span {ofReal (family.load p 2)}
    exact
      globalCyclicOrientedFactorIdeal_two_eq_span_ofReal_load
        family p

/-- Every phase-indexed finite product is invariant under quadratic
conjugation. -/
theorem map_star_globalCyclicOrientedFactorIdeal
    (i : Fin 3) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (globalCyclicOrientedFactorIdeal family p i) =
      globalCyclicOrientedFactorIdeal family p i := by
  rw [globalCyclicOrientedFactorIdeal]
  change
    (Ideal.mapHom
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring))
        (∏ s : PrimeSupport family p, s.cyclicPairPower i) =
      ∏ s : PrimeSupport family p, s.cyclicPairPower i
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro s hs
  exact PrimeSupport.map_star_cyclicPairPower s i

/-- The complete finite oriented factorization is invariant under quadratic
conjugation, with no change to support or exponents. -/
theorem map_star_globalDegreeSixOrientedFactorIdeal :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (globalDegreeSixOrientedFactorIdeal family p) =
      globalDegreeSixOrientedFactorIdeal family p := by
  rw [globalDegreeSixOrientedFactorIdeal]
  change
    (Ideal.mapHom
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring))
        (∏ s : PrimeSupport family p, s.orientedPairPower) =
      ∏ s : PrimeSupport family p, s.orientedPairPower
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro s hs
  exact PrimeSupport.map_star_orientedPairPower s

/-- ULTRA/U1.1 packet: the exact finite factorization from N2 together with
the real order-three kernel cycle and quadratic-conjugation invariance. -/
structure GlobalOrientedPrimeFactorizationPacket where
  launchpad :
    DegreeSixOrientedLoadFactorizationPacket family p
  realKernelCycle :
    ∀ s : PrimeSupport family p,
      Ideal.map SevenRealCubicInt.rotateEquiv.toRingHom
          (s.address.galoisKernel 0) =
        s.address.galoisKernel 1 ∧
      Ideal.map SevenRealCubicInt.rotateEquiv.toRingHom
          (s.address.galoisKernel 1) =
        s.address.galoisKernel 2 ∧
      Ideal.map SevenRealCubicInt.rotateEquiv.toRingHom
          (s.address.galoisKernel 2) =
        s.address.galoisKernel 0
  degreeSixKernelCycle :
    ∀ s : PrimeSupport family p,
      Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
          (s.cyclotomicAddress.cyclicKernel 0) =
        s.cyclotomicAddress.cyclicKernel 1 ∧
      Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
          (s.cyclotomicAddress.cyclicKernel 1) =
        s.cyclotomicAddress.cyclicKernel 2 ∧
      Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
          (s.cyclotomicAddress.cyclicKernel 2) =
        s.cyclotomicAddress.cyclicKernel 0
  degreeSixConjugateKernelCycle :
    ∀ s : PrimeSupport family p,
      Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
          (s.cyclotomicAddress.cyclicConjugateKernel 0) =
        s.cyclotomicAddress.cyclicConjugateKernel 1 ∧
      Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
          (s.cyclotomicAddress.cyclicConjugateKernel 1) =
        s.cyclotomicAddress.cyclicConjugateKernel 2 ∧
      Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
          (s.cyclotomicAddress.cyclicConjugateKernel 2) =
        s.cyclotomicAddress.cyclicConjugateKernel 0
  cyclicRestriction :
    ∀ (s : PrimeSupport family p) (i : Fin 3),
      Ideal.comap ofReal
          (s.cyclotomicAddress.cyclicKernel i) =
        s.address.galoisKernel i ∧
      Ideal.comap ofReal
          (s.cyclotomicAddress.cyclicConjugateKernel i) =
        s.address.galoisKernel i
  cyclicLocalFibrePower :
    ∀ (s : PrimeSupport family p) (i : Fin 3),
      Ideal.map ofReal
          ((s.address.galoisKernel i) ^
            padicValNat s.1 (family.cell p)) =
        s.cyclicPairPower i
  cyclicQuadraticPairInvariant :
    ∀ (s : PrimeSupport family p) (i : Fin 3),
      Ideal.map
          (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
          (s.cyclicPairPower i) =
        s.cyclicPairPower i
  cyclicGlobalFactorization :
    ∀ i : Fin 3,
      globalCyclicOrientedFactorIdeal family p i =
        Ideal.span {ofReal (family.load p i)}
  cyclicGlobalRotation :
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (globalCyclicOrientedFactorIdeal family p 0) =
      globalCyclicOrientedFactorIdeal family p 1 ∧
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (globalCyclicOrientedFactorIdeal family p 1) =
      globalCyclicOrientedFactorIdeal family p 2 ∧
    Ideal.map SevenCyclotomicDegreeSixInt.rotateEquiv.toRingHom
        (globalCyclicOrientedFactorIdeal family p 2) =
      globalCyclicOrientedFactorIdeal family p 0
  cyclicGlobalQuadraticInvariant :
    ∀ i : Fin 3,
      Ideal.map
          (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
          (globalCyclicOrientedFactorIdeal family p i) =
        globalCyclicOrientedFactorIdeal family p i
  quadraticPairInvariant :
    ∀ s : PrimeSupport family p,
      Ideal.map
          (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
          s.orientedPairPower =
        s.orientedPairPower
  globalQuadraticInvariant :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (globalDegreeSixOrientedFactorIdeal family p) =
      globalDegreeSixOrientedFactorIdeal family p

/-- Canonical global factorization packet with both Galois coherences. -/
theorem globalOrientedPrimeFactorizationPacket :
    GlobalOrientedPrimeFactorizationPacket family p where
  launchpad :=
    degreeSixOrientedLoadFactorizationPacket family p
  realKernelCycle := fun s =>
    ⟨s.address.map_rotate_galoisKernel_zero_eq_one,
      s.address.map_rotate_galoisKernel_one_eq_two,
      s.address.map_rotate_galoisKernel_two_eq_zero⟩
  degreeSixKernelCycle := fun s =>
    ⟨s.cyclotomicAddress.map_rotate_cyclicKernel_zero_eq_one,
      s.cyclotomicAddress.map_rotate_cyclicKernel_one_eq_two,
      s.cyclotomicAddress.map_rotate_cyclicKernel_two_eq_zero⟩
  degreeSixConjugateKernelCycle := fun s =>
    ⟨s.cyclotomicAddress.map_rotate_cyclicConjugateKernel_zero_eq_one,
      s.cyclotomicAddress.map_rotate_cyclicConjugateKernel_one_eq_two,
      s.cyclotomicAddress.map_rotate_cyclicConjugateKernel_two_eq_zero⟩
  cyclicRestriction := fun s i =>
    ⟨s.cyclicKernel_comap_ofReal i,
      s.cyclicConjugateKernel_comap_ofReal i⟩
  cyclicLocalFibrePower := fun s i =>
    s.map_galoisKernelPower_eq_cyclicPairPower i
  cyclicQuadraticPairInvariant := fun s i =>
    s.map_star_cyclicPairPower i
  cyclicGlobalFactorization :=
    globalCyclicOrientedFactorIdeal_eq_span_ofReal_load
      family p
  cyclicGlobalRotation :=
    ⟨map_rotate_globalCyclicOrientedFactorIdeal_zero_eq_one
        family p,
      map_rotate_globalCyclicOrientedFactorIdeal_one_eq_two
        family p,
      map_rotate_globalCyclicOrientedFactorIdeal_two_eq_zero
        family p⟩
  cyclicGlobalQuadraticInvariant :=
    map_star_globalCyclicOrientedFactorIdeal family p
  quadraticPairInvariant :=
    fun s => PrimeSupport.map_star_orientedPairPower s
  globalQuadraticInvariant :=
    map_star_globalDegreeSixOrientedFactorIdeal family p

end RamifiedFusionRow2LoadFamily


end

end DkMath.FLT.Seven
