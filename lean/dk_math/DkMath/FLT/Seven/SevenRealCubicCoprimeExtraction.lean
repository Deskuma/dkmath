/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicNumberField
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedRealCubicNorm
import Mathlib.RingTheory.PrincipalIdealDomain

#print "file: DkMath.FLT.Seven.SevenRealCubicCoprimeExtraction"

namespace DkMath.FLT.Seven

open scoped NumberField

noncomputable section

namespace SevenRealCubic

/-- The coordinate model inherits the principal-ideal property from its
explicit equivalence with the full ring of integers. -/
noncomputable instance modelIsPrincipalIdealRing :
    IsPrincipalIdealRing SevenRealCubicInt := by
  let : IsPrincipalIdealRing (𝓞 Field) :=
    ringOfIntegers_isPrincipalIdealRing
  exact
    IsPrincipalIdealRing.of_surjective
      modelEquivRingOfIntegers.symm.toRingHom
      modelEquivRingOfIntegers.symm.surjective

end SevenRealCubic

namespace SevenRealCubicInt

/-- A linear source in the basis `1, alpha, alpha²`. -/
def linearSource (a b : ℤ) : SevenRealCubicInt :=
  ⟨a, b, 0⟩

@[simp] theorem linearSource_fst (a b : ℤ) :
    (linearSource a b).fst = a := rfl

@[simp] theorem linearSource_snd (a b : ℤ) :
    (linearSource a b).snd = b := rfl

@[simp] theorem linearSource_thd (a b : ℤ) :
    (linearSource a b).thd = 0 := rfl

theorem linearSource_eq (a b : ℤ) :
    linearSource a b =
      (a : SevenRealCubicInt) + (b : SevenRealCubicInt) * alpha := by
  ext <;> simp [linearSource, alpha]

@[simp] theorem leftSource_eq_linearSource (a n : ℤ) :
    leftSource a n = linearSource a (-n) := by
  ext <;> simp [leftSource, linearSource]

@[simp] theorem rightSource_eq_linearSource (a n : ℤ) :
    rightSource a n = linearSource (a + n) n := rfl

/-- The first cyclic conjugate differs from a linear source by the
Eisenstein axis, the unit `alpha`, and its second coordinate. -/
theorem rotateEquiv_linearSource_sub
    (a b : ℤ) :
    rotateEquiv (linearSource a b) - linearSource a b =
      eisensteinAxis * alpha * (b : SevenRealCubicInt) := by
  ext <;>
    simp [linearSource, rotateEquiv, rotateHom, eisensteinAxis, alpha]
  all_goals ring

set_option maxHeartbeats 800000 in
-- Expanding the three cyclic coordinate products exceeds the project default.
/-- The determinant norm is the product of the three cyclic conjugates. -/
theorem mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm
    (x : SevenRealCubicInt) :
    x * rotateEquiv x * rotateEquiv (rotateEquiv x) =
      (norm x : SevenRealCubicInt) := by
  rw [intCast_eq]
  rcases x with ⟨a, b, c⟩
  ext <;>
    simp [rotateEquiv, rotateHom, norm, pow_succ, ofInt] <;>
    ring

private theorem prime_dvd_intCast_of_dvd_eisensteinAxis
    {q : SevenRealCubicInt} (hq : Prime q)
    (hqtheta : q ∣ eisensteinAxis) :
    q ∣ (7 : SevenRealCubicInt) := by
  have hqcube : q ∣ eisensteinAxis ^ 3 :=
    dvd_pow hqtheta (by norm_num)
  rw [eisensteinAxis_cube] at hqcube
  rcases hq.dvd_mul.mp hqcube with hqseven | hqunit
  · obtain ⟨k, hk⟩ := hqseven
    refine ⟨-k, ?_⟩
    calc
      (7 : SevenRealCubicInt) =
          -(-(7 : SevenRealCubicInt)) := by ring
      _ = -(q * k) := by rw [hk]
      _ = q * (-k) := by ring
  · exact
      (hq.not_unit
        (isUnit_of_dvd_unit hqunit
          (eisensteinAxisUnit_isUnit.pow 2))).elim

/-- A primitive linear source whose second coordinate is divisible by seven
is coprime to its first cyclic conjugate. -/
theorem linearSource_isCoprime_rotateEquiv
    (a b : ℤ) (hab : IsCoprime a b) (hseven : (7 : ℤ) ∣ b) :
    IsCoprime (linearSource a b)
      (rotateEquiv (linearSource a b)) := by
  apply isCoprime_of_prime_dvd
  · rintro ⟨hx, _⟩
    have ha : a = 0 := by
      have := congrArg SevenRealCubicInt.fst hx
      simpa using this
    have hb : b = 0 := by
      have := congrArg SevenRealCubicInt.snd hx
      simpa using this
    subst a
    subst b
    rcases hab with ⟨u, v, huv⟩
    norm_num at huv
  · intro q hq hqx hqy
    have hqdiff :
        q ∣ rotateEquiv (linearSource a b) - linearSource a b :=
      dvd_sub hqy hqx
    rw [rotateEquiv_linearSource_sub] at hqdiff
    have hqb : q ∣ (b : SevenRealCubicInt) := by
      rcases hq.dvd_mul.mp hqdiff with hqthetaAlpha | hqb
      · rcases hq.dvd_mul.mp hqthetaAlpha with hqtheta | hqalpha
        · have hqseven :
              q ∣ (7 : SevenRealCubicInt) :=
            prime_dvd_intCast_of_dvd_eisensteinAxis hq hqtheta
          obtain ⟨k, rfl⟩ := hseven
          convert dvd_mul_of_dvd_left hqseven (k : SevenRealCubicInt) using 1
          norm_num
        · exact
            (hq.not_unit
              (isUnit_of_dvd_unit hqalpha alpha_isUnit)).elim
      · exact hqb
    have hqa : q ∣ (a : SevenRealCubicInt) := by
      rw [linearSource_eq] at hqx
      simpa using
        (dvd_sub hqx
          (dvd_mul_of_dvd_left hqb alpha))
    have hcop :
        IsCoprime (a : SevenRealCubicInt)
          (b : SevenRealCubicInt) :=
      hab.map (Int.castRingHom SevenRealCubicInt)
    exact hq.not_unit (hcop.isUnit_of_dvd' hqa hqb)

/-- The three cyclic conjugates of a primitive seven-loaded linear source are
pairwise coprime. -/
theorem linearSource_cyclic_pairwiseCoprime
    (a b : ℤ) (hab : IsCoprime a b) (hseven : (7 : ℤ) ∣ b) :
    IsCoprime (linearSource a b)
        (rotateEquiv (linearSource a b)) ∧
      IsCoprime (rotateEquiv (linearSource a b))
        (rotateEquiv (rotateEquiv (linearSource a b))) ∧
      IsCoprime (linearSource a b)
        (rotateEquiv (rotateEquiv (linearSource a b))) := by
  let x := linearSource a b
  have h01 : IsCoprime x (rotateEquiv x) :=
    linearSource_isCoprime_rotateEquiv a b hab hseven
  have h12 :
      IsCoprime (rotateEquiv x)
        (rotateEquiv (rotateEquiv x)) :=
    h01.map rotateEquiv.toRingHom
  have h20 :
      IsCoprime (rotateEquiv (rotateEquiv x)) x := by
    have h := h12.map rotateEquiv.toRingHom
    change
      IsCoprime (rotateEquiv (rotateEquiv x))
        (rotateEquiv (rotateEquiv (rotateEquiv x))) at h
    rwa [rotateEquiv_three] at h
  exact ⟨h01, h12, h20.symm⟩

/-- A primitive seven-loaded linear source is coprime to the product of its
other two cyclic conjugates. -/
theorem linearSource_isCoprime_rotateEquiv_product
    (a b : ℤ) (hab : IsCoprime a b) (hseven : (7 : ℤ) ∣ b) :
    IsCoprime (linearSource a b)
      (rotateEquiv (linearSource a b) *
        rotateEquiv (rotateEquiv (linearSource a b))) := by
  rcases linearSource_cyclic_pairwiseCoprime a b hab hseven with
    ⟨h01, _, h02⟩
  exact h01.mul_right h02

/-- If the norm of a primitive seven-loaded linear source is a seventh
power, then the source itself is a seventh power up to a unit. -/
theorem exists_unit_mul_pow_seven_of_linearSource_norm_eq
    (a b z : ℤ) (hab : IsCoprime a b) (hseven : (7 : ℤ) ∣ b)
    (hnorm : norm (linearSource a b) = z ^ 7) :
    ∃ (u : SevenRealCubicIntˣ) (root : SevenRealCubicInt),
      linearSource a b = (u : SevenRealCubicInt) * root ^ 7 := by
  have hcop :
      IsCoprime (linearSource a b)
        (rotateEquiv (linearSource a b) *
          rotateEquiv (rotateEquiv (linearSource a b))) :=
    linearSource_isCoprime_rotateEquiv_product a b hab hseven
  have hproduct :
      linearSource a b *
          (rotateEquiv (linearSource a b) *
            rotateEquiv (rotateEquiv (linearSource a b))) =
        (z : SevenRealCubicInt) ^ 7 := by
    calc
      _ = linearSource a b *
            rotateEquiv (linearSource a b) *
              rotateEquiv (rotateEquiv (linearSource a b)) := by ring
      _ = (norm (linearSource a b) : SevenRealCubicInt) :=
        mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm _
      _ = (z ^ 7 : ℤ) := by rw [hnorm]
      _ = (z : SevenRealCubicInt) ^ 7 := by norm_cast
  obtain ⟨root, u, hu⟩ :=
    exists_associated_pow_of_mul_eq_pow'
      hcop hproduct
  exact ⟨u, root, by simpa [mul_comm] using hu.symm⟩

end SevenRealCubicInt

/-- RAMIFIED-011A output: both real-cubic norm sources are seventh powers up
to independently displayed units. -/
structure RamifiedRealCubicUpToUnitPacket : Type where
  normPacket : RamifiedRealCubicNormPacket
  leftUnit : SevenRealCubicIntˣ
  leftPowerRoot : SevenRealCubicInt
  leftSource_eq :
    SevenRealCubicInt.leftSource
        normPacket.quadratic.innerRoot.fst
        normPacket.quadratic.innerRoot.snd =
      (leftUnit : SevenRealCubicInt) * leftPowerRoot ^ 7
  rightUnit : SevenRealCubicIntˣ
  rightPowerRoot : SevenRealCubicInt
  rightSource_eq :
    SevenRealCubicInt.rightSource
        normPacket.quadratic.innerRoot.fst
        normPacket.quadratic.innerRoot.snd =
      (rightUnit : SevenRealCubicInt) * rightPowerRoot ^ 7

namespace RamifiedRealCubicNormPacket

open SevenRealCubicInt

theorem innerSnd_seven_dvd (p : RamifiedRealCubicNormPacket) :
    (7 : ℤ) ∣ p.quadratic.innerRoot.snd := by
  rw [p.innerSnd_eq]
  refine ⟨7 ^ 3 * p.innerSndRoot ^ 7, ?_⟩
  ring

theorem leftSource_coordinates_isCoprime
    (p : RamifiedRealCubicNormPacket) :
    IsCoprime p.quadratic.innerRoot.fst
      (-p.quadratic.innerRoot.snd) :=
  p.quadratic.innerRoot_coordinates_isCoprime.neg_right

theorem rightSource_coordinates_isCoprime
    (p : RamifiedRealCubicNormPacket) :
    IsCoprime
      (p.quadratic.innerRoot.fst +
        p.quadratic.innerRoot.snd)
      p.quadratic.innerRoot.snd := by
  simpa using
    p.quadratic.innerRoot_coordinates_isCoprime.add_mul_left_left 1

theorem leftSource_cyclic_pairwiseCoprime
    (p : RamifiedRealCubicNormPacket) :
    let x :=
      leftSource p.quadratic.innerRoot.fst
        p.quadratic.innerRoot.snd
    IsCoprime x (rotateEquiv x) ∧
      IsCoprime (rotateEquiv x) (rotateEquiv (rotateEquiv x)) ∧
      IsCoprime x (rotateEquiv (rotateEquiv x)) := by
  simpa only [leftSource_eq_linearSource] using
    linearSource_cyclic_pairwiseCoprime
      p.quadratic.innerRoot.fst
      (-p.quadratic.innerRoot.snd)
      p.leftSource_coordinates_isCoprime
      (dvd_neg.mpr p.innerSnd_seven_dvd)

theorem rightSource_cyclic_pairwiseCoprime
    (p : RamifiedRealCubicNormPacket) :
    let x :=
      rightSource p.quadratic.innerRoot.fst
        p.quadratic.innerRoot.snd
    IsCoprime x (rotateEquiv x) ∧
      IsCoprime (rotateEquiv x) (rotateEquiv (rotateEquiv x)) ∧
      IsCoprime x (rotateEquiv (rotateEquiv x)) := by
  simpa only [rightSource_eq_linearSource] using
    linearSource_cyclic_pairwiseCoprime
      (p.quadratic.innerRoot.fst +
        p.quadratic.innerRoot.snd)
      p.quadratic.innerRoot.snd
      p.rightSource_coordinates_isCoprime
      p.innerSnd_seven_dvd

/-- The left source is a seventh power up to a unit. -/
theorem exists_leftSource_unit_mul_pow_seven
    (p : RamifiedRealCubicNormPacket) :
    ∃ (u : SevenRealCubicIntˣ) (root : SevenRealCubicInt),
      leftSource p.quadratic.innerRoot.fst
          p.quadratic.innerRoot.snd =
        (u : SevenRealCubicInt) * root ^ 7 := by
  simpa only [leftSource_eq_linearSource] using
    exists_unit_mul_pow_seven_of_linearSource_norm_eq
      p.quadratic.innerRoot.fst
      (-p.quadratic.innerRoot.snd)
      p.leftRoot
      p.leftSource_coordinates_isCoprime
      (dvd_neg.mpr p.innerSnd_seven_dvd)
      (by simpa only [← leftSource_eq_linearSource] using
        p.norm_leftSource_eq)

/-- The right source is a seventh power up to a unit. -/
theorem exists_rightSource_unit_mul_pow_seven
    (p : RamifiedRealCubicNormPacket) :
    ∃ (u : SevenRealCubicIntˣ) (root : SevenRealCubicInt),
      rightSource p.quadratic.innerRoot.fst
          p.quadratic.innerRoot.snd =
        (u : SevenRealCubicInt) * root ^ 7 := by
  simpa only [rightSource_eq_linearSource] using
    exists_unit_mul_pow_seven_of_linearSource_norm_eq
      (p.quadratic.innerRoot.fst +
        p.quadratic.innerRoot.snd)
      p.quadratic.innerRoot.snd
      p.rightRoot
      p.rightSource_coordinates_isCoprime
      p.innerSnd_seven_dvd
      (by simpa only [← rightSource_eq_linearSource] using
        p.norm_rightSource_eq)

/-- Every RAMIFIED-009 norm packet now inhabits the RAMIFIED-011A
unit-times-seventh-power extraction packet. -/
theorem nonempty_upToUnit
    (p : RamifiedRealCubicNormPacket) :
    Nonempty RamifiedRealCubicUpToUnitPacket := by
  rcases p.exists_leftSource_unit_mul_pow_seven with
    ⟨leftUnit, leftPowerRoot, hleft⟩
  rcases p.exists_rightSource_unit_mul_pow_seven with
    ⟨rightUnit, rightPowerRoot, hright⟩
  exact ⟨{
    normPacket := p
    leftUnit := leftUnit
    leftPowerRoot := leftPowerRoot
    leftSource_eq := hleft
    rightUnit := rightUnit
    rightPowerRoot := rightPowerRoot
    rightSource_eq := hright }⟩

end RamifiedRealCubicNormPacket

namespace RamifiedRealCubicUpToUnitPacket

open SevenRealCubicInt

/-- The RAMIFIED-009 pure source difference, rewritten using the two
unit-times-seventh-power extractions. -/
theorem unitWeightedPowerDifference_eq
    (p : RamifiedRealCubicUpToUnitPacket) :
    (p.rightUnit : SevenRealCubicInt) * p.rightPowerRoot ^ 7 -
        (p.leftUnit : SevenRealCubicInt) * p.leftPowerRoot ^ 7 =
      normalizedAxis ^ 6 *
        normalizedWitness p.normPacket.innerSndRoot ^ 7 := by
  rw [← p.rightSource_eq, ← p.leftSource_eq]
  exact
    RamifiedRealCubicNormPacket.sourceDifference_eq_normalizedAxis_pow_six_mul_pow_seven
      p.normPacket

end RamifiedRealCubicUpToUnitPacket


end

end DkMath.FLT.Seven
