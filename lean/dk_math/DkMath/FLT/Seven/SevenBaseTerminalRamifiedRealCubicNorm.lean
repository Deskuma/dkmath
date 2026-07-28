/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRamifiedQuadraticInnerRoot
import DkMath.FLT.Seven.SevenRealCubicInt

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRamifiedRealCubicNorm"

namespace DkMath.FLT.Seven

namespace RamifiedQuadraticInnerRootPacket

/-- Absorb the sign in the odd seventh power while retaining the visible
depth-four factor. -/
theorem exists_signed_innerSndRoot
    (p : RamifiedQuadraticInnerRootPacket) :
    ∃ innerSndRoot : ℤ,
      p.innerRoot.snd = 7 ^ 4 * innerSndRoot ^ 7 := by
  rcases p.exists_inner_secondCoordinate_split with
    ⟨innerVerticalRoot, innerHorizontalRoot, hsnd, hcore⟩
  by_cases hn : 0 ≤ p.innerRoot.snd
  · refine ⟨innerVerticalRoot, ?_⟩
    calc
      p.innerRoot.snd =
          (Int.natAbs p.innerRoot.snd : ℤ) :=
        (Int.natAbs_of_nonneg hn).symm
      _ = (7 ^ 4 * innerVerticalRoot ^ 7 : ℕ) := by rw [hsnd]
      _ = 7 ^ 4 * (innerVerticalRoot : ℤ) ^ 7 := by norm_cast
  · refine ⟨-(innerVerticalRoot : ℤ), ?_⟩
    have hneg : 0 ≤ -p.innerRoot.snd := by omega
    have habs :
        (Int.natAbs p.innerRoot.snd : ℤ) =
          -p.innerRoot.snd := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg hneg
    calc
      p.innerRoot.snd =
          -(Int.natAbs p.innerRoot.snd : ℤ) := by omega
      _ = -((7 ^ 4 * innerVerticalRoot ^ 7 : ℕ) : ℤ) := by
        rw [hsnd]
      _ = 7 ^ 4 * (-(innerVerticalRoot : ℤ)) ^ 7 := by
        push_cast
        ring

end RamifiedQuadraticInnerRootPacket

/-- RAMIFIED-009 receiver packet: the signed cubic norm roots and the signed
depth-four second-coordinate root are chosen together. -/
structure RamifiedRealCubicNormPacket : Type where
  quadratic : RamifiedQuadraticInnerRootPacket
  innerSndRoot : ℤ
  innerSnd_eq :
    quadratic.innerRoot.snd = 7 ^ 4 * innerSndRoot ^ 7
  leftRoot : ℤ
  rightRoot : ℤ
  leftCubic_eq :
    seventhPowerSndLeftCubic
        quadratic.innerRoot.fst quadratic.innerRoot.snd =
      leftRoot ^ 7
  rightCubic_eq :
    seventhPowerSndRightCubic
        quadratic.innerRoot.fst quadratic.innerRoot.snd =
      rightRoot ^ 7

namespace RamifiedQuadraticInnerRootPacket

/-- Every RAMIFIED-008 receiver packet inhabits the real-cubic norm packet. -/
theorem nonempty_realCubicNorm
    (p : RamifiedQuadraticInnerRootPacket) :
    Nonempty RamifiedRealCubicNormPacket := by
  rcases p.exists_signed_innerSndRoot with ⟨innerSndRoot, hsnd⟩
  rcases p.exists_inner_cubic_factor_signed_seventh_powers with
    ⟨⟨leftRoot, hleft⟩, ⟨rightRoot, hright⟩⟩
  exact ⟨{
    quadratic := p
    innerSndRoot := innerSndRoot
    innerSnd_eq := hsnd
    leftRoot := leftRoot
    rightRoot := rightRoot
    leftCubic_eq := hleft
    rightCubic_eq := hright }⟩

end RamifiedQuadraticInnerRootPacket

namespace RamifiedRealCubicNormPacket

open SevenRealCubicInt

/-- The left signed seventh power is the determinant norm of `a - alpha*n`. -/
theorem norm_leftSource_eq (p : RamifiedRealCubicNormPacket) :
    norm
        (leftSource p.quadratic.innerRoot.fst
          p.quadratic.innerRoot.snd) =
      p.leftRoot ^ 7 := by
  rw [norm_leftSource, p.leftCubic_eq]

/-- The right signed seventh power is the determinant norm of
`a + (1 + alpha)*n`. -/
theorem norm_rightSource_eq (p : RamifiedRealCubicNormPacket) :
    norm
        (rightSource p.quadratic.innerRoot.fst
          p.quadratic.innerRoot.snd) =
      p.rightRoot ^ 7 := by
  rw [norm_rightSource, p.rightCubic_eq]

/-- Integer shadow of the two norm sources: their signed seventh-power gap
is the exact cubic-factor difference. -/
theorem signedRootGap_seventhPower_eq
    (p : RamifiedRealCubicNormPacket) :
    p.rightRoot ^ 7 - p.leftRoot ^ 7 =
      7 * p.quadratic.innerRoot.fst *
        p.quadratic.innerRoot.snd *
        (p.quadratic.innerRoot.fst +
          p.quadratic.innerRoot.snd) := by
  rw [← p.rightCubic_eq, ← p.leftCubic_eq]
  exact seventhPowerSnd_cubic_sub _ _

/-- The source difference is exactly the ramified cubic axis times the inner
second coordinate. -/
theorem sourceDifference_eq_ramifiedAxis_mul
    (p : RamifiedRealCubicNormPacket) :
    rightSource p.quadratic.innerRoot.fst
          p.quadratic.innerRoot.snd -
        leftSource p.quadratic.innerRoot.fst
          p.quadratic.innerRoot.snd =
      ramifiedAxis *
        (p.quadratic.innerRoot.snd : SevenRealCubicInt) :=
  rightSource_sub_leftSource _ _

/-- RAMIFIED-008's signed depth-four coordinate turns the real-cubic source
difference into a pure normalized-axis sixth power times a seventh power. -/
theorem sourceDifference_eq_normalizedAxis_pow_six_mul_pow_seven
    (p : RamifiedRealCubicNormPacket) :
    rightSource p.quadratic.innerRoot.fst
          p.quadratic.innerRoot.snd -
        leftSource p.quadratic.innerRoot.fst
          p.quadratic.innerRoot.snd =
      normalizedAxis ^ 6 *
        normalizedWitness p.innerSndRoot ^ 7 := by
  calc
    _ = ramifiedAxis *
        (p.quadratic.innerRoot.snd : SevenRealCubicInt) :=
      p.sourceDifference_eq_ramifiedAxis_mul
    _ = ramifiedAxis *
        ((7 ^ 4 * p.innerSndRoot ^ 7 : ℤ) :
          SevenRealCubicInt) := by rw [p.innerSnd_eq]
    _ = _ :=
      ramifiedAxis_mul_seven_pow_four_mul_pow_seven p.innerSndRoot

#print axioms
  RamifiedQuadraticInnerRootPacket.exists_signed_innerSndRoot
#print axioms
  RamifiedQuadraticInnerRootPacket.nonempty_realCubicNorm
#print axioms RamifiedRealCubicNormPacket.norm_leftSource_eq
#print axioms RamifiedRealCubicNormPacket.norm_rightSource_eq
#print axioms RamifiedRealCubicNormPacket.signedRootGap_seventhPower_eq
#print axioms
  RamifiedRealCubicNormPacket.sourceDifference_eq_normalizedAxis_pow_six_mul_pow_seven

end RamifiedRealCubicNormPacket

end DkMath.FLT.Seven
