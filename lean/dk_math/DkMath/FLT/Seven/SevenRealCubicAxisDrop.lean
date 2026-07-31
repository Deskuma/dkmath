/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicUnitClass
import Mathlib.Algebra.Prime.Lemmas

#print "file: DkMath.FLT.Seven.SevenRealCubicAxisDrop"

namespace DkMath.FLT.Seven

noncomputable section

namespace SevenRealCubicInt

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Scalar theta-coordinate as a ring homomorphism to the residue field. -/
def thetaResidue : SevenRealCubicInt →+* ZMod 7 where
  toFun := thetaConstModSeven
  map_zero' := by norm_num [thetaConstModSeven]
  map_one' := thetaConstModSeven_one
  map_add' x y := by
    rcases x with ⟨a, b, c⟩
    rcases y with ⟨d, e, f⟩
    simp [thetaConstModSeven]
    ring
  map_mul' := thetaConstModSeven_mul

/-- Exact divisibility depth at the Eisenstein axis `theta`. -/
def HasExactThetaDepth
    (x : SevenRealCubicInt) (k : ℕ) : Prop :=
  eisensteinAxis ^ k ∣ x ∧
    ¬eisensteinAxis ^ (k + 1) ∣ x

/-- Multiplicativity of the determinant norm iterated over natural powers. -/
theorem norm_pow (x : SevenRealCubicInt) (n : ℕ) :
    norm (x ^ n) = norm x ^ n := by
  induction n with
  | zero => norm_num [norm]
  | succ n ih =>
      rw [pow_succ, norm_mul, ih, pow_succ]

/-- Divisibility by the Eisenstein axis is detected by the scalar
theta-coordinate modulo seven. -/
theorem eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero
    (x : SevenRealCubicInt) :
    eisensteinAxis ∣ x ↔ thetaConstModSeven x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [thetaConstModSeven_mul]
    norm_num [thetaConstModSeven, eisensteinAxis]
  · intro hx
    have hdiv :
        (7 : ℤ) ∣ x.fst + 3 * x.snd + 9 * x.thd := by
      apply
        (ZMod.intCast_zmod_eq_zero_iff_dvd
          (x.fst + 3 * x.snd + 9 * x.thd) 7).mp
      simpa [thetaConstModSeven] using hx
    rcases hdiv with ⟨k, hk⟩
    refine
      ⟨⟨x.snd + 3 * x.thd - 2 * k,
          x.thd - k, -k⟩, ?_⟩
    ext <;> simp [eisensteinAxis] <;> omega

theorem eisensteinAxis_prime :
    Prime eisensteinAxis := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg SevenRealCubicInt.snd h
    norm_num [eisensteinAxis] at this
  · intro hunit
    have hdvd : eisensteinAxis ∣ (1 : SevenRealCubicInt) :=
      hunit.dvd
    rw [eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero] at hdvd
    norm_num [thetaConstModSeven] at hdvd
  · intro x y hxy
    rw [eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero] at hxy
    rw [eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero,
      eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero]
    rw [thetaConstModSeven_mul] at hxy
    exact mul_eq_zero.mp hxy

private theorem exactDepth_mul
    {x y : SevenRealCubicInt} {m n : ℕ}
    (hx : HasExactThetaDepth x m)
    (hy : HasExactThetaDepth y n) :
    HasExactThetaDepth (x * y) (m + n) := by
  rcases hx.1 with ⟨x0, hx0⟩
  rcases hy.1 with ⟨y0, hy0⟩
  have hx0_not : ¬eisensteinAxis ∣ x0 := by
    intro h
    apply hx.2
    rcases h with ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [hx0]
    simp [pow_succ, mul_assoc, mul_comm]
  have hy0_not : ¬eisensteinAxis ∣ y0 := by
    intro h
    apply hy.2
    rcases h with ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [hy0]
    simp [pow_succ, mul_assoc, mul_comm]
  constructor
  · refine ⟨x0 * y0, ?_⟩
    rw [hx0, hy0, pow_add]
    ring
  · rintro ⟨z, hz⟩
    have hcancel :
        eisensteinAxis ∣ x0 * y0 := by
      have hz' :
          eisensteinAxis ^ (m + n + 1) ∣
            eisensteinAxis ^ (m + n) * (x0 * y0) := by
        refine ⟨z, ?_⟩
        calc
          eisensteinAxis ^ (m + n) * (x0 * y0) =
              x * y := by
            rw [hx0, hy0, pow_add]
            ring
          _ = eisensteinAxis ^ (m + n + 1) * z := hz
      rw [show m + n + 1 = (m + n) + 1 by omega,
        pow_add, pow_one,
        mul_dvd_mul_iff_left
          (pow_ne_zero (m + n) eisensteinAxis_prime.ne_zero)] at hz'
      exact hz'
    exact
      (eisensteinAxis_prime.dvd_or_dvd hcancel).elim
        hx0_not hy0_not

private theorem exactDepth_pow
    {x : SevenRealCubicInt} {m : ℕ}
    (hx : HasExactThetaDepth x m) (n : ℕ) :
    HasExactThetaDepth (x ^ n) (m * n) := by
  induction n with
  | zero =>
      constructor
      · simp
      · intro h
        exact eisensteinAxis_prime.not_unit
          (isUnit_of_dvd_one (by simpa using h))
  | succ n ih =>
      rw [pow_succ, Nat.mul_succ]
      exact exactDepth_mul ih hx

private theorem exactDepth_left_of_mul
    {x y : SevenRealCubicInt} {m n : ℕ}
    (hxy : HasExactThetaDepth (x * y) (m + n))
    (hy : HasExactThetaDepth y n) :
    HasExactThetaDepth x m := by
  rcases hy.1 with ⟨y0, hy0⟩
  have hy0_not : ¬eisensteinAxis ∣ y0 := by
    intro h
    apply hy.2
    rcases h with ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [hy0]
    simp [pow_succ, mul_assoc, mul_comm]
  have hxmuly0 : eisensteinAxis ^ m ∣ x * y0 := by
    have hprod :
        eisensteinAxis ^ (m + n) ∣
          eisensteinAxis ^ n * (x * y0) := by
      rcases hxy.1 with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      calc
        eisensteinAxis ^ n * (x * y0) =
            x * y := by rw [hy0]; ring
        _ = eisensteinAxis ^ (m + n) * z := hz
    rw [pow_add] at hprod
    rw [mul_comm (eisensteinAxis ^ m) (eisensteinAxis ^ n)] at hprod
    rw [mul_dvd_mul_iff_left
      (pow_ne_zero n eisensteinAxis_prime.ne_zero)] at hprod
    exact hprod
  have hx : eisensteinAxis ^ m ∣ x :=
    eisensteinAxis_prime.pow_dvd_of_dvd_mul_right
      m hy0_not hxmuly0
  refine ⟨hx, ?_⟩
  intro hxnext
  apply hxy.2
  rcases hxnext with ⟨x1, hx1⟩
  refine ⟨x1 * y0, ?_⟩
  rw [hx1, hy0,
    show m + n + 1 = (m + 1) + n by omega,
    pow_add]
  ring

theorem exactDepth_of_associated
    {x y : SevenRealCubicInt} {k : ℕ}
    (hxy : Associated x y)
    (hx : HasExactThetaDepth x k) :
    HasExactThetaDepth y k := by
  rcases hxy with ⟨u, rfl⟩
  have hu : HasExactThetaDepth (u : SevenRealCubicInt) 0 := by
    constructor
    · simp
    · intro h
      exact eisensteinAxis_prime.not_unit
        (isUnit_of_dvd_unit (by simpa using h) u.isUnit)
  simpa using exactDepth_mul hx hu

theorem normalizedAxis_associated_eisensteinAxis :
    Associated normalizedAxis eisensteinAxis := by
  refine
    (associated_mul_unit_left ramifiedAxis
      (ramifiedUnit ^ 4)
      (ramifiedUnit_isUnit.pow 4)).trans
      ramifiedAxis_associated_eisensteinAxis

theorem normalizedAxis_exactThetaDepth :
    HasExactThetaDepth normalizedAxis 1 := by
  apply exactDepth_of_associated
    normalizedAxis_associated_eisensteinAxis.symm
  refine ⟨by simp, ?_⟩
  rintro ⟨z, hz⟩
  have hmul : eisensteinAxis * z = 1 := by
    apply mul_left_cancel₀ eisensteinAxis_prime.ne_zero
    simpa [pow_two, mul_assoc] using hz.symm
  exact eisensteinAxis_prime.not_unit
    (IsUnit.of_mul_eq_one z hmul)

/-- Unit coefficient in the identity `7 = theta^3 * thetaSevenUnit`. -/
def thetaSevenUnit : SevenRealCubicInt :=
  -(eisensteinAxisUnitInv ^ 2)

theorem seven_eq_eisensteinAxis_cube_mul_unit :
    (7 : SevenRealCubicInt) =
      eisensteinAxis ^ 3 * thetaSevenUnit := by
  change ofInt 7 =
    eisensteinAxis ^ 3 * thetaSevenUnit
  ext <;>
    norm_num [eisensteinAxis, thetaSevenUnit,
      eisensteinAxisUnitInv, mul, pow_succ]

theorem thetaSevenUnit_isUnit :
    IsUnit thetaSevenUnit := by
  have hinv : IsUnit eisensteinAxisUnitInv := by
    apply IsUnit.of_mul_eq_one eisensteinAxisUnit
    rw [mul_comm]
    exact eisensteinAxisUnit_mul_inv
  exact (hinv.pow 2).neg

/-- Homogeneous quotient in the factorization of a seventh-power
difference. -/
def seventhQuotient
    (x y : SevenRealCubicInt) : SevenRealCubicInt :=
  x ^ 6 + x ^ 5 * y + x ^ 4 * y ^ 2 +
    x ^ 3 * y ^ 3 + x ^ 2 * y ^ 4 +
    x * y ^ 5 + y ^ 6

theorem pow_seven_sub_pow_seven_factorization
    (x y : SevenRealCubicInt) :
    x ^ 7 - y ^ 7 =
      (x - y) * seventhQuotient x y := by
  simp [seventhQuotient]
  ring

theorem seventhQuotient_add_gap
    (y d : SevenRealCubicInt) :
    seventhQuotient (y + d) y =
      7 * y ^ 6 + 21 * y ^ 5 * d +
        35 * y ^ 4 * d ^ 2 +
        35 * y ^ 3 * d ^ 3 +
        21 * y ^ 2 * d ^ 4 +
        7 * y * d ^ 5 + d ^ 6 := by
  simp [seventhQuotient]
  ring

/-- Away from the root gap, the homogeneous quotient reduces to
`7 * y^6`.  This is the coprime-core input for the axis drop. -/
theorem gap_dvd_seventhQuotient_sub_seven_mul_pow_six
    (x y : SevenRealCubicInt) :
    x - y ∣ seventhQuotient x y - 7 * y ^ 6 := by
  refine
    ⟨21 * y ^ 5 +
        35 * y ^ 4 * (x - y) +
        35 * y ^ 3 * (x - y) ^ 2 +
        21 * y ^ 2 * (x - y) ^ 3 +
        7 * y * (x - y) ^ 4 +
        (x - y) ^ 5, ?_⟩
  simp [seventhQuotient]
  ring

/-- Frobenius in the axis residue field. -/
theorem eisensteinAxis_dvd_pow_seven_sub_self
    (x : SevenRealCubicInt) :
    eisensteinAxis ∣ x ^ 7 - x := by
  rw [eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero]
  change thetaResidue (x ^ 7 - x) = 0
  rw [map_sub, map_pow, ZMod.pow_card, sub_self]

/-- Once the root gap is axis-divisible and the left root is an axis-unit,
the homogeneous seventh quotient has exact theta-depth three. -/
theorem exists_seventhQuotient_core_exactDepth_three
    (x y : SevenRealCubicInt)
    (hy : ¬eisensteinAxis ∣ y)
    (hgap : eisensteinAxis ∣ x - y) :
    ∃ core : SevenRealCubicInt,
      seventhQuotient x y = eisensteinAxis ^ 3 * core ∧
        ¬eisensteinAxis ∣ core := by
  rcases hgap with ⟨d, hd⟩
  have hx : x = y + eisensteinAxis * d := by
    rw [sub_eq_iff_eq_add] at hd
    simpa [add_comm] using hd
  let core : SevenRealCubicInt :=
    thetaSevenUnit * y ^ 6 +
      3 * thetaSevenUnit * eisensteinAxis * d * y ^ 5 +
      5 * thetaSevenUnit * eisensteinAxis ^ 2 * d ^ 2 * y ^ 4 +
      5 * thetaSevenUnit * eisensteinAxis ^ 3 * d ^ 3 * y ^ 3 +
      3 * thetaSevenUnit * eisensteinAxis ^ 4 * d ^ 4 * y ^ 2 +
      thetaSevenUnit * eisensteinAxis ^ 5 * d ^ 5 * y +
      eisensteinAxis ^ 3 * d ^ 6
  refine ⟨core, ?_, ?_⟩
  · rw [hx, seventhQuotient_add_gap,
      show (21 : SevenRealCubicInt) = 3 * 7 by norm_num,
      show (35 : SevenRealCubicInt) = 5 * 7 by norm_num,
      seven_eq_eisensteinAxis_cube_mul_unit]
    dsimp [core]
    ring
  · rw [eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero]
    change thetaResidue core ≠ 0
    have hyres : thetaResidue y ≠ 0 := by
      simpa [eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero,
        thetaResidue] using hy
    have hures : thetaResidue thetaSevenUnit ≠ 0 := by
      intro hu
      exact eisensteinAxis_prime.not_unit
        (isUnit_of_dvd_unit
          ((eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero _).mpr hu)
          thetaSevenUnit_isUnit)
    dsimp [core]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    have htheta : thetaResidue eisensteinAxis = 0 := by
      norm_num [thetaResidue, thetaConstModSeven, eisensteinAxis]
    rw [htheta]
    simp only [mul_zero, zero_mul, add_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_eq_zero, pow_eq_zero_iff, not_or]
    exact ⟨hures, hyres⟩

theorem intCast_exactThetaDepth_zero_of_not_seven_dvd
    (m : ℤ) (hm : ¬(7 : ℤ) ∣ m) :
    HasExactThetaDepth
      (m : SevenRealCubicInt) 0 := by
  constructor
  · simp
  · simpa [HasExactThetaDepth,
      eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero,
      thetaConstModSeven,
      ZMod.intCast_zmod_eq_zero_iff_dvd] using hm

theorem normalizedWitness_exactThetaDepth
    (m : ℤ) (hm : ¬(7 : ℤ) ∣ m) :
    HasExactThetaDepth (normalizedWitness m) 1 := by
  have hinv : IsUnit ramifiedUnitInv := by
    apply IsUnit.of_mul_eq_one ramifiedUnit
    rw [mul_comm]
    exact ramifiedUnit_mul_inv
  have hunit :
      HasExactThetaDepth
        (ramifiedUnitInv ^ 8) 0 := by
    refine ⟨by simp, ?_⟩
    intro h
    exact eisensteinAxis_prime.not_unit
      (isUnit_of_dvd_unit (by simpa using h) (hinv.pow 8))
  unfold normalizedWitness
  simpa using
    exactDepth_mul
      (exactDepth_mul hunit normalizedAxis_exactThetaDepth)
      (intCast_exactThetaDepth_zero_of_not_seven_dvd m hm)

end SevenRealCubicInt

namespace RamifiedRealCubicNormPacket

theorem innerSndRoot_not_seven_dvd
    (p : RamifiedRealCubicNormPacket) :
    ¬(7 : ℤ) ∣ p.innerSndRoot := by
  intro hm
  have hn0 :
      Int.natAbs p.quadratic.innerRoot.snd ≠ 0 := by
    intro hn
    have hsnd : p.quadratic.innerRoot.snd = 0 := by
      simpa using (Int.natAbs_eq_zero.mp hn)
    have hdepth := p.quadratic.innerRootSnd_depth_eq_four
    rw [hsnd] at hdepth
    norm_num at hdepth
  have h5int :
      (7 ^ 5 : ℤ) ∣ p.quadratic.innerRoot.snd := by
    rcases hm with ⟨k, hk⟩
    refine ⟨7 ^ 6 * k ^ 7, ?_⟩
    rw [p.innerSnd_eq, hk]
    ring
  have h5nat :
      7 ^ 5 ∣ Int.natAbs p.quadratic.innerRoot.snd := by
    simpa using (Int.natAbs_dvd_natAbs.mpr h5int)
  have hle :=
    (@padicValNat_dvd_iff_le 7
      ⟨by norm_num⟩
      (Int.natAbs p.quadratic.innerRoot.snd) 5 hn0).mp h5nat
  rw [p.quadratic.innerRootSnd_depth_eq_four] at hle
  omega

end RamifiedRealCubicNormPacket

namespace RamifiedRealCubicExactPowerPacket

open SevenRealCubicInt

theorem leftRoot_not_eisensteinAxis_dvd
    (p : RamifiedRealCubicExactPowerPacket) :
    ¬eisensteinAxis ∣ p.leftRoot := by
  intro hroot
  have hsource :
      eisensteinAxis ∣
        leftSource
          p.upToUnit.normPacket.quadratic.innerRoot.fst
          p.upToUnit.normPacket.quadratic.innerRoot.snd := by
    rw [p.leftSource_eq]
    exact dvd_pow hroot (by norm_num)
  have hconst :=
    thetaConstModSeven_linearSource_ne_zero
      p.upToUnit.normPacket.quadratic.innerRoot.fst
      (-p.upToUnit.normPacket.quadratic.innerRoot.snd)
      p.upToUnit.normPacket.leftSource_coordinates_isCoprime
      (dvd_neg.mpr p.upToUnit.normPacket.innerSnd_seven_dvd)
  apply hconst
  rw [← eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero]
  simpa only [leftSource_eq_linearSource] using hsource

theorem rhs_exactThetaDepth_thirteen
    (p : RamifiedRealCubicExactPowerPacket) :
    HasExactThetaDepth
      (normalizedAxis ^ 6 *
        normalizedWitness
          p.upToUnit.normPacket.innerSndRoot ^ 7) 13 := by
  have haxis :=
    exactDepth_pow normalizedAxis_exactThetaDepth 6
  have hwitness :=
    normalizedWitness_exactThetaDepth
      p.upToUnit.normPacket.innerSndRoot
      p.upToUnit.normPacket.innerSndRoot_not_seven_dvd
  have hwitness7 := exactDepth_pow hwitness 7
  simpa using exactDepth_mul haxis hwitness7

theorem eisensteinAxis_dvd_rootGap
    (p : RamifiedRealCubicExactPowerPacket) :
    eisensteinAxis ∣ p.rightRoot - p.leftRoot := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpow :
      eisensteinAxis ∣
        p.rightRoot ^ 7 - p.leftRoot ^ 7 := by
    rw [p.pureDifference_eq]
    exact
      (dvd_pow_self eisensteinAxis (by norm_num)).trans
        p.rhs_exactThetaDepth_thirteen.1
  rw [eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero] at hpow ⊢
  change thetaResidue
      (p.rightRoot ^ 7 - p.leftRoot ^ 7) = 0 at hpow
  change thetaResidue (p.rightRoot - p.leftRoot) = 0
  rw [map_sub, map_pow, map_pow] at hpow
  rw [map_sub]
  rw [ZMod.pow_card, ZMod.pow_card] at hpow
  exact hpow

/-- The two exact-power sources are coprime.  A common prime over the
ramified axis contradicts the nonzero theta residue of the left source;
every other common prime would divide both primitive integer coordinates. -/
theorem sources_isCoprime
    (p : RamifiedRealCubicExactPowerPacket) :
    IsCoprime
      (leftSource
        p.upToUnit.normPacket.quadratic.innerRoot.fst
        p.upToUnit.normPacket.quadratic.innerRoot.snd)
      (rightSource
        p.upToUnit.normPacket.quadratic.innerRoot.fst
        p.upToUnit.normPacket.quadratic.innerRoot.snd) := by
  let a := p.upToUnit.normPacket.quadratic.innerRoot.fst
  let n := p.upToUnit.normPacket.quadratic.innerRoot.snd
  apply isCoprime_of_prime_dvd
  · rintro ⟨hleft, _⟩
    apply p.leftRoot_not_eisensteinAxis_dvd
    have hroot : p.leftRoot = 0 := by
      apply eq_zero_of_pow_eq_zero
      rw [← p.leftSource_eq, hleft]
    simp [hroot]
  · intro q hq hqleft hqright
    have hqdiff :
        q ∣ ramifiedAxis * (n : SevenRealCubicInt) := by
      rw [← rightSource_sub_leftSource]
      exact dvd_sub hqright hqleft
    rcases hq.dvd_mul.mp hqdiff with hqaxis | hqn
    · have hramPrime : Prime ramifiedAxis :=
        ramifiedAxis_associated_eisensteinAxis.symm.prime
          eisensteinAxis_prime
      have hqtheta :
          Associated q eisensteinAxis :=
        (hq.associated_of_dvd hramPrime hqaxis).trans
          ramifiedAxis_associated_eisensteinAxis
      have hqroot : q ∣ p.leftRoot := by
        apply hq.dvd_of_dvd_pow
        rwa [← p.leftSource_eq]
      exact
        p.leftRoot_not_eisensteinAxis_dvd
          (hqtheta.dvd_iff_dvd_left.mp hqroot)
    · have hqna : q ∣ (n : SevenRealCubicInt) * alpha :=
        dvd_mul_of_dvd_left hqn alpha
      have hqa : q ∣ (a : SevenRealCubicInt) := by
        rw [leftSource_eq_linearSource, linearSource_eq] at hqleft
        have hsum := dvd_add hqleft hqna
        simpa [a, n] using hsum
      have hcop :
          IsCoprime (a : SevenRealCubicInt)
            (n : SevenRealCubicInt) := by
        exact
          p.upToUnit.normPacket.quadratic.innerRoot_coordinates_isCoprime.map
            (Int.castRingHom SevenRealCubicInt)
      exact hq.not_unit (hcop.isUnit_of_dvd' hqa hqn)

/-- Exact seventh roots inherit coprimality from their two sources. -/
theorem roots_isCoprime
    (p : RamifiedRealCubicExactPowerPacket) :
    IsCoprime p.leftRoot p.rightRoot := by
  apply
    (IsCoprime.pow_iff (m := 7) (n := 7)
      (by norm_num) (by norm_num)).mp
  rw [← p.leftSource_eq, ← p.rightSource_eq]
  exact p.sources_isCoprime

/-- The determinant norms of the exact algebraic roots recover the signed
integer norm roots from RAMIFIED-009. -/
theorem norm_leftRoot_eq_signedRoot
    (p : RamifiedRealCubicExactPowerPacket) :
    norm p.leftRoot =
      p.upToUnit.normPacket.leftRoot := by
  apply (show Odd 7 by norm_num).pow_injective
  change norm p.leftRoot ^ 7 =
    p.upToUnit.normPacket.leftRoot ^ 7
  rw [← norm_pow, ← p.leftSource_eq]
  exact p.upToUnit.normPacket.norm_leftSource_eq

theorem norm_rightRoot_eq_signedRoot
    (p : RamifiedRealCubicExactPowerPacket) :
    norm p.rightRoot =
      p.upToUnit.normPacket.rightRoot := by
  apply (show Odd 7 by norm_num).pow_injective
  change norm p.rightRoot ^ 7 =
    p.upToUnit.normPacket.rightRoot ^ 7
  rw [← norm_pow, ← p.rightSource_eq]
  exact p.upToUnit.normPacket.norm_rightSource_eq

/-- Exact signed-root gap shadow.  This identifies the two integer roots,
but does not turn the nonlinear norm of the algebraic gap into their
difference. -/
theorem signedRootGap_eq_norm_sub_norm
    (p : RamifiedRealCubicExactPowerPacket) :
    p.upToUnit.normPacket.rightRoot -
        p.upToUnit.normPacket.leftRoot =
      norm p.rightRoot - norm p.leftRoot := by
  rw [p.norm_leftRoot_eq_signedRoot,
    p.norm_rightRoot_eq_signedRoot]

end RamifiedRealCubicExactPowerPacket

/-- RAMIFIED-013A exact depth ledger and explicit axis-free cores. -/
structure RamifiedRealCubicDepthLedgerPacket : Type where
  exactPower : RamifiedRealCubicExactPowerPacket
  rootGap : SevenRealCubicInt
  quotient : SevenRealCubicInt
  gapCore : SevenRealCubicInt
  quotientCore : SevenRealCubicInt
  rootGap_def :
    rootGap = exactPower.rightRoot - exactPower.leftRoot
  quotient_def :
    quotient =
      SevenRealCubicInt.seventhQuotient
        exactPower.rightRoot exactPower.leftRoot
  factorization :
    exactPower.rightRoot ^ 7 -
        exactPower.leftRoot ^ 7 =
      rootGap * quotient
  rhs_exactDepth :
    SevenRealCubicInt.HasExactThetaDepth
      (SevenRealCubicInt.normalizedAxis ^ 6 *
        SevenRealCubicInt.normalizedWitness
          exactPower.upToUnit.normPacket.innerSndRoot ^ 7) 13
  quotient_eq :
    quotient =
      SevenRealCubicInt.eisensteinAxis ^ 3 * quotientCore
  quotientCore_not_axis_dvd :
    ¬SevenRealCubicInt.eisensteinAxis ∣ quotientCore
  quotient_exactDepth :
    SevenRealCubicInt.HasExactThetaDepth quotient 3
  rootGap_eq :
    rootGap = SevenRealCubicInt.eisensteinAxis ^ 10 * gapCore
  gapCore_not_axis_dvd :
    ¬SevenRealCubicInt.eisensteinAxis ∣ gapCore
  rootGap_exactDepth :
    SevenRealCubicInt.HasExactThetaDepth rootGap 10

namespace RamifiedRealCubicExactPowerPacket

open SevenRealCubicInt

theorem nonempty_depthLedger
    (p : RamifiedRealCubicExactPowerPacket) :
    Nonempty RamifiedRealCubicDepthLedgerPacket := by
  let rootGap := p.rightRoot - p.leftRoot
  let quotient := seventhQuotient p.rightRoot p.leftRoot
  obtain ⟨quotientCore, hquotient, hquotientCore⟩ :=
    exists_seventhQuotient_core_exactDepth_three
      p.rightRoot p.leftRoot
      p.leftRoot_not_eisensteinAxis_dvd
      p.eisensteinAxis_dvd_rootGap
  have hcore0 : HasExactThetaDepth quotientCore 0 := by
    refine ⟨by simp, ?_⟩
    simpa using hquotientCore
  have htheta1 : HasExactThetaDepth eisensteinAxis 1 := by
    refine ⟨by simp, ?_⟩
    rintro ⟨z, hz⟩
    have hmul : eisensteinAxis * z = 1 := by
      apply mul_left_cancel₀ eisensteinAxis_prime.ne_zero
      simpa [pow_two, mul_assoc] using hz.symm
    exact eisensteinAxis_prime.not_unit
      (IsUnit.of_mul_eq_one z hmul)
  have hquotientDepth :
      HasExactThetaDepth quotient 3 := by
    rw [show quotient =
        eisensteinAxis ^ 3 * quotientCore by
          simpa [quotient] using hquotient]
    simpa using
      exactDepth_mul (exactDepth_pow htheta1 3) hcore0
  have hproductDepth :
      HasExactThetaDepth (rootGap * quotient) 13 := by
    rw [show rootGap * quotient =
        p.rightRoot ^ 7 - p.leftRoot ^ 7 by
          simpa [rootGap, quotient] using
            (pow_seven_sub_pow_seven_factorization
              p.rightRoot p.leftRoot).symm]
    rw [p.pureDifference_eq]
    exact p.rhs_exactThetaDepth_thirteen
  have hgapDepth :
      HasExactThetaDepth rootGap 10 := by
    have := exactDepth_left_of_mul
      (m := 10) (n := 3) hproductDepth hquotientDepth
    norm_num at this ⊢
    exact this
  rcases hgapDepth.1 with ⟨gapCore, hgapCore⟩
  have hgapCoreNot : ¬eisensteinAxis ∣ gapCore := by
    intro h
    apply hgapDepth.2
    rcases h with ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [hgapCore]
    simp [pow_succ, mul_assoc, mul_comm]
  exact ⟨{
    exactPower := p
    rootGap := rootGap
    quotient := quotient
    gapCore := gapCore
    quotientCore := quotientCore
    rootGap_def := rfl
    quotient_def := rfl
    factorization := by
      simpa [rootGap, quotient] using
        pow_seven_sub_pow_seven_factorization
          p.rightRoot p.leftRoot
    rhs_exactDepth := p.rhs_exactThetaDepth_thirteen
    quotient_eq := by simpa [quotient] using hquotient
    quotientCore_not_axis_dvd := hquotientCore
    quotient_exactDepth := hquotientDepth
    rootGap_eq := hgapCore
    gapCore_not_axis_dvd := hgapCoreNot
    rootGap_exactDepth := hgapDepth }⟩

end RamifiedRealCubicExactPowerPacket

namespace RamifiedRealCubicDepthLedgerPacket

open SevenRealCubicInt

/-- After the exact theta powers have been removed, the root-gap core and
the homogeneous-quotient core are coprime. -/
theorem normalizedFactors_isCoprime
    (p : RamifiedRealCubicDepthLedgerPacket) :
    IsCoprime p.gapCore p.quotientCore := by
  apply isCoprime_of_prime_dvd
  · rintro ⟨hgap, _⟩
    apply p.gapCore_not_axis_dvd
    simp [hgap]
  · intro q hq hqgap hqquotient
    have hqRootGap : q ∣ p.rootGap := by
      rw [p.rootGap_eq]
      exact dvd_mul_of_dvd_right hqgap _
    have hqGap :
        q ∣ p.exactPower.rightRoot -
          p.exactPower.leftRoot := by
      rwa [p.rootGap_def] at hqRootGap
    have hqQuotient : q ∣ p.quotient := by
      rw [p.quotient_eq]
      exact dvd_mul_of_dvd_right hqquotient _
    have hqLeft : ¬q ∣ p.exactPower.leftRoot := by
      intro hleft
      have hright :
          q ∣ p.exactPower.rightRoot := by
        have := dvd_add hqGap hleft
        simpa using this
      exact hq.not_unit
        (p.exactPower.roots_isCoprime.isUnit_of_dvd'
          hleft hright)
    have hqRemainder :
        q ∣ p.quotient -
          7 * p.exactPower.leftRoot ^ 6 := by
      rw [p.quotient_def]
      exact hqGap.trans
        (gap_dvd_seventhQuotient_sub_seven_mul_pow_six
          p.exactPower.rightRoot p.exactPower.leftRoot)
    have hqSevenMul :
        q ∣ 7 * p.exactPower.leftRoot ^ 6 := by
      have := dvd_sub hqQuotient hqRemainder
      simpa using this
    rcases hq.dvd_mul.mp hqSevenMul with hqSeven | hqLeftPow
    · have hqThetaCube :
          q ∣ eisensteinAxis ^ 3 := by
        rw [seven_eq_eisensteinAxis_cube_mul_unit] at hqSeven
        exact
          (hq.dvd_mul.mp hqSeven).resolve_right
            (fun hunit =>
              hq.not_unit
                (isUnit_of_dvd_unit hunit thetaSevenUnit_isUnit))
      have hqTheta : q ∣ eisensteinAxis :=
        hq.dvd_of_dvd_pow hqThetaCube
      have hassoc : Associated q eisensteinAxis :=
        hq.associated_of_dvd eisensteinAxis_prime hqTheta
      exact p.gapCore_not_axis_dvd
        (hassoc.dvd_iff_dvd_left.mp hqgap)
    · exact hqLeft (hq.dvd_of_dvd_pow hqLeftPow)

/-- The product of the two axis-free cores is associated to the seventh
power of the signed inner second-coordinate root. -/
theorem cores_product_associated_pow_seven
    (p : RamifiedRealCubicDepthLedgerPacket) :
    Associated
      ((p.exactPower.upToUnit.normPacket.innerSndRoot :
          SevenRealCubicInt) ^ 7)
      (p.gapCore * p.quotientCore) := by
  let m := p.exactPower.upToUnit.normPacket.innerSndRoot
  have hinv : IsUnit ramifiedUnitInv := by
    apply IsUnit.of_mul_eq_one ramifiedUnit
    rw [mul_comm]
    exact ramifiedUnit_mul_inv
  have haxis :
      Associated normalizedAxis eisensteinAxis :=
    normalizedAxis_associated_eisensteinAxis
  have hwitness :
      Associated (normalizedWitness m)
        (eisensteinAxis * (m : SevenRealCubicInt)) := by
    change
      Associated
        (ramifiedUnitInv ^ 8 * normalizedAxis *
          (m : SevenRealCubicInt))
        (eisensteinAxis * (m : SevenRealCubicInt))
    have hunit :
        Associated
          (ramifiedUnitInv ^ 8 * normalizedAxis *
            (m : SevenRealCubicInt))
          (normalizedAxis * (m : SevenRealCubicInt)) := by
      simpa only [mul_assoc] using
        associated_unit_mul_left
          (normalizedAxis * (m : SevenRealCubicInt))
          (ramifiedUnitInv ^ 8) (hinv.pow 8)
    exact hunit.trans
      (haxis.mul_right (m : SevenRealCubicInt))
  have hrhs :
      Associated
        (normalizedAxis ^ 6 * normalizedWitness m ^ 7)
        (eisensteinAxis ^ 13 *
          (m : SevenRealCubicInt) ^ 7) := by
    have h :=
      (haxis.pow_pow (n := 6)).mul_mul
        (hwitness.pow_pow (n := 7))
    have heq :
        eisensteinAxis ^ 6 *
            (eisensteinAxis * (m : SevenRealCubicInt)) ^ 7 =
          eisensteinAxis ^ 13 *
            (m : SevenRealCubicInt) ^ 7 := by
      ring
    rw [← heq]
    exact h
  have hleft :
      p.rootGap * p.quotient =
        eisensteinAxis ^ 13 *
          (p.gapCore * p.quotientCore) := by
    rw [p.rootGap_eq, p.quotient_eq]
    ring
  have hmiddle :
      p.rootGap * p.quotient =
        normalizedAxis ^ 6 * normalizedWitness m ^ 7 := by
    rw [← p.factorization, p.exactPower.pureDifference_eq]
  have hcommon :
      Associated
        (eisensteinAxis ^ 13 *
          (p.gapCore * p.quotientCore))
        (eisensteinAxis ^ 13 *
          (m : SevenRealCubicInt) ^ 7) := by
    exact
      (Associated.of_eq (hleft.symm.trans hmiddle)).trans hrhs
  have hcores :
      Associated
        (p.gapCore * p.quotientCore)
        ((m : SevenRealCubicInt) ^ 7) :=
    Associated.of_mul_left hcommon (Associated.refl _)
      (pow_ne_zero 13 eisensteinAxis_prime.ne_zero)
  simpa [m] using hcores.symm

/-- PID coprime-power extraction places the complete away-axis content of
the root gap in a seventh power, up to a unit. -/
theorem exists_gapCore_associated_pow_seven
    (p : RamifiedRealCubicDepthLedgerPacket) :
    ∃ t : SevenRealCubicInt,
      Associated (t ^ 7) p.gapCore :=
  exists_associated_pow_of_associated_pow_mul
    p.normalizedFactors_isCoprime
    p.cores_product_associated_pow_seven

/-- The symmetric PID extraction places the quotient core in a seventh
power as well. -/
theorem exists_quotientCore_associated_pow_seven
    (p : RamifiedRealCubicDepthLedgerPacket) :
    ∃ t : SevenRealCubicInt,
      Associated (t ^ 7) p.quotientCore := by
  apply exists_associated_pow_of_associated_pow_mul
    p.normalizedFactors_isCoprime.symm
  simpa [mul_comm] using p.cores_product_associated_pow_seven

end RamifiedRealCubicDepthLedgerPacket

/-- RAMIFIED-013B output: exact depth, coprime away-axis cores, and the
root gap written as the cube of an axis associate times a seventh power. -/
structure RamifiedRealCubicAxisDropPacket : Type where
  depthLedger : RamifiedRealCubicDepthLedgerPacket
  roots_isCoprime :
    IsCoprime depthLedger.exactPower.leftRoot
      depthLedger.exactPower.rightRoot
  normalizedFactors_isCoprime :
    IsCoprime depthLedger.gapCore depthLedger.quotientCore
  droppedAxis : SevenRealCubicInt
  descentWitness : SevenRealCubicInt
  droppedAxis_associated :
    Associated droppedAxis SevenRealCubicInt.eisensteinAxis
  rootGap_eq :
    depthLedger.rootGap =
      droppedAxis ^ 3 * descentWitness ^ 7

/-- Symmetric RAMIFIED epilogue: both factors in the seventh-power
difference have an axis-cube times seventh-power presentation. -/
structure RamifiedRealCubicBalancedAxisSplitPacket : Type where
  axisDrop : RamifiedRealCubicAxisDropPacket
  quotientAxis : SevenRealCubicInt
  quotientWitness : SevenRealCubicInt
  quotientAxis_associated :
    Associated quotientAxis SevenRealCubicInt.eisensteinAxis
  quotient_eq :
    axisDrop.depthLedger.quotient =
      quotientAxis ^ 3 * quotientWitness ^ 7

namespace RamifiedRealCubicDepthLedgerPacket

open SevenRealCubicInt

/-- The exponents three and seven absorb the arbitrary PID extraction
unit, so no second unit-class computation is required. -/
theorem nonempty_axisDrop
    (p : RamifiedRealCubicDepthLedgerPacket) :
    Nonempty RamifiedRealCubicAxisDropPacket := by
  obtain ⟨t, ht⟩ := p.exists_gapCore_associated_pow_seven
  rcases ht with ⟨u, hu⟩
  let droppedAxis : SevenRealCubicInt :=
    ((u⁻¹ ^ 2 : SevenRealCubicIntˣ) :
      SevenRealCubicInt) * eisensteinAxis
  let descentWitness : SevenRealCubicInt :=
    (u : SevenRealCubicInt) * eisensteinAxis * t
  have haxis :
      Associated droppedAxis eisensteinAxis := by
    dsimp [droppedAxis]
    refine ⟨(u⁻¹ ^ 2)⁻¹, ?_⟩
    have hcoefficient :
        ((u⁻¹ : SevenRealCubicIntˣ) :
            SevenRealCubicInt) ^ 2 *
            (((u⁻¹ ^ 2)⁻¹ : SevenRealCubicIntˣ) :
              SevenRealCubicInt) = 1 := by
      exact congrArg
        (fun v : SevenRealCubicIntˣ =>
          (v : SevenRealCubicInt))
        (by simp : (u⁻¹ ^ 2) * (u⁻¹ ^ 2)⁻¹ = 1)
    calc
      ((u⁻¹ : SevenRealCubicIntˣ) :
            SevenRealCubicInt) ^ 2 *
          eisensteinAxis *
          (((u⁻¹ ^ 2)⁻¹ : SevenRealCubicIntˣ) :
            SevenRealCubicInt) =
          (((u⁻¹ : SevenRealCubicIntˣ) :
              SevenRealCubicInt) ^ 2 *
            (((u⁻¹ ^ 2)⁻¹ : SevenRealCubicIntˣ) :
              SevenRealCubicInt)) *
            eisensteinAxis := by ring
      _ = eisensteinAxis := by rw [hcoefficient, one_mul]
  have hunitUnits :
      (u⁻¹ ^ 2) ^ 3 * u ^ 7 = u := by
    group
  have hunit :
      (((u⁻¹ ^ 2 : SevenRealCubicIntˣ) :
          SevenRealCubicInt) ^ 3) *
          ((u : SevenRealCubicInt) ^ 7) =
        (u : SevenRealCubicInt) := by
    exact congrArg
      (fun v : SevenRealCubicIntˣ =>
        (v : SevenRealCubicInt)) hunitUnits
  have hgap :
      p.rootGap =
        droppedAxis ^ 3 * descentWitness ^ 7 := by
    calc
      p.rootGap =
          eisensteinAxis ^ 10 * p.gapCore :=
        p.rootGap_eq
      _ = eisensteinAxis ^ 10 *
          (t ^ 7 * (u : SevenRealCubicInt)) := by
        rw [hu]
      _ = (((u⁻¹ ^ 2 : SevenRealCubicIntˣ) :
              SevenRealCubicInt) ^ 3 *
            ((u : SevenRealCubicInt) ^ 7)) *
          eisensteinAxis ^ 10 * t ^ 7 := by
        rw [hunit]
        ring
      _ = droppedAxis ^ 3 * descentWitness ^ 7 := by
        dsimp [droppedAxis, descentWitness]
        ring
  exact ⟨{
    depthLedger := p
    roots_isCoprime := p.exactPower.roots_isCoprime
    normalizedFactors_isCoprime :=
      p.normalizedFactors_isCoprime
    droppedAxis := droppedAxis
    descentWitness := descentWitness
    droppedAxis_associated := haxis
    rootGap_eq := hgap }⟩

end RamifiedRealCubicDepthLedgerPacket

namespace RamifiedRealCubicAxisDropPacket

open SevenRealCubicInt

/-- The quotient's arbitrary extraction unit is absorbed by the same
coprime exponents three and seven used for the root gap. -/
theorem nonempty_balancedAxisSplit
    (p : RamifiedRealCubicAxisDropPacket) :
    Nonempty RamifiedRealCubicBalancedAxisSplitPacket := by
  let ledger := p.depthLedger
  obtain ⟨t, ht⟩ := ledger.exists_quotientCore_associated_pow_seven
  rcases ht with ⟨u, hu⟩
  let quotientAxis : SevenRealCubicInt :=
    ((u⁻¹ ^ 2 : SevenRealCubicIntˣ) :
      SevenRealCubicInt) * eisensteinAxis
  let quotientWitness : SevenRealCubicInt :=
    (u : SevenRealCubicInt) * t
  have haxis :
      Associated quotientAxis eisensteinAxis := by
    dsimp [quotientAxis]
    refine ⟨(u⁻¹ ^ 2)⁻¹, ?_⟩
    have hcoefficient :
        ((u⁻¹ : SevenRealCubicIntˣ) :
            SevenRealCubicInt) ^ 2 *
            (((u⁻¹ ^ 2)⁻¹ : SevenRealCubicIntˣ) :
              SevenRealCubicInt) = 1 := by
      exact congrArg
        (fun v : SevenRealCubicIntˣ =>
          (v : SevenRealCubicInt))
        (by simp : (u⁻¹ ^ 2) * (u⁻¹ ^ 2)⁻¹ = 1)
    calc
      ((u⁻¹ : SevenRealCubicIntˣ) :
            SevenRealCubicInt) ^ 2 *
          eisensteinAxis *
          (((u⁻¹ ^ 2)⁻¹ : SevenRealCubicIntˣ) :
            SevenRealCubicInt) =
          (((u⁻¹ : SevenRealCubicIntˣ) :
              SevenRealCubicInt) ^ 2 *
            (((u⁻¹ ^ 2)⁻¹ : SevenRealCubicIntˣ) :
              SevenRealCubicInt)) *
            eisensteinAxis := by ring
      _ = eisensteinAxis := by rw [hcoefficient, one_mul]
  have hunitUnits :
      (u⁻¹ ^ 2) ^ 3 * u ^ 7 = u := by
    group
  have hunit :
      (((u⁻¹ ^ 2 : SevenRealCubicIntˣ) :
          SevenRealCubicInt) ^ 3) *
          ((u : SevenRealCubicInt) ^ 7) =
        (u : SevenRealCubicInt) := by
    exact congrArg
      (fun v : SevenRealCubicIntˣ =>
        (v : SevenRealCubicInt)) hunitUnits
  have hquotient :
      ledger.quotient =
        quotientAxis ^ 3 * quotientWitness ^ 7 := by
    calc
      ledger.quotient =
          eisensteinAxis ^ 3 * ledger.quotientCore :=
        ledger.quotient_eq
      _ = eisensteinAxis ^ 3 *
          (t ^ 7 * (u : SevenRealCubicInt)) := by
        rw [hu]
      _ = (((u⁻¹ ^ 2 : SevenRealCubicIntˣ) :
              SevenRealCubicInt) ^ 3 *
            ((u : SevenRealCubicInt) ^ 7)) *
          eisensteinAxis ^ 3 * t ^ 7 := by
        rw [hunit]
        ring
      _ = quotientAxis ^ 3 * quotientWitness ^ 7 := by
        dsimp [quotientAxis, quotientWitness]
        ring
  exact ⟨{
    axisDrop := p
    quotientAxis := quotientAxis
    quotientWitness := quotientWitness
    quotientAxis_associated := haxis
    quotient_eq := hquotient }⟩

end RamifiedRealCubicAxisDropPacket

namespace RamifiedRealCubicDepthLedgerPacket

/-- Every depth ledger has the symmetric axis split at its RAMIFIED exit. -/
theorem nonempty_balancedAxisSplit
    (p : RamifiedRealCubicDepthLedgerPacket) :
    Nonempty RamifiedRealCubicBalancedAxisSplitPacket := by
  rcases p.nonempty_axisDrop with ⟨axisDrop⟩
  exact axisDrop.nonempty_balancedAxisSplit

end RamifiedRealCubicDepthLedgerPacket

namespace RamifiedRealCubicExactPowerPacket

/-- Every exact-power packet reaches the completed ramified axis-drop
packet. -/
theorem nonempty_axisDrop
    (p : RamifiedRealCubicExactPowerPacket) :
    Nonempty RamifiedRealCubicAxisDropPacket := by
  rcases p.nonempty_depthLedger with ⟨ledger⟩
  exact ledger.nonempty_axisDrop

end RamifiedRealCubicExactPowerPacket

namespace RamifiedRealCubicAxisDropPacket

open SevenRealCubicInt

/-- The dropped axis remains a prime element in the unique ramified
prime class. -/
theorem droppedAxis_prime
    (p : RamifiedRealCubicAxisDropPacket) :
    Prime p.droppedAxis :=
  p.droppedAxis_associated.symm.prime eisensteinAxis_prime

/-- Association to theta also records exact dropped-axis depth one. -/
theorem droppedAxis_exactThetaDepth
    (p : RamifiedRealCubicAxisDropPacket) :
    HasExactThetaDepth p.droppedAxis 1 :=
  exactDepth_of_associated p.droppedAxis_associated.symm
    (exactDepth_of_associated
      normalizedAxis_associated_eisensteinAxis
      normalizedAxis_exactThetaDepth)

end RamifiedRealCubicAxisDropPacket

namespace RamifiedRealCubicNormPacket

/-- Public RAMIFIED-009-to-013 endpoint: the real-cubic norm packet reaches
the completed axis drop through exact source powers and the depth ledger. -/
theorem nonempty_axisDrop
    (p : RamifiedRealCubicNormPacket) :
    Nonempty RamifiedRealCubicAxisDropPacket := by
  rcases p.nonempty_exactPower with ⟨exactPower⟩
  exact exactPower.nonempty_axisDrop

end RamifiedRealCubicNormPacket


end

end DkMath.FLT.Seven
