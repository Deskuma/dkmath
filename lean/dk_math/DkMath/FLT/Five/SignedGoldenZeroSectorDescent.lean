/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.SignedGoldenZeroSectorInversion
import DkMath.FLT.Five.GoldenUnitClassification

#print "file: DkMath.FLT.Five.SignedGoldenZeroSectorDescent"

namespace DkMath.FLT.Five

/--
The quadratic re-entry map used in the classical exponent-five descent.  Its
norm is the quartic occurring in the second coordinate of a golden fifth
power, while its second coordinate is a square.
-/
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2, x.snd ^ 2⟩

theorem goldenZeroSectorLift_snd (x : GoldenInt) :
    (goldenZeroSectorLift x).snd = x.snd ^ 2 := rfl

theorem goldenZeroSectorLift_norm (x : GoldenInt) :
    goldenNorm (goldenZeroSectorLift x) =
      goldenFifthSndFactor x.fst x.snd := by
  simp only [goldenZeroSectorLift, goldenNorm, goldenFifthSndFactor]
  ring

theorem goldenZeroSectorLift_mul_conj (x : GoldenInt) :
    goldenMul (goldenZeroSectorLift x) (goldenConj (goldenZeroSectorLift x)) =
      goldenOfInt (goldenFifthSndFactor x.fst x.snd) := by
  rw [golden_mul_conj, goldenZeroSectorLift_norm]

/--
The invariant preserved by the fifth-power re-entry.  The visible coordinate
is five times a fifth power, and the quartic is itself a fifth power.  Keeping
both statements is what makes the construction genuinely recursive.
-/
structure GoldenZeroSectorDescentPacket where
  base : GoldenInt
  t : ℕ
  D : ℕ
  t_pos : 0 < t
  D_pos : 0 < D
  coprime_coords : Nat.Coprime base.fst.natAbs base.snd.natAbs
  snd_eq :
    base.snd = 5 * (t : ℤ) ^ 5 ∨
      base.snd = -(5 * (t : ℤ) ^ 5)
  H_eq :
    goldenFifthSndFactor base.fst base.snd = (D : ℤ) ^ 5
  five_not_dvd_norm : ¬ (5 : ℤ) ∣ goldenNorm base

def goldenZeroSectorDescentMeasure (p : GoldenZeroSectorDescentPacket) : ℕ :=
  p.base.snd.natAbs

namespace GoldenZeroSectorDescentPacket

theorem snd_ne_zero (p : GoldenZeroSectorDescentPacket) :
    p.base.snd ≠ 0 := by
  have ht : (0 : ℤ) < p.t := by exact_mod_cast p.t_pos
  rcases p.snd_eq with h | h
  · rw [h]
    exact ne_of_gt (mul_pos (by norm_num) (pow_pos ht 5))
  · rw [h]
    exact neg_ne_zero.mpr (ne_of_gt (mul_pos (by norm_num) (pow_pos ht 5)))

theorem snd_natAbs_eq (p : GoldenZeroSectorDescentPacket) :
    p.base.snd.natAbs = 5 * p.t ^ 5 := by
  rcases p.snd_eq with h | h <;> rw [h]
  · simp [Int.natAbs_mul, Int.natAbs_pow]
  · simp [Int.natAbs_mul, Int.natAbs_pow]

theorem H_pos (p : GoldenZeroSectorDescentPacket) :
    0 < goldenFifthSndFactor p.base.fst p.base.snd := by
  rw [p.H_eq]
  exact pow_pos (by exact_mod_cast p.D_pos) 5

theorem five_not_dvd_H (p : GoldenZeroSectorDescentPacket) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd := by
  intro hH
  apply p.five_not_dvd_norm
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq p.base
  have hnormSq : (5 : ℤ) ∣ goldenNorm p.base ^ 2 := by
    convert dvd_sub hH hdiff using 1 <;> ring
  exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq

theorem five_not_dvd_D (p : GoldenZeroSectorDescentPacket) :
    ¬ 5 ∣ p.D := by
  intro hD
  apply p.five_not_dvd_H
  rw [p.H_eq]
  exact dvd_pow (Int.natCast_dvd.mpr hD) (by decide : 5 ≠ 0)

theorem coprime_s_H (p : GoldenZeroSectorDescentPacket) :
    Nat.Coprime p.base.snd.natAbs
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs :=
  coprime_natAbs_goldenFifthSndFactor_of_coprime
    p.base.fst p.base.snd p.coprime_coords

theorem coprime_D_s (p : GoldenZeroSectorDescentPacket) :
    Nat.Coprime p.D p.base.snd.natAbs := by
  have hcop := p.coprime_s_H
  have hHAbs :
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs = p.D ^ 5 := by
    rw [p.H_eq, Int.natAbs_pow]
    simp
  rw [hHAbs] at hcop
  exact ((Nat.coprime_pow_right_iff (by decide : 0 < 5)
    p.base.snd.natAbs p.D).mp hcop).symm

/-- The re-entry element and its conjugate have no nonunit common divisor. -/
theorem lift_relPrime_conj (p : GoldenZeroSectorDescentPacket) :
    GoldenRelPrime (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base)) := by
  intro z hzAlpha hzConj
  have hzDiff : GoldenDivides z
      (goldenZeroSectorLift p.base -
        goldenConj (goldenZeroSectorLift p.base)) :=
    goldenDivides_sub hzAlpha hzConj
  have hzNormAlpha : goldenNorm z ∣
      goldenNorm (goldenZeroSectorLift p.base) :=
    goldenNorm_dvd_of_goldenDivides hzAlpha
  have hzNormDiff : goldenNorm z ∣
      goldenNorm (goldenZeroSectorLift p.base -
        goldenConj (goldenZeroSectorLift p.base)) :=
    goldenNorm_dvd_of_goldenDivides hzDiff
  have hzD : (goldenNorm z).natAbs ∣ p.D ^ 5 := by
    apply Int.dvd_natCast.mp
    simpa [goldenZeroSectorLift_norm, p.H_eq] using hzNormAlpha
  have hzS : (goldenNorm z).natAbs ∣
      5 * p.base.snd.natAbs ^ 4 := by
    apply Int.dvd_natCast.mp
    have hpos : goldenNorm z ∣ (5 : ℤ) * p.base.snd ^ 4 := by
      apply Int.dvd_neg.mp
      convert hzNormDiff using 1
      rw [goldenNorm_sub_conj, goldenZeroSectorLift_snd]
      ring
    have habspow : abs p.base.snd ^ 4 = p.base.snd ^ 4 := by
      rw [← abs_pow]
      exact abs_of_nonneg (by positivity)
    simpa [Int.natCast_natAbs, habspow] using hpos
  have hD5 : Nat.Coprime (p.D ^ 5) 5 :=
    Nat.Coprime.pow_left 5
      ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr
        p.five_not_dvd_D).symm
  have hDS : Nat.Coprime (p.D ^ 5) (p.base.snd.natAbs ^ 4) :=
    (Nat.Coprime.pow_left 5 p.coprime_D_s).pow_right 4
  have hcop : Nat.Coprime (p.D ^ 5)
      (5 * p.base.snd.natAbs ^ 4) := hD5.mul_right hDS
  have hone : (goldenNorm z).natAbs = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hzD hzS
  apply goldenUnit_of_norm_eq_one_or_neg_one
  omega

end GoldenZeroSectorDescentPacket

/--
A nonzero unit sector cannot have second coordinate divisible by five while
the fifth-power base has norm prime to five.  This is the packet-independent
form of the sector calculation used by the original zero-sector reduction.
-/
theorem five_dvd_norm_of_nonzero_goldenUnitSector
    {alpha gamma : GoldenInt} {i : Fin 5}
    (hi : i ≠ 0)
    (hAlpha : alpha =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5))
    (hFive : (5 : ℤ) ∣ alpha.snd) :
    (5 : ℤ) ∣ goldenNorm gamma := by
  have hS := five_dvd_goldenFifthSndPoly gamma.fst gamma.snd
  apply five_dvd_goldenNorm_of_five_dvd_fifthFst
  fin_cases i
  · exact (hi rfl).elim
  · rw [hAlpha, golden_unit_one_mul_fifth_snd] at hFive
    convert dvd_sub hFive hS using 1 <;> ring
  · rw [hAlpha, golden_unit_two_mul_fifth_snd] at hFive
    convert dvd_sub hFive (dvd_mul_of_dvd_right hS 2) using 1 <;> ring
  · rw [hAlpha, golden_unit_three_mul_fifth_snd] at hFive
    have h2F : (5 : ℤ) ∣
        2 * goldenFifthFstPoly gamma.fst gamma.snd := by
      convert dvd_sub hFive (dvd_mul_of_dvd_right hS 3) using 1 <;> ring
    rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp h2F with h52 | hF
    · norm_num at h52
    · exact hF
  · rw [hAlpha, golden_unit_four_mul_fifth_snd] at hFive
    have h3F : (5 : ℤ) ∣
        3 * goldenFifthFstPoly gamma.fst gamma.snd := by
      convert dvd_sub hFive (dvd_mul_of_dvd_right hS 5) using 1 <;> ring
    rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp h3F with h53 | hF
    · norm_num at h53
    · exact hF

namespace GoldenZeroSectorDescentPacket

/-- The re-entry element is an honest fifth power; all nonzero unit sectors die mod five. -/
theorem exists_lift_eq_fifthPower (p : GoldenZeroSectorDescentPacket) :
    ∃ gamma : GoldenInt,
      goldenZeroSectorLift p.base = goldenPow gamma 5 ∧
      goldenNorm gamma = (p.D : ℤ) := by
  have hmul :
      goldenMul (goldenZeroSectorLift p.base)
          (goldenConj (goldenZeroSectorLift p.base)) =
        goldenPow (goldenOfInt (p.D : ℤ)) 5 := by
    calc
      goldenMul (goldenZeroSectorLift p.base)
          (goldenConj (goldenZeroSectorLift p.base)) =
          goldenOfInt (goldenFifthSndFactor p.base.fst p.base.snd) :=
        goldenZeroSectorLift_mul_conj p.base
      _ = goldenOfInt ((p.D : ℤ) ^ 5) := by rw [p.H_eq]
      _ = goldenPow (goldenOfInt (p.D : ℤ)) 5 :=
        goldenOfInt_pow_five (p.D : ℤ)
  obtain ⟨epsilon, gamma, hepsilon, hfactor⟩ :=
    goldenCoprimeFactorOfFifthPower
      (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base))
      (goldenOfInt (p.D : ℤ)) p.lift_relPrime_conj hmul
  obtain ⟨i, delta, hdelta⟩ :=
    goldenUnitClassesModFifth epsilon hepsilon
  let theta := goldenMul delta gamma
  have hSector : goldenZeroSectorLift p.base =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow theta 5) := by
    rw [hfactor, hdelta]
    simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
    ring
  have hFiveAlpha : (5 : ℤ) ∣ (goldenZeroSectorLift p.base).snd := by
    rw [goldenZeroSectorLift_snd]
    rcases p.snd_eq with hs | hs
    · exact dvd_pow (by rw [hs]; exact dvd_mul_right 5 _)
        (by decide : 2 ≠ 0)
    · exact dvd_pow (by rw [hs]; exact dvd_neg.mpr (dvd_mul_right 5 _))
        (by decide : 2 ≠ 0)
  have hThetaNorm : ¬ (5 : ℤ) ∣ goldenNorm theta := by
    intro h5theta
    apply p.five_not_dvd_H
    rw [← goldenZeroSectorLift_norm p.base, hSector, goldenNorm_mul]
    apply dvd_mul_of_dvd_right
    change (5 : ℤ) ∣ goldenNorm (theta ^ 5)
    rw [goldenNorm_pow]
    exact dvd_pow h5theta (by decide : 5 ≠ 0)
  have hi : i = 0 := by
    by_contra hi
    exact hThetaNorm
      (five_dvd_norm_of_nonzero_goldenUnitSector hi hSector hFiveAlpha)
  subst i
  have hroot : goldenZeroSectorLift p.base = goldenPow theta 5 := by
    simpa [goldenPhi_pow_zero, golden_mul_eq] using hSector
  refine ⟨theta, hroot, ?_⟩
  have hn := congrArg goldenNorm hroot
  rw [goldenZeroSectorLift_norm, p.H_eq, golden_pow_eq,
    goldenNorm_pow] at hn
  exact (show Odd 5 by decide).pow_injective hn.symm

theorem fifthRoot_snd_factor_eq
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    p.base.snd ^ 2 =
      5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd := by
  have h := congrArg (fun x : GoldenInt => x.snd) hroot
  change (goldenZeroSectorLift p.base).snd =
    (goldenPow gamma 5).snd at h
  rw [goldenZeroSectorLift_snd, goldenPow_five_snd,
    goldenFifthSndPoly_eq] at h
  exact h

theorem fifthRoot_H_pos
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    0 < goldenFifthSndFactor gamma.fst gamma.snd := by
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
  have hnonneg := goldenFifthSndFactor_nonneg gamma.fst gamma.snd
  have hne : goldenFifthSndFactor gamma.fst gamma.snd ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hEq
    omega
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem fifthRoot_snd_pos
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    0 < gamma.snd := by
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
  have hH := p.fifthRoot_H_pos gamma hroot
  nlinarith

theorem fifthRoot_coprime_coords
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨q, hqPrime, hqF, hqSnd⟩
  have hqFZ : (q : ℤ) ∣ gamma.fst := Int.natCast_dvd.mpr hqF
  have hqSndZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqSnd
  have hqNormZ : (q : ℤ) ∣ goldenNorm gamma := by
    simp only [goldenNorm]
    exact dvd_sub (dvd_add (dvd_pow hqFZ (by decide : 2 ≠ 0))
      (dvd_mul_of_dvd_left hqFZ gamma.snd))
      (dvd_pow hqSndZ (by decide : 2 ≠ 0))
  have hqD : q ∣ p.D := by
    rw [hnorm] at hqNormZ
    exact_mod_cast hqNormZ
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hqBaseSqZ : (q : ℤ) ∣ p.base.snd ^ 2 := by
    rw [hEq]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqSndZ 5) _
  have hqBaseSq : q ∣ p.base.snd.natAbs ^ 2 := by
    simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hqBaseSqZ
  have hqBase : q ∣ p.base.snd.natAbs :=
    hqPrime.dvd_of_dvd_pow hqBaseSq
  exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqD hqBase)
    p.coprime_D_s

theorem fifthRoot_five_not_dvd_H
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd := by
  intro hH
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
  have hnormSq : (5 : ℤ) ∣ goldenNorm gamma ^ 2 := by
    convert dvd_sub hH hdiff using 1 <;> ring
  have hnormFive : (5 : ℤ) ∣ goldenNorm gamma :=
    (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
  rw [hnorm] at hnormFive
  exact p.five_not_dvd_D (by exact_mod_cast hnormFive)

theorem fifthRoot_measure_lt
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    gamma.snd.natAbs < p.base.snd.natAbs := by
  have hn : 0 < gamma.snd := p.fifthRoot_snd_pos gamma hroot
  have hH : 0 < goldenFifthSndFactor gamma.fst gamma.snd :=
    p.fifthRoot_H_pos gamma hroot
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hdiag := sixteen_mul_goldenFifthSndFactor_eq gamma.fst gamma.snd
  have hbound :
      5 * gamma.snd ^ 4 ≤
        16 * goldenFifthSndFactor gamma.fst gamma.snd := by
    calc
      5 * gamma.snd ^ 4 ≤
          zeroSectorX gamma.fst gamma.snd ^ 4 +
            10 * zeroSectorX gamma.fst gamma.snd ^ 2 * gamma.snd ^ 2 +
            5 * gamma.snd ^ 4 := by
        have hx : 0 ≤ zeroSectorX gamma.fst gamma.snd ^ 4 := by positivity
        have hcross : 0 ≤
            10 * zeroSectorX gamma.fst gamma.snd ^ 2 * gamma.snd ^ 2 := by
          positivity
        linarith
      _ = 16 * goldenFifthSndFactor gamma.fst gamma.snd := hdiag.symm
  have hn4 : gamma.snd ≤ gamma.snd ^ 4 := by
    have hn0 : 0 ≤ gamma.snd := hn.le
    have hn1 : 0 ≤ gamma.snd - 1 := by omega
    have hquad : 0 ≤ gamma.snd ^ 2 + gamma.snd + 1 := by positivity
    have hnonneg : 0 ≤
        gamma.snd * (gamma.snd - 1) *
          (gamma.snd ^ 2 + gamma.snd + 1) :=
      mul_nonneg (mul_nonneg hn0 hn1) hquad
    nlinarith
  have hn_lt_fiveH :
      gamma.snd < 5 * goldenFifthSndFactor gamma.fst gamma.snd := by
    nlinarith
  apply Int.natAbs_lt_iff_sq_lt.mpr
  nlinarith

/-- Coprime splitting of `n * H = 5 * (t^2)^5` preserves the recursive shape. -/
theorem fifthRoot_power_split
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    ∃ u v : ℕ,
      0 < u ∧ 0 < v ∧
      gamma.snd = 5 * (u : ℤ) ^ 5 ∧
      goldenFifthSndFactor gamma.fst gamma.snd = (v : ℤ) ^ 5 := by
  have hn : 0 < gamma.snd := p.fifthRoot_snd_pos gamma hroot
  have hH : 0 < goldenFifthSndFactor gamma.fst gamma.snd :=
    p.fifthRoot_H_pos gamma hroot
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hAbs := congrArg Int.natAbs hEq
  have hNatEq :
      p.base.snd.natAbs ^ 2 =
        5 * gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
    simpa [Int.natAbs_pow, Int.natAbs_mul] using hAbs
  have hProduct :
      gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
        5 * (p.t ^ 2) ^ 5 := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 5)
    calc
      5 * (gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs) =
          p.base.snd.natAbs ^ 2 := by
        rw [hNatEq]
        ring
      _ = (5 * p.t ^ 5) ^ 2 := by rw [p.snd_natAbs_eq]
      _ = 5 * (5 * (p.t ^ 2) ^ 5) := by ring
  have hFiveNotH :
      ¬ 5 ∣ (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
    intro h
    exact p.fifthRoot_five_not_dvd_H gamma hnorm
      (Int.natCast_dvd.mpr h)
  have hFiveN : 5 ∣ gamma.snd.natAbs := by
    have hFiveProduct : 5 ∣
        gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
      rw [hProduct]
      exact dvd_mul_right 5 _
    rcases (show Nat.Prime 5 by norm_num).dvd_mul.mp hFiveProduct with h | h
    · exact h
    · exact (hFiveNotH h).elim
  rcases hFiveN with ⟨n0, hn0⟩
  have hn0Eq :
      n0 * (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
        (p.t ^ 2) ^ 5 := by
    rw [hn0] at hProduct
    apply Nat.mul_left_cancel (by norm_num : 0 < 5)
    simpa [mul_assoc] using hProduct
  have hrootCoprime := p.fifthRoot_coprime_coords gamma hroot hnorm
  have hcopNH := coprime_natAbs_goldenFifthSndFactor_of_coprime
    gamma.fst gamma.snd hrootCoprime
  have hn0Dvd : n0 ∣ gamma.snd.natAbs := by
    rw [hn0]
    exact dvd_mul_left n0 5
  have hcopN0H : Nat.Coprime n0
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs :=
    hcopNH.of_dvd_left hn0Dvd
  have hunit : IsUnit (gcd n0
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs) := by
    simpa [Nat.Coprime] using hcopN0H
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hunit hn0Eq
  have hunit' : IsUnit (gcd
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs n0) := by
    simpa [gcd_comm] using hunit
  obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow hunit'
    (by simpa [mul_comm] using hn0Eq)
  have huPos : 0 < u := by
    by_contra hu0
    have huZero : u = 0 := Nat.eq_zero_of_not_pos hu0
    have hnZero : gamma.snd.natAbs = 0 := by simp [hn0, hu, huZero]
    exact (Int.natAbs_ne_zero.mpr (ne_of_gt hn)) hnZero
  have hvPos : 0 < v := by
    by_contra hv0
    have hvZero : v = 0 := Nat.eq_zero_of_not_pos hv0
    have hHZero :
        (goldenFifthSndFactor gamma.fst gamma.snd).natAbs = 0 := by
      simp [hv, hvZero]
    exact (Int.natAbs_ne_zero.mpr (ne_of_gt hH)) hHZero
  refine ⟨u, v, huPos, hvPos, ?_, ?_⟩
  · have hcast : (gamma.snd.natAbs : ℤ) = 5 * (u : ℤ) ^ 5 := by
      exact_mod_cast (by rw [hn0, hu])
    rw [Int.ofNat_natAbs_of_nonneg hn.le] at hcast
    exact hcast
  · have hcast :
        ((goldenFifthSndFactor gamma.fst gamma.snd).natAbs : ℤ) =
          (v : ℤ) ^ 5 := by exact_mod_cast hv
    rw [Int.ofNat_natAbs_of_nonneg hH.le] at hcast
    exact hcast

end GoldenZeroSectorDescentPacket

/-- One certified re-entry step with strict decrease of the visible coordinate. -/
structure GoldenZeroSectorStrictDescent
    (source : GoldenZeroSectorDescentPacket) where
  next : GoldenZeroSectorDescentPacket
  lift_eq : goldenZeroSectorLift source.base = goldenPow next.base 5
  measure_lt :
    goldenZeroSectorDescentMeasure next <
      goldenZeroSectorDescentMeasure source

theorem GoldenZeroSectorDescentPacket.strictDescent
    (p : GoldenZeroSectorDescentPacket) :
    Nonempty (GoldenZeroSectorStrictDescent p) := by
  obtain ⟨gamma, hroot, hnorm⟩ := p.exists_lift_eq_fifthPower
  obtain ⟨u, v, hu, hv, hsnd, hH⟩ :=
    p.fifthRoot_power_split gamma hroot hnorm
  have hcop := p.fifthRoot_coprime_coords gamma hroot hnorm
  have h5norm : ¬ (5 : ℤ) ∣ goldenNorm gamma := by
    rw [hnorm]
    intro h
    exact p.five_not_dvd_D (by exact_mod_cast h)
  let next : GoldenZeroSectorDescentPacket := {
    base := gamma
    t := u
    D := v
    t_pos := hu
    D_pos := hv
    coprime_coords := hcop
    snd_eq := Or.inl hsnd
    H_eq := hH
    five_not_dvd_norm := h5norm }
  exact ⟨{
    next := next
    lift_eq := hroot
    measure_lt := p.fifthRoot_measure_lt gamma hroot }⟩

/-- Infinite descent excludes every packet carrying the recursive fifth-power shape. -/
theorem goldenZeroSectorDescentPacket_false
    (p : GoldenZeroSectorDescentPacket) : False := by
  have noAt : ∀ n : ℕ, ∀ q : GoldenZeroSectorDescentPacket,
      goldenZeroSectorDescentMeasure q = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro q hq
        obtain ⟨step⟩ := q.strictDescent
        exact ih (goldenZeroSectorDescentMeasure step.next)
          (by simpa [hq] using step.measure_lt) step.next rfl
  exact noAt (goldenZeroSectorDescentMeasure p) p rfl

/-- Every certified arithmetic candidate enters the recursive descent invariant. -/
def goldenZeroSectorDescentPacket_of_candidate
    (p : GoldenZeroSectorCandidate) : GoldenZeroSectorDescentPacket where
  base := ⟨p.r, p.s⟩
  t := 5 * p.c ^ 2
  D := p.d ^ 2
  t_pos := mul_pos (by norm_num) (pow_pos p.c_pos 2)
  D_pos := pow_pos p.d_pos 2
  coprime_coords := p.coprime_coords
  snd_eq := Or.inr (by
    rw [p.s_eq_neg_five_pow_mul_tenth]
    push_cast
    ring)
  H_eq := by
    rw [p.H_eq_tenth]
    push_cast
    ring
  five_not_dvd_norm := by
    intro hFive
    apply p.five_not_dvd_b
    rcases p.norm_eq_or_eq_neg with h | h
    · rw [h] at hFive
      exact_mod_cast hFive
    · rw [h] at hFive
      exact_mod_cast (Int.dvd_neg.mp hFive)

/-- The deterministic candidate emitted by inversion is impossible. -/
theorem goldenZeroSectorCandidate_false
    (p : GoldenZeroSectorCandidate) : False :=
  goldenZeroSectorDescentPacket_false
    (goldenZeroSectorDescentPacket_of_candidate p)

end DkMath.FLT.Five
