/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOnePrimitiveRamifiedProvenance
import DkMath.FLT.Seven.CoprimeTripleRouting
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedCompensationRouting

#print "file: DkMath.FLT.Seven.PrimeTraceOneHigherDepthRamifiedRouting"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The 7-primary factorization of the gap root.  The unit is retained as a
separate positive factor so that the second-coordinate routing remains
available when the distinguished depth is larger than one. -/
structure RamifiedGapRootPrimaryDecomposition
    (p : PrimitiveRamifiedSummitPacket) : Type where
  depth : ℕ
  unitRoot : ℕ
  depth_eq : depth = padicValNat 7 p.gapRoot
  unitRoot_pos : 0 < unitRoot
  gapRoot_eq : p.gapRoot = 7 ^ depth * unitRoot
  unitRoot_not_seven_dvd : ¬ 7 ∣ unitRoot

namespace RamifiedGapRootPrimaryDecomposition

noncomputable def ofSummit (p : PrimitiveRamifiedSummitPacket) :
    RamifiedGapRootPrimaryDecomposition p := by
  let h := Nat.exists_eq_pow_mul_and_not_dvd p.gapRoot_pos.ne' 7 (by norm_num)
  let k := Classical.choose h
  let h' := Classical.choose_spec h
  let u := Classical.choose h'
  have hu : ¬ 7 ∣ u := (Classical.choose_spec h').1
  have hku : p.gapRoot = 7 ^ k * u := (Classical.choose_spec h').2
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0, mul_zero] at hku
    exact p.gapRoot_pos.ne' hku
  have hval : padicValNat 7 p.gapRoot = k := by
    rw [hku, padicValNat.mul (pow_ne_zero _ (by norm_num)) hu0,
      padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hu, add_zero]
  have hu_pos : 0 < u := by
    have : 0 < 7 ^ k * u := by simpa [hku] using p.gapRoot_pos
    omega
  exact {
    depth := k
    unitRoot := u
    depth_eq := hval.symm
    unitRoot_pos := hu_pos
    gapRoot_eq := hku
    unitRoot_not_seven_dvd := hu }

theorem depth_eq_zero_iff
    (d : RamifiedGapRootPrimaryDecomposition p) :
    d.depth = 0 ↔ ¬ 7 ∣ p.gapRoot := by
  constructor
  · intro hd hdiv
    have hle : 1 ≤ padicValNat 7 p.gapRoot :=
      (padicValNat_dvd_iff_le p.gapRoot_pos.ne').mp hdiv
    rw [← d.depth_eq, hd] at hle
    omega
  · intro hnd
    rw [d.depth_eq, padicValNat.eq_zero_of_not_dvd hnd]

theorem unitRoot_eq_gapRoot_of_depth_eq_zero
    (d : RamifiedGapRootPrimaryDecomposition p) (hd : d.depth = 0) :
    d.unitRoot = p.gapRoot := by
  have h := d.gapRoot_eq
  rw [hd, pow_zero, one_mul] at h
  exact h.symm

end RamifiedGapRootPrimaryDecomposition

namespace PrimitiveRamifiedSummitPacket

/-- The integer identity obtained after cancelling the visible factor seven;
unlike the terminal version, this theorem has no terminality hypothesis. -/
theorem rootSnd_mul_sndCore_eq
    (p : PrimitiveRamifiedSummitPacket) :
    p.root.snd * seventhPowerSndCore p.root.fst p.root.snd =
      7 ^ 5 * (p.gapRoot : ℤ) ^ 7 *
        (ramifiedGapQuotient
          (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd := by
  have h := p.seventhPowerSnd_eq_gap_mul_quotient
  rw [seventhPowerSnd_eq_seven_mul] at h
  have hscaled :
      7 * (p.root.snd * seventhPowerSndCore p.root.fst p.root.snd) =
        7 * (7 ^ 5 * (p.gapRoot : ℤ) ^ 7 *
          (ramifiedGapQuotient
            (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd) := by
    calc
      _ = 7 * p.root.snd * seventhPowerSndCore p.root.fst p.root.snd := by ring
      _ = _ := h
      _ = _ := by ring
  exact mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num) hscaled

theorem rootSnd_sndCore_coprime
    (p : PrimitiveRamifiedSummitPacket) :
    Nat.Coprime (Int.natAbs p.root.snd)
      (Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd)) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hqv : (q : ℤ) ∣ p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqS : (q : ℤ) ∣ seventhPowerSndCore p.root.fst p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_right _ _))
  have hrest : (q : ℤ) ∣ seventhPowerSndCore p.root.fst p.root.snd -
      p.root.fst ^ 6 := by
    rcases hqv with ⟨k, hk⟩
    use 3 * p.root.fst ^ 5 * k -
      5 * p.root.fst ^ 4 * (q : ℤ) * k ^ 2 -
      15 * p.root.fst ^ 3 * (q : ℤ) ^ 2 * k ^ 3 -
      3 * p.root.fst ^ 2 * (q : ℤ) ^ 3 * k ^ 4 +
      5 * p.root.fst * (q : ℤ) ^ 4 * k ^ 5 +
      (q : ℤ) ^ 5 * k ^ 6
    simp [seventhPowerSndCore, hk]
    ring
  have hqu6 : (q : ℤ) ∣ p.root.fst ^ 6 := by
    have := dvd_sub hqS hrest
    convert this using 1
    ring
  have hqu : (q : ℤ) ∣ p.root.fst :=
    (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqu6
  exact (Nat.prime_iff_prime_int.mp hq).not_isUnit
    (p.root_coordinates_isCoprime.isUnit_of_dvd' hqu hqv)

theorem rootNorm_rootSnd_coprime
    (p : PrimitiveRamifiedSummitPacket) :
    Nat.Coprime p.residualRoot (Int.natAbs p.root.snd) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hqB : (q : ℤ) ∣ norm p.root := by
    rw [p.root_norm_eq]
    exact Int.ofNat_dvd.mpr (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqv : (q : ℤ) ∣ p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_right _ _))
  have hqrest : (q : ℤ) ∣ p.root.fst * p.root.snd +
      2 * p.root.snd ^ 2 := by
    exact dvd_add (dvd_mul_of_dvd_right hqv p.root.fst)
      (dvd_mul_of_dvd_right (dvd_pow hqv (by decide : 2 ≠ 0)) 2)
  have hqu2 : (q : ℤ) ∣ p.root.fst ^ 2 := by
    have := dvd_sub hqB hqrest
    simpa [DkMath.NumberTheory.TraceOneQuadratic.norm] using this
  have hqu : (q : ℤ) ∣ p.root.fst :=
    (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqu2
  exact (Nat.prime_iff_prime_int.mp hq).not_isUnit
    (p.root_coordinates_isCoprime.isUnit_of_dvd' hqu hqv)

theorem rootNorm_sndCore_coprime
    (p : PrimitiveRamifiedSummitPacket) :
    Nat.Coprime p.residualRoot
      (Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd)) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hqB : (q : ℤ) ∣ norm p.root := by
    rw [p.root_norm_eq]
    exact Int.ofNat_dvd.mpr (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqS : (q : ℤ) ∣ seventhPowerSndCore p.root.fst p.root.snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_right _ _))
  have hq49v6 : (q : ℤ) ∣ 49 * p.root.snd ^ 6 := by
    have hid :=
      TerminalPrimitiveRamifiedSummitPacket.sndCore_eq_norm_mul_quartic_sub_49_mul_snd_pow_six
      p.root.fst p.root.snd
    have hqNormMul : (q : ℤ) ∣ norm p.root *
        (p.root.fst ^ 4 + 2 * p.root.fst ^ 3 * p.root.snd -
          9 * p.root.fst ^ 2 * p.root.snd ^ 2 -
          10 * p.root.fst * p.root.snd ^ 3 + 25 * p.root.snd ^ 4) :=
      dvd_mul_of_dvd_left hqB _
    have := dvd_sub hqNormMul hqS
    convert this using 1
    linear_combination hid
  rcases (Nat.prime_iff_prime_int.mp hq).dvd_mul.mp hq49v6 with hq49 | hqv6
  · have hq7 : q ∣ 7 := by
      apply hq.dvd_of_dvd_pow (n := 2)
      exact_mod_cast (show (q : ℤ) ∣ (7 : ℤ) ^ 2 by
        simpa [pow_two] using hq49)
    have hqeq : q = 7 :=
      ((Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hq7).resolve_left hq.ne_one
    subst q
    exact p.residualRoot_not_seven_dvd
      (hqg.trans (Nat.gcd_dvd_left _ _))
  · have hqv : (q : ℤ) ∣ p.root.snd :=
      (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqv6
    have hqvAbs : q ∣ Int.natAbs p.root.snd := Int.natCast_dvd.mp hqv
    exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt
      (hqg.trans (Nat.gcd_dvd_left _ _)) hqvAbs) p.rootNorm_rootSnd_coprime

theorem gapRoot_endpointRight_coprime
    (p : PrimitiveRamifiedSummitPacket) :
    Nat.Coprime p.gapRoot (Int.natAbs p.endpointRight) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hqA : (q : ℤ) ∣ (p.gapRoot : ℤ) :=
    Int.natCast_dvd_natCast.mpr (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqe : (q : ℤ) ∣ p.endpointRight :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_right _ _))
  have hqgap : (q : ℤ) ∣ p.endpointLeft - p.endpointRight := by
    rw [p.gap_eq]
    exact dvd_mul_of_dvd_right (dvd_pow hqA (by decide : 7 ≠ 0)) _
  have hqc : (q : ℤ) ∣ p.endpointLeft := by
    have := dvd_add hqgap hqe
    convert this using 1
    ring
  exact (Nat.prime_iff_prime_int.mp hq).not_isUnit
    (p.endpoint_coprime.isUnit_of_dvd' hqc hqe)

theorem gapRoot_gapQuotient_coprime
    (p : PrimitiveRamifiedSummitPacket) :
    Nat.Coprime p.gapRoot
      (Int.natAbs (ramifiedGapQuotient
        (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  let h : ℤ := 7 ^ 5 * (p.gapRoot : ℤ) ^ 7
  have hqA : (q : ℤ) ∣ (p.gapRoot : ℤ) :=
    Int.natCast_dvd_natCast.mpr (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqh : (q : ℤ) ∣ h :=
    dvd_mul_of_dvd_right (dvd_pow hqA (by decide : 7 ≠ 0)) _
  have hqQ : (q : ℤ) ∣ (ramifiedGapQuotient h p.endpointRight).snd :=
    Int.natAbs_dvd_natAbs.mp (hqg.trans (Nat.gcd_dvd_right _ _))
  have hqrest : (q : ℤ) ∣ -7 * p.endpointRight * h - 14 * h ^ 2 := by
    convert dvd_add (dvd_mul_of_dvd_right hqh (-7 * p.endpointRight))
      (dvd_mul_of_dvd_right (dvd_pow hqh (by decide : 2 ≠ 0)) (-14)) using 1
    ring
  have hqe2 : (q : ℤ) ∣ p.endpointRight ^ 2 := by
    have := dvd_sub hqQ hqrest
    have hneg : (q : ℤ) ∣ -(p.endpointRight ^ 2) := by
      convert this using 1
      simp [ramifiedGapQuotient]
    simpa only [dvd_neg] using hneg
  have hqe : (q : ℤ) ∣ p.endpointRight :=
    (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqe2
  have hqeAbs : q ∣ Int.natAbs p.endpointRight := Int.natCast_dvd.mp hqe
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt
    (hqg.trans (Nat.gcd_dvd_left _ _)) hqeAbs) p.gapRoot_endpointRight_coprime

theorem secondCoordinate_natAbs_product_eq
    (p : PrimitiveRamifiedSummitPacket) :
    Int.natAbs p.root.snd * Int.natAbs
        (seventhPowerSndCore p.root.fst p.root.snd) =
      7 ^ 5 * p.gapRoot ^ 7 * Int.natAbs
        (ramifiedGapQuotient
          (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd := by
  have h := congrArg Int.natAbs p.rootSnd_mul_sndCore_eq
  simpa [Int.natAbs_mul, Int.natAbs_pow] using h

end PrimitiveRamifiedSummitPacket

structure RamifiedPrimarySecondCoordinateRoutingPacket
    (p : PrimitiveRamifiedSummitPacket) : Type where
  primary : RamifiedGapRootPrimaryDecomposition p
  routing : CoprimeTripleRouting
    (Int.natAbs p.root.snd)
    (Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd))
    1
    (7 ^ (5 + 7 * primary.depth))
    (primary.unitRoot ^ 7)
      (Int.natAbs (ramifiedGapQuotient
      (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd)

def RamifiedPrimarySecondCoordinateRoutingPacket.summit
    {p : PrimitiveRamifiedSummitPacket}
    (_ : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    PrimitiveRamifiedSummitPacket := p

namespace PrimitiveRamifiedSummitPacket

theorem nonempty_primarySecondCoordinateRouting
    (p : PrimitiveRamifiedSummitPacket) :
    Nonempty (RamifiedPrimarySecondCoordinateRoutingPacket p) := by
  let d := RamifiedGapRootPrimaryDecomposition.ofSummit p
  let Q := (ramifiedGapQuotient
    (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd
  have hvPos : 0 < Int.natAbs p.root.snd :=
    Int.natAbs_pos.mpr p.root_snd_ne_zero
  have hS0 : seventhPowerSndCore p.root.fst p.root.snd ≠ 0 := by
    intro h0
    exact p.sndCore_not_seven_dvd (by rw [h0]; exact dvd_zero 7)
  have hSPos : 0 < Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd) :=
    Int.natAbs_pos.mpr hS0
  have hQ7 : ¬ (7 : ℤ) ∣ Q :=
    ramifiedGapQuotient_snd_not_seven_dvd p.endpointRight_not_seven_dvd
  have hQ0 : Q ≠ 0 := fun h0 => hQ7 (by rw [h0]; exact dvd_zero 7)
  have hQPos : 0 < Int.natAbs Q := Int.natAbs_pos.mpr hQ0
  have hpow : p.gapRoot ^ 7 = 7 ^ (7 * d.depth) * d.unitRoot ^ 7 := by
    rw [d.gapRoot_eq]
    rw [mul_pow, ← pow_mul, Nat.mul_comm d.depth 7]
  have hprod : Int.natAbs p.root.snd *
      Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd) =
      7 ^ (5 + 7 * d.depth) * d.unitRoot ^ 7 * Int.natAbs Q := by
    calc
      _ = 7 ^ 5 * p.gapRoot ^ 7 * Int.natAbs Q :=
        p.secondCoordinate_natAbs_product_eq
      _ = 7 ^ (5 + 7 * d.depth) * d.unitRoot ^ 7 * Int.natAbs Q := by
        rw [hpow]
        ring
  have h7U : Nat.Coprime (7 ^ (5 + 7 * d.depth)) (d.unitRoot ^ 7) := by
    exact (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr
      d.unitRoot_not_seven_dvd).pow_left _).pow_right 7
  have h7Q : Nat.Coprime (7 ^ (5 + 7 * d.depth)) (Int.natAbs Q) := by
    apply ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr ?_).pow_left _
    intro hd
    exact hQ7 (Int.natCast_dvd.mpr hd)
  have hUQ : Nat.Coprime (d.unitRoot ^ 7) (Int.natAbs Q) := by
    apply (p.gapRoot_gapQuotient_coprime.of_dvd_left ?_).pow_left 7
    exact ⟨7 ^ d.depth, by rw [d.gapRoot_eq]; ring⟩
  rcases nonempty_coprimeTripleRouting
      ⟨hvPos, hSPos, by norm_num⟩
      ⟨by positivity, pow_pos d.unitRoot_pos 7, hQPos⟩
      p.rootSnd_sndCore_coprime (Nat.coprime_one_right _)
      (Nat.coprime_one_right _) h7U h7Q hUQ (by simpa using hprod) with ⟨routing⟩
  exact ⟨{
    primary := d
    routing := routing }⟩

noncomputable def primarySecondCoordinateRouting
    (p : PrimitiveRamifiedSummitPacket) :
    RamifiedPrimarySecondCoordinateRoutingPacket p :=
  Classical.choice p.nonempty_primarySecondCoordinateRouting

theorem primarySecondCoordinateRouting_depth_zero_calibration
    (p : PrimitiveRamifiedSummitPacket)
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p)
    (hd : r.primary.depth = 0) :
    r.primary.unitRoot = p.gapRoot ∧
    7 ^ (5 + 7 * r.primary.depth) = 7 ^ 5 ∧
    r.primary.unitRoot ^ 7 = p.gapRoot ^ 7 := by
  have hu := r.primary.unitRoot_eq_gapRoot_of_depth_eq_zero hd
  rw [hu, hd]
  simp

theorem higher_depth_implies_seven_dvd_gapRoot
    (p : PrimitiveRamifiedSummitPacket)
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p)
    (hhigher : 2 ≤ r.primary.depth) :
    7 ∣ p.gapRoot := by
  apply dvd_of_one_le_padicValNat
  rw [← r.primary.depth_eq]
  omega

end PrimitiveRamifiedSummitPacket

namespace PrimitiveCounterexampleRamifiedProvenance

theorem primary_depth_add_one_eq_distinguished_depth
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    (RamifiedGapRootPrimaryDecomposition.ofSummit r.summit).depth + 1 =
      padicValNat 7 r.distinguishedEndpoint := by
  let d := RamifiedGapRootPrimaryDecomposition.ofSummit r.summit
  rw [d.depth_eq, r.distinguished_padicValNat]
  omega

theorem nonempty_primary_routing
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    Nonempty (RamifiedPrimarySecondCoordinateRoutingPacket r.summit) :=
  r.summit.nonempty_primarySecondCoordinateRouting

end PrimitiveCounterexampleRamifiedProvenance

end DkMath.FLT.Seven
