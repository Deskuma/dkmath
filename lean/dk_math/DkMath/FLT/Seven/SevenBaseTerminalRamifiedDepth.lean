/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRamifiedSummit

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRamifiedDepth"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem PrimitiveRamifiedSummitPacket.root_norm_not_seven_dvd
    (p : PrimitiveRamifiedSummitPacket) :
    ¬ (7 : ℤ) ∣ norm p.root := by
  rw [p.root_norm_eq]
  exact fun h => p.residualRoot_not_seven_dvd (Int.ofNat_dvd.mp h)

theorem PrimitiveRamifiedSummitPacket.sndCore_not_seven_dvd
    (p : PrimitiveRamifiedSummitPacket) :
    ¬ (7 : ℤ) ∣
      seventhPowerSndCore p.root.fst p.root.snd :=
  seven_not_dvd_seventhPowerSndCore_of_norm p.root_norm_not_seven_dvd

theorem ramifiedGapQuotient_snd_not_seven_dvd
    {h e : ℤ} (he : ¬ (7 : ℤ) ∣ e) :
    ¬ (7 : ℤ) ∣ (ramifiedGapQuotient h e).snd := by
  intro hq
  have hrest : (7 : ℤ) ∣ 7 * e * h + 14 * h ^ 2 := by
    use e * h + 2 * h ^ 2
    ring
  have he2 : (7 : ℤ) ∣ e ^ 2 := by
    have hneg : (7 : ℤ) ∣ -(e ^ 2) := by
      have hadd := dvd_add hq hrest
      simpa [ramifiedGapQuotient] using hadd
    simpa only [dvd_neg] using hneg
  exact he ((show Prime (7 : ℤ) by norm_num).dvd_of_dvd_pow he2)

theorem PrimitiveRamifiedSummitPacket.seventhPowerSnd_eq_gap_mul_quotient
    (p : PrimitiveRamifiedSummitPacket) :
    seventhPowerSnd p.root.fst p.root.snd =
      (7 ^ 6 * (p.gapRoot : ℤ) ^ 7) *
        (ramifiedGapQuotient
          (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd := by
  let h : ℤ := 7 ^ 5 * (p.gapRoot : ℤ) ^ 7
  have hgap : p.endpointLeft = p.endpointRight + 7 * h := by
    dsimp [h]
    nlinarith [p.gap_eq]
  have hexpand :=
    cyclotomicSevenToTraceOne_add_seven_mul h p.endpointRight
  rw [← hgap] at hexpand
  have haxis :
      sevenAxis *
          (((-p.endpointRight ^ 3 : ℤ) : TraceOneInt (-2)) +
            ((7 * h : ℤ) : TraceOneInt (-2)) *
              ramifiedGapQuotient h p.endpointRight) =
        sevenAxis * p.root ^ 7 := hexpand.symm.trans p.coordinate_eq
  have haxis0 : sevenAxis ≠ 0 := by
    intro h0
    have := congrArg TraceOneInt.snd h0
    norm_num at this
  have hroot :
      (((-p.endpointRight ^ 3 : ℤ) : TraceOneInt (-2)) +
          ((7 * h : ℤ) : TraceOneInt (-2)) *
            ramifiedGapQuotient h p.endpointRight) =
        p.root ^ 7 :=
    mul_left_cancel₀ haxis0 haxis
  have hsnd := congrArg TraceOneInt.snd hroot
  rw [show (p.root ^ 7).snd =
      seventhPowerSnd p.root.fst p.root.snd by
        rcases p.root with ⟨u, v⟩
        exact traceOne_pow_seven_snd u v] at hsnd
  simp [show ((7 : TraceOneInt (-2)).fst) = 7 by rfl,
    show ((7 : TraceOneInt (-2)).snd) = 0 by rfl] at hsnd
  dsimp [h] at hsnd
  norm_num at hsnd ⊢
  ring_nf at hsnd ⊢
  exact hsnd.symm

theorem PrimitiveRamifiedSummitPacket.root_snd_ne_zero
    (p : PrimitiveRamifiedSummitPacket) : p.root.snd ≠ 0 := by
  intro hv
  have heq := p.seventhPowerSnd_eq_gap_mul_quotient
  have hleft : seventhPowerSnd p.root.fst p.root.snd = 0 := by
    rw [hv]
    simp [seventhPowerSnd]
  have hA : (p.gapRoot : ℤ) ≠ 0 := by exact_mod_cast p.gapRoot_pos.ne'
  have hQ : (ramifiedGapQuotient
      (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd ≠ 0 := by
    intro h0
    exact (ramifiedGapQuotient_snd_not_seven_dvd
      p.endpointRight_not_seven_dvd) (by rw [h0]; exact dvd_zero 7)
  have hrhs :
      (7 ^ 6 * (p.gapRoot : ℤ) ^ 7) *
        (ramifiedGapQuotient
          (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 7 hA)) hQ
  apply hrhs
  rw [← heq, hleft]

/-- RAMIFIED-001 exact depth transfer: the root second coordinate has depth
`5 mod 7`, with quotient determined by the natural gap root. -/
theorem PrimitiveRamifiedSummitPacket.rootSnd_padicValNat
    (p : PrimitiveRamifiedSummitPacket) :
    padicValNat 7 (Int.natAbs p.root.snd) =
      5 + 7 * padicValNat 7 p.gapRoot := by
  have heq := p.seventhPowerSnd_eq_gap_mul_quotient
  rw [seventhPowerSnd_eq_seven_mul] at heq
  let core := seventhPowerSndCore p.root.fst p.root.snd
  let Q := (ramifiedGapQuotient
    (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd
  have hcore7 : ¬ (7 : ℤ) ∣ core := p.sndCore_not_seven_dvd
  have hQ7 : ¬ (7 : ℤ) ∣ Q :=
    ramifiedGapQuotient_snd_not_seven_dvd p.endpointRight_not_seven_dvd
  have hv0 := p.root_snd_ne_zero
  have hA0 : (p.gapRoot : ℤ) ≠ 0 := by exact_mod_cast p.gapRoot_pos.ne'
  have hc0 : core ≠ 0 :=
    fun h0 => hcore7 (by rw [h0]; exact dvd_zero 7)
  have hQ0 : Q ≠ 0 :=
    fun h0 => hQ7 (by rw [h0]; exact dvd_zero 7)
  change 7 * p.root.snd * core =
    7 ^ 6 * (p.gapRoot : ℤ) ^ 7 * Q at heq
  have hval := congrArg (padicValInt 7) heq
  simp only [padicValInt] at hval ⊢
  simp only [Int.natAbs_mul, Int.natAbs_pow,
    Int.natAbs_natCast] at hval
  have h7abs : Int.natAbs (7 : ℤ) = 7 := rfl
  rw [h7abs] at hval
  rw [
    padicValNat.mul
      (mul_ne_zero (by norm_num) (Int.natAbs_ne_zero.mpr hv0))
      (Int.natAbs_ne_zero.mpr hc0),
    padicValNat.mul (by norm_num) (Int.natAbs_ne_zero.mpr hv0),
    padicValNat.mul
      (mul_ne_zero
        (by positivity : 7 ^ 6 ≠ 0)
        (by exact pow_ne_zero 7 p.gapRoot_pos.ne'))
      (Int.natAbs_ne_zero.mpr hQ0),
    padicValNat.mul
      (by positivity : 7 ^ 6 ≠ 0)
      (by exact pow_ne_zero 7 p.gapRoot_pos.ne'),
    padicValNat.eq_zero_of_not_dvd
      (fun hd => hcore7 (Int.natCast_dvd.mpr hd)),
    padicValNat.eq_zero_of_not_dvd
      (fun hd => hQ7 (Int.natCast_dvd.mpr hd))] at hval
  rw [padicValNat.self (by norm_num),
    padicValNat.prime_pow 6,
    padicValNat.pow p.gapRoot 7] at hval
  omega


end DkMath.FLT.Seven
