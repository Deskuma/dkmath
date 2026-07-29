/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRamifiedResidualRootClass

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRamifiedCompensationRouting"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A ramified summit together with the terminal carrier from which it was
constructed.  This is strictly stronger than `PrimitiveRamifiedSummitPacket`:
the latter deliberately forgets the selected terminal row and its carrier. -/
structure TerminalPrimitiveRamifiedSummitPacket : Type where
  summit : PrimitiveRamifiedSummitPacket
  carrierUnit : ℕ
  carrierUnit_pos : 0 < carrierUnit
  carrierUnit_not_seven_dvd : ¬ 7 ∣ carrierUnit
  carrier_eq :
    carrierUnit = summit.gapRoot * summit.residualRoot
  gap_residual_coprime :
    Nat.Coprime summit.gapRoot summit.residualRoot

namespace TerminalPrimitiveRamifiedSummitPacket

theorem gapRoot_not_seven_dvd
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    ¬ 7 ∣ p.summit.gapRoot := by
  intro h
  apply p.carrierUnit_not_seven_dvd
  rw [p.carrier_eq]
  exact dvd_mul_of_dvd_left h _

/-- The terminal origin removes the variable gap-root contribution from the
generic RAMIFIED-001 depth formula. -/
theorem rootSnd_depth_eq_five
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    padicValNat 7 (Int.natAbs p.summit.root.snd) = 5 := by
  rw [p.summit.rootSnd_padicValNat,
    padicValNat.eq_zero_of_not_dvd p.gapRoot_not_seven_dvd]

theorem endpointGap_depth_eq_six
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    padicValNat 7
      (Int.natAbs
        (p.summit.endpointLeft - p.summit.endpointRight)) = 6 := by
  rw [p.summit.endpointGap_padicValNat,
    padicValNat.eq_zero_of_not_dvd p.gapRoot_not_seven_dvd]

theorem cubicGap_depth_eq_six
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    padicValNat 7
      (Int.natAbs
        (ramifiedRightCubic p.summit.root.fst p.summit.root.snd -
          ramifiedLeftCubic p.summit.root.fst p.summit.root.snd)) = 6 := by
  rw [p.summit.cubicGap_padicValNat,
    padicValNat.eq_zero_of_not_dvd p.gapRoot_not_seven_dvd]

/-- Cancel the visible factor seven in the RAMIFIED-001 second-coordinate
equation. -/
theorem rootSnd_mul_sndCore_eq
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    p.summit.root.snd *
        seventhPowerSndCore p.summit.root.fst p.summit.root.snd =
      7 ^ 5 * (p.summit.gapRoot : ℤ) ^ 7 *
        (ramifiedGapQuotient
          (7 ^ 5 * (p.summit.gapRoot : ℤ) ^ 7)
          p.summit.endpointRight).snd := by
  have h := p.summit.seventhPowerSnd_eq_gap_mul_quotient
  rw [seventhPowerSnd_eq_seven_mul] at h
  have hscaled :
    7 * (p.summit.root.snd *
        seventhPowerSndCore p.summit.root.fst p.summit.root.snd) =
      7 * (7 ^ 5 * (p.summit.gapRoot : ℤ) ^ 7 *
        (ramifiedGapQuotient
          (7 ^ 5 * (p.summit.gapRoot : ℤ) ^ 7)
          p.summit.endpointRight).snd) := by
    calc
      _ = 7 * p.summit.root.snd *
          seventhPowerSndCore p.summit.root.fst p.summit.root.snd := by ring
      _ = _ := h
      _ = _ := by ring
  exact mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num) hscaled

/-- Polynomial certificate isolating the root norm inside the seventh-power
second-coordinate core. -/
theorem sndCore_eq_norm_mul_quartic_sub_49_mul_snd_pow_six
    (u v : ℤ) :
    seventhPowerSndCore u v =
      norm (⟨u, v⟩ : TraceOneInt (-2)) *
        (u ^ 4 + 2 * u ^ 3 * v - 9 * u ^ 2 * v ^ 2 -
          10 * u * v ^ 3 + 25 * v ^ 4) -
      49 * v ^ 6 := by
  simp [seventhPowerSndCore,
    DkMath.NumberTheory.TraceOneQuadratic.norm]
  ring

theorem rootSnd_sndCore_coprime
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    Nat.Coprime
      (Int.natAbs p.summit.root.snd)
      (Int.natAbs
        (seventhPowerSndCore
          p.summit.root.fst p.summit.root.snd)) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hqv : (q : ℤ) ∣ p.summit.root.snd :=
    Int.natAbs_dvd_natAbs.mp
      (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqS : (q : ℤ) ∣
      seventhPowerSndCore p.summit.root.fst p.summit.root.snd :=
    Int.natAbs_dvd_natAbs.mp
      (hqg.trans (Nat.gcd_dvd_right _ _))
  have hrest : (q : ℤ) ∣
      seventhPowerSndCore p.summit.root.fst p.summit.root.snd -
        p.summit.root.fst ^ 6 := by
    rcases hqv with ⟨k, hk⟩
    use
      3 * p.summit.root.fst ^ 5 * k -
      5 * p.summit.root.fst ^ 4 * (q : ℤ) * k ^ 2 -
      15 * p.summit.root.fst ^ 3 * (q : ℤ) ^ 2 * k ^ 3 -
      3 * p.summit.root.fst ^ 2 * (q : ℤ) ^ 3 * k ^ 4 +
      5 * p.summit.root.fst * (q : ℤ) ^ 4 * k ^ 5 +
      (q : ℤ) ^ 5 * k ^ 6
    simp [seventhPowerSndCore, hk]
    ring
  have hqu6 : (q : ℤ) ∣ p.summit.root.fst ^ 6 := by
    have := dvd_sub hqS hrest
    convert this using 1
    ring
  have hqu : (q : ℤ) ∣ p.summit.root.fst :=
    (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqu6
  exact (Nat.prime_iff_prime_int.mp hq).not_unit
    (p.summit.root_coordinates_isCoprime.isUnit_of_dvd' hqu hqv)

theorem rootNorm_rootSnd_coprime
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    Nat.Coprime p.summit.residualRoot
      (Int.natAbs p.summit.root.snd) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hqB : (q : ℤ) ∣ norm p.summit.root := by
    rw [p.summit.root_norm_eq]
    exact Int.ofNat_dvd.mpr
      (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqv : (q : ℤ) ∣ p.summit.root.snd :=
    Int.natAbs_dvd_natAbs.mp
      (hqg.trans (Nat.gcd_dvd_right _ _))
  have hqrest : (q : ℤ) ∣
      p.summit.root.fst * p.summit.root.snd +
        2 * p.summit.root.snd ^ 2 := by
    exact dvd_add
      (dvd_mul_of_dvd_right hqv p.summit.root.fst)
      (dvd_mul_of_dvd_right (dvd_pow hqv (by decide : 2 ≠ 0)) 2)
  have hqu2 : (q : ℤ) ∣ p.summit.root.fst ^ 2 := by
    have := dvd_sub hqB hqrest
    simpa [DkMath.NumberTheory.TraceOneQuadratic.norm] using this
  have hqu : (q : ℤ) ∣ p.summit.root.fst :=
    (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqu2
  exact (Nat.prime_iff_prime_int.mp hq).not_unit
    (p.summit.root_coordinates_isCoprime.isUnit_of_dvd' hqu hqv)

theorem rootNorm_sndCore_coprime
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    Nat.Coprime p.summit.residualRoot
      (Int.natAbs
        (seventhPowerSndCore
          p.summit.root.fst p.summit.root.snd)) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hqB : (q : ℤ) ∣ norm p.summit.root := by
    rw [p.summit.root_norm_eq]
    exact Int.ofNat_dvd.mpr
      (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqS : (q : ℤ) ∣
      seventhPowerSndCore p.summit.root.fst p.summit.root.snd :=
    Int.natAbs_dvd_natAbs.mp
      (hqg.trans (Nat.gcd_dvd_right _ _))
  have hq49v6 : (q : ℤ) ∣ 49 * p.summit.root.snd ^ 6 := by
    have hid :=
      sndCore_eq_norm_mul_quartic_sub_49_mul_snd_pow_six
        p.summit.root.fst p.summit.root.snd
    have hqNormMul : (q : ℤ) ∣
        norm p.summit.root *
          (p.summit.root.fst ^ 4 +
            2 * p.summit.root.fst ^ 3 * p.summit.root.snd -
            9 * p.summit.root.fst ^ 2 * p.summit.root.snd ^ 2 -
            10 * p.summit.root.fst * p.summit.root.snd ^ 3 +
            25 * p.summit.root.snd ^ 4) :=
      dvd_mul_of_dvd_left hqB _
    have := dvd_sub hqNormMul hqS
    convert this using 1
    nlinarith [hid]
  rcases (Nat.prime_iff_prime_int.mp hq).dvd_mul.mp hq49v6 with
      hq49 | hqv6
  · have hq7 : q ∣ 7 := by
      apply hq.dvd_of_dvd_pow (n := 2)
      exact_mod_cast (show (q : ℤ) ∣ (7 : ℤ) ^ 2 by
        simpa [pow_two] using hq49)
    have hqeq : q = 7 :=
      ((Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hq7).resolve_left
        hq.ne_one
    subst q
    exact p.summit.residualRoot_not_seven_dvd
      (hqg.trans (Nat.gcd_dvd_left _ _))
  · have hqv : (q : ℤ) ∣ p.summit.root.snd :=
      (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqv6
    have hqvAbs : q ∣ Int.natAbs p.summit.root.snd :=
      Int.natCast_dvd.mp hqv
    exact
      (Nat.not_coprime_of_dvd_of_dvd hq.one_lt
        (hqg.trans (Nat.gcd_dvd_left _ _)) hqvAbs)
        p.rootNorm_rootSnd_coprime

theorem gapRoot_endpointRight_coprime
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    Nat.Coprime p.summit.gapRoot
      (Int.natAbs p.summit.endpointRight) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  have hqA : (q : ℤ) ∣ (p.summit.gapRoot : ℤ) :=
    Int.natCast_dvd_natCast.mpr
      (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqe : (q : ℤ) ∣ p.summit.endpointRight :=
    Int.natAbs_dvd_natAbs.mp
      (hqg.trans (Nat.gcd_dvd_right _ _))
  have hqgap : (q : ℤ) ∣
      p.summit.endpointLeft - p.summit.endpointRight := by
    rw [p.summit.gap_eq]
    exact dvd_mul_of_dvd_right (dvd_pow hqA (by decide : 7 ≠ 0)) _
  have hqc : (q : ℤ) ∣ p.summit.endpointLeft := by
    have := dvd_add hqgap hqe
    convert this using 1
    ring
  exact (Nat.prime_iff_prime_int.mp hq).not_unit
    (p.summit.endpoint_coprime.isUnit_of_dvd' hqc hqe)

theorem gapRoot_gapQuotient_coprime
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    Nat.Coprime p.summit.gapRoot
      (Int.natAbs
        (ramifiedGapQuotient
          (7 ^ 5 * (p.summit.gapRoot : ℤ) ^ 7)
          p.summit.endpointRight).snd) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  rcases Nat.exists_prime_and_dvd hg with ⟨q, hq, hqg⟩
  let h : ℤ := 7 ^ 5 * (p.summit.gapRoot : ℤ) ^ 7
  have hqA : (q : ℤ) ∣ (p.summit.gapRoot : ℤ) :=
    Int.natCast_dvd_natCast.mpr
      (hqg.trans (Nat.gcd_dvd_left _ _))
  have hqh : (q : ℤ) ∣ h := by
    exact dvd_mul_of_dvd_right (dvd_pow hqA (by decide : 7 ≠ 0)) _
  have hqQ : (q : ℤ) ∣
      (ramifiedGapQuotient h p.summit.endpointRight).snd := by
    exact Int.natAbs_dvd_natAbs.mp
      (hqg.trans (Nat.gcd_dvd_right _ _))
  have hqrest : (q : ℤ) ∣
      -7 * p.summit.endpointRight * h - 14 * h ^ 2 := by
    convert dvd_add
      (dvd_mul_of_dvd_right hqh (-7 * p.summit.endpointRight))
      (dvd_mul_of_dvd_right
        (dvd_pow hqh (by decide : 2 ≠ 0)) (-14)) using 1
  have hqe2 : (q : ℤ) ∣ p.summit.endpointRight ^ 2 := by
    have := dvd_sub hqQ hqrest
    have hneg : (q : ℤ) ∣ -(p.summit.endpointRight ^ 2) := by
      convert this using 1
      simp [ramifiedGapQuotient]
    simpa only [dvd_neg] using hneg
  have hqe : (q : ℤ) ∣ p.summit.endpointRight :=
    (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hqe2
  have hqeAbs : q ∣ Int.natAbs p.summit.endpointRight :=
    Int.natCast_dvd.mp hqe
  exact
    (Nat.not_coprime_of_dvd_of_dvd hq.one_lt
      (hqg.trans (Nat.gcd_dvd_left _ _)) hqeAbs)
      p.gapRoot_endpointRight_coprime

theorem secondCoordinate_natAbs_product_eq
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    Int.natAbs p.summit.root.snd *
        Int.natAbs
          (seventhPowerSndCore
            p.summit.root.fst p.summit.root.snd) =
      7 ^ 5 * p.summit.gapRoot ^ 7 *
        Int.natAbs
          (ramifiedGapQuotient
            (7 ^ 5 * (p.summit.gapRoot : ℤ) ^ 7)
            p.summit.endpointRight).snd := by
  have h := congrArg Int.natAbs p.rootSnd_mul_sndCore_eq
  simpa [Int.natAbs_mul, Int.natAbs_pow] using h

end TerminalPrimitiveRamifiedSummitPacket

/-- The exact `2 × 3` factor-address board of RAMIFIED-006.  Its third left
row is the neutral factor one. -/
structure RamifiedSecondCoordinateRoutingPacket : Type where
  terminal : TerminalPrimitiveRamifiedSummitPacket
  routing :
    CoprimeTripleRouting
      (Int.natAbs terminal.summit.root.snd)
      (Int.natAbs
        (seventhPowerSndCore
          terminal.summit.root.fst terminal.summit.root.snd))
      1
      (7 ^ 5)
      (terminal.summit.gapRoot ^ 7)
      (Int.natAbs
        (ramifiedGapQuotient
          (7 ^ 5 * (terminal.summit.gapRoot : ℤ) ^ 7)
          terminal.summit.endpointRight).snd)

theorem TerminalPrimitiveRamifiedSummitPacket.nonempty_secondCoordinateRouting
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    Nonempty RamifiedSecondCoordinateRoutingPacket := by
  let Q := (ramifiedGapQuotient
    (7 ^ 5 * (p.summit.gapRoot : ℤ) ^ 7)
    p.summit.endpointRight).snd
  have hvPos : 0 < Int.natAbs p.summit.root.snd :=
    Int.natAbs_pos.mpr p.summit.root_snd_ne_zero
  have hS0 :
      seventhPowerSndCore p.summit.root.fst p.summit.root.snd ≠ 0 :=
    fun h0 => p.summit.sndCore_not_seven_dvd (by
      rw [h0]
      exact dvd_zero 7)
  have hSPos : 0 < Int.natAbs
      (seventhPowerSndCore p.summit.root.fst p.summit.root.snd) :=
    Int.natAbs_pos.mpr hS0
  have hQ7 : ¬ (7 : ℤ) ∣ Q :=
    ramifiedGapQuotient_snd_not_seven_dvd
      p.summit.endpointRight_not_seven_dvd
  have hQ0 : Q ≠ 0 := fun h0 => hQ7 (by rw [h0]; exact dvd_zero 7)
  have hQPos : 0 < Int.natAbs Q := Int.natAbs_pos.mpr hQ0
  have h7A : Nat.Coprime (7 ^ 5) (p.summit.gapRoot ^ 7) :=
    ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr
      p.gapRoot_not_seven_dvd).pow 5 7
  have h7Q : Nat.Coprime (7 ^ 5) (Int.natAbs Q) :=
    ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr
      (fun hd => hQ7 (Int.natCast_dvd.mpr hd))).pow_left 5
  have hAQ : Nat.Coprime (p.summit.gapRoot ^ 7) (Int.natAbs Q) :=
    p.gapRoot_gapQuotient_coprime.pow_left 7
  rcases nonempty_coprimeTripleRouting
      ⟨hvPos, hSPos, by norm_num⟩
      ⟨by positivity, pow_pos p.summit.gapRoot_pos 7, hQPos⟩
      p.rootSnd_sndCore_coprime (Nat.coprime_one_right _)
      (Nat.coprime_one_right _) h7A h7Q hAQ
      (by simpa [Q, mul_assoc] using p.secondCoordinate_natAbs_product_eq) with
    ⟨routing⟩
  exact ⟨⟨p, routing⟩⟩

noncomputable def
    TerminalPrimitiveRamifiedSummitPacket.secondCoordinateRouting
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    RamifiedSecondCoordinateRoutingPacket :=
  Classical.choice p.nonempty_secondCoordinateRouting

/-- The part of the gap quotient whose prime support is actually routed into
the root second coordinate. -/
def TerminalPrimitiveRamifiedSummitPacket.ramifiedCompensationCore
    (p : TerminalPrimitiveRamifiedSummitPacket) : ℕ :=
  Nat.gcd
    (Int.natAbs p.summit.root.snd)
    (Int.natAbs
      (ramifiedGapQuotient
        (7 ^ 5 * (p.summit.gapRoot : ℤ) ^ 7)
        p.summit.endpointRight).snd)

theorem TerminalPrimitiveRamifiedSummitPacket.compensationCore_dvd_rootSnd
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    p.ramifiedCompensationCore ∣ Int.natAbs p.summit.root.snd :=
  Nat.gcd_dvd_left _ _

theorem
    TerminalPrimitiveRamifiedSummitPacket.compensationCore_dvd_gapQuotient
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    p.ramifiedCompensationCore ∣
      Int.natAbs
        (ramifiedGapQuotient
          (7 ^ 5 * (p.summit.gapRoot : ℤ) ^ 7)
          p.summit.endpointRight).snd :=
  Nat.gcd_dvd_right _ _

/-- The precise remaining integer receiver identified by RAMIFIED-006. -/
def TerminalPrimitiveRamifiedSummitPacket.RamifiedCubicGapSeventhShapeReceiver
    (p : TerminalPrimitiveRamifiedSummitPacket) : Prop :=
  ∃ w : ℕ,
    p.ramifiedCompensationCore * p.summit.residualRoot = w ^ 7

set_option maxRecDepth 100000 in
private theorem zmod49_seventh_of_mod7_one_eq_one :
    ∀ b w : ZMod 49,
      b = w ^ 7 →
      sevenPowerReductionHom 1 b = 1 →
      b = 1 := by
  decide

/-- If no compensation prime is present, the global shape receiver can only
occupy the principal residual-root digit. -/
theorem
    TerminalPrimitiveRamifiedSummitPacket.receiver_of_compensationCore_eq_one
    (p : TerminalPrimitiveRamifiedSummitPacket)
    (hcore : p.ramifiedCompensationCore = 1)
    (hreceiver : p.RamifiedCubicGapSeventhShapeReceiver) :
    (p.summit.residualRoot : ZMod 49) = 1 := by
  rcases hreceiver with ⟨w, hw⟩
  rw [hcore, one_mul] at hw
  apply zmod49_seventh_of_mod7_one_eq_one
    (p.summit.residualRoot : ZMod 49) (w : ZMod 49)
  · calc
      (p.summit.residualRoot : ZMod 49) =
          ((w ^ 7 : ℕ) : ZMod 49) :=
        congrArg (fun n : ℕ => (n : ZMod 49)) hw
      _ = (w : ZMod 49) ^ 7 := Nat.cast_pow w 7
  · simpa using p.summit.residualRoot_mod7_eq_one

/-- The terminal Row-Y constructor retains the carrier forgotten by the common
summit façade. -/
noncomputable def AwaySevenBaseTerminalRowYProfile.terminalRamifiedSummit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hy : AwaySevenBaseTerminalRowYProfile terminal) :
    TerminalPrimitiveRamifiedSummitPacket := by
  let summit := hy.ramifiedSummit
  refine {
    summit := summit
    carrierUnit := terminal.core.carrier.carrierUnit
    carrierUnit_pos := terminal.core.carrier.carrierUnit_pos
    carrierUnit_not_seven_dvd :=
      terminal.core.carrier.seven_not_dvd_carrierUnit
    carrier_eq := ?_
    gap_residual_coprime := ?_ }
  · apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 7)
    calc
      7 * terminal.core.carrier.carrierUnit = y := hy.2.1.symm
      _ = 7 * summit.gapRoot * summit.residualRoot := by
        have h := summit.distinguished_eq
        change (y : ℤ) =
          7 * (summit.gapRoot : ℤ) * summit.residualRoot at h
        exact_mod_cast h
      _ = 7 * (summit.gapRoot * summit.residualRoot) := by ring
  · dsimp [summit, AwaySevenBaseTerminalRowYProfile.ramifiedSummit]
    exact
      (Classical.choice hy.to_swapped_ramified).seventhPower.residual.powerSplit.coprime_a_b

/-- The signed terminal Row-Z constructor retains the same carrier datum. -/
noncomputable def AwaySevenBaseTerminalRowZProfile.terminalRamifiedSummit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {terminal : AwaySevenBaseTerminalUnitSectorPacket source r p}
    (hz : AwaySevenBaseTerminalRowZProfile terminal) :
    TerminalPrimitiveRamifiedSummitPacket := by
  let summit := hz.ramifiedSummit
  refine {
    summit := summit
    carrierUnit := terminal.core.carrier.carrierUnit
    carrierUnit_pos := terminal.core.carrier.carrierUnit_pos
    carrierUnit_not_seven_dvd :=
      terminal.core.carrier.seven_not_dvd_carrierUnit
    carrier_eq := ?_
    gap_residual_coprime := ?_ }
  · apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 7)
    calc
      7 * terminal.core.carrier.carrierUnit = z := hz.2.1.symm
      _ = 7 * summit.gapRoot * summit.residualRoot := by
        have h := summit.distinguished_eq
        change (z : ℤ) =
          7 * (summit.gapRoot : ℤ) * summit.residualRoot at h
        exact_mod_cast h
      _ = 7 * (summit.gapRoot * summit.residualRoot) := by ring
  · dsimp [summit, AwaySevenBaseTerminalRowZProfile.ramifiedSummit]
    exact hz.signedResidualCore.powerSplit.coprime_a_b

/-- Every surviving terminal row supplies the strengthened summit. -/
theorem AwaySevenBaseTerminalUnitSectorPacket.nonempty_terminalRamifiedSummit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    Nonempty TerminalPrimitiveRamifiedSummitPacket := by
  rcases terminal.row_profile_decision with hy | hz | hs
  · exact ⟨hy.terminalRamifiedSummit⟩
  · exact ⟨hz.terminalRamifiedSummit⟩
  · exact hs.false_of_swapped_away.elim

noncomputable def
    AwaySevenBaseTerminalUnitSectorPacket.terminalRamifiedSummit
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    (terminal : AwaySevenBaseTerminalUnitSectorPacket source r p) :
    TerminalPrimitiveRamifiedSummitPacket :=
  Classical.choice terminal.nonempty_terminalRamifiedSummit

#print axioms
  AwaySevenBaseTerminalUnitSectorPacket.terminalRamifiedSummit
#print axioms TerminalPrimitiveRamifiedSummitPacket.rootSnd_depth_eq_five
#print axioms TerminalPrimitiveRamifiedSummitPacket.rootSnd_mul_sndCore_eq
#print axioms
  TerminalPrimitiveRamifiedSummitPacket.nonempty_secondCoordinateRouting
#print axioms
  TerminalPrimitiveRamifiedSummitPacket.receiver_of_compensationCore_eq_one

end DkMath.FLT.Seven
