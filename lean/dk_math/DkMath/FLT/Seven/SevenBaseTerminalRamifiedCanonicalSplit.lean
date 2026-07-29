/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRamifiedCompensationRouting

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRamifiedCanonicalSplit"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The canonical four-factor normalization of the RAMIFIED-006 `2 × 3`
routing board. -/
structure RamifiedSecondCoordinateCanonicalSplit : Type where
  terminal : TerminalPrimitiveRamifiedSummitPacket
  verticalGapRoot : ℕ
  horizontalGapRoot : ℕ
  compensationCore : ℕ
  quotientRemainder : ℕ
  compensationCore_eq :
    compensationCore = terminal.ramifiedCompensationCore
  gapRoot_eq :
    terminal.summit.gapRoot =
      verticalGapRoot * horizontalGapRoot
  rootSnd_eq :
    Int.natAbs terminal.summit.root.snd =
      7 ^ 5 * verticalGapRoot ^ 7 * compensationCore
  sndCore_eq :
    Int.natAbs
        (seventhPowerSndCore
          terminal.summit.root.fst terminal.summit.root.snd) =
      horizontalGapRoot ^ 7 * quotientRemainder
  gapQuotient_eq :
    Int.natAbs
        (ramifiedGapQuotient
          (7 ^ 5 * (terminal.summit.gapRoot : ℤ) ^ 7)
          terminal.summit.endpointRight).snd =
      compensationCore * quotientRemainder

namespace RamifiedSecondCoordinateRoutingPacket

private theorem column_coprime_7_gap
    (p : RamifiedSecondCoordinateRoutingPacket) :
    Nat.Coprime (7 ^ 5) (p.terminal.summit.gapRoot ^ 7) :=
  ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr
    p.terminal.gapRoot_not_seven_dvd).pow 5 7

private theorem column_coprime_7_quotient
    (p : RamifiedSecondCoordinateRoutingPacket) :
    Nat.Coprime (7 ^ 5)
      (Int.natAbs
        (ramifiedGapQuotient
          (7 ^ 5 * (p.terminal.summit.gapRoot : ℤ) ^ 7)
          p.terminal.summit.endpointRight).snd) := by
  apply
    ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr ?_).pow_left 5
  intro h
  exact
    (ramifiedGapQuotient_snd_not_seven_dvd
      p.terminal.summit.endpointRight_not_seven_dvd)
      (Int.natCast_dvd.mpr h)

private theorem column_coprime_gap_quotient
    (p : RamifiedSecondCoordinateRoutingPacket) :
    Nat.Coprime (p.terminal.summit.gapRoot ^ 7)
      (Int.natAbs
        (ramifiedGapQuotient
          (7 ^ 5 * (p.terminal.summit.gapRoot : ℤ) ^ 7)
          p.terminal.summit.endpointRight).snd) :=
  p.terminal.gapRoot_gapQuotient_coprime.pow_left 7

theorem c13_eq_compensationCore
    (p : RamifiedSecondCoordinateRoutingPacket) :
    p.routing.c13 = p.terminal.ramifiedCompensationCore := by
  exact p.routing.c13_eq_gcd
    p.column_coprime_7_quotient
    p.column_coprime_gap_quotient

private theorem c31_eq_one
    (p : RamifiedSecondCoordinateRoutingPacket) :
    p.routing.c31 = 1 := by
  rw [p.routing.c31_eq_gcd
    p.column_coprime_7_gap p.column_coprime_7_quotient]
  simp

private theorem c32_eq_one
    (p : RamifiedSecondCoordinateRoutingPacket) :
    p.routing.c32 = 1 := by
  rw [p.routing.c32_eq_gcd
    p.column_coprime_7_gap p.column_coprime_gap_quotient]
  simp

private theorem c33_eq_one
    (p : RamifiedSecondCoordinateRoutingPacket) :
    p.routing.c33 = 1 := by
  rw [p.routing.c33_eq_gcd
    p.column_coprime_7_quotient p.column_coprime_gap_quotient]
  simp

private theorem c21_eq_one
    (p : RamifiedSecondCoordinateRoutingPacket) :
    p.routing.c21 = 1 := by
  have hS7 : Nat.Coprime
      (Int.natAbs
        (seventhPowerSndCore
          p.terminal.summit.root.fst p.terminal.summit.root.snd))
      (7 ^ 5) := by
    exact
      ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr
        (fun h => p.terminal.summit.sndCore_not_seven_dvd
          (Int.natCast_dvd.mpr h))).symm.pow_right 5
  rw [p.routing.c21_eq_gcd
    p.column_coprime_7_gap p.column_coprime_7_quotient]
  exact Nat.coprime_iff_gcd_eq_one.mp hS7

private theorem c11_eq_seven_pow_five
    (p : RamifiedSecondCoordinateRoutingPacket) :
    p.routing.c11 = 7 ^ 5 := by
  have h := p.routing.col1
  rw [p.c21_eq_one, p.c31_eq_one] at h
  simpa using h.symm

/-- Every second-coordinate routing board has the unique canonical split. -/
theorem nonempty_canonicalSplit
    (p : RamifiedSecondCoordinateRoutingPacket) :
    Nonempty RamifiedSecondCoordinateCanonicalSplit := by
  have hcol2 : p.routing.c12 * p.routing.c22 =
      p.terminal.summit.gapRoot ^ 7 := by
    have h := p.routing.col2
    rw [p.c32_eq_one, mul_one] at h
    exact h.symm
  rcases seventh_power_factor_split p.routing.col2_coprime.1 hcol2 with
    ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩
  let C := p.terminal.ramifiedCompensationCore
  let D := p.routing.c23
  have hA : p.terminal.summit.gapRoot = X * Y := by
    apply Nat.pow_left_injective (by decide : 7 ≠ 0)
    calc
      p.terminal.summit.gapRoot ^ 7 =
          p.routing.c12 * p.routing.c22 := hcol2.symm
      _ = X ^ 7 * Y ^ 7 := by rw [hX, hY]
      _ = (X * Y) ^ 7 := by ring
  have hV :
      Int.natAbs p.terminal.summit.root.snd =
        7 ^ 5 * X ^ 7 * C := by
    calc
      _ = p.routing.c11 * p.routing.c12 * p.routing.c13 :=
        p.routing.row1
      _ = _ := by
        rw [p.c11_eq_seven_pow_five, hX,
          p.c13_eq_compensationCore]
  have hS :
      Int.natAbs
          (seventhPowerSndCore
            p.terminal.summit.root.fst p.terminal.summit.root.snd) =
        Y ^ 7 * D := by
    calc
      _ = p.routing.c21 * p.routing.c22 * p.routing.c23 :=
        p.routing.row2
      _ = _ := by rw [p.c21_eq_one, one_mul, hY]
  have hQ :
      Int.natAbs
          (ramifiedGapQuotient
            (7 ^ 5 * (p.terminal.summit.gapRoot : ℤ) ^ 7)
            p.terminal.summit.endpointRight).snd =
        C * D := by
    calc
      _ = p.routing.c13 * p.routing.c23 * p.routing.c33 :=
        p.routing.col3
      _ = _ := by
        rw [p.c33_eq_one, mul_one, p.c13_eq_compensationCore]
  exact ⟨{
    terminal := p.terminal
    verticalGapRoot := X
    horizontalGapRoot := Y
    compensationCore := C
    quotientRemainder := D
    compensationCore_eq := rfl
    gapRoot_eq := hA
    rootSnd_eq := hV
    sndCore_eq := hS
    gapQuotient_eq := hQ }⟩

end RamifiedSecondCoordinateRoutingPacket

noncomputable def TerminalPrimitiveRamifiedSummitPacket.canonicalSplit
    (p : TerminalPrimitiveRamifiedSummitPacket) :
    RamifiedSecondCoordinateCanonicalSplit :=
  Classical.choice p.secondCoordinateRouting.nonempty_canonicalSplit

namespace RamifiedSecondCoordinateCanonicalSplit

/-- Exact natural form of the outer root-cubic gap. -/
theorem cubicGap_natAbs_eq
    (p : RamifiedSecondCoordinateCanonicalSplit) :
    Int.natAbs
        (ramifiedRightCubic p.terminal.summit.root.fst
            p.terminal.summit.root.snd -
          ramifiedLeftCubic p.terminal.summit.root.fst
            p.terminal.summit.root.snd) =
      7 ^ 6 * p.verticalGapRoot ^ 7 *
        (p.compensationCore * p.terminal.summit.residualRoot) := by
  rw [ramifiedRightCubic_sub_left,
    p.terminal.summit.root_norm_eq, Int.natAbs_mul,
    Int.natAbs_mul, Int.natAbs_natCast, p.rootSnd_eq]
  ring

def CubicGapSeventhShape (p : RamifiedSecondCoordinateCanonicalSplit) : Prop :=
  ∃ W : ℕ,
    Int.natAbs
        (ramifiedRightCubic p.terminal.summit.root.fst
            p.terminal.summit.root.snd -
          ramifiedLeftCubic p.terminal.summit.root.fst
            p.terminal.summit.root.snd) =
      7 ^ 6 * W ^ 7

theorem vertical_coprime_compensation_residual
    (p : RamifiedSecondCoordinateCanonicalSplit) :
    Nat.Coprime p.verticalGapRoot
      (p.compensationCore * p.terminal.summit.residualRoot) := by
  have hXA : p.verticalGapRoot ∣ p.terminal.summit.gapRoot := by
    rw [p.gapRoot_eq]
    exact dvd_mul_right _ _
  have hCQ : p.compensationCore ∣
      Int.natAbs
        (ramifiedGapQuotient
          (7 ^ 5 * (p.terminal.summit.gapRoot : ℤ) ^ 7)
          p.terminal.summit.endpointRight).snd := by
    rw [p.gapQuotient_eq]
    exact dvd_mul_right _ _
  have hXC : Nat.Coprime p.verticalGapRoot p.compensationCore :=
    (p.terminal.gapRoot_gapQuotient_coprime.of_dvd_left hXA).of_dvd_right hCQ
  have hXB : Nat.Coprime
      p.verticalGapRoot p.terminal.summit.residualRoot :=
    p.terminal.gap_residual_coprime.of_dvd_left hXA
  exact hXC.mul_right hXB

theorem receiver_iff_cubicGap_seventh_shape
    (p : RamifiedSecondCoordinateCanonicalSplit) :
    p.terminal.RamifiedCubicGapSeventhShapeReceiver ↔
      p.CubicGapSeventhShape := by
  constructor
  · rintro ⟨w, hw⟩
    rw [← p.compensationCore_eq] at hw
    refine ⟨p.verticalGapRoot * w, ?_⟩
    rw [p.cubicGap_natAbs_eq, hw]
    ring
  · rintro ⟨W, hW⟩
    have hcancel :
        p.verticalGapRoot ^ 7 *
            (p.compensationCore * p.terminal.summit.residualRoot) =
          W ^ 7 := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 7 ^ 6)
      calc
        7 ^ 6 * (p.verticalGapRoot ^ 7 *
            (p.compensationCore * p.terminal.summit.residualRoot)) =
          7 ^ 6 * p.verticalGapRoot ^ 7 *
            (p.compensationCore * p.terminal.summit.residualRoot) := by ring
        _ = _ := p.cubicGap_natAbs_eq.symm.trans hW
    have hreceiver := (seventh_power_factor_split
      (p.vertical_coprime_compensation_residual.pow_left 7)
      hcancel).2
    simpa [p.compensationCore_eq] using hreceiver

theorem compensation_coprime_residual
    (p : RamifiedSecondCoordinateCanonicalSplit) :
    Nat.Coprime p.compensationCore p.terminal.summit.residualRoot := by
  have hCV : p.compensationCore ∣
      Int.natAbs p.terminal.summit.root.snd := by
    rw [p.rootSnd_eq]
    exact dvd_mul_left _ _
  exact
    (p.terminal.rootNorm_rootSnd_coprime.of_dvd_right hCV).symm

theorem receiver_iff_independent_seventh_powers
    (p : RamifiedSecondCoordinateCanonicalSplit) :
    p.terminal.RamifiedCubicGapSeventhShapeReceiver ↔
      (∃ c : ℕ, p.compensationCore = c ^ 7) ∧
      (∃ b : ℕ, p.terminal.summit.residualRoot = b ^ 7) := by
  constructor
  · rintro ⟨w, hw⟩
    rw [← p.compensationCore_eq] at hw
    exact seventh_power_factor_split p.compensation_coprime_residual hw
  · rintro ⟨⟨c, hc⟩, ⟨b, hb⟩⟩
    refine ⟨c * b, ?_⟩
    rw [← p.compensationCore_eq, hc, hb]
    ring

#print axioms RamifiedSecondCoordinateRoutingPacket.nonempty_canonicalSplit
#print axioms RamifiedSecondCoordinateCanonicalSplit.cubicGap_natAbs_eq
#print axioms
  RamifiedSecondCoordinateCanonicalSplit.receiver_iff_cubicGap_seventh_shape
#print axioms
  RamifiedSecondCoordinateCanonicalSplit.receiver_iff_independent_seventh_powers

end RamifiedSecondCoordinateCanonicalSplit

end DkMath.FLT.Seven
