/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneHigherDepthRamifiedRouting
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedGapUnitBridge
import DkMath.FLT.Seven.SevenBaseTerminalRamifiedQuadraticInnerRoot

#print "file: DkMath.FLT.Seven.PrimeTraceOneHigherDepthRamifiedCanonicalReceiver"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def PrimitiveRamifiedSummitPacket.ramifiedPrimaryCompensationCore
    (p : PrimitiveRamifiedSummitPacket) : ℕ :=
  Nat.gcd
    (Int.natAbs p.root.snd)
    (Int.natAbs
      (ramifiedGapQuotient
        (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd)

structure RamifiedPrimarySecondCoordinateCanonicalSplit
    (p : PrimitiveRamifiedSummitPacket) : Type where
  primaryRouting : RamifiedPrimarySecondCoordinateRoutingPacket p
  verticalUnitRoot : ℕ
  horizontalUnitRoot : ℕ
  compensationCore : ℕ
  quotientRemainder : ℕ
  unitRoot_eq :
    primaryRouting.primary.unitRoot = verticalUnitRoot * horizontalUnitRoot
  compensationCore_eq :
    compensationCore = p.ramifiedPrimaryCompensationCore
  rootSnd_eq :
    Int.natAbs p.root.snd =
      7 ^ (5 + 7 * primaryRouting.primary.depth) *
        verticalUnitRoot ^ 7 * compensationCore
  sndCore_eq :
    Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd) =
      horizontalUnitRoot ^ 7 * quotientRemainder
  gapQuotient_eq :
    Int.natAbs
      (ramifiedGapQuotient
        (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd =
      compensationCore * quotientRemainder

namespace RamifiedPrimarySecondCoordinateCanonicalSplit

private theorem primary_column_coprime_7_unit
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    Nat.Coprime (7 ^ (5 + 7 * r.primary.depth)) (r.primary.unitRoot ^ 7) := by
  exact (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr
    r.primary.unitRoot_not_seven_dvd).pow_left _).pow_right 7

private theorem primary_column_coprime_7_quotient
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    Nat.Coprime (7 ^ (5 + 7 * r.primary.depth))
      (Int.natAbs (ramifiedGapQuotient
        (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd) := by
  apply ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr ?_).pow_left _
  intro h
  exact ramifiedGapQuotient_snd_not_seven_dvd p.endpointRight_not_seven_dvd
    (Int.natCast_dvd.mpr h)

private theorem primary_column_coprime_unit_quotient
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    Nat.Coprime (r.primary.unitRoot ^ 7)
      (Int.natAbs (ramifiedGapQuotient
        (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd) := by
  apply (p.gapRoot_gapQuotient_coprime.of_dvd_left ?_).pow_left 7
  exact ⟨7 ^ r.primary.depth, by rw [r.primary.gapRoot_eq]; ring⟩

private theorem primary_sndCore_coprime_primary
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    Nat.Coprime (Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd))
      (7 ^ (5 + 7 * r.primary.depth)) := by
  apply (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr ?_).pow_left _).symm
  intro h
  exact p.sndCore_not_seven_dvd (Int.natCast_dvd.mpr h)

private theorem c31_eq_one
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    r.routing.c31 = 1 := by
  rw [r.routing.c31_eq_gcd]
  · simp
  · exact primary_column_coprime_7_unit r
  · exact primary_column_coprime_7_quotient r

private theorem c32_eq_one
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    r.routing.c32 = 1 := by
  rw [r.routing.c32_eq_gcd]
  · simp
  · exact primary_column_coprime_7_unit r
  · exact primary_column_coprime_unit_quotient r

private theorem c33_eq_one
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    r.routing.c33 = 1 := by
  rw [r.routing.c33_eq_gcd]
  · simp
  · exact primary_column_coprime_7_quotient r
  · exact primary_column_coprime_unit_quotient r

private theorem c21_eq_one
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    r.routing.c21 = 1 := by
  rw [r.routing.c21_eq_gcd]
  · exact Nat.coprime_iff_gcd_eq_one.mp (primary_sndCore_coprime_primary r)
  · exact primary_column_coprime_7_unit r
  · exact primary_column_coprime_7_quotient r

private theorem c11_eq_primary
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    r.routing.c11 = 7 ^ (5 + 7 * r.primary.depth) := by
  have h := r.routing.col1
  rw [c21_eq_one r, c31_eq_one r] at h
  simpa using h.symm

private theorem c13_eq_compensationCore
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    r.routing.c13 = p.ramifiedPrimaryCompensationCore := by
  exact r.routing.c13_eq_gcd
    (primary_column_coprime_7_quotient (p := p) r)
    (primary_column_coprime_unit_quotient (p := p) r)

theorem nonempty
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    Nonempty (RamifiedPrimarySecondCoordinateCanonicalSplit p) := by
  have hcol2 : r.routing.c12 * r.routing.c22 = r.primary.unitRoot ^ 7 := by
    have h := r.routing.col2
    rw [c32_eq_one r, mul_one] at h
    exact h.symm
  rcases seventh_power_factor_split r.routing.col2_coprime.1 hcol2 with
    ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩
  let C := p.ramifiedPrimaryCompensationCore
  let D := r.routing.c23
  have hU : r.primary.unitRoot = X * Y := by
    apply Nat.pow_left_injective (by decide : 7 ≠ 0)
    calc
      r.primary.unitRoot ^ 7 = r.routing.c12 * r.routing.c22 := hcol2.symm
      _ = X ^ 7 * Y ^ 7 := by rw [hX, hY]
      _ = (X * Y) ^ 7 := by ring
  have hV : Int.natAbs p.root.snd =
      7 ^ (5 + 7 * r.primary.depth) * X ^ 7 * C := by
    calc
      _ = r.routing.c11 * r.routing.c12 * r.routing.c13 := r.routing.row1
      _ = _ := by rw [c11_eq_primary r, hX, c13_eq_compensationCore r]
  have hS : Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd) =
      Y ^ 7 * D := by
    calc
      _ = r.routing.c21 * r.routing.c22 * r.routing.c23 := r.routing.row2
      _ = _ := by rw [c21_eq_one r, one_mul, hY]
  have hQ : Int.natAbs
      (ramifiedGapQuotient
        (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd = C * D := by
    calc
      _ = r.routing.c13 * r.routing.c23 * r.routing.c33 := r.routing.col3
      _ = _ := by rw [c33_eq_one r, mul_one, c13_eq_compensationCore r]
  exact ⟨{
    primaryRouting := r
    verticalUnitRoot := X
    horizontalUnitRoot := Y
    compensationCore := C
    quotientRemainder := D
    unitRoot_eq := hU
    compensationCore_eq := rfl
    rootSnd_eq := hV
    sndCore_eq := hS
    gapQuotient_eq := hQ }⟩

end RamifiedPrimarySecondCoordinateCanonicalSplit

noncomputable def PrimitiveRamifiedSummitPacket.primaryCanonicalSplit
    (p : PrimitiveRamifiedSummitPacket) :
    RamifiedPrimarySecondCoordinateCanonicalSplit p :=
  let r := Classical.choice p.nonempty_primarySecondCoordinateRouting
  Classical.choice (RamifiedPrimarySecondCoordinateCanonicalSplit.nonempty r)

namespace RamifiedPrimarySecondCoordinateRoutingPacket

private theorem column_coprime_7_unit
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    Nat.Coprime (7 ^ (5 + 7 * r.primary.depth)) (r.primary.unitRoot ^ 7) := by
  exact (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr
    r.primary.unitRoot_not_seven_dvd).pow_left _).pow_right 7

private theorem column_coprime_7_quotient
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    Nat.Coprime (7 ^ (5 + 7 * r.primary.depth))
      (Int.natAbs (ramifiedGapQuotient
        (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd) := by
  apply ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr ?_).pow_left _
  intro h
  exact ramifiedGapQuotient_snd_not_seven_dvd p.endpointRight_not_seven_dvd
    (Int.natCast_dvd.mpr h)

private theorem column_coprime_unit_quotient
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    Nat.Coprime (r.primary.unitRoot ^ 7)
      (Int.natAbs (ramifiedGapQuotient
        (7 ^ 5 * (p.gapRoot : ℤ) ^ 7) p.endpointRight).snd) := by
  apply (p.gapRoot_gapQuotient_coprime.of_dvd_left ?_).pow_left 7
  exact ⟨7 ^ r.primary.depth, by rw [r.primary.gapRoot_eq]; ring⟩

private theorem summit_sndCore_not_seven_dvd
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    ¬ (7 : ℤ) ∣ seventhPowerSndCore p.root.fst p.root.snd :=
  p.sndCore_not_seven_dvd

private theorem summit_sndCore_not_seven_dvd_coprime_primary
    (r : RamifiedPrimarySecondCoordinateRoutingPacket p) :
    Nat.Coprime (Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd))
      (7 ^ (5 + 7 * r.primary.depth)) := by
  apply (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr ?_).pow_left _).symm
  intro h
  exact r.summit_sndCore_not_seven_dvd (Int.natCast_dvd.mpr h)

end RamifiedPrimarySecondCoordinateRoutingPacket

namespace RamifiedPrimarySecondCoordinateCanonicalSplit

theorem cubicGap_natAbs_eq
    (p : RamifiedPrimarySecondCoordinateCanonicalSplit p) :
    Int.natAbs
        (ramifiedRightCubic p.primaryRouting.summit.root.fst
            p.primaryRouting.summit.root.snd -
          ramifiedLeftCubic p.primaryRouting.summit.root.fst
            p.primaryRouting.summit.root.snd) =
      7 ^ (6 + 7 * p.primaryRouting.primary.depth) *
        p.verticalUnitRoot ^ 7 *
        (p.compensationCore * p.primaryRouting.summit.residualRoot) := by
  have hroot : Int.natAbs p.primaryRouting.summit.root.snd =
      7 ^ (5 + 7 * p.primaryRouting.primary.depth) *
        p.verticalUnitRoot ^ 7 * p.compensationCore := by
    simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit] using p.rootSnd_eq
  rw [ramifiedRightCubic_sub_left,
    p.primaryRouting.summit.root_norm_eq, Int.natAbs_mul,
    Int.natAbs_mul, Int.natAbs_natCast, hroot]
  ring

def CubicGapSeventhShape
    (p : RamifiedPrimarySecondCoordinateCanonicalSplit p) : Prop :=
  ∃ W : ℕ,
    Int.natAbs
        (ramifiedRightCubic p.primaryRouting.summit.root.fst
            p.primaryRouting.summit.root.snd -
          ramifiedLeftCubic p.primaryRouting.summit.root.fst
            p.primaryRouting.summit.root.snd) =
      7 ^ (6 + 7 * p.primaryRouting.primary.depth) * W ^ 7

def CubicGapSeventhShapeReceiver
    (p : RamifiedPrimarySecondCoordinateCanonicalSplit p) : Prop :=
  ∃ w : ℕ, p.compensationCore * p.primaryRouting.summit.residualRoot = w ^ 7

theorem depth_zero_compensation_core_eq_terminal
    (p : RamifiedPrimarySecondCoordinateCanonicalSplit q)
    (t : TerminalPrimitiveRamifiedSummitPacket)
    (ht : t.summit = q)
    (_hd : p.primaryRouting.primary.depth = 0) :
    p.compensationCore = t.ramifiedCompensationCore := by
  rw [p.compensationCore_eq]
  unfold PrimitiveRamifiedSummitPacket.ramifiedPrimaryCompensationCore
  unfold TerminalPrimitiveRamifiedSummitPacket.ramifiedCompensationCore
  simpa [ht]

theorem depth_zero_receiver_iff_terminal_receiver
    (p : RamifiedPrimarySecondCoordinateCanonicalSplit q)
    (t : TerminalPrimitiveRamifiedSummitPacket)
    (ht : t.summit = q)
    (hd : p.primaryRouting.primary.depth = 0) :
    p.CubicGapSeventhShapeReceiver ↔
      t.RamifiedCubicGapSeventhShapeReceiver := by
  have hcore := p.depth_zero_compensation_core_eq_terminal t ht hd
  simpa [CubicGapSeventhShapeReceiver,
    TerminalPrimitiveRamifiedSummitPacket.RamifiedCubicGapSeventhShapeReceiver,
    RamifiedPrimarySecondCoordinateRoutingPacket.summit, hcore, ht]

theorem vertical_coprime_compensation_residual
    (p : RamifiedPrimarySecondCoordinateCanonicalSplit p)
    (hgap : Nat.Coprime p.primaryRouting.summit.gapRoot
      p.primaryRouting.summit.residualRoot) :
    Nat.Coprime p.verticalUnitRoot
      (p.compensationCore * p.primaryRouting.summit.residualRoot) := by
  have hVU : p.verticalUnitRoot ∣ p.primaryRouting.summit.gapRoot := by
    have hVU' : p.verticalUnitRoot ∣ p.primaryRouting.primary.unitRoot :=
      ⟨p.horizontalUnitRoot, by rw [p.unitRoot_eq]
        <;> ring⟩
    have hUG : p.primaryRouting.primary.unitRoot ∣
        p.primaryRouting.summit.gapRoot := by
      refine ⟨7 ^ p.primaryRouting.primary.depth, ?_⟩
      simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit, Nat.mul_comm] using
        p.primaryRouting.primary.gapRoot_eq
    exact dvd_trans hVU' hUG
  have hCQ : p.compensationCore ∣ Int.natAbs
      (ramifiedGapQuotient
        (7 ^ 5 * (p.primaryRouting.summit.gapRoot : ℤ) ^ 7)
        p.primaryRouting.summit.endpointRight).snd := by
    refine ⟨p.quotientRemainder, ?_⟩
    simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit] using
      p.gapQuotient_eq
  have hVC : Nat.Coprime p.verticalUnitRoot p.compensationCore :=
    (PrimitiveRamifiedSummitPacket.gapRoot_gapQuotient_coprime
      p.primaryRouting.summit).of_dvd_left hVU |>.of_dvd_right hCQ
  exact hVC.mul_right (hgap.of_dvd_left hVU)

theorem receiver_iff_cubicGap_seventh_shape
    (p : RamifiedPrimarySecondCoordinateCanonicalSplit p)
    (hgap : Nat.Coprime p.primaryRouting.summit.gapRoot
      p.primaryRouting.summit.residualRoot) :
    p.CubicGapSeventhShapeReceiver ↔ p.CubicGapSeventhShape := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨p.verticalUnitRoot * w, ?_⟩
    rw [p.cubicGap_natAbs_eq, hw]
    ring
  · rintro ⟨W, hW⟩
    have hcancel : p.verticalUnitRoot ^ 7 *
        (p.compensationCore * p.primaryRouting.summit.residualRoot) = W ^ 7 := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 7 ^
        (6 + 7 * p.primaryRouting.primary.depth))
      calc
        7 ^ (6 + 7 * p.primaryRouting.primary.depth) *
            (p.verticalUnitRoot ^ 7 *
              (p.compensationCore * p.primaryRouting.summit.residualRoot)) =
          7 ^ (6 + 7 * p.primaryRouting.primary.depth) * p.verticalUnitRoot ^ 7 *
            (p.compensationCore * p.primaryRouting.summit.residualRoot) := by ring
        _ = _ := p.cubicGap_natAbs_eq.symm.trans hW
    have hsplit := seventh_power_factor_split
      ((p.vertical_coprime_compensation_residual hgap).pow_left 7) hcancel
    exact hsplit.2

theorem compensation_coprime_residual
    (p : RamifiedPrimarySecondCoordinateCanonicalSplit p) :
    Nat.Coprime p.compensationCore p.primaryRouting.summit.residualRoot := by
  have hC : p.compensationCore ∣ Int.natAbs p.primaryRouting.summit.root.snd := by
    have hroot : Int.natAbs p.primaryRouting.summit.root.snd =
        7 ^ (5 + 7 * p.primaryRouting.primary.depth) *
          p.verticalUnitRoot ^ 7 * p.compensationCore := by
      simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit] using p.rootSnd_eq
    rw [hroot]
    exact dvd_mul_left _ _
  exact (PrimitiveRamifiedSummitPacket.rootNorm_rootSnd_coprime
    p.primaryRouting.summit).of_dvd_right hC |>.symm

theorem receiver_iff_independent_seventh_powers
    (p : RamifiedPrimarySecondCoordinateCanonicalSplit p) :
    p.CubicGapSeventhShapeReceiver ↔
      (∃ c : ℕ, p.compensationCore = c ^ 7) ∧
      (∃ b : ℕ, p.primaryRouting.summit.residualRoot = b ^ 7) := by
  constructor
  · rintro ⟨w, hw⟩
    exact seventh_power_factor_split p.compensation_coprime_residual hw
  · rintro ⟨⟨c, hc⟩, ⟨b, hb⟩⟩
    exact ⟨c * b, by rw [hc, hb]; ring⟩

end RamifiedPrimarySecondCoordinateCanonicalSplit

structure RamifiedPrimaryQuadraticInnerRootPacket
    (p : PrimitiveRamifiedSummitPacket) : Type where
  canonical : RamifiedPrimarySecondCoordinateCanonicalSplit p
  receiver : canonical.CubicGapSeventhShapeReceiver
  compensationRoot : ℕ
  residualNormRoot : ℕ
  compensationCore_eq : canonical.compensationCore = compensationRoot ^ 7
  residualRoot_eq : p.residualRoot = residualNormRoot ^ 7
  innerRoot : TraceOneInt (-2)
  root_eq : p.root = innerRoot ^ 7

namespace RamifiedPrimarySecondCoordinateCanonicalSplit

theorem nonempty_primaryQuadraticInnerRoot
    (p : RamifiedPrimarySecondCoordinateCanonicalSplit q)
    (receiver : p.CubicGapSeventhShapeReceiver) :
    Nonempty (RamifiedPrimaryQuadraticInnerRootPacket q) := by
  rcases p.receiver_iff_independent_seventh_powers.mp receiver with
    ⟨⟨c, hc⟩, ⟨b, hb⟩⟩
  have hmul : p.primaryRouting.summit.root *
      conj p.primaryRouting.summit.root = (b : TraceOneInt (-2)) ^ 7 := by
    rw [traceOne_mul_conj, p.primaryRouting.summit.root_norm_eq, hb]
    change ((((b : ℤ) ^ 7 : ℤ)) : TraceOneInt (-2)) =
      (b : TraceOneInt (-2)) ^ 7
    norm_cast
  rcases exists_eq_seventh_power_of_coprime_mul_eq_pow
      (PrimitiveRamifiedSummitPacket.root_gcd_conj_isUnit
        p.primaryRouting.summit) hmul with
    ⟨innerRoot, hroot⟩
  exact ⟨{
    canonical := p
    receiver := receiver
    compensationRoot := c
    residualNormRoot := b
    compensationCore_eq := hc
    residualRoot_eq := hb
    innerRoot := innerRoot
    root_eq := hroot }⟩

end RamifiedPrimarySecondCoordinateCanonicalSplit

namespace RamifiedPrimaryQuadraticInnerRootPacket

theorem innerRoot_coordinates_isCoprime
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    IsCoprime p.innerRoot.fst p.innerRoot.snd := by
  apply coordinates_isCoprime_of_pow_seven_coordinates_isCoprime
  rw [← p.root_eq]
  exact p.canonical.primaryRouting.summit.root_coordinates_isCoprime

theorem innerRoot_norm_eq
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    norm p.innerRoot = p.residualNormRoot := by
  have hpows : norm p.innerRoot ^ 7 = (p.residualNormRoot : ℤ) ^ 7 := by
    calc
      _ = norm (p.innerRoot ^ 7) :=
        (traceOne_norm_pow_ramified p.innerRoot 7).symm
      _ = norm p.canonical.primaryRouting.summit.root := by
        simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit] using
          (show norm (p.innerRoot ^ 7) = norm q.root by rw [p.root_eq])
      _ = p.canonical.primaryRouting.summit.residualRoot :=
        p.canonical.primaryRouting.summit.root_norm_eq
      _ = _ := by
        have hres : q.residualRoot = p.residualNormRoot ^ 7 := by
          simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit] using
            p.residualRoot_eq
        simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit] using
          congrArg (fun n : ℕ => (n : ℤ)) hres
  have hnonneg : 0 ≤ norm p.innerRoot :=
    traceOneNegTwo_norm_nonneg p.innerRoot
  have habspows : Int.natAbs (norm p.innerRoot) ^ 7 = p.residualNormRoot ^ 7 := by
    rw [← Int.natAbs_pow, hpows]
    simp
  have habs : Int.natAbs (norm p.innerRoot) = p.residualNormRoot :=
    Nat.pow_left_injective (by decide : 7 ≠ 0) habspows
  calc
    norm p.innerRoot = (Int.natAbs (norm p.innerRoot) : ℤ) :=
      (Int.natAbs_of_nonneg hnonneg).symm
    _ = p.residualNormRoot := congrArg Nat.cast habs

theorem innerRoot_norm_not_seven_dvd
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    ¬ (7 : ℤ) ∣ norm p.innerRoot := by
  rw [p.innerRoot_norm_eq]
  intro h
  apply p.canonical.primaryRouting.summit.residualRoot_not_seven_dvd
  have hres : q.residualRoot = p.residualNormRoot ^ 7 := by
    simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit] using
      p.residualRoot_eq
  have hres' : p.canonical.primaryRouting.summit.residualRoot =
      p.residualNormRoot ^ 7 := by
    simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit] using hres
  rw [hres']
  exact dvd_pow (Int.ofNat_dvd.mp h) (by norm_num)

theorem rootSnd_eq_seventhPowerSnd
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    p.canonical.primaryRouting.summit.root.snd =
      seventhPowerSnd p.innerRoot.fst p.innerRoot.snd := by
  have h := congrArg TraceOneInt.snd p.root_eq
  simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit,
    show (p.innerRoot ^ 7).snd =
      seventhPowerSnd p.innerRoot.fst p.innerRoot.snd by
    rcases p.innerRoot with ⟨a, b⟩
    exact traceOne_pow_seven_snd a b] using h

theorem innerRoot_snd_ne_zero
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    p.innerRoot.snd ≠ 0 := by
  intro hv
  apply p.canonical.primaryRouting.summit.root_snd_ne_zero
  rw [p.rootSnd_eq_seventhPowerSnd, hv]
  simp [seventhPowerSnd]

theorem innerSndCore_not_seven_dvd
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    ¬ (7 : ℤ) ∣ seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd :=
  seven_not_dvd_seventhPowerSndCore_of_norm p.innerRoot_norm_not_seven_dvd

theorem innerSndCore_ne_zero
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd ≠ 0 := by
  intro h
  exact p.innerSndCore_not_seven_dvd (by rw [h]; exact dvd_zero 7)

theorem innerRootSnd_innerSndCore_coprime
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    Nat.Coprime (Int.natAbs p.innerRoot.snd)
      (Int.natAbs (seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd)) :=
  rootSnd_sndCore_coprime_of_coordinates_isCoprime
    p.innerRoot p.innerRoot_coordinates_isCoprime

theorem rootSnd_natAbs_eq
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    Int.natAbs p.canonical.primaryRouting.summit.root.snd =
      7 ^ (5 + 7 * p.canonical.primaryRouting.primary.depth) *
        (p.canonical.verticalUnitRoot * p.compensationRoot) ^ 7 := by
  calc
    _ = 7 ^ (5 + 7 * p.canonical.primaryRouting.primary.depth) *
        p.canonical.verticalUnitRoot ^ 7 * p.canonical.compensationCore :=
      p.canonical.rootSnd_eq
    _ = _ := by rw [p.compensationCore_eq]; ring

theorem inner_secondCoordinate_product_eq
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    Int.natAbs p.innerRoot.snd *
        Int.natAbs (seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd) =
      7 ^ 4 *
        (7 ^ p.canonical.primaryRouting.primary.depth *
          (p.canonical.verticalUnitRoot * p.compensationRoot)) ^ 7 := by
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 7)
  calc
    7 * (Int.natAbs p.innerRoot.snd *
        Int.natAbs (seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd)) =
      Int.natAbs (seventhPowerSnd p.innerRoot.fst p.innerRoot.snd) := by
        rw [seventhPowerSnd_eq_seven_mul, Int.natAbs_mul, Int.natAbs_mul]
        norm_num
        ring
    _ = Int.natAbs p.canonical.primaryRouting.summit.root.snd := by
      rw [p.rootSnd_eq_seventhPowerSnd]
    _ = 7 ^ (5 + 7 * p.canonical.primaryRouting.primary.depth) *
        (p.canonical.verticalUnitRoot * p.compensationRoot) ^ 7 :=
      p.rootSnd_natAbs_eq
    _ = 7 * (7 ^ 4 *
        (7 ^ p.canonical.primaryRouting.primary.depth *
          (p.canonical.verticalUnitRoot * p.compensationRoot)) ^ 7) := by
      rw [pow_add, show 7 * p.canonical.primaryRouting.primary.depth =
        p.canonical.primaryRouting.primary.depth * 7 by omega, pow_mul]
      ring

theorem innerRootSnd_depth_eq_four_add_seven_mul
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    padicValNat 7 (Int.natAbs p.innerRoot.snd) =
      4 + 7 * p.canonical.primaryRouting.primary.depth := by
  have hload : padicValNat 7
      (Int.natAbs p.canonical.primaryRouting.summit.root.snd) =
        1 + padicValNat 7 (Int.natAbs p.innerRoot.snd) := by
    rw [p.rootSnd_eq_seventhPowerSnd, seventhPowerSnd_eq_seven_mul,
      Int.natAbs_mul, Int.natAbs_mul]
    norm_num
    exact padicValNat_seven_mul_of_core_not_dvd
      (Int.natAbs_ne_zero.mpr p.innerRoot_snd_ne_zero)
      (Int.natAbs_ne_zero.mpr p.innerSndCore_ne_zero)
      (fun h => p.innerSndCore_not_seven_dvd (Int.natCast_dvd.mpr h))
  rw [p.canonical.primaryRouting.summit.rootSnd_padicValNat] at hload
  have hgap : padicValNat 7 p.canonical.primaryRouting.summit.gapRoot =
      p.canonical.primaryRouting.primary.depth := by
    simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit] using
      p.canonical.primaryRouting.primary.depth_eq.symm
  rw [hgap] at hload
  omega

theorem exists_inner_secondCoordinate_split
    (p : RamifiedPrimaryQuadraticInnerRootPacket q) :
    ∃ innerVerticalRoot innerHorizontalRoot : ℕ,
      Int.natAbs p.innerRoot.snd =
        7 ^ 4 * innerVerticalRoot ^ 7 ∧
      Int.natAbs (seventhPowerSndCore p.innerRoot.fst p.innerRoot.snd) =
        innerHorizontalRoot ^ 7 := by
  apply seventh_power_split_after_seven_pow_four
    p.innerRootSnd_innerSndCore_coprime
  · intro h
    exact p.innerSndCore_not_seven_dvd (Int.natCast_dvd.mpr h)
  · exact p.inner_secondCoordinate_product_eq

end RamifiedPrimaryQuadraticInnerRootPacket

namespace PrimitiveCounterexampleRamifiedProvenance

theorem innerRootSnd_depth_add_three_eq_distinguished_depth
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    (p : RamifiedPrimaryQuadraticInnerRootPacket r.summit) :
    padicValNat 7 (Int.natAbs p.innerRoot.snd) + 3 =
      7 * padicValNat 7 r.distinguishedEndpoint := by
  rw [p.innerRootSnd_depth_eq_four_add_seven_mul]
  have hprimary := p.canonical.primaryRouting.primary.depth_eq
  have hdist := r.distinguished_padicValNat
  have hprimary' : p.canonical.primaryRouting.primary.depth =
      padicValNat 7 r.summit.gapRoot := by
    simpa [RamifiedPrimarySecondCoordinateRoutingPacket.summit] using hprimary
  rw [← hprimary'] at hdist
  omega

end PrimitiveCounterexampleRamifiedProvenance

end DkMath.FLT.Seven
