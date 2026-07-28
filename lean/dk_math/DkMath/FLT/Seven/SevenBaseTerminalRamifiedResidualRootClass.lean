/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRamifiedUnitClassAudit

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRamifiedResidualRootClass"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The exact root-second-coordinate depth is already at least two, so this
coordinate vanishes on the mod-`49` audit plane. -/
theorem PrimitiveRamifiedSummitPacket.root_snd_cast_mod49_eq_zero
    (p : PrimitiveRamifiedSummitPacket) :
    (p.root.snd : ZMod 49) = 0 := by
  have hv0 : Int.natAbs p.root.snd ≠ 0 :=
    Int.natAbs_ne_zero.mpr p.root_snd_ne_zero
  have hdepth :
      2 ≤ padicValNat 7 (Int.natAbs p.root.snd) := by
    rw [p.rootSnd_padicValNat]
    omega
  have h49nat : 7 ^ 2 ∣ Int.natAbs p.root.snd :=
    (@padicValNat_dvd_iff_le 7 inferInstance
      (Int.natAbs p.root.snd) 2 hv0).mpr hdepth
  have h49 : (49 : ℤ) ∣ p.root.snd := by
    norm_num at h49nat
    exact Int.natCast_dvd.mpr h49nat
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h49

/-- At modulus `49`, the ramified quotient loses every term containing the
high-depth gap parameter. -/
theorem
    PrimitiveRamifiedSummitPacket.ramifiedGapQuotient_snd_mod49_eq_neg_endpointRight_sq
    (p : PrimitiveRamifiedSummitPacket) :
    ((ramifiedGapQuotient
        (7 ^ 5 * (p.gapRoot : ℤ) ^ 7)
        p.endpointRight).snd : ZMod 49) =
      -(p.endpointRight : ZMod 49) ^ 2 := by
  have h16807 : (16807 : ZMod 49) = 0 := by decide
  simp only [ramifiedGapQuotient]
  push_cast
  rw [h16807]
  ring

/-- The root norm reduces to the square of the surviving first coordinate. -/
theorem PrimitiveRamifiedSummitPacket.residualRoot_mod49_eq_rootFst_sq
    (p : PrimitiveRamifiedSummitPacket) :
    (p.residualRoot : ZMod 49) =
      (p.root.fst : ZMod 49) ^ 2 := by
  have hnorm :=
    congrArg (fun z : ℤ => (z : ZMod 49)) p.root_norm_eq
  push_cast at hnorm
  simpa [DkMath.NumberTheory.TraceOneQuadratic.norm,
    p.root_snd_cast_mod49_eq_zero] using hnorm.symm

/-- The second-coordinate core reduces to the cube of the residual root. -/
theorem PrimitiveRamifiedSummitPacket.sndCore_mod49_eq_residualRoot_cube
    (p : PrimitiveRamifiedSummitPacket) :
    (seventhPowerSndCore p.root.fst p.root.snd : ZMod 49) =
      (p.residualRoot : ZMod 49) ^ 3 := by
  rw [p.residualRoot_mod49_eq_rootFst_sq]
  simp [seventhPowerSndCore, p.root_snd_cast_mod49_eq_zero]
  ring

noncomputable def PrimitiveRamifiedSummitPacket.residualRootInverseMod49
    (p : PrimitiveRamifiedSummitPacket) : ZMod 49 :=
  ↑((intCast_isUnit_zmod_sevenPower
    (k := 2)
    (fun h => p.residualRoot_not_seven_dvd
      (Int.ofNat_dvd.mp h))).unit⁻¹)

theorem PrimitiveRamifiedSummitPacket.residualRoot_mul_inverseMod49
    (p : PrimitiveRamifiedSummitPacket) :
    (p.residualRoot : ZMod 49) * p.residualRootInverseMod49 = 1 :=
  (intCast_isUnit_zmod_sevenPower
    (k := 2)
    (fun h => p.residualRoot_not_seven_dvd
      (Int.ofNat_dvd.mp h))).mul_val_inv

/-- Canonical RAMIFIED-005 normal form: the bridge unit is a negative endpoint
square times the inverse square of the residual root. -/
theorem PrimitiveRamifiedSummitPacket.explicitUnit_mod49_eq
    (p : PrimitiveRamifiedSummitPacket) :
    p.ramifiedGapUnitBridge.explicitUnit 2 =
      -(p.endpointRight : ZMod 49) ^ 2 *
        p.residualRootInverseMod49 ^ 2 := by
  let B : ZMod 49 := (p.residualRoot : ZMod 49)
  let BInv : ZMod 49 := p.residualRootInverseMod49
  have hcore :
      (seventhPowerSndCore p.root.fst p.root.snd : ZMod 49) = B ^ 3 :=
    p.sndCore_mod49_eq_residualRoot_cube
  have hBinv : B * BInv = 1 :=
    p.residualRoot_mul_inverseMod49
  apply (p.ramifiedGapUnitBridge.leftUnit_isUnit 2).mul_right_cancel
  calc
    p.ramifiedGapUnitBridge.explicitUnit 2 *
        (p.ramifiedGapUnitBridge.leftUnit : ZMod 49) =
      (p.ramifiedGapUnitBridge.rightUnit : ZMod 49) :=
        p.ramifiedGapUnitBridge.explicitUnit_mul_leftUnit 2
    _ = -(p.endpointRight : ZMod 49) ^ 2 * B := by
      change
        (((ramifiedGapQuotient
          (7 ^ 5 * (p.gapRoot : ℤ) ^ 7)
          p.endpointRight).snd * norm p.root : ℤ) : ZMod 49) =
          -(p.endpointRight : ZMod 49) ^ 2 * B
      push_cast
      have hQ :=
        p.ramifiedGapQuotient_snd_mod49_eq_neg_endpointRight_sq
      norm_num at hQ
      rw [hQ]
      have hnorm :=
        congrArg (fun z : ℤ => (z : ZMod 49)) p.root_norm_eq
      push_cast at hnorm
      rw [hnorm]
    _ = (-(p.endpointRight : ZMod 49) ^ 2 * BInv ^ 2) *
        (p.ramifiedGapUnitBridge.leftUnit : ZMod 49) := by
      change
        -(p.endpointRight : ZMod 49) ^ 2 * B =
          (-(p.endpointRight : ZMod 49) ^ 2 * BInv ^ 2) *
            (seventhPowerSndCore
              p.root.fst p.root.snd : ZMod 49)
      rw [hcore]
      calc
        -(p.endpointRight : ZMod 49) ^ 2 *
            B =
          -(p.endpointRight : ZMod 49) ^ 2 *
            (B * BInv) ^ 2 * B := by rw [hBinv]; simp
        _ = _ := by ring

/-- The first ramified coordinate equation on the mod-`49` plane. -/
theorem PrimitiveRamifiedSummitPacket.rootFst_pow_seven_mod49
    (p : PrimitiveRamifiedSummitPacket) :
    (p.root.fst : ZMod 49) ^ 7 =
      -(p.endpointRight : ZMod 49) ^ 3 := by
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
  have hfst := congrArg TraceOneInt.fst hroot
  rw [show (p.root ^ 7).fst =
      seventhPowerFst p.root.fst p.root.snd by
        rcases p.root with ⟨u, v⟩
        exact traceOne_pow_seven_fst u v] at hfst
  simp only [Int.reduceNeg, Int.cast_neg, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, fst_add,
    fst_neg, traceOneInt_intCast_pow_fst, fst_mul, traceOneInt_intCast_fst, neg_mul,
    traceOneInt_intCast_snd, mul_zero, add_zero, snd_mul, zero_add] at hfst
  have hcast :=
    congrArg (fun z : ℤ => (z : ZMod 49)) hfst
  push_cast at hcast
  have h16807 : (16807 : ZMod 49) = 0 := by decide
  simp [h, seventhPowerFst, p.root_snd_cast_mod49_eq_zero, h16807] at hcast
  simpa using hcast.symm

private theorem residual_mod7_eq_one_of_relations :
    ∀ B u e : ZMod 7, IsUnit e →
      B = u ^ 2 → u = -e ^ 3 → B = 1 := by
  decide

/-- The residual root has trivial tame residue. -/
theorem PrimitiveRamifiedSummitPacket.residualRoot_mod7_eq_one
    (p : PrimitiveRamifiedSummitPacket) :
    (p.residualRoot : ZMod 7) = 1 := by
  have hB49 := p.residualRoot_mod49_eq_rootFst_sq
  have hu49 := p.rootFst_pow_seven_mod49
  have hB := congrArg (sevenPowerReductionHom 1) hB49
  have hu := congrArg (sevenPowerReductionHom 1) hu49
  simp only [map_pow, map_neg] at hB hu
  simp only [Nat.reducePow, Nat.reduceAdd, sevenPowerReductionHom, Nat.succ_eq_add_one, pow_one,
    map_natCast, Int.reduceNeg, map_intCast, ZMod.pow_card] at hB hu
  have he : IsUnit (p.endpointRight : ZMod 7) :=
    intCast_isUnit_zmod_sevenPower
      (k := 1) p.endpointRight_not_seven_dvd
  exact residual_mod7_eq_one_of_relations _ _ _ he hB hu

private theorem zmod49_seventh_eq_one_of_reduction_eq_one :
    ∀ B : ZMod 49, sevenPowerReductionHom 1 B = 1 → B ^ 7 = 1 := by
  decide

/-- Consequently the residual root belongs to the seven-element principal
unit kernel at modulus `49`. -/
theorem PrimitiveRamifiedSummitPacket.residualRoot_seventh_eq_one_mod49
    (p : PrimitiveRamifiedSummitPacket) :
    (p.residualRoot : ZMod 49) ^ 7 = 1 := by
  have hB := p.residualRoot_mod7_eq_one
  have hreduce :
      sevenPowerReductionHom 1 (p.residualRoot : ZMod 49) = 1 := by
    simpa using hB
  exact zmod49_seventh_eq_one_of_reduction_eq_one _ hreduce

private theorem zmod49_seventh_root_one_classifier :
    ∀ B : ZMod 49, B ^ 7 = 1 →
      B = 1 ∨ B = 8 ∨ B = 15 ∨ B = 22 ∨
      B = 29 ∨ B = 36 ∨ B = 43 := by
  decide

/-- Complete mod-`49` classifier for the residual root. -/
theorem PrimitiveRamifiedSummitPacket.residualRoot_mod49_classifier
    (p : PrimitiveRamifiedSummitPacket) :
    (p.residualRoot : ZMod 49) = 1 ∨
    (p.residualRoot : ZMod 49) = 8 ∨
    (p.residualRoot : ZMod 49) = 15 ∨
    (p.residualRoot : ZMod 49) = 22 ∨
    (p.residualRoot : ZMod 49) = 29 ∨
    (p.residualRoot : ZMod 49) = 36 ∨
    (p.residualRoot : ZMod 49) = 43 := by
  exact zmod49_seventh_root_one_classifier _
    p.residualRoot_seventh_eq_one_mod49

/-- The endpoint contributes only a tame sixth-root component modulo `49`. -/
theorem PrimitiveRamifiedSummitPacket.endpointRight_sixth_eq_one_mod49
    (p : PrimitiveRamifiedSummitPacket) :
    (p.endpointRight : ZMod 49) ^ 6 = 1 := by
  have hu := p.rootFst_pow_seven_mod49
  have hB := p.residualRoot_mod49_eq_rootFst_sq
  calc
    (p.endpointRight : ZMod 49) ^ 6 =
        (-(p.endpointRight : ZMod 49) ^ 3) ^ 2 := by ring
    _ = ((p.root.fst : ZMod 49) ^ 7) ^ 2 := by rw [hu]
    _ = ((p.root.fst : ZMod 49) ^ 2) ^ 7 := by ring
    _ = (p.residualRoot : ZMod 49) ^ 7 := by rw [hB]
    _ = 1 := p.residualRoot_seventh_eq_one_mod49

set_option maxRecDepth 100000 in
private theorem canonical_unit_fixed_iff_residual_eq_one :
    ∀ E B BInv : ZMod 49,
      E ^ 6 = 1 → B ^ 7 = 1 → B * BInv = 1 →
        (((-E ^ 2 * BInv ^ 2) ^ 7 = -E ^ 2 * BInv ^ 2) ↔
          B = 1) := by
  decide

/-- The true RAMIFIED-005 branch selector is the one principal digit of the
residual root. -/
theorem
    PrimitiveRamifiedSummitPacket.isSeventhPowerMod49_iff_residualRoot_eq_one
    (p : PrimitiveRamifiedSummitPacket) :
    p.ramifiedGapUnitBridge.IsSeventhPowerMod49 ↔
      (p.residualRoot : ZMod 49) = 1 := by
  rw [p.ramifiedGapUnitBridge.isSeventhPowerMod49_iff,
    p.explicitUnit_mod49_eq]
  exact canonical_unit_fixed_iff_residual_eq_one
    (p.endpointRight : ZMod 49)
    (p.residualRoot : ZMod 49)
    p.residualRootInverseMod49
    p.endpointRight_sixth_eq_one_mod49
    p.residualRoot_seventh_eq_one_mod49
    p.residualRoot_mul_inverseMod49

private theorem canonical_unit_three_residues_of_residual_one :
    ∀ E BInv : ZMod 49,
      E ^ 6 = 1 → BInv = 1 →
        -E ^ 2 * BInv ^ 2 = 19 ∨
        -E ^ 2 * BInv ^ 2 = 31 ∨
        -E ^ 2 * BInv ^ 2 = 48 := by
  decide

/-- The generic six seventh-power residues shrink to three for a canonical
ramified summit. -/
theorem PrimitiveRamifiedSummitPacket.isSeventhPowerMod49_iff_three_residues
    (p : PrimitiveRamifiedSummitPacket) :
    p.ramifiedGapUnitBridge.IsSeventhPowerMod49 ↔
      p.ramifiedGapUnitBridge.explicitUnit 2 = 19 ∨
      p.ramifiedGapUnitBridge.explicitUnit 2 = 31 ∨
      p.ramifiedGapUnitBridge.explicitUnit 2 = 48 := by
  constructor
  · intro h
    have hB :=
      p.isSeventhPowerMod49_iff_residualRoot_eq_one.mp h
    have hBinv : p.residualRootInverseMod49 = 1 := by
      have hm := p.residualRoot_mul_inverseMod49
      rw [hB, one_mul] at hm
      exact hm
    have hthree := canonical_unit_three_residues_of_residual_one
      (p.endpointRight : ZMod 49)
      p.residualRootInverseMod49
      p.endpointRight_sixth_eq_one_mod49 hBinv
    rw [p.explicitUnit_mod49_eq]
    exact hthree
  · intro h
    rw [p.ramifiedGapUnitBridge.isSeventhPowerMod49_iff_residue]
    rcases h with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

#print axioms PrimitiveRamifiedSummitPacket.explicitUnit_mod49_eq
#print axioms PrimitiveRamifiedSummitPacket.residualRoot_mod49_classifier
#print axioms
  PrimitiveRamifiedSummitPacket.isSeventhPowerMod49_iff_residualRoot_eq_one
#print axioms
  PrimitiveRamifiedSummitPacket.isSeventhPowerMod49_iff_three_residues

end DkMath.FLT.Seven
