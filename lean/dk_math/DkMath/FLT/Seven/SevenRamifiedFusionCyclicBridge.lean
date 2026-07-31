/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionCycleNormalForm

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCyclicBridge"

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
set_option maxRecDepth 2000
set_option linter.style.longLine false

private theorem natAbs_cast_sq_eq (z : ℤ) :
    ((Int.natAbs z : ℕ) : ZMod 7) ^ 2 = (z : ZMod 7) ^ 2 := by
  have hs : ((Int.natAbs z : ℕ) : ℤ) ^ 2 = z ^ 2 := by
    rcases Int.natAbs_eq z with h | h
    · nlinarith
    · nlinarith
  have hc := congrArg (fun t : ℤ => (t : ZMod 7)) hs
  push_cast at hc
  rw [← Int.natCast_natAbs] at hc
  exact hc

private theorem abs_cast_sq_eq (z : ℤ) :
    ((|z| : ℤ) : ZMod 7) ^ 2 = (z : ZMod 7) ^ 2 := by
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
  · rw [abs_of_nonpos hz]
    push_cast
    ring

private theorem absoluteSlope_algebra
    (d e a n m : ZMod 7)
    (he : e ^ 2 = 1) (hn : n ^ 2 = a ^ 2)
    (hprod : d * e = a * n * m)
    (ha : a ≠ 0) (hn0 : n ≠ 0) (he0 : e ≠ 0) :
    (d / e) / n ^ 3 = m / a := by
  field_simp
  calc
    d * a = d * a * (e ^ 2) := by rw [he, mul_one]
    _ = (d * e) * (a * e) := by ring
    _ = (a * n * m) * (a * e) := by rw [hprod]
    _ = m * e * n * a ^ 2 := by ring
    _ = m * e * n * n ^ 2 := by rw [← hn]
    _ = e * n ^ 3 * m := by ring

private def natAbsUnit (z : ℤ) (hz : ¬(7 : ℤ) ∣ z) :
    (ZMod 7)ˣ :=
  Units.mk0 ((Int.natAbs z : ℕ) : ZMod 7) (by
    intro hzero
    apply hz
    apply Int.natAbs_dvd_natAbs.mp
    have hnat : 7 ∣ Int.natAbs z :=
      (ZMod.natCast_eq_zero_iff (Int.natAbs z) 7).mp hzero
    simpa using hnat)

namespace RamifiedSignedRootRoutingPacket

theorem cycleRatio12_eq_unitBoard
    (p : RamifiedSignedRootRoutingPacket) :
    p.cycleRatio12 = p.activeUnitBoard.cycleRatio12 :=
  rfl

theorem cycleRatio23_eq_unitBoard
    (p : RamifiedSignedRootRoutingPacket) :
    p.cycleRatio23 = p.activeUnitBoard.cycleRatio23 :=
  rfl

private theorem rowMargin1_eq
    (p : RamifiedSignedRootRoutingPacket) :
    p.activeUnitBoard.rowMargin1 =
      natAbsUnit p.signedDepth.gapRoot
        p.signedDepth.gapRoot_not_seven_dvd := by
  apply Units.ext
  simp [ActiveUnitBoard.rowMargin1, natAbsUnit]
  have h := congrArg (fun n : ℕ => (n : ZMod 7)) p.routing.row1
  push_cast at h
  simpa [Int.natCast_natAbs] using h.symm

private theorem rowMargin2_eq
    (p : RamifiedSignedRootRoutingPacket) :
    p.activeUnitBoard.rowMargin2 =
      natAbsUnit p.signedDepth.quotientRoot
        p.signedDepth.quotientRoot_not_seven_dvd := by
  apply Units.ext
  simp [ActiveUnitBoard.rowMargin2, natAbsUnit]
  have h := congrArg (fun n : ℕ => (n : ZMod 7)) p.routing.row2
  push_cast at h
  simpa [Int.natCast_natAbs] using h.symm

private theorem columnMargin2_eq
    (p : RamifiedSignedRootRoutingPacket) :
    p.activeUnitBoard.columnMargin2 =
      natAbsUnit
        (p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst +
         p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.snd)
        p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.innerFst_add_innerSnd_not_seven_dvd := by
  apply Units.ext
  simp only [ActiveUnitBoard.columnMargin2, Units.val_mul, activeUnitBoard_u12_val, Int.reduceNeg,
    activeUnitBoard_u22_val, natAbsUnit, Nat.cast_natAbs, Units.val_mk0]
  have h := congrArg (fun n : ℕ => (n : ZMod 7)) p.routing.col2
  push_cast at h
  rw [p.thirdRow_eq_one.2.1] at h
  norm_num at h
  exact h.symm

/-- The unsigned slope retained by the natural-number routing margins. -/
def absoluteFusionSlopeUnit
    (p : RamifiedSignedRootRoutingPacket) : (ZMod 7)ˣ :=
  let q :=
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  natAbsUnit q.innerSndRoot q.innerSndRoot_not_seven_dvd /
    natAbsUnit q.quadratic.innerRoot.fst q.innerFst_not_seven_dvd

theorem cycleRatio_div_eq_absoluteFusionSlope
    (p : RamifiedSignedRootRoutingPacket) :
    p.cycleRatio12 / p.cycleRatio23 =
      p.absoluteFusionSlopeUnit := by
  let q :=
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  let d := p.signedDepth.gapRoot
  let e := p.signedDepth.quotientRoot
  let a := q.quadratic.innerRoot.fst
  let n := q.quadratic.innerRoot.fst + q.quadratic.innerRoot.snd
  let m := q.innerSndRoot
  rw [p.cycleRatio12_eq_unitBoard, p.cycleRatio23_eq_unitBoard,
    p.activeUnitBoard.cycleRatio12_div_cycleRatio23_eq,
    p.rowMargin1_eq, p.rowMargin2_eq, p.columnMargin2_eq]
  apply Units.ext
  simp only [natAbsUnit, Nat.cast_natAbs, Int.reduceNeg, Units.val_div_eq_div_val, Units.val_mk0,
    Units.val_pow_eq_pow_val, absoluteFusionSlopeUnit]
  have hprodNat := congrArg Int.natAbs p.signedDepth.normalizedEquation
  simp only [Int.natAbs_mul, Int.natAbs_pow] at hprodNat
  have hprod := congrArg (fun z : ℕ => (z : ZMod 7)) hprodNat
  push_cast at hprod
  have heSigned : (e : ZMod 7) = 1 := by
    simpa [e] using p.signedDepth.quotientRoot_modSeven_eq_one
  have he : ((Int.natAbs e : ℕ) : ZMod 7) ^ 2 = 1 := by
    rw [natAbs_cast_sq_eq, heSigned]
    norm_num
  have hsnd : (q.quadratic.innerRoot.snd : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr q.innerSnd_seven_dvd
  have hn : ((Int.natAbs n : ℕ) : ZMod 7) ^ 2 =
      ((Int.natAbs a : ℕ) : ZMod 7) ^ 2 := by
    rw [natAbs_cast_sq_eq, natAbs_cast_sq_eq]
    dsimp [n, a, q]
    push_cast
    rw [hsnd]
    ring
  have hm :
      ((Int.natAbs m : ℕ) : ZMod 7) ^ 7 =
        ((Int.natAbs m : ℕ) : ZMod 7) :=
    ZMod.pow_card _
  change
    ((Int.natAbs d : ℕ) : ZMod 7) *
        ((Int.natAbs e : ℕ) : ZMod 7) =
      ((Int.natAbs a : ℕ) : ZMod 7) *
        ((Int.natAbs n : ℕ) : ZMod 7) *
        ((Int.natAbs m : ℕ) : ZMod 7) ^ 7 at hprod
  rw [hm] at hprod
  have ha0 : ((Int.natAbs a : ℕ) : ZMod 7) ≠ 0 := by
    intro hz
    exact q.innerFst_not_seven_dvd
      (Int.natAbs_dvd_natAbs.mp (by
        simpa using (ZMod.natCast_eq_zero_iff (Int.natAbs a) 7).mp hz))
  have hn0 : ((Int.natAbs n : ℕ) : ZMod 7) ≠ 0 := by
    intro hz
    exact q.innerFst_add_innerSnd_not_seven_dvd
      (Int.natAbs_dvd_natAbs.mp (by
        simpa using (ZMod.natCast_eq_zero_iff (Int.natAbs n) 7).mp hz))
  have he0 : ((Int.natAbs e : ℕ) : ZMod 7) ≠ 0 := by
    intro hz
    exact p.signedDepth.quotientRoot_not_seven_dvd
      (Int.natAbs_dvd_natAbs.mp (by
        simpa using (ZMod.natCast_eq_zero_iff (Int.natAbs e) 7).mp hz))
  simp only [← Int.natCast_natAbs]
  change
    (((Int.natAbs d : ℕ) : ZMod 7) /
        ((Int.natAbs e : ℕ) : ZMod 7)) /
        ((Int.natAbs n : ℕ) : ZMod 7) ^ 3 =
      ((Int.natAbs m : ℕ) : ZMod 7) /
        ((Int.natAbs a : ℕ) : ZMod 7)
  exact absoluteSlope_algebra _ _ _ _ _ he hn hprod ha0 hn0 he0

end RamifiedSignedRootRoutingPacket

namespace RamifiedFusionRoutingAuditPacket

theorem cycleRatio_square_div_eq_fusionSlope_sq
    (p : RamifiedFusionRoutingAuditPacket) :
    (((p.routing.cycleRatio12 / p.routing.cycleRatio23 :
        (ZMod 7)ˣ) : ZMod 7) ^ 2) =
      p.jet.fusionSlope ^ 2 := by
  rw [p.routing.cycleRatio_div_eq_absoluteFusionSlope]
  simp only [RamifiedSignedRootRoutingPacket.absoluteFusionSlopeUnit, natAbsUnit, Nat.cast_natAbs,
    Int.reduceNeg, Units.val_div_eq_div_val, Units.val_mk0,
    RamifiedPairedThetaRootJetPacket.fusionSlope]
  rw [div_pow, div_pow]
  rw [abs_cast_sq_eq, abs_cast_sq_eq, p.signedDepth_eq]

end RamifiedFusionRoutingAuditPacket


end

end DkMath.FLT.Seven
