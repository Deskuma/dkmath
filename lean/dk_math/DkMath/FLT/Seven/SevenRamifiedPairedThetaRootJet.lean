/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedThetaJetLifting
import DkMath.FLT.Seven.SevenRamifiedSignedRootDepth
import DkMath.FLT.Seven.SevenRamifiedFusionUnitSector

#print "file: DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJet"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- One exact algebraic root, normalized as a controlled theta jet. -/
structure RamifiedThetaRootJetPacket
    (a m sign : ℤ) (sourceRoot : SevenRealCubicInt) : Type where
  root : SevenRealCubicInt
  root_eq_source : root = sourceRoot
  thetaConst : ℤ
  thetaLinearCore : ℤ
  thetaSquareCore : ℤ
  root_eq :
    root = ofThetaCoordinates thetaConst
      (7 ^ 3 * thetaLinearCore) (7 ^ 6 * thetaSquareCore)
  thetaConst_not_seven_dvd : ¬(7 : ℤ) ∣ thetaConst
  thetaLinearCore_not_seven_dvd : ¬(7 : ℤ) ∣ thetaLinearCore
  thetaSquareCore_not_seven_dvd : ¬(7 : ℤ) ∣ thetaSquareCore
  thetaConst_modSeven : (thetaConst : ZMod 7) = (a : ZMod 7)
  thetaLinearCore_modSeven :
    (thetaLinearCore : ZMod 7) = (sign : ZMod 7) * (m : ZMod 7)
  quadraticJet_modSeven :
    ((thetaConst * thetaSquareCore +
      3 * thetaLinearCore ^ 2 : ℤ) : ZMod 7) = 0

private theorem nonempty_thetaRootJet
    {a m sign : ℤ} (root : SevenRealCubicInt)
    (ha : ¬(7 : ℤ) ∣ a) (hm : ¬(7 : ℤ) ∣ m)
    (hsign : sign = 1 ∨ sign = -1)
    (hconst : (thetaConstInt root : ZMod 7) = (a : ZMod 7))
    (hlinear :
      thetaLinearInt (root ^ 7) = sign * 7 ^ 4 * m ^ 7)
    (hsquare : thetaSquareInt (root ^ 7) = 0) :
    Nonempty (RamifiedThetaRootJetPacket a m sign root) := by
  let A := thetaConstInt root
  let B := thetaLinearInt root
  let C := thetaSquareInt root
  have hA : ¬(7 : ℤ) ∣ A := by
    intro h
    have hzero : (A : ZMod 7) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr h
    rw [hconst] at hzero
    exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hzero)
  have hG :
      seventhThetaLinearQuotient A B C =
        sign * 7 ^ 3 * m ^ 7 := by
    have hcoord := thetaLinear_pow_seven A B C
    rw [← theta_coordinate_decomposition root] at hcoord
    apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
    calc
      7 * seventhThetaLinearQuotient A B C =
          thetaLinearInt (root ^ 7) := hcoord.symm
      _ = sign * 7 ^ 4 * m ^ 7 := hlinear
      _ = 7 * (sign * 7 ^ 3 * m ^ 7) := by ring
  have hH : seventhThetaSquareQuotient A B C = 0 := by
    have hcoord := thetaSquare_pow_seven A B C
    rw [← theta_coordinate_decomposition root] at hcoord
    apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
    calc
      7 * seventhThetaSquareQuotient A B C =
          thetaSquareInt (root ^ 7) := hcoord.symm
      _ = 0 := hsquare
      _ = 7 * 0 := by ring
  rcases nonempty_triangularThetaJetExact hA hm hsign hG hH with
    ⟨jet⟩
  exact ⟨{
    root := root
    root_eq_source := rfl
    thetaConst := A
    thetaLinearCore := jet.linearCore
    thetaSquareCore := jet.squareCore
    root_eq := by
      rw [theta_coordinate_decomposition root]
      simp only [A, B, C, jet.linear_eq, jet.square_eq]
    thetaConst_not_seven_dvd := hA
    thetaLinearCore_not_seven_dvd := jet.linearCore_not_seven_dvd
    thetaSquareCore_not_seven_dvd := jet.squareCore_not_seven_dvd
    thetaConst_modSeven := hconst
    thetaLinearCore_modSeven := jet.linearCore_modSeven
    quadraticJet_modSeven := jet.quadraticJet_modSeven }⟩

/-- FUSION-002 output: the exact left and right roots occupy opposite
linear theta-jet sectors with a common quadratic correction sector. -/
structure RamifiedPairedThetaRootJetPacket : Type where
  signedDepth : RamifiedSignedRootDepthPacket
  left : RamifiedThetaRootJetPacket
    ((signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit
      ).normPacket.quadratic.innerRoot.fst)
    ((signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit
      ).normPacket.innerSndRoot) (-1)
    signedDepth.balanced.axisDrop.depthLedger.exactPower.leftRoot
  right : RamifiedThetaRootJetPacket
    ((signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit
      ).normPacket.quadratic.innerRoot.fst)
    ((signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit
      ).normPacket.innerSndRoot) 1
    signedDepth.balanced.axisDrop.depthLedger.exactPower.rightRoot
  left_root_eq :
    left.root =
      signedDepth.balanced.axisDrop.depthLedger.exactPower.leftRoot
  right_root_eq :
    right.root =
      signedDepth.balanced.axisDrop.depthLedger.exactPower.rightRoot
  squareCores_modSeven_eq :
    (left.thetaSquareCore : ZMod 7) =
      (right.thetaSquareCore : ZMod 7)

namespace RamifiedSignedRootDepthPacket

theorem nonempty_pairedThetaRootJet
    (p : RamifiedSignedRootDepthPacket) :
    Nonempty RamifiedPairedThetaRootJetPacket := by
  let exact := p.balanced.axisDrop.depthLedger.exactPower
  let q := exact.upToUnit.normPacket
  let a := q.quadratic.innerRoot.fst
  let n := q.quadratic.innerRoot.snd
  let m := q.innerSndRoot
  have hn0 : (n : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr q.innerSnd_seven_dvd
  have hleftConst :
      (thetaConstInt exact.leftRoot : ZMod 7) = (a : ZMod 7) := by
    have h := congrArg thetaConstModSeven exact.leftSource_eq
    rw [thetaConstModSeven_pow, ZMod.pow_card] at h
    have hs :
        thetaConstModSeven (leftSource a n) = (a : ZMod 7) := by
      change ((a + 3 * (-n) + 9 * 0 : ℤ) : ZMod 7) = (a : ZMod 7)
      push_cast
      rw [hn0]
      ring
    exact h.symm.trans hs
  have hrightConst :
      (thetaConstInt exact.rightRoot : ZMod 7) = (a : ZMod 7) := by
    have h := congrArg thetaConstModSeven exact.rightSource_eq
    rw [thetaConstModSeven_pow, ZMod.pow_card] at h
    have hs :
        thetaConstModSeven (rightSource a n) = (a : ZMod 7) := by
      change (((a + n) + 3 * n + 9 * 0 : ℤ) : ZMod 7) = (a : ZMod 7)
      push_cast
      rw [hn0]
      ring
    exact h.symm.trans hs
  have hleftLinear :
      thetaLinearInt (exact.leftRoot ^ 7) =
        (-1 : ℤ) * 7 ^ 4 * m ^ 7 := by
    rw [← exact.leftSource_eq]
    rw [(leftSource_thetaCoordinates a n).2.1]
    dsimp [n, m]
    rw [q.innerSnd_eq]
    ring
  have hrightLinear :
      thetaLinearInt (exact.rightRoot ^ 7) =
        (1 : ℤ) * 7 ^ 4 * m ^ 7 := by
    rw [← exact.rightSource_eq]
    rw [(rightSource_thetaCoordinates a n).2.1]
    dsimp [n, m]
    rw [q.innerSnd_eq]
    ring
  have hleftSquare :
      thetaSquareInt (exact.leftRoot ^ 7) = 0 := by
    rw [← exact.leftSource_eq]
    exact (leftSource_thetaCoordinates a n).2.2
  have hrightSquare :
      thetaSquareInt (exact.rightRoot ^ 7) = 0 := by
    rw [← exact.rightSource_eq]
    exact (rightSource_thetaCoordinates a n).2.2
  rcases nonempty_thetaRootJet exact.leftRoot
      q.innerFst_not_seven_dvd q.innerSndRoot_not_seven_dvd
      (Or.inr rfl) hleftConst hleftLinear hleftSquare with ⟨left⟩
  rcases nonempty_thetaRootJet exact.rightRoot
      q.innerFst_not_seven_dvd q.innerSndRoot_not_seven_dvd
      (Or.inl rfl) hrightConst hrightLinear hrightSquare with ⟨right⟩
  have hsquare :
      (left.thetaSquareCore : ZMod 7) =
        (right.thetaSquareCore : ZMod 7) := by
    have hleft := left.quadraticJet_modSeven
    have hright := right.quadraticJet_modSeven
    push_cast at hleft hright
    rw [left.thetaConst_modSeven,
      left.thetaLinearCore_modSeven] at hleft
    rw [right.thetaConst_modSeven,
      right.thetaLinearCore_modSeven] at hright
    norm_num at hleft hright
    have ha0 : (a : ZMod 7) ≠ 0 := by
      intro hz
      exact q.innerFst_not_seven_dvd
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz)
    apply mul_left_cancel₀ ha0
    linear_combination hleft - hright
  exact ⟨{
    signedDepth := p
    left := left
    right := right
    left_root_eq := left.root_eq_source
    right_root_eq := right.root_eq_source
    squareCores_modSeven_eq := hsquare }⟩

end RamifiedSignedRootDepthPacket

namespace RamifiedPairedThetaRootJetPacket

theorem linearCore_gap_modSeven
    (p : RamifiedPairedThetaRootJetPacket) :
    ((p.right.thetaLinearCore -
        p.left.thetaLinearCore : ℤ) : ZMod 7) =
      2 *
        (p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit
          ).normPacket.innerSndRoot := by
  push_cast
  rw [p.right.thetaLinearCore_modSeven,
    p.left.thetaLinearCore_modSeven]
  norm_num
  ring

theorem squareCore_gap_modSeven
    (p : RamifiedPairedThetaRootJetPacket) :
    ((p.right.thetaSquareCore -
        p.left.thetaSquareCore : ℤ) : ZMod 7) = 0 := by
  push_cast
  rw [← p.squareCores_modSeven_eq]
  ring

private theorem thetaResidue_of_exact_gap_coordinates
    (A B C : ℤ) (g : SevenRealCubicInt)
    (h :
      ofThetaCoordinates A (7 ^ 3 * B) (7 ^ 6 * C) =
        eisensteinAxis ^ 10 * g) :
    thetaResidue g = -(B : ZMod 7) := by
  rcases g with ⟨x, y, z⟩
  have hlin := congrArg thetaLinearInt h
  norm_num [thetaLinearInt, ofThetaCoordinates,
    eisensteinAxis_sq_coordinates, eisensteinAxis,
    SevenRealCubicInt.mul, pow_succ] at hlin ⊢
  ring_nf at hlin
  have hB : B = 1378 * x - 1165 * y + 901 * z := by omega
  change thetaConstModSeven { fst := x, snd := y, thd := z } = -↑B
  simp only [thetaConstModSeven]
  rw [← Int.cast_neg, ← sub_eq_zero, ← Int.cast_sub]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr
  refine ⟨197 * x - 166 * y + 130 * z, ?_⟩
  rw [hB]
  ring

/-- The exact leading theta residue of the depth-ten algebraic root gap.
This is stronger than the previously known nondivisibility of `gapCore`. -/
theorem gapCore_thetaResidue_eq
    (p : RamifiedPairedThetaRootJetPacket) :
    thetaResidue
        p.signedDepth.balanced.axisDrop.depthLedger.gapCore =
      -2 *
        (p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit
          ).normPacket.innerSndRoot := by
  let d := p.signedDepth.balanced.axisDrop.depthLedger
  have hcoordinates :
      ofThetaCoordinates
          (p.right.thetaConst - p.left.thetaConst)
          (7 ^ 3 *
            (p.right.thetaLinearCore - p.left.thetaLinearCore))
          (7 ^ 6 *
            (p.right.thetaSquareCore - p.left.thetaSquareCore)) =
        eisensteinAxis ^ 10 * d.gapCore := by
    calc
      _ = p.right.root - p.left.root := by
        rw [p.right.root_eq, p.left.root_eq]
        ext <;>
          norm_num [ofThetaCoordinates,
            eisensteinAxis_sq_coordinates] <;> ring
      _ = d.exactPower.rightRoot - d.exactPower.leftRoot := by
        rw [p.right_root_eq, p.left_root_eq]
      _ = d.rootGap := d.rootGap_def.symm
      _ = eisensteinAxis ^ 10 * d.gapCore := d.rootGap_eq
  have hlead :=
    thetaResidue_of_exact_gap_coordinates
      (p.right.thetaConst - p.left.thetaConst)
      (p.right.thetaLinearCore - p.left.thetaLinearCore)
      (p.right.thetaSquareCore - p.left.thetaSquareCore)
      d.gapCore hcoordinates
  rw [hlead, p.linearCore_gap_modSeven]
  ring

theorem left_not_sourcePlane
    (p : RamifiedPairedThetaRootJetPacket) :
    ¬IsSourcePlane p.left.root := by
  intro hplane
  have hsquare : thetaSquareInt p.left.root = 0 :=
    (isSourcePlane_iff_thetaSquareInt_eq_zero p.left.root).mp hplane
  rw [p.left.root_eq] at hsquare
  norm_num [thetaSquareInt, ofThetaCoordinates,
    eisensteinAxis_sq_coordinates] at hsquare
  have hcore : p.left.thetaSquareCore = 0 := by
    apply mul_left_cancel₀ (by norm_num : (7 ^ 6 : ℤ) ≠ 0)
    simpa using hsquare
  exact p.left.thetaSquareCore_not_seven_dvd
    (by rw [hcore]; exact dvd_zero 7)

theorem right_not_sourcePlane
    (p : RamifiedPairedThetaRootJetPacket) :
    ¬IsSourcePlane p.right.root := by
  intro hplane
  have hsquare : thetaSquareInt p.right.root = 0 :=
    (isSourcePlane_iff_thetaSquareInt_eq_zero p.right.root).mp hplane
  rw [p.right.root_eq] at hsquare
  norm_num [thetaSquareInt, ofThetaCoordinates,
    eisensteinAxis_sq_coordinates] at hsquare
  have hcore : p.right.thetaSquareCore = 0 := by
    apply mul_left_cancel₀ (by norm_num : (7 ^ 6 : ℤ) ≠ 0)
    simpa using hsquare
  exact p.right.thetaSquareCore_not_seven_dvd
    (by rw [hcore]; exact dvd_zero 7)

/-- The common projective FUSION slope `m/a`. -/
def fusionSlope (p : RamifiedPairedThetaRootJetPacket) : ZMod 7 :=
  let q :=
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  (q.innerSndRoot : ZMod 7) /
    (q.quadratic.innerRoot.fst : ZMod 7)

theorem fusionSlope_eq_gapRoot_div_cube
    (p : RamifiedPairedThetaRootJetPacket) :
    p.fusionSlope =
      (p.signedDepth.gapRoot : ZMod 7) /
        ((p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit
          ).normPacket.quadratic.innerRoot.fst : ZMod 7) ^ 3 := by
  let q :=
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  have ha0 : (q.quadratic.innerRoot.fst : ZMod 7) ≠ 0 := by
    intro hz
    exact q.innerFst_not_seven_dvd
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz)
  rw [p.signedDepth.gapRoot_modSeven_eq]
  dsimp [fusionSlope, q]
  field_simp

theorem right_normalizedLinearJet_eq_slope
    (p : RamifiedPairedThetaRootJetPacket) :
    (p.right.thetaLinearCore : ZMod 7) /
        (p.right.thetaConst : ZMod 7) =
      p.fusionSlope := by
  rw [p.right.thetaLinearCore_modSeven,
    p.right.thetaConst_modSeven]
  norm_num [fusionSlope]

theorem left_normalizedLinearJet_eq_neg_slope
    (p : RamifiedPairedThetaRootJetPacket) :
    (p.left.thetaLinearCore : ZMod 7) /
        (p.left.thetaConst : ZMod 7) =
      -p.fusionSlope := by
  rw [p.left.thetaLinearCore_modSeven,
    p.left.thetaConst_modSeven]
  norm_num [fusionSlope]
  ring

theorem right_normalizedQuadraticJet_eq
    (p : RamifiedPairedThetaRootJetPacket) :
    (p.right.thetaSquareCore : ZMod 7) /
        (p.right.thetaConst : ZMod 7) =
      -3 * p.fusionSlope ^ 2 := by
  have h := p.right.quadraticJet_modSeven
  push_cast at h
  rw [p.right.thetaConst_modSeven,
    p.right.thetaLinearCore_modSeven] at h
  norm_num at h
  let q :=
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  have ha0 : (q.quadratic.innerRoot.fst : ZMod 7) ≠ 0 := by
    intro hz
    exact q.innerFst_not_seven_dvd
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz)
  rw [p.right.thetaConst_modSeven]
  dsimp [q] at ha0
  dsimp [fusionSlope, q]
  rw [div_eq_iff ha0]
  field_simp [ha0]
  linear_combination h

theorem left_normalizedQuadraticJet_eq
    (p : RamifiedPairedThetaRootJetPacket) :
    (p.left.thetaSquareCore : ZMod 7) /
        (p.left.thetaConst : ZMod 7) =
      -3 * p.fusionSlope ^ 2 := by
  rw [p.left.thetaConst_modSeven,
    p.squareCores_modSeven_eq,
    ← p.right.thetaConst_modSeven]
  exact p.right_normalizedQuadraticJet_eq

theorem fusionSlope_ne_zero
    (p : RamifiedPairedThetaRootJetPacket) :
    p.fusionSlope ≠ 0 := by
  let q :=
    p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  have hm0 : (q.innerSndRoot : ZMod 7) ≠ 0 := by
    intro hz
    exact q.innerSndRoot_not_seven_dvd
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz)
  have ha0 : (q.quadratic.innerRoot.fst : ZMod 7) ≠ 0 := by
    intro hz
    exact q.innerFst_not_seven_dvd
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz)
  dsimp [fusionSlope, q]
  exact div_ne_zero hm0 ha0

end RamifiedPairedThetaRootJetPacket

/-- Canonical `2 × 3` address carried by a nonzero modulo-seven slope. -/
structure SevenUnitGridAddress where
  slope : ZMod 7
  rowComponent : ZMod 7
  columnComponent : ZMod 7
  row_eq : rowComponent = slope ^ 3
  column_eq : columnComponent = slope ^ 2

namespace SevenUnitGridAddress

def ofSlope (s : ZMod 7) : SevenUnitGridAddress :=
  ⟨s, s ^ 3, s ^ 2, rfl, rfl⟩

theorem row_div_column_eq_slope
    (a : SevenUnitGridAddress) (ha : a.slope ≠ 0) :
    a.rowComponent / a.columnComponent = a.slope := by
  rw [a.row_eq, a.column_eq]
  field_simp

end SevenUnitGridAddress

namespace RamifiedPairedThetaRootJetPacket

def unitGridAddress
    (p : RamifiedPairedThetaRootJetPacket) : SevenUnitGridAddress :=
  SevenUnitGridAddress.ofSlope p.fusionSlope

theorem unitGridAddress_reconstructs_slope
    (p : RamifiedPairedThetaRootJetPacket) :
    p.unitGridAddress.rowComponent /
        p.unitGridAddress.columnComponent =
      p.fusionSlope :=
  p.unitGridAddress.row_div_column_eq_slope p.fusionSlope_ne_zero

end RamifiedPairedThetaRootJetPacket


end

end DkMath.FLT.Seven
