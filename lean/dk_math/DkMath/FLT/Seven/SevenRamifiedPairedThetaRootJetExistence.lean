/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJet
import DkMath.FLT.Seven.SevenRamifiedThetaJetLifting

#print "file: DkMath.FLT.Seven.SevenRamifiedPairedThetaRootJetExistence"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

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

/-- Construct the paired theta-root jet from the signed-root depth packet.

This theorem is kept in a separate existence module because its proof uses the
large theta-power and triangular-lifting calculations.  The structural packet
and its FUSION API remain available without importing this branch.
-/
theorem RamifiedSignedRootDepthPacket.nonempty_pairedThetaRootJet
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

end

end DkMath.FLT.Seven
